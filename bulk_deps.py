#!/usr/bin/env python3
"""
bulk_deps.py — Batch extraction of theorem dependencies using extract_deps.

Three subcommands:

  theory    — Extract deps from a single .thy file (no theorem names needed).
  afp       — Bulk export for an AFP-like directory structure, grouped by session.
  isabelle  — Bulk export for Isabelle built-in sessions from src/ components.

Examples:
  uv run bulk_deps.py theory \\
    --session HOL-Examples \\
    --theory ~/Isabelle2025/src/HOL/Examples/Ackermann.thy \\
    --out /tmp/test_out/Ackermann.toml.zst \\
    --isabelle-home ~/Isabelle2025

  uv run bulk_deps.py afp \\
    --afp $AFP \\
    --out-dir /tmp/deps_out \\
    --sessions "Completeness" \\
    --compress \\
    --isabelle-home ~/Isabelle2025 \\
    --verbose

  uv run bulk_deps.py isabelle HOL \\
    --out-dir /tmp/isabelle_deps \\
    --isabelle-home ~/Isabelle2025 \\
    --sessions "HOL-Examples" \\
    --verbose
"""

from __future__ import annotations

import argparse
import fnmatch
import logging
import os
import re
import shutil
import subprocess
import sys
import tempfile
from concurrent.futures import ProcessPoolExecutor, as_completed
from pathlib import Path

import zstandard as zstd
from isabelle_client import get_isabelle_client, start_isabelle_server  # type: ignore

from dep_extract import _iter_messages, read_theory_name
from session import (
    build_dir_session_map,
    glob_theory_file_with_session,
    parse_root_file,
)
from thy_filter import has_supported_commands

log = logging.getLogger(__name__)

WRAPPER_THEORY_NAME = "Deps_Wrapper"


# ---------------------------------------------------------------------------
# Filesystem helpers
# ---------------------------------------------------------------------------
def _safe(s: str) -> str:
    """Replace characters unsafe in filenames with underscores."""
    return re.sub(r"[#/ ]", "_", s)


# ---------------------------------------------------------------------------
# Isabelle / AFP version detection
# ---------------------------------------------------------------------------
def _setup_isabelle_path(isabelle_home: Path | None) -> None:
    """Prepend isabelle_home/bin to PATH so all 'isabelle' subprocess calls resolve correctly."""
    if isabelle_home:
        bin_dir = str(isabelle_home / "bin")
        current = os.environ.get("PATH", "")
        if bin_dir not in current.split(os.pathsep):
            os.environ["PATH"] = bin_dir + os.pathsep + current


def get_isabelle_id(isabelle_home: Path | None = None) -> str:
    """Return the Isabelle version string from `isabelle version`."""
    bin_ = str(isabelle_home / "bin" / "isabelle") if isabelle_home else "isabelle"
    try:
        r = subprocess.run(
            [bin_, "version"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if r.returncode == 0 and r.stdout.strip():
            return r.stdout.strip()
    except Exception:
        pass
    return "unknown"


def detect_afp_version(afp_root: Path, override: str | None) -> str:
    """Detect AFP version string from $AFP/etc/version (VERSION=... line)."""
    if override:
        return override
    version_file = afp_root / "etc" / "version"
    if version_file.exists():
        try:
            for line in version_file.read_text(encoding="utf-8").splitlines():
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                if line.startswith("VERSION="):
                    v = line[len("VERSION=") :].strip()
                    if v:
                        return v
        except Exception:
            pass
    return "unknown"


# ---------------------------------------------------------------------------
# Wrapper theory construction
# ---------------------------------------------------------------------------


def write_wrapper_theory(
    wrapper_dir: Path,
    session_name: str,
    theory_name: str,
    theory_path: Path,
    out_filename: str,
    exportdeps_dir: Path,
) -> None:
    """Write a self-contained Deps_Wrapper.thy that calls extract_deps on theory_path.

    Loads BackwardCompatibleAPI.ML, ExportDeps.ML, and ExtractFacts.ML directly
    via ML_file instead of importing ExportDeps.ExtractFacts.  This avoids
    cross-lineage theory import conflicts (e.g., HOL vs ZF application syntax).
    """
    target_import = f"{session_name}.{theory_name}"
    backcomp_ml = (exportdeps_dir / "BackwardCompatibleAPI.ML").resolve()
    exportdeps_ml = (exportdeps_dir / "ExportDeps.ML").resolve()
    extractfacts_ml = (exportdeps_dir / "ExtractFacts.ML").resolve()
    body = (
        f"theory {WRAPPER_THEORY_NAME}\n"
        f'  imports "{target_import}"\n'
        f'  keywords "extract_facts" :: diag and "extract_deps" :: diag\n'
        f"begin\n"
        f"\n"
        f'ML_file "{backcomp_ml}"\n'
        f'ML_file "{exportdeps_ml}"\n'
        f'ML_file "{extractfacts_ml}"\n'
        f"\n"
        f'extract_deps "{theory_path}" in "{out_filename}"\n'
        f"\n"
        f"end\n"
    )
    (wrapper_dir / f"{WRAPPER_THEORY_NAME}.thy").write_text(body, encoding="utf-8")


# ---------------------------------------------------------------------------
# Output path computation
# ---------------------------------------------------------------------------


def output_path_for(
    out_dir: Path,
    isabelle_id: str,
    session_name: str,
    theory_name: str,
    compress: bool,
) -> Path:
    """Compute the canonical output path for one theory."""
    ext = ".toml.zst" if compress else ".toml"
    return (
        out_dir
        / _safe(isabelle_id)
        / _safe(session_name)
        / f"{_safe(theory_name)}{ext}"
    )


# ---------------------------------------------------------------------------
# Core: run extract_deps for one theory within an open Isabelle session
# ---------------------------------------------------------------------------


def run_extract_deps(
    isabelle,
    session_id: str,
    session_name: str,
    theory_name: str,
    theory_path: Path,
    out_path: Path,
    compress: bool,
    verbose: bool,
    exportdeps_dir: Path,
) -> bool:
    """Run extract_deps for one theory.  Returns True if output was produced."""
    # Always produce plain .toml from ML; Python handles optional compression.
    out_filename = "deps_out.toml"

    with tempfile.TemporaryDirectory(prefix="isabelle-bulk-") as tmp:
        tmp_dir = Path(tmp).resolve()
        write_wrapper_theory(
            tmp_dir,
            session_name,
            theory_name,
            theory_path,
            out_filename,
            exportdeps_dir,
        )

        try:
            use_resps = isabelle.use_theories(
                theories=[WRAPPER_THEORY_NAME],
                master_dir=str(tmp_dir),
                session_id=session_id,
            )
            if verbose:
                for m in _iter_messages(use_resps):
                    log.debug("[use] %s", m)
        except Exception as e:
            log.error("use_theories failed for %s: %s", theory_path.name, e)
            return False

        produced = tmp_dir / out_filename
        if not produced.exists():
            return False

        out_path.parent.mkdir(parents=True, exist_ok=True)
        if compress:
            cctx = zstd.ZstdCompressor()
            with open(produced, "rb") as f_in, open(out_path, "wb") as f_out:
                cctx.copy_stream(f_in, f_out)
        else:
            shutil.copyfile(produced, out_path)
        return True


# ---------------------------------------------------------------------------
# Session-level worker — one Isabelle server per call, used by afp/isabelle subcommands
# ---------------------------------------------------------------------------
def _setup_logging(
    log_file: Path | None,
    process_name: str,
    verbose: bool,
    also_console: bool = False,
) -> logging.Logger:
    """Configure logging for a process with optional file output."""
    logger = logging.getLogger(process_name)
    logger.setLevel(logging.DEBUG if verbose else logging.INFO)
    logger.handlers.clear()  # Remove any existing handlers

    # Format with timestamp and process name
    formatter = logging.Formatter(
        "%(asctime)s %(levelname)s %(message)s", datefmt="%H:%M:%S"
    )

    # Add file handler if log_file specified
    if log_file:
        log_file.parent.mkdir(parents=True, exist_ok=True)
        file_handler = logging.FileHandler(log_file, mode="a", encoding="utf-8")
        file_handler.setFormatter(formatter)
        logger.addHandler(file_handler)

    # Optional console output
    if also_console:
        console_handler = logging.StreamHandler()
        console_handler.setFormatter(formatter)
        logger.addHandler(console_handler)

    return logger


def _session_worker(
    session_name: str,
    theory_paths: list[str],
    dirs: list[str],
    out_dir_str: str,
    isabelle_id: str,
    compress: bool,
    skip_existing: bool,
    verbose: bool,
    log_dir_str: str | None,
    exportdeps_dir_str: str,
    isabelle_home_str: str | None = None,
) -> dict:
    """Process all theories in one session.  Designed to run in a subprocess."""
    # Ensure the correct isabelle binary is on PATH in this (sub)process.
    _setup_isabelle_path(Path(isabelle_home_str) if isabelle_home_str else None)

    # Set up logging for this subprocess
    log_file = None
    if log_dir_str:
        log_dir = Path(log_dir_str)
        # Create subdirectory for Isabelle version
        isabelle_dir = log_dir / _safe(isabelle_id)
        log_file = isabelle_dir / f"{_safe(session_name)}.log"

    _log = _setup_logging(log_file, session_name, verbose, also_console=False)

    out_dir = Path(out_dir_str)
    exportdeps_dir = Path(exportdeps_dir_str)
    success = skipped = no_cmds = 0
    errors: list[str] = []

    server_info, _proc = start_isabelle_server()
    isabelle = get_isabelle_client(server_info)

    try:
        _log.info("session_start (dirs=%d)", len(dirs))
        start_resps = isabelle.session_start(
            session=session_name,
            dirs=dirs,
            verbose=verbose,
        )
        if verbose:
            for m in _iter_messages(start_resps):
                _log.debug("[start] %s", m)
        session_id = start_resps[-1].response_body.session_id
        _log.info("session_id=%s", session_id)

        for thy_str in theory_paths:
            thy_path = Path(thy_str)

            try:
                thy_name = read_theory_name(thy_path)
            except Exception as e:
                _log.warning("Cannot read theory name from %s: %s", thy_path.name, e)
                errors.append(f"{thy_path}: {e}")
                continue

            out_path = output_path_for(
                out_dir, isabelle_id, session_name, thy_name, compress
            )

            if skip_existing and out_path.exists():
                _log.debug("skip existing: %s", out_path.name)
                skipped += 1
                continue

            if not has_supported_commands(thy_path):
                _log.debug("skip (no supported commands): %s", thy_path.name)
                no_cmds += 1
                continue

            _log.info("processing %s", thy_path.name)
            try:
                ok = run_extract_deps(
                    isabelle,
                    session_id,
                    session_name,
                    thy_name,
                    thy_path,
                    out_path,
                    compress,
                    verbose,
                    exportdeps_dir,
                )
            except Exception as e:
                _log.error("Error processing %s: %s", thy_path.name, e)
                errors.append(str(thy_path))
                continue

            if ok:
                success += 1
                _log.info("wrote: %s", out_path)
            else:
                _log.warning("No output produced for %s", thy_path.name)
                errors.append(str(thy_path))

    except Exception as e:
        _log.error("Session failed: %s", e)
        errors.append(f"<session-start>: {e}")
    finally:
        try:
            isabelle.shutdown()
        except Exception:
            pass

    _log.info(
        "done: success=%d  skipped=%d  no_cmds=%d  errors=%d",
        success,
        skipped,
        no_cmds,
        len(errors),
    )
    return {
        "session": session_name,
        "success": success,
        "skipped": skipped,
        "no_cmds": no_cmds,
        "errors": errors,
    }


# ---------------------------------------------------------------------------
# Isabelle home detection
# ---------------------------------------------------------------------------


def get_isabelle_home() -> Path | None:
    """Return ISABELLE_HOME via `isabelle getenv`."""
    try:
        r = subprocess.run(
            ["isabelle", "getenv", "ISABELLE_HOME"],
            capture_output=True,
            text=True,
            timeout=30,
        )
        if r.returncode == 0:
            for line in r.stdout.splitlines():
                if line.startswith("ISABELLE_HOME="):
                    v = line[len("ISABELLE_HOME=") :].strip()
                    if v:
                        return Path(v)
    except Exception:
        pass
    return None


# ---------------------------------------------------------------------------
# Shared dispatch helper for afp / isabelle subcommands
# ---------------------------------------------------------------------------


def _run_sessions(
    by_session: dict[str, list[str]],
    dirs: list[str],
    exportdeps_dir: Path,
    out_dir: Path,
    isabelle_id: str,
    compress: bool,
    skip_existing: bool,
    jobs: int,
    verbose: bool,
    log_dir: Path | None,
    isabelle_home: Path | None = None,
) -> tuple[int, int, int, int]:
    """Dispatch _session_worker for all sessions; return (success, skipped, no_cmds, errors)."""
    total_success = total_skipped = total_no_cmds = total_errors = 0
    log_dir_str = str(log_dir) if log_dir else None
    exportdeps_dir_str = str(exportdeps_dir)
    isabelle_home_str = str(isabelle_home) if isabelle_home else None

    if jobs <= 1:
        for sname, thy_paths in by_session.items():
            result = _session_worker(
                sname,
                thy_paths,
                dirs,
                str(out_dir),
                isabelle_id,
                compress,
                skip_existing,
                verbose,
                log_dir_str,
                exportdeps_dir_str,
                isabelle_home_str,
            )
            total_success += result["success"]
            total_skipped += result["skipped"]
            total_no_cmds += result["no_cmds"]
            total_errors += len(result["errors"])
            if result["errors"]:
                log.warning("[%s] %d error(s)", sname, len(result["errors"]))
    else:
        with ProcessPoolExecutor(max_workers=jobs) as executor:
            futures = {
                executor.submit(
                    _session_worker,
                    sname,
                    thy_paths,
                    dirs,
                    str(out_dir),
                    isabelle_id,
                    compress,
                    skip_existing,
                    verbose,
                    log_dir_str,
                    exportdeps_dir_str,
                    isabelle_home_str,
                ): sname
                for sname, thy_paths in by_session.items()
            }
            for future in as_completed(futures):
                sname = futures[future]
                try:
                    result = future.result()
                    total_success += result["success"]
                    total_skipped += result["skipped"]
                    total_no_cmds += result["no_cmds"]
                    total_errors += len(result["errors"])
                    if result["errors"]:
                        log.warning("[%s] %d error(s)", sname, len(result["errors"]))
                except Exception as e:
                    log.error("[%s] worker crashed: %s", sname, e)
                    total_errors += 1
    return total_success, total_skipped, total_no_cmds, total_errors


# ---------------------------------------------------------------------------
# theory subcommand
# ---------------------------------------------------------------------------


def cmd_theory(args) -> int:
    theory_path = Path(args.theory).resolve()
    if not theory_path.exists():
        log.error("Theory file not found: %s", theory_path)
        return 2

    out_path = Path(args.out).resolve()
    compress = args.out.endswith(".zst")

    isabelle_home = (
        Path(args.isabelle_home).resolve() if args.isabelle_home else None
    )
    _setup_isabelle_path(isabelle_home)

    script_dir = Path(__file__).resolve().parent
    exportdeps_dir = (
        Path(args.exportdeps_dir).resolve()
        if args.exportdeps_dir
        else script_dir / "ExportDeps"
    )
    dirs = [str(exportdeps_dir)] + list(args.dir)

    try:
        theory_name = read_theory_name(theory_path)
    except ValueError as e:
        log.error("%s", e)
        return 2

    server_info, _proc = start_isabelle_server()
    isabelle = get_isabelle_client(server_info)

    try:
        log.info("session_start(session=%s)", args.session)
        start_resps = isabelle.session_start(
            session=args.session,
            dirs=dirs,
            verbose=args.verbose,
        )
        if args.verbose:
            for m in _iter_messages(start_resps):
                log.debug("[start] %s", m)
        session_id = start_resps[-1].response_body.session_id
        log.info("session_id=%s", session_id)

        ok = run_extract_deps(
            isabelle,
            session_id,
            args.session,
            theory_name,
            theory_path,
            out_path,
            compress,
            args.verbose,
            exportdeps_dir,
        )

        if not ok:
            log.error(
                "No output produced. Check --session, --dir, and theory validity. "
                "Re-run with --verbose for Isabelle diagnostics."
            )
            return 3

        print(f"[ok] wrote: {out_path}")
        return 0

    finally:
        try:
            isabelle.shutdown()
        except Exception:
            pass


# ---------------------------------------------------------------------------
# afp subcommand
# ---------------------------------------------------------------------------
def cmd_afp(args) -> int:
    isabelle_home = (
        Path(args.isabelle_home).resolve()
        if args.isabelle_home
        else get_isabelle_home()
    )
    if not isabelle_home or not isabelle_home.exists():
        log.error(
            "Cannot find Isabelle home. Pass --isabelle-home or ensure `isabelle` is in PATH."
        )
        return 2

    afp_root = Path(args.afp).resolve()
    if not afp_root.exists():
        log.error("AFP root not found: %s", afp_root)
        return 2

    afp_thys = afp_root / "thys"
    out_dir = Path(args.out_dir).resolve()
    compress = bool(args.compress)
    skip_existing = bool(args.skip_existing)
    jobs = max(1, int(args.jobs))
    verbose = bool(args.verbose)

    _setup_isabelle_path(isabelle_home)
    isabelle_id = get_isabelle_id(isabelle_home)
    afp_version = detect_afp_version(afp_root, args.afp_version)
    log.info("isabelle_id=%s  afp_version=%s", isabelle_id, afp_version)

    script_dir = Path(__file__).resolve().parent
    exportdeps_dir = (
        Path(args.exportdeps_dir).resolve()
        if args.exportdeps_dir
        else script_dir / "ExportDeps"
    )
    if not exportdeps_dir.exists():
        log.error("ExportDeps directory not found: %s", exportdeps_dir)
        return 2

    log.info("Discovering theories in %s ...", afp_thys)
    pairs = list(glob_theory_file_with_session(afp_thys, verbose=verbose))
    log.info("Found %d theory files", len(pairs))

    # Collect all AFP ROOT-file parent dirs so cross-session deps can be resolved.
    all_afp_dirs: set[Path] = set()
    for _, session in pairs:
        if session is not None:
            all_afp_dirs.add(session.root_file.parent)

    dirs = [str(exportdeps_dir)] + [str(d) for d in sorted(all_afp_dirs)]
    all_sessions = set()

    # Group theories by session, applying optional glob filter.
    by_session: dict[str, list[str]] = {}
    for thy_path, session in pairs:
        all_sessions.add(session.name if session else "<no-session>")
        if session is None:
            continue
        sname = session.name
        if args.sessions and not fnmatch.fnmatch(sname, args.sessions):
            continue
        by_session.setdefault(sname, []).append(str(thy_path))

    log.info("Processing %d sessions  (jobs=%d)", len(by_session), jobs)

    # Set up log directory if specified
    log_dir = None
    if args.log_dir:
        log_dir = Path(args.log_dir).resolve()
        log.info("Writing session logs to: %s", log_dir)
        log_dir.mkdir(parents=True, exist_ok=True)

    success, skipped, no_cmds, errors = _run_sessions(
        by_session,
        dirs,
        exportdeps_dir,
        out_dir,
        isabelle_id,
        compress,
        skip_existing,
        jobs,
        verbose,
        log_dir,
        isabelle_home,
    )
    print(
        f"\nDone.  success={success}  skipped={skipped}"
        f"  no_cmds={no_cmds}  errors={errors}"
    )
    return 0


# ---------------------------------------------------------------------------
# isabelle subcommand
# ---------------------------------------------------------------------------
def cmd_isabelle(args) -> int:
    isabelle_home = (
        Path(args.isabelle_home).resolve()
        if args.isabelle_home
        else get_isabelle_home()
    )
    if not isabelle_home or not isabelle_home.exists():
        log.error(
            "Cannot find Isabelle home. Pass --isabelle-home or ensure `isabelle` is in PATH."
        )
        return 2

    _setup_isabelle_path(isabelle_home)
    isabelle_id = get_isabelle_id(isabelle_home)
    out_dir = Path(args.out_dir).resolve()
    compress = bool(args.compress)
    skip_existing = bool(args.skip_existing)
    jobs = max(1, int(args.jobs))
    verbose = bool(args.verbose)

    script_dir = Path(__file__).resolve().parent
    exportdeps_dir = (
        Path(args.exportdeps_dir).resolve()
        if args.exportdeps_dir
        else script_dir / "ExportDeps"
    )
    if not exportdeps_dir.exists():
        log.error("ExportDeps directory not found: %s", exportdeps_dir)
        return 2

    # Built-in sessions need no extra --dir entries beyond ExportDeps.
    dirs = [str(exportdeps_dir)]

    by_session: dict[str, list[str]] = {}
    for component in args.components:
        component_dir = (isabelle_home / "src" / component).resolve()
        root_file = component_dir / "ROOT"
        if not root_file.exists():
            log.warning(
                "No ROOT file found for component %s (%s), skipping",
                component,
                component_dir,
            )
            continue
        sessions = parse_root_file(root_file)
        dir_session_map = build_dir_session_map(sessions)
        log.info("Component %s: %d sessions", component, len(sessions))
        for thy_file in sorted(component_dir.glob("**/*.thy")):
            session = dir_session_map.get(thy_file.parent)
            if session is None:
                continue
            sname = session.name
            if sname == "Pure":
                continue
            if args.sessions and not fnmatch.fnmatch(sname, args.sessions):
                continue
            by_session.setdefault(sname, []).append(str(thy_file))

    log.info("Processing %d sessions (jobs=%d)", len(by_session), jobs)

    # Set up log directory if specified
    log_dir = None
    if args.log_dir:
        log_dir = Path(args.log_dir).resolve()
        log.info("Writing session logs to: %s", log_dir)
        log_dir.mkdir(parents=True, exist_ok=True)

    success, skipped, no_cmds, errors = _run_sessions(
        by_session,
        dirs,
        exportdeps_dir,
        out_dir,
        isabelle_id,
        compress,
        skip_existing,
        jobs,
        verbose,
        log_dir,
        isabelle_home,
    )
    print(
        f"\nDone.  success={success}  skipped={skipped}"
        f"  no_cmds={no_cmds}  errors={errors}"
    )
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def _add_exportdeps_dir(p: argparse.ArgumentParser) -> None:
    p.add_argument(
        "--exportdeps-dir",
        default=None,
        metavar="PATH",
        help="ExportDeps/ directory (default: <script_dir>/ExportDeps/)",
    )


def _add_isabelle_home(p: argparse.ArgumentParser) -> None:
    p.add_argument(
        "--isabelle-home",
        default=None,
        metavar="PATH",
        help="Isabelle installation directory (default: auto-detect via PATH / `isabelle getenv`)",
    )


def main(argv: list[str]) -> int:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s %(levelname)s %(message)s",
    )

    ap = argparse.ArgumentParser(
        description="Batch theorem dependency extraction via extract_deps."
    )
    sub = ap.add_subparsers(dest="subcommand", required=True)

    # ---- theory ----
    p_thy = sub.add_parser("theory", help="Extract deps from a single theory file")
    p_thy.add_argument(
        "--session", required=True, help="Isabelle session containing the theory"
    )
    p_thy.add_argument("--theory", required=True, help="Path to the .thy file")
    p_thy.add_argument("--out", required=True, help="Output file (.toml or .toml.zst)")
    p_thy.add_argument(
        "--dir",
        action="append",
        default=[],
        metavar="PATH",
        help="Extra -d DIR for Isabelle (repeatable; ExportDeps is added automatically)",
    )
    _add_exportdeps_dir(p_thy)
    _add_isabelle_home(p_thy)
    p_thy.add_argument("--verbose", action="store_true")

    # ---- afp ----
    p_afp = sub.add_parser(
        "afp", help="Bulk export for an AFP-style directory structure"
    )
    p_afp.add_argument(
        "--afp",
        default=None,
        metavar="PATH",
        help="AFP root directory (default: $AFP environment variable)",
    )
    p_afp.add_argument(
        "--afp-version",
        default=None,
        metavar="STR",
        help="AFP version string (overrides auto-detection)",
    )
    p_afp.add_argument(
        "--out-dir", required=True, metavar="PATH", help="Output root directory"
    )
    _add_exportdeps_dir(p_afp)
    _add_isabelle_home(p_afp)
    p_afp.add_argument(
        "--compress", action="store_true", help="Write .toml.zst instead of .toml"
    )
    p_afp.add_argument(
        "--jobs",
        type=int,
        default=1,
        metavar="N",
        help="Number of parallel session workers (default: 1)",
    )
    p_afp.add_argument(
        "--skip-existing",
        action="store_true",
        help="Skip theories whose output file already exists (resumable runs)",
    )
    p_afp.add_argument(
        "--sessions",
        default=None,
        metavar="PATTERN",
        help="Glob pattern for session names to process (e.g. 'Completeness')",
    )
    p_afp.add_argument(
        "--log-dir",
        default=None,
        metavar="PATH",
        help="Directory to write per-session log files (one .log per session)",
    )
    p_afp.add_argument("--verbose", action="store_true")

    # ---- isabelle ----
    p_isabelle = sub.add_parser(
        "isabelle",
        help="Bulk export for Isabelle built-in sessions from src/ components",
    )
    p_isabelle.add_argument(
        "components",
        nargs="+",
        metavar="COMPONENT",
        help="Component names under src/ to process (e.g. HOL FOL ZF)",
    )
    p_isabelle.add_argument("--out-dir", required=True, metavar="PATH")
    _add_exportdeps_dir(p_isabelle)
    _add_isabelle_home(p_isabelle)
    p_isabelle.add_argument("--compress", action="store_true", help="Write .toml.zst")
    p_isabelle.add_argument("--jobs", type=int, default=1, metavar="N")
    p_isabelle.add_argument("--skip-existing", action="store_true")
    p_isabelle.add_argument(
        "--sessions",
        default=None,
        metavar="PATTERN",
        help="Optional glob filter on session names (e.g. 'HOL-*')",
    )
    p_isabelle.add_argument(
        "--log-dir",
        default=None,
        metavar="PATH",
        help="Directory to write per-session log files (one .log per session)",
    )
    p_isabelle.add_argument("--verbose", action="store_true")

    args = ap.parse_args(argv)

    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    if args.subcommand == "afp" and args.afp is None:
        args.afp = os.environ.get("AFP")
        if not args.afp:
            ap.error("Provide --afp or set the AFP environment variable")

    if args.subcommand == "theory":
        return cmd_theory(args)
    elif args.subcommand == "afp":
        return cmd_afp(args)
    elif args.subcommand == "isabelle":
        return cmd_isabelle(args)
    else:
        ap.print_help()
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
