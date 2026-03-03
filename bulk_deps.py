#!/usr/bin/env python3
"""
bulk_deps.py — Batch extraction of theorem dependencies using extract_deps.

Two subcommands:

  theory  — Extract deps from a single .thy file (no theorem names needed).
  afp     — Bulk export for an AFP-like directory structure, grouped by session.

Examples:
  uv run bulk_deps.py theory \\
    --session HOL-Examples \\
    --theory ~/Isabelle2025/src/HOL/Examples/Ackermann.thy \\
    --out /tmp/test_out/Ackermann.toml.xz \\
    --dir ExportDeps

  uv run bulk_deps.py afp \\
    --afp $AFP \\
    --out-dir /tmp/deps_out \\
    --sessions "Completeness" \\
    --compress \\
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

from isabelle_client import get_isabelle_client, start_isabelle_server  # type: ignore

from dep_extract import _iter_messages, read_theory_name
from session import glob_theory_file_with_session

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

def get_isabelle_id() -> str:
    """Return the Isabelle version string from `isabelle version`."""
    try:
        r = subprocess.run(
            ["isabelle", "version"],
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
                    v = line[len("VERSION="):].strip()
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
) -> None:
    """Write Deps_Wrapper.thy that calls extract_deps on theory_path."""
    target_import = f"{session_name}.{theory_name}"
    body = (
        f"theory {WRAPPER_THEORY_NAME}\n"
        f'  imports ExportDeps.ExtractFacts "{target_import}"\n'
        f"begin\n"
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
    version: str,
    session_name: str,
    theory_name: str,
    compress: bool,
) -> Path:
    """Compute the canonical output path for one theory."""
    ext = ".toml.xz" if compress else ".toml"
    return (
        out_dir
        / _safe(isabelle_id)
        / _safe(version)
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
) -> bool:
    """Run extract_deps for one theory.  Returns True if output was produced."""
    out_filename = "deps_out.toml.xz" if compress else "deps_out.toml"

    with tempfile.TemporaryDirectory(prefix="isabelle-bulk-") as tmp:
        tmp_dir = Path(tmp).resolve()
        write_wrapper_theory(
            tmp_dir, session_name, theory_name, theory_path, out_filename
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
        shutil.copyfile(produced, out_path)
        return True


# ---------------------------------------------------------------------------
# Session-level worker — one Isabelle server per call, used by afp subcommand
# ---------------------------------------------------------------------------

def _session_worker(
    session_name: str,
    theory_paths: list[str],
    dirs: list[str],
    out_dir_str: str,
    isabelle_id: str,
    version: str,
    compress: bool,
    skip_existing: bool,
    verbose: bool,
) -> dict:
    """Process all theories in one session.  Designed to run in a subprocess."""
    # Re-configure logging for this (sub)process.
    logging.basicConfig(
        level=logging.DEBUG if verbose else logging.INFO,
        format=f"%(levelname)s [{session_name}] %(message)s",
        force=True,
    )
    _log = logging.getLogger(__name__)

    out_dir = Path(out_dir_str)
    success = skipped = 0
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
                out_dir, isabelle_id, version, session_name, thy_name, compress
            )

            if skip_existing and out_path.exists():
                _log.debug("skip existing: %s", out_path.name)
                skipped += 1
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

    _log.info("done: success=%d  skipped=%d  errors=%d", success, skipped, len(errors))
    return {
        "session": session_name,
        "success": success,
        "skipped": skipped,
        "errors": errors,
    }


# ---------------------------------------------------------------------------
# theory subcommand
# ---------------------------------------------------------------------------

def cmd_theory(args) -> int:
    theory_path = Path(args.theory).resolve()
    if not theory_path.exists():
        log.error("Theory file not found: %s", theory_path)
        return 2

    out_path = Path(args.out).resolve()
    compress = args.out.endswith(".xz")

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

    isabelle_id = get_isabelle_id()
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

    # Group theories by session, applying optional glob filter.
    by_session: dict[str, list[str]] = {}
    for thy_path, session in pairs:
        if session is None:
            continue
        sname = session.name
        if args.sessions and not fnmatch.fnmatch(sname, args.sessions):
            continue
        by_session.setdefault(sname, []).append(str(thy_path))

    log.info("Processing %d sessions  (jobs=%d)", len(by_session), jobs)

    total_success = total_skipped = total_errors = 0

    if jobs <= 1:
        for sname, thy_paths in by_session.items():
            result = _session_worker(
                sname,
                thy_paths,
                dirs,
                str(out_dir),
                isabelle_id,
                afp_version,
                compress,
                skip_existing,
                verbose,
            )
            total_success += result["success"]
            total_skipped += result["skipped"]
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
                    afp_version,
                    compress,
                    skip_existing,
                    verbose,
                ): sname
                for sname, thy_paths in by_session.items()
            }
            for future in as_completed(futures):
                sname = futures[future]
                try:
                    result = future.result()
                    total_success += result["success"]
                    total_skipped += result["skipped"]
                    total_errors += len(result["errors"])
                    if result["errors"]:
                        log.warning("[%s] %d error(s)", sname, len(result["errors"]))
                except Exception as e:
                    log.error("[%s] worker crashed: %s", sname, e)
                    total_errors += 1

    print(
        f"\nDone.  success={total_success}  skipped={total_skipped}  errors={total_errors}"
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
    p_thy.add_argument(
        "--out", required=True, help="Output file (.toml or .toml.xz)"
    )
    p_thy.add_argument(
        "--dir",
        action="append",
        default=[],
        metavar="PATH",
        help="Extra -d DIR for Isabelle (repeatable; ExportDeps is added automatically)",
    )
    _add_exportdeps_dir(p_thy)
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
    p_afp.add_argument("--out-dir", required=True, metavar="PATH", help="Output root directory")
    _add_exportdeps_dir(p_afp)
    p_afp.add_argument(
        "--compress", action="store_true", help="Write .toml.xz instead of .toml"
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
    p_afp.add_argument("--verbose", action="store_true")

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
    else:
        ap.print_help()
        return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
