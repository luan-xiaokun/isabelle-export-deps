#!/usr/bin/env python3
"""
dep_extract.py (prototype, hardened)

Generate a wrapper theory that imports:
  - ExportDeps session-qualified theory  (e.g., ExportDeps.ExportDeps)
  - Target session-qualified theory      (e.g., HOL-Examples.Ackermann)

Then runs `export_deps ... in "<out>"` via Isabelle Server using isabelle-client.

Typical usage:
  python dep_extract.py \
    --target-session HOL-Examples \
    --theory /path/to/src/HOL/Examples/Ackermann.thy \
    --thms foo \
    --out /tmp/deps.txt \
    --dir /path/to/ExportDeps/root

Notes:
- Requires: pip install isabelle-client
- Assumes Isabelle is installed and available to isabelle-client.
"""

from __future__ import annotations

import argparse
import re
import shutil
import sys
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

from isabelle_client import get_isabelle_client, start_isabelle_server  # type: ignore

THEORY_HEADER_RE = re.compile(r'^\s*theory\s+"?([A-Za-z0-9_\'.]+)"?')


@dataclass(frozen=True)
class JobConfig:
    target_session: str
    theory_path: Path
    theorem_names: list[str]
    out_file: Path

    exportdeps_session: str = "ExportDeps"
    exportdeps_theory: str = (
        "ExportDeps"  # the theory file ExportDeps.thy defines `theory ExportDeps`
    )
    wrapper_theory_name: str = "Deps_Wrapper"

    dirs: list[str] = None  # additional -d dirs
    include_sessions: list[str] = None  # optional include_sessions
    verbose: bool = False


def read_theory_name(theory_file: Path) -> str:
    """Extract theory name from header line: `theory Name`."""
    with theory_file.open("r", encoding="utf-8") as f:
        for line in f:
            m = THEORY_HEADER_RE.match(line)
            if m:
                return m.group(1)
            if line.strip().startswith("imports") or line.strip().startswith("begin"):
                break
    raise ValueError(f"Cannot find theory header in: {theory_file}")


def write_wrapper_theory(
    wrapper_dir: Path,
    wrapper_theory_name: str,
    exportdeps_import: str,
    target_import: str,
    theorem_names: list[str],
    out_rel_path: str,
) -> Path:
    """Create wrapper theory file in wrapper_dir."""
    wrapper_path = wrapper_dir / f"{wrapper_theory_name}.thy"
    thms = " ".join(theorem_names)
    body = f"""theory {wrapper_theory_name}
  imports "{exportdeps_import}" "{target_import}"
begin

export_deps {thms} in "{out_rel_path}"

end
"""
    wrapper_path.write_text(body, encoding="utf-8")
    return wrapper_path


def _iter_messages(responses: Iterable[object]) -> Iterable[str]:
    """
    Best-effort extraction of human-readable messages from isabelle-client responses.
    The exact shapes differ a bit across versions; we try common fields.
    """
    for r in responses:
        # Common: NotificationResponse has .response_body with .message or similar
        body = getattr(r, "response_body", None)
        if body is None:
            continue
        # Try common fields
        for attr in ("message", "messages", "errors", "error", "status"):
            if hasattr(body, attr):
                val = getattr(body, attr)
                if isinstance(val, str):
                    yield val
                elif isinstance(val, list):
                    for x in val:
                        yield str(x)
                else:
                    yield str(val)


def run_isabelle_wrapper(cfg: JobConfig, wrapper_dir: Path) -> None:
    """Start Isabelle server, start session, run wrapper theory."""
    server_info, _proc = start_isabelle_server()
    isabelle = get_isabelle_client(server_info)

    def log(msg: str) -> None:
        if cfg.verbose:
            print(msg, file=sys.stderr)

    try:
        log(
            f"[isabelle] session_start(session={cfg.target_session}) dirs={cfg.dirs} include={cfg.include_sessions}"
        )
        start_resps = isabelle.session_start(
            session=cfg.target_session,
            dirs=cfg.dirs or [],
            include_sessions=cfg.include_sessions or [],
            verbose=cfg.verbose,
        )
        session_id = start_resps[-1].response_body.session_id
        log(f"[isabelle] session_id={session_id}")

        use_resps = isabelle.use_theories(
            theories=[cfg.wrapper_theory_name],
            master_dir=str(wrapper_dir),
            session_id=session_id,
        )

        # If something went wrong, Isabelle typically reports it via notifications.
        # Print anything we can extract in verbose mode.
        if cfg.verbose:
            for m in _iter_messages(start_resps):
                print(f"[isabelle][start] {m}", file=sys.stderr)
            for m in _iter_messages(use_resps):
                print(f"[isabelle][use] {m}", file=sys.stderr)

        # Heuristic failure detection: some versions provide a final status object;
        # but we avoid depending on internal shapes. If wrapper failed, output file won't exist,
        # and caller will report an error.
        _ = use_resps

    finally:
        isabelle.shutdown()


def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser()

    ap.add_argument(
        "--target-session",
        required=True,
        help="Session that contains the target theory (e.g. HOL-Examples, HOL, AFP entry session).",
    )
    ap.add_argument("--theory", required=True, help="Path to target .thy file")
    ap.add_argument(
        "--thms",
        nargs="+",
        required=True,
        help="Theorem/fact names in target theory context",
    )
    ap.add_argument("--out", required=True, help="Output file path (final destination)")

    ap.add_argument(
        "--exportdeps-session",
        default="ExportDeps",
        help="Session name that provides ExportDeps theory (default: ExportDeps)",
    )
    ap.add_argument(
        "--exportdeps-theory",
        default="ExportDeps",
        help="Theory name inside exportdeps-session (default: ExportDeps)",
    )

    ap.add_argument(
        "--dir",
        action="append",
        default=[],
        help="Additional Isabelle -d DIR entries (repeatable). "
        "Add the directory that contains your ExportDeps ROOT/ROOTS, and e.g. AFP root if needed.",
    )
    ap.add_argument(
        "--include-session",
        action="append",
        default=[],
        help="Sessions whose theories are included in the overall namespace "
        "(rarely needed; repeatable).",
    )
    ap.add_argument(
        "--verbose", action="store_true", help="Print Isabelle server diagnostics"
    )

    args = ap.parse_args(argv)

    cfg = JobConfig(
        target_session=args.target_session,
        theory_path=Path(args.theory).resolve(),
        theorem_names=list(args.thms),
        out_file=Path(args.out).resolve(),
        exportdeps_session=args.exportdeps_session,
        exportdeps_theory=args.exportdeps_theory,
        dirs=list(args.dir),
        include_sessions=list(args.include_session),
        verbose=bool(args.verbose),
    )

    if not cfg.theory_path.exists():
        print(f"[error] theory file not found: {cfg.theory_path}", file=sys.stderr)
        return 2

    target_theory_name = read_theory_name(cfg.theory_path)

    # session-qualified imports (avoid namespace ambiguity)
    exportdeps_import = f"{cfg.exportdeps_session}.{cfg.exportdeps_theory}"
    target_import = f"{cfg.target_session}.{target_theory_name}"

    with tempfile.TemporaryDirectory(prefix="isabelle-deps-") as tmp:
        tmp_dir = Path(tmp).resolve()
        out_rel = "deps_out.toml"

        wrapper_path = write_wrapper_theory(
            wrapper_dir=tmp_dir,
            wrapper_theory_name=cfg.wrapper_theory_name,
            exportdeps_import=exportdeps_import,
            target_import=target_import,
            theorem_names=cfg.theorem_names,
            out_rel_path=out_rel,
        )
        if cfg.verbose:
            print(f"[debug] wrote wrapper theory: {wrapper_path}", file=sys.stderr)
            print(
                f"[debug] wrapper imports: {exportdeps_import} , {target_import}",
                file=sys.stderr,
            )

        run_isabelle_wrapper(cfg, wrapper_dir=tmp_dir)

        produced = tmp_dir / out_rel
        if not produced.exists():
            print(
                "[error] export did not produce output file.\n"
                "Likely causes:\n"
                "  - wrong --target-session\n"
                "  - missing --dir entries (ExportDeps root / AFP root / project root)\n"
                "  - target theory not part of target session's build graph\n"
                "  - theorem names not in scope / typos\n"
                "Re-run with --verbose for Isabelle diagnostics.",
                file=sys.stderr,
            )
            return 3

        cfg.out_file.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(produced, cfg.out_file)
        print(f"[ok] wrote: {cfg.out_file}")

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
