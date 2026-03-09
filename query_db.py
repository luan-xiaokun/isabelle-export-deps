#!/usr/bin/env python3
"""query_db.py — Query the isabelle-export-deps SQLite database.

Subcommands:
    deps    Forward deps: list all theorems that a given key depends on.
    rdeps   Reverse deps: list all theorems that depend on a given key.
    search  Search by pretty name (supports % wildcard).
    show    Show full details of a theorem.

Examples:
    uv run query_db.py deps \\
        --db deps_db/Isabelle2025-2.db \\
        --key "HOL.Binomial:Binomial.n_subsets"

    uv run query_db.py rdeps \\
        --db deps_db/Isabelle2025-2.db \\
        --key "HOL.Binomial:Binomial.n_subsets"

    uv run query_db.py search \\
        --db deps_db/Isabelle2025-2.db \\
        --name "n_subsets" \\
        [--theory "HOL.Binomial"]

    uv run query_db.py show \\
        --db deps_db/Isabelle2025-2.db \\
        --key "HOL.Binomial:Binomial.n_subsets" \\
        [--isabelle-home ~/Isabelle2025] [--afp-root /data/afp]
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from deps_db import DepEdge, Theorem, denormalize_pos, open_db


# ---------------------------------------------------------------------------
# Formatting helpers
# ---------------------------------------------------------------------------

def _thm_to_dict(thm: Theorem, isabelle_home: Path | None, afp_root: Path | None) -> dict:
    """Convert a Theorem instance to a plain dict (for JSON output or further processing)."""
    return {
        "key":            thm.key,
        "raw":            thm.raw,
        "sel":            thm.sel,
        "pretty":         thm.pretty,
        "theory":         thm.theory,
        "thm_id":         thm.thm_id,
        "fingerprint":    thm.fingerprint,
        "proposition":    thm.proposition,
        "constants":      json.loads(thm.constants) if thm.constants else None,
        "types":          json.loads(thm.types)     if thm.types     else None,
        "has_skip_proof": bool(thm.has_skip_proof)  if thm.has_skip_proof is not None else None,
        "pos":            denormalize_pos(thm.pos or "", isabelle_home, afp_root) or None,
    }


def _print_short(thm: Theorem, isabelle_home: Path | None, afp_root: Path | None) -> None:
    pretty = thm.pretty or thm.raw or thm.key
    pos    = denormalize_pos(thm.pos or "", isabelle_home, afp_root)
    suffix = f"  @ {pos}" if pos else ""
    print(f"  {thm.key}  ({pretty}){suffix}")


def _print_full(thm: Theorem, isabelle_home: Path | None, afp_root: Path | None) -> None:
    d = _thm_to_dict(thm, isabelle_home, afp_root)
    lines = [
        f"key:    {d['key']}",
        f"name:   {d['pretty'] or d['raw'] or ''}",
        f"theory: {d['theory'] or ''}",
    ]
    if d["pos"]:
        lines.append(f"pos:    {d['pos']}")
    if d["thm_id"]:
        lines.append(f"thm_id: {d['thm_id']}")
    if d["fingerprint"]:
        lines.append(f"fingerprint: {d['fingerprint']}")
    if d["has_skip_proof"] is not None:
        lines.append(f"skip_proof: {d['has_skip_proof']}")
    if d["proposition"]:
        lines.append(f"prop:   {d['proposition']}")
    if d["constants"]:
        lines.append(f"consts: {', '.join(d['constants'])}")
    if d["types"]:
        lines.append(f"types:  {', '.join(d['types'])}")
    print("\n".join(lines))


# ---------------------------------------------------------------------------
# Subcommands
# ---------------------------------------------------------------------------

def cmd_deps(args) -> int:
    """List all theorems that the given key depends on (forward lookup)."""
    open_db(Path(args.db))
    isabelle_home = Path(args.isabelle_home).resolve() if args.isabelle_home else None
    afp_root      = Path(args.afp_root).resolve()      if args.afp_root      else None

    try:
        src = Theorem.get(Theorem.key == args.key)
    except Theorem.DoesNotExist:
        print(f"Theorem not found: {args.key}")
        return 1

    dep_ids = DepEdge.select(DepEdge.dep).where(DepEdge.theorem == src)
    deps    = list(Theorem.select().where(Theorem.id.in_(dep_ids)).order_by(Theorem.key))

    if not deps:
        print(f"No dependencies found for: {args.key}")
        return 0

    if args.json:
        print(json.dumps([_thm_to_dict(t, isabelle_home, afp_root) for t in deps], indent=2))
    else:
        print(f"Dependencies of {args.key!r} ({len(deps)}):")
        for thm in deps:
            _print_short(thm, isabelle_home, afp_root)
    return 0


def cmd_rdeps(args) -> int:
    """List all theorems that depend on the given key (reverse lookup)."""
    open_db(Path(args.db))
    isabelle_home = Path(args.isabelle_home).resolve() if args.isabelle_home else None
    afp_root      = Path(args.afp_root).resolve()      if args.afp_root      else None

    try:
        target = Theorem.get(Theorem.key == args.key)
    except Theorem.DoesNotExist:
        print(f"Theorem not found: {args.key}")
        return 1

    rdep_theorem_ids = DepEdge.select(DepEdge.theorem).where(DepEdge.dep == target)
    rdeps = list(Theorem.select().where(Theorem.id.in_(rdep_theorem_ids)).order_by(Theorem.key))

    if not rdeps:
        print(f"No reverse dependencies found for: {args.key}")
        return 0

    if args.json:
        print(json.dumps([_thm_to_dict(t, isabelle_home, afp_root) for t in rdeps], indent=2))
    else:
        print(f"Theorems depending on {args.key!r} ({len(rdeps)}):")
        for thm in rdeps:
            _print_short(thm, None, None)
    return 0


def cmd_search(args) -> int:
    """Search theorems by pretty name; % acts as a wildcard."""
    open_db(Path(args.db))

    query = Theorem.select().where(Theorem.pretty.ilike(args.name))
    if args.theory:
        query = query.where(Theorem.theory == args.theory)
    results = list(query.order_by(Theorem.key))

    if not results:
        print(f"No theorems found matching: {args.name!r}")
        return 0

    if args.json:
        print(json.dumps([_thm_to_dict(t, None, None) for t in results], indent=2))
    else:
        print(f"Found {len(results)} theorem(s):")
        for thm in results:
            _print_short(thm, None, None)
    return 0


def cmd_show(args) -> int:
    """Show full details of a single theorem."""
    open_db(Path(args.db))
    isabelle_home = Path(args.isabelle_home).resolve() if args.isabelle_home else None
    afp_root      = Path(args.afp_root).resolve()      if args.afp_root      else None

    try:
        thm = Theorem.get(Theorem.key == args.key)
    except Theorem.DoesNotExist:
        print(f"Theorem not found: {args.key}")
        return 1

    if args.json:
        print(json.dumps(_thm_to_dict(thm, isabelle_home, afp_root), indent=2))
    else:
        _print_full(thm, isabelle_home, afp_root)
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main(argv: list[str]) -> int:
    ap = argparse.ArgumentParser(
        description="Query an isabelle-export-deps SQLite database.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = ap.add_subparsers(dest="subcommand", required=True)

    def _add_db(p):
        p.add_argument("--db", required=True, metavar="PATH", help="SQLite database path")

    def _add_pos_args(p):
        p.add_argument("--isabelle-home", default=None, metavar="PATH",
                       help="Isabelle home (for pos path expansion)")
        p.add_argument("--afp-root",      default=None, metavar="PATH",
                       help="AFP root (for pos path expansion)")

    def _add_json_args(p):
        p.add_argument("--json", action="store_true",
                       help="Output results as JSON (instead of human-readable)")

    # deps
    p_deps = sub.add_parser("deps", help="List forward dependencies of a theorem")
    _add_db(p_deps); _add_pos_args(p_deps); _add_json_args(p_deps)
    p_deps.add_argument("--key", required=True, help="Theorem key (Session.Theory:name)")

    # rdeps
    p_rdeps = sub.add_parser("rdeps", help="List theorems that depend on a given key")
    _add_db(p_rdeps); _add_pos_args(p_rdeps); _add_json_args(p_rdeps)
    p_rdeps.add_argument("--key", required=True, help="Theorem key (Session.Theory:name)")

    # search
    p_search = sub.add_parser("search", help="Search theorems by pretty name (% wildcard)")
    _add_db(p_search); _add_json_args(p_search)
    p_search.add_argument("--name",   required=True, help="Pretty name pattern (% = wildcard)")
    p_search.add_argument("--theory", default=None,  help="Restrict to a specific theory")

    # show
    p_show = sub.add_parser("show", help="Show full details of a theorem")
    _add_db(p_show); _add_pos_args(p_show); _add_json_args(p_show)
    p_show.add_argument("--key", required=True, help="Theorem key (Session.Theory:name)")

    args = ap.parse_args(argv)

    if args.subcommand == "deps":
        return cmd_deps(args)
    elif args.subcommand == "rdeps":
        return cmd_rdeps(args)
    elif args.subcommand == "search":
        return cmd_search(args)
    elif args.subcommand == "show":
        return cmd_show(args)

    ap.print_help()
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
