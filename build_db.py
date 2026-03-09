#!/usr/bin/env python3
"""build_db.py — Build and maintain the isabelle-export-deps SQLite database.

Subcommands:

  import          Import .toml/.toml.zst files produced by bulk_deps.py.
  prepare-share   Checkpoint + VACUUM + ANALYZE + zstd-compress a DB for sharing.

Examples:
    uv run build_db.py import \\
        --input-dir /bulk_out/Isabelle2025-2 \\
        --output-db deps_db/Isabelle2025-2.db \\
        [--isabelle-home /opt/Isabelle2025] \\
        [--afp-root /data/afp] \\
        [--verbose]

    uv run build_db.py prepare-share \\
        --db deps_db/Isabelle2025-2.db \\
        --out deps_db/Isabelle2025-2.db.zst \\
        [--compression-level 19]

The input directory is expected to contain .toml or .toml.zst files nested under
session subdirectories (the layout produced by bulk_deps.py).
When both .toml and .toml.zst exist for the same stem, .toml.zst takes precedence.
"""
from __future__ import annotations

import argparse
import io
import json
import logging
import sqlite3
import sys
import tomllib
from pathlib import Path

import zstandard as zstd
from peewee import EXCLUDED, fn
from tqdm import tqdm

from deps_db import DepEdge, Theorem, Theory, create_schema, db, normalize_pos, open_db

log = logging.getLogger(__name__)

# ---------------------------------------------------------------------------
# In-memory cache: theorem key → DB row id
#
# The same HOL lemmas (e.g. HOL.refl, HOL.TrueI) appear as dependencies in
# practically every theory file.  Without a cache, each file would re-SELECT
# those IDs from SQLite tens of thousands of times.  With this cache those
# lookups happen once per run, collapsing millions of queries to a handful.
# ---------------------------------------------------------------------------
_key_to_id: dict[str, int] = {}

# Rows per INSERT chunk — keeps parameter count well under SQLite's 999 limit.
_INSERT_CHUNK = 100


# ---------------------------------------------------------------------------
# File loading
# ---------------------------------------------------------------------------
def _load_toml(path: Path) -> dict:
    """Load a .toml or .toml.zst file and return the parsed dict."""
    data = path.read_bytes()
    if path.name.endswith(".zst"):
        dctx = zstd.ZstdDecompressor()
        with dctx.stream_reader(io.BytesIO(data)) as reader:
            data = reader.read()
    return tomllib.loads(data.decode("utf-8"))


def _collect_files(input_dir: Path) -> list[Path]:
    """Collect unique TOML files; prefer .toml.zst over .toml for the same stem."""
    file_map: dict[tuple[Path, str], Path] = {}
    for path in input_dir.rglob("*.toml"):
        file_map.setdefault((path.parent, path.stem), path)
    for path in input_dir.rglob("*.toml.zst"):
        stem = path.name[: -len(".toml.zst")]
        file_map[(path.parent, stem)] = path  # .zst always wins
    return sorted(file_map.values())


# ---------------------------------------------------------------------------
# Upsert helpers
# ---------------------------------------------------------------------------
def _upsert_theory(
    current_theory: str, session: str, ancestors: list, exporter_version
) -> Theory:
    """Insert or update a theory row; return the instance."""
    (
        Theory.insert(
            theory=current_theory,
            session=session,
            ancestors=json.dumps(ancestors),
            exporter_version=exporter_version,
        )
        .on_conflict(
            conflict_target=[Theory.theory],
            preserve=[Theory.ancestors, Theory.exporter_version],
        )
        .execute()
    )
    return Theory.get(Theory.theory == current_theory)


def _upsert_theorem_full(
    thm: dict, home_theory: Theory, isabelle_home: Path | None, afp_root: Path | None
) -> int:
    """Upsert a theorem with full data; return its DB id."""
    key = thm["key"]
    skip = thm.get("has_skip_proof")
    (
        Theorem.insert(
            key=key,
            raw=thm.get("raw"),
            sel=thm.get("sel", 0),
            pretty=thm.get("pretty"),
            theory=thm.get("theory"),
            home_theory_id=home_theory.id,
            thm_id=thm.get("thm_id"),
            fingerprint=thm.get("fingerprint"),
            proposition=thm.get("proposition"),
            constants=(
                json.dumps(thm["constants"])
                if thm.get("constants") is not None
                else None
            ),
            types=json.dumps(thm["types"]) if thm.get("types") is not None else None,
            has_skip_proof=(1 if skip else 0) if skip is not None else None,
            pos=normalize_pos(thm.get("pos") or "", isabelle_home, afp_root),
        )
        .on_conflict(
            conflict_target=[Theorem.key],
            # Always overwrite with incoming (full) data:
            preserve=[
                Theorem.raw,
                Theorem.sel,
                Theorem.pretty,
                Theorem.theory,
                Theorem.thm_id,
                Theorem.fingerprint,
                Theorem.pos,
            ],
            # Keep existing value when incoming is NULL:
            update={
                Theorem.home_theory_id: fn.COALESCE(
                    EXCLUDED.home_theory_id, Theorem.home_theory_id
                ),
                Theorem.proposition: fn.COALESCE(
                    EXCLUDED.proposition, Theorem.proposition
                ),
                Theorem.constants: fn.COALESCE(EXCLUDED.constants, Theorem.constants),
                Theorem.types: fn.COALESCE(EXCLUDED.types, Theorem.types),
                Theorem.has_skip_proof: fn.COALESCE(
                    EXCLUDED.has_skip_proof, Theorem.has_skip_proof
                ),
            },
        )
        .execute()
    )

    # Fetch id from cache or DB (single-column scalar — much lighter than .get())
    if key not in _key_to_id:
        _key_to_id[key] = Theorem.select(Theorem.id).where(Theorem.key == key).scalar()
    return _key_to_id[key]


def _resolve_dep_ids(
    deps: list[dict], isabelle_home: Path | None, afp_root: Path | None
) -> list[int]:
    """Ensure all dep keys exist in DB; return their ids in the same order.

    For keys already in the cache this costs zero queries.  For new keys:
      - one batched INSERT OR IGNORE (chunked to stay under SQLite param limit)
      - one batched SELECT id, key WHERE key IN (...)
    """
    unknown = [d for d in deps if d["key"] not in _key_to_id]

    if unknown:
        # Batch-insert partial rows for all unseen deps
        rows = [
            {
                "key": d["key"],
                "raw": d.get("raw"),
                "sel": d.get("sel", 0),
                "pretty": d.get("pretty"),
                "theory": d.get("theory"),
                "thm_id": d.get("thm_id"),
                "fingerprint": d.get("fingerprint"),
                "pos": normalize_pos(d.get("pos") or "", isabelle_home, afp_root),
            }
            for d in unknown
        ]
        for i in range(0, len(rows), _INSERT_CHUNK):
            (
                Theorem.insert_many(rows[i : i + _INSERT_CHUNK])
                .on_conflict_ignore()
                .execute()
            )

        # Batch-fetch their ids (SQLite IN limit is 999)
        unknown_keys = [d["key"] for d in unknown]
        for i in range(0, len(unknown_keys), 999):
            chunk = unknown_keys[i : i + 999]
            for t in Theorem.select(Theorem.id, Theorem.key).where(
                Theorem.key.in_(chunk)
            ):
                _key_to_id[t.key] = t.id

    return [_key_to_id[d["key"]] for d in deps if d["key"] in _key_to_id]


# ---------------------------------------------------------------------------
# Per-file import
# ---------------------------------------------------------------------------
def import_file(path: Path, isabelle_home: Path | None, afp_root: Path | None) -> int:
    """Import one TOML file.  Returns the number of top-level theorems processed."""
    try:
        doc = _load_toml(path)
    except Exception as e:
        log.error("Failed to load %s: %s", path, e)
        return 0

    meta = doc.get("meta", {})
    current_theory = meta.get("current_theory", "")
    ancestors = meta.get("theory_ancestors", [])
    session = (
        current_theory.rsplit(".", 1)[0] if "." in current_theory else current_theory
    )

    theory = _upsert_theory(
        current_theory, session, ancestors, meta.get("exporter_version")
    )

    theorems = doc.get("theorems", [])
    for thm in theorems:
        if not thm.get("key"):
            continue

        thm_db_id = _upsert_theorem_full(thm, theory, isabelle_home, afp_root)

        valid_deps = [d for d in thm.get("dependencies", []) if d.get("key")]
        if valid_deps:
            dep_ids = _resolve_dep_ids(valid_deps, isabelle_home, afp_root)
            (
                DepEdge.insert_many(
                    [{"theorem_id": thm_db_id, "dep_id": did} for did in dep_ids]
                )
                .on_conflict_ignore()
                .execute()
            )

    return len(theorems)


# ---------------------------------------------------------------------------
# prepare-share: checkpoint + VACUUM + ANALYZE + zstd compress
# ---------------------------------------------------------------------------
def cmd_prepare_share(args) -> int:
    """Prepare a DB for sharing: WAL checkpoint, VACUUM, ANALYZE, then zstd compress."""
    db_path = Path(args.db).resolve()
    out_path = Path(args.out).resolve()
    level = args.compression_level

    if not db_path.exists():
        log.error("Database not found: %s", db_path)
        return 2

    size_before = db_path.stat().st_size
    log.info("DB size before VACUUM: %.1f MB", size_before / 1024**2)

    conn = sqlite3.connect(str(db_path))
    try:
        log.info("Running WAL checkpoint (TRUNCATE)...")
        conn.execute("PRAGMA wal_checkpoint(TRUNCATE);")
        log.info("Running VACUUM (this may take a while)...")
        conn.execute("VACUUM;")
        log.info("Running ANALYZE...")
        conn.execute("ANALYZE;")
        conn.close()
    except Exception:
        conn.close()
        raise

    size_after = db_path.stat().st_size
    log.info(
        "DB size after VACUUM: %.1f MB  (delta: %+.1f MB)",
        size_after / 1024**2,
        (size_after - size_before) / 1024**2,
    )

    out_path.parent.mkdir(parents=True, exist_ok=True)
    cctx = zstd.ZstdCompressor(level=level, threads=-1)
    log.info("Compressing → %s  (level=%d, multi-threaded)...", out_path, level)

    with db_path.open("rb") as src, out_path.open("wb") as dst:
        with cctx.stream_writer(dst, closefd=False) as writer:
            buf = bytearray(1024 * 1024)
            while True:
                n = src.readinto(buf)
                if not n:
                    break
                writer.write(buf[:n])

    size_zst = out_path.stat().st_size
    ratio = size_after / size_zst if size_zst else float("inf")
    log.info("Compressed size: %.1f MB  (ratio: %.2fx)", size_zst / 1024**2, ratio)
    log.info("Done. Receiver can decompress with: zstd -d %s", out_path.name)
    return 0


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------
def _cmd_import(args) -> int:
    if args.verbose:
        logging.getLogger().setLevel(logging.DEBUG)

    input_dir = Path(args.input_dir).resolve()
    output_db = Path(args.output_db).resolve()
    isabelle_home = Path(args.isabelle_home).resolve() if args.isabelle_home else None
    afp_root = Path(args.afp_root).resolve() if args.afp_root else None

    if not input_dir.exists():
        log.error("Input directory not found: %s", input_dir)
        return 2

    open_db(output_db, create=True)
    create_schema()

    files = _collect_files(input_dir)
    log.info("Found %d file(s) in %s", len(files), input_dir)

    total_thms = 0
    for i, path in tqdm(enumerate(files, 1), desc="Importing files", total=len(files)):
        with db.atomic():
            n = import_file(path, isabelle_home, afp_root)
        total_thms += n
        if args.verbose:
            log.debug("[%d/%d] %s → %d theorem(s)", i, len(files), path.name, n)
        elif i % 100 == 0 or i == len(files):
            log.info("[%d/%d] %d theorem(s) so far", i, len(files), total_thms)

    log.info(
        "Done. %d theorem(s) from %d file(s) → %s", total_thms, len(files), output_db
    )
    db.close()
    return 0


def main(argv: list[str]) -> int:
    logging.basicConfig(
        level=logging.INFO, format="%(asctime)s %(levelname)s %(message)s"
    )

    ap = argparse.ArgumentParser(
        description="Build and maintain the isabelle-export-deps SQLite database.",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    sub = ap.add_subparsers(dest="subcommand", required=True)

    # ---- import subcommand ----
    p_import = sub.add_parser(
        "import", help="Import .toml/.toml.zst files into a SQLite database"
    )
    p_import.add_argument(
        "--input-dir",
        required=True,
        metavar="PATH",
        help="Directory tree containing .toml or .toml.zst files",
    )
    p_import.add_argument(
        "--output-db", required=True, metavar="PATH", help="Output SQLite database path"
    )
    p_import.add_argument(
        "--isabelle-home",
        default=None,
        metavar="PATH",
        help="Isabelle installation directory (for pos normalization)",
    )
    p_import.add_argument(
        "--afp-root",
        default=None,
        metavar="PATH",
        help="AFP root directory (for pos normalization)",
    )
    p_import.add_argument("--verbose", action="store_true")

    # ---- prepare-share subcommand ----
    p_share = sub.add_parser(
        "prepare-share",
        help="WAL checkpoint + VACUUM + ANALYZE + zstd compress a DB for sharing",
    )
    p_share.add_argument(
        "--db", required=True, metavar="PATH", help="Source SQLite database"
    )
    p_share.add_argument(
        "--out", required=True, metavar="PATH", help="Output .db.zst path"
    )
    p_share.add_argument(
        "--compression-level",
        type=int,
        default=19,
        metavar="N",
        help="zstd compression level (1-22, default 19)",
    )

    args = ap.parse_args(argv)

    if args.subcommand == "import":
        return _cmd_import(args)
    elif args.subcommand == "prepare-share":
        return cmd_prepare_share(args)

    ap.print_help()
    return 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
