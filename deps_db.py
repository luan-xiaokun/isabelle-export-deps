"""deps_db.py — Peewee models and shared helpers for isabelle-export-deps."""

from __future__ import annotations

from pathlib import Path

from peewee import (
    CompositeKey,
    ForeignKeyField,
    IntegerField,
    Model,
    SqliteDatabase,
    TextField,
)

# ---------------------------------------------------------------------------
# Global deferred database — call open_db() before using any model
# ---------------------------------------------------------------------------
db = SqliteDatabase(None)


class _Base(Model):
    class Meta:
        database = db


class Theory(_Base):
    """One Isabelle theory file (e.g. HOL.Nat, HOL-Examples.Ackermann)."""

    session = TextField()
    theory = TextField(unique=True)  # fully-qualified: "Session.Theory"
    ancestors = TextField(null=True)  # JSON array of ancestor theory names
    exporter_version = TextField(null=True)

    class Meta:
        table_name = "theories"


class Theorem(_Base):
    """One theorem/lemma/definition, identified by its unique key."""

    key = TextField(unique=True)  # "Session.Theory:thm_name"
    raw = TextField(null=True)
    sel = IntegerField(default=0)
    pretty = TextField(null=True, index=True)
    theory = TextField(null=True, index=True)  # "Session.Theory"
    home_theory_id = IntegerField(
        null=True
    )  # FK → theories.id; NULL when seen only as dep
    thm_id = TextField(null=True)
    fingerprint = TextField(null=True)
    proposition = TextField(null=True)  # NULL when seen only as a dependency
    constants = TextField(null=True)  # JSON array; NULL when seen only as dep
    types = TextField(null=True)  # JSON array; NULL when seen only as dep
    has_skip_proof = IntegerField(null=True)  # 0 / 1 / NULL
    pos = TextField(null=True)  # normalized symbolic path

    class Meta:
        table_name = "theorems"


class DepEdge(_Base):
    """Directed dependency edge: theorem depends on dep."""

    # theorem_id is the leading column of the composite PK (theorem_id, dep_id),
    # so the PK index already covers forward-dep lookups — no extra index needed.
    theorem = ForeignKeyField(
        Theorem, column_name="theorem_id", backref="outgoing_deps", index=False
    )
    dep = ForeignKeyField(
        Theorem, column_name="dep_id", backref="incoming_deps", index=True
    )  # index enables fast reverse lookup

    class Meta:
        table_name = "dep_edges"
        primary_key = CompositeKey("theorem", "dep")


# ---------------------------------------------------------------------------
# pos normalization
# ---------------------------------------------------------------------------
def normalize_pos(pos: str, isabelle_home: Path | None, afp_root: Path | None) -> str:
    """Normalize absolute paths inside a pos string to a portable symbolic form.

    Pos format:  "file:line:offset:end_offset"

    ~~/.../foo.thy:…  → kept as-is (already symbolic — Isabelle HOME)
    -:-:8:12          → kept as-is (no source file)
    /opt/Isabelle/…   → ~~/…        (isabelle_home prefix)
    /data/afp/…       → $AFP/…      (afp_root prefix)
    """
    if not pos or pos.startswith("~~") or pos.startswith("-:"):
        return pos

    # The trailing three colon-separated fields are always integers.
    parts = pos.split(":")
    if len(parts) < 4:
        return pos
    try:
        int(parts[-3])
        int(parts[-2])
        int(parts[-1])
    except ValueError:
        return pos

    file_part = ":".join(parts[:-3])
    suffix = ":" + ":".join(parts[-3:])

    if isabelle_home is not None:
        src_dir = isabelle_home / "src"
        if not src_dir.exists():
            raise RuntimeError(f"Expected src/ not found in ISABELLE_HOME: {src_dir}")
        ih = str(isabelle_home)
        if file_part.startswith(ih):
            return "~~" + file_part[len(ih) :] + suffix

    if afp_root is not None:
        ar = str(afp_root)
        if file_part.startswith(ar):
            return "$AFP" + file_part[len(ar) :] + suffix

    return pos


def denormalize_pos(pos: str, isabelle_home: Path | None, afp_root: Path | None) -> str:
    """Restore a symbolic pos string to an absolute path."""
    if not pos:
        return pos
    if isabelle_home is not None and pos.startswith("~~"):
        return str(isabelle_home) + pos[len("~~") :]
    if afp_root is not None and pos.startswith("$AFP"):
        return str(afp_root) + pos[len("$AFP") :]
    return pos


# ---------------------------------------------------------------------------
# DB lifecycle
# ---------------------------------------------------------------------------
def open_db(db_path: Path, *, create: bool = False) -> SqliteDatabase:
    """Initialize and connect the global Peewee database.

    Must be called before using any model.  Returns the db object so callers
    can use db.atomic() etc. directly.
    """
    if not create and not db_path.exists():
        raise FileNotFoundError(f"Database not found: {db_path}")
    db_path.parent.mkdir(parents=True, exist_ok=True)
    db.init(
        str(db_path),
        pragmas={
            "journal_mode": "wal",
            "synchronous": "normal",
            "foreign_keys": 1,
        },
    )
    db.connect()
    return db


def create_schema() -> None:
    """Create all tables and indexes (idempotent via safe=True)."""
    db.create_tables([Theory, Theorem, DepEdge], safe=True)
