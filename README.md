# isabelle-export-deps

Extract theorem dependency snapshots from Isabelle theories. Given a target theory and theorem names, this tool produces a structured TOML report including:

- Theory import closure (ancestors)
- Theorem dependencies (`thm_deps`) with canonical keys, source positions, etc.
- Proposition text, constants, types, and fingerprints for each theorem

It works by generating a temporary wrapper theory that loads the `ExportDeps` ML implementation (via `ML_file`) and the target theory, then runs the `extract_deps` command via the Isabelle Server through [isabelle-client](https://pypi.org/project/isabelle-client/).

## Requirements

- **Isabelle 2022 to 2025-2** (installed; path passed via `--isabelle-home` or `isabelle` in `$PATH`)
- **Python ≥ 3.13**
- **[uv](https://github.com/astral-sh/uv)** (recommended) or pip

## Installation

```bash
git clone <this-repo>
cd isabelle-export-deps
uv sync
```

## AFP Environment Variable (Linux)

This repository provides a helper script to configure the AFP root path:

```bash
source ./set_afp_env.sh /path/to/afp
```

If no path is provided, the script prompts you to input the AFP path interactively.

After sourcing, `AFP` points to your AFP root directory and AFP theories are under `$AFP/thys`.

---

## Extraction

### Single theory (`dep_extract.py`)

Extracts dependencies for specific named theorems from one theory file:

```
uv run dep_extract.py \
  --target-session <SESSION> \
  --theory <PATH_TO_THY> \
  --thms <THM1> [<THM2> ...] \
  --out <OUTPUT_FILE> \
  --dir <DIR> [--dir <DIR2> ...] \
  [--isabelle-home <PATH>] \
  [--verbose]
```

| Option | Description |
|---|---|
| `--target-session` | The Isabelle session containing the target theory (e.g. `HOL-Examples`, `Completeness`) |
| `--theory` | Absolute or relative path to the target `.thy` file |
| `--thms` | One or more theorem/fact names to analyze |
| `--out` | Path where the TOML report will be written (`.toml` or `.toml.zst`) |
| `--dir` | Additional Isabelle root directories (**repeatable**; `ExportDeps/` is added automatically) |
| `--isabelle-home` | Isabelle installation directory (default: auto-detect via `$PATH`) |
| `--verbose` | Print Isabelle server diagnostics to stderr |

### Bulk extraction (`bulk_deps.py`)

Three subcommands for batch processing:

```
uv run bulk_deps.py theory --session <S> --theory <PATH> --out <FILE> [--isabelle-home <PATH>]
uv run bulk_deps.py afp    --afp <PATH> --out-dir <DIR> [--isabelle-home <PATH>] [--jobs N]
uv run bulk_deps.py isabelle <COMPONENT...> --out-dir <DIR> [--isabelle-home <PATH>] [--jobs N]
```

All subcommands accept `--isabelle-home PATH` to specify the Isabelle installation directory
(default: auto-detect via `isabelle getenv` or `isabelle` in `$PATH`).

### `--dir` Rules

- **Isabelle built-in sessions** (e.g. `HOL-Examples`, `HOL-Library`): `ExportDeps/` is added automatically; no extra `--dir` needed.
- **AFP entries**: pass `--dir $AFP/thys/<EntryName>` (the directory containing the entry's `ROOT` file).
- **Custom projects**: pass the directory containing the project's `ROOT` file.

---

## Database

After running bulk extraction you can import all `.toml`/`.toml.zst` files into a SQLite database for fast querying.

### Build the database (`build_db.py`)

#### `import` — populate from TOML files

```
uv run build_db.py import \
  --input-dir <DIR> \
  --output-db <PATH.db> \
  [--isabelle-home <PATH>] \
  [--afp-root <PATH>] \
  [--verbose]
```

| Option | Description |
|---|---|
| `--input-dir` | Directory tree containing `.toml` / `.toml.zst` files (layout produced by `bulk_deps.py`) |
| `--output-db` | Output SQLite database path (created if absent) |
| `--isabelle-home` | Isabelle installation directory — used to normalize `~~/.../file.thy` positions |
| `--afp-root` | AFP root directory — used to normalize `$AFP/…` positions |
| `--verbose` | Log every imported file |

When both `.toml` and `.toml.zst` exist for the same stem, `.toml.zst` takes precedence.

#### `prepare-share` — compact and compress for distribution

```
uv run build_db.py prepare-share \
  --db <PATH.db> \
  --out <PATH.db.zst> \
  [--compression-level 19]
```

Runs a WAL checkpoint, `VACUUM`, `ANALYZE`, then compresses the database with zstd.
The recipient decompresses with `zstd -d <file>.db.zst`.

### Query the database (`query_db.py`)

All subcommands accept `--db PATH` (required) plus optional `--isabelle-home` / `--afp-root` for source-position expansion, and `--json` to emit machine-readable JSON.

#### `deps` — forward dependencies

List every theorem that a given theorem depends on:

```
uv run query_db.py deps \
  --db deps_db/Isabelle2025-2.db \
  --key "HOL.Binomial:Binomial.n_subsets"
```

#### `rdeps` — reverse dependencies

List every theorem that depends on a given theorem:

```
uv run query_db.py rdeps \
  --db deps_db/Isabelle2025-2.db \
  --key "HOL.Binomial:Binomial.n_subsets"
```

#### `search` — search by name

Search theorems by pretty name (`%` is a wildcard); optionally restrict to a theory:

```
uv run query_db.py search \
  --db deps_db/Isabelle2025-2.db \
  --name "n_subsets%" \
  [--theory "HOL.Binomial"]
```

#### `show` — full theorem details

Show all stored fields for a single theorem:

```
uv run query_db.py show \
  --db deps_db/Isabelle2025-2.db \
  --key "HOL.Binomial:Binomial.n_subsets" \
  [--isabelle-home ~/Isabelle2025] [--afp-root /data/afp]
```

### Database schema

The SQLite database contains three tables:

| Table | Description |
|---|---|
| `theories` | One row per theory file (`session`, `theory`, `ancestors`, `exporter_version`) |
| `theorems` | One row per theorem/lemma/definition (`key`, `pretty`, `theory`, `proposition`, `constants`, `types`, `fingerprint`, `pos`, …) |
| `dep_edges` | Directed dependency edges (`theorem_id → dep_id`) |

Source positions (`pos`) are stored in a portable symbolic form (`~~/.../file.thy` for Isabelle built-ins, `$AFP/.../file.thy` for AFP) and expanded back to absolute paths at query time when `--isabelle-home` / `--afp-root` are provided.

---

## Examples

### 1. HOL built-in theory (Ackermann)

```bash
uv run dep_extract.py \
  --target-session HOL-Examples \
  --theory ~/Isabelle2025/src/HOL/Examples/Ackermann.thy \
  --thms ackloop_dom_longer \
  --out examples/ackermann.toml \
  --dir ExportDeps
```

### 2. AFP entry (Completeness)

```bash
uv run dep_extract.py \
  --target-session Completeness \
  --theory $AFP/thys/Completeness/Completeness.thy \
  --thms validProofTree \
  --out examples/completeness.toml \
  --dir ExportDeps \
  --dir $AFP/thys/Completeness \
  --verbose
```

### 3. Bulk AFP extraction

```bash
uv run bulk_deps.py afp \
  --afp $AFP \
  --out-dir /tmp/deps_out \
  --isabelle-home ~/Isabelle2025 \
  --compress \
  --jobs 4
```

### 4. Import into a database

```bash
uv run build_db.py import \
  --input-dir /tmp/deps_out \
  --output-db deps_db/Isabelle2025.db \
  --isabelle-home ~/Isabelle2025 \
  --afp-root $AFP
```

### 5. Query the database

```bash
# All theorems that ackloop_dom_longer depends on
uv run query_db.py deps \
  --db deps_db/Isabelle2025.db \
  --key "HOL-Examples.Ackermann:ackloop_dom_longer"

# Search by name
uv run query_db.py search --db deps_db/Isabelle2025.db --name "ackloop%"

# Full details
uv run query_db.py show \
  --db deps_db/Isabelle2025.db \
  --key "HOL-Examples.Ackermann:ackloop_dom_longer" \
  --isabelle-home ~/Isabelle2025
```

---

## Output format (TOML)

Output is TOML (optionally compressed with zstandard, `.toml.zst`):

```toml
[meta]
current_theory = "Draft.Deps_Wrapper"
theory_ancestors = ["Draft.Deps_Wrapper", "HOL.HOL", ...]
exporter_version = "0.1.0"
isabelle_identifier = "Isabelle2025"

[[theorems]]
key = "HOL-Examples.Ackermann:ackloop_dom_longer"
raw = "ackloop_dom_longer"
sel = 0
pretty = "ackloop_dom_longer"
theory = "HOL-Examples.Ackermann"
fingerprint = "<sha1>"
proposition = "ackloop m n ⟹ ackloop m (n + 1)"
constants = ["HOL-Examples.Ackermann.ackloop"]
types = ["HOL.Nat.nat"]
has_skip_proof = false
pos = ".../Ackermann.thy:42:1:..."

[[theorems.dependencies]]
key = "HOL.Nat:Suc_le_mono"
# ... same fields minus proposition/constants/types/has_skip_proof
```

See the [examples/](examples/) directory for full sample outputs.

---

## Supported Fact-Defining Commands

The following Isabelle outer-syntax commands are recognised by the extractor
(`ExportDeps/ExtractFacts.thy`) and by the Python pre-filter (`thy_filter.py`).
Both must be kept in sync when adding new command support.

| Command | Extracted facts |
|---|---|
| `theorem` / `lemma` / `corollary` / `proposition` / `schematic_goal` | `[name]` |
| `lemmas` | `[name]` |
| `definition` | `[name]`, `[name_def]` |
| `fun` | `.simps`, `.induct`, `.elims`, `.cases`, `.psimps`, `.pinduct`, `.pelims`, `.domintros`, named clause facts (`name.label`) |
| `primrec` | `.simps`, `.induct`, named clause facts |
| `inductive` | `.intros`, `.cases`, `.induct`, `.inducts`, `.simps`, named clause facts |
| `datatype` | `.inject`, `.distinct`, `.exhaust`, `.nchotomy`, `.case`, `.disc`, `.discI`, `.sel`, `.split`, `.split_asm`, `.induct`, `.rec`, `.map`, `.rel`, `.rel_induct`, `.set`, `.set_cases`, `.set_intros`, `.set_induct`, `.map_disc_iff`, `.map_sel` |
| `axiomatization` | fact names from `where` labels (e.g. `axiomatization where foo: "..."` → `foo`) |
| `nominal_datatype` | same suffixes as `datatype` |
| `nominal_primrec` | same as `primrec` |
| `nominal_inductive` | same as `inductive` |

**Maintenance**: to add a new command, update *both*:
1. `supported_command` in `ExportDeps/ExtractFacts.thy`
2. `SUPPORTED_COMMANDS` in `thy_filter.py`

---

## Project Structure

```
dep_extract.py              Single-theory extraction (named theorems)
bulk_deps.py                Batch extraction (by session/AFP/Isabelle src)
build_db.py                 Build/maintain the SQLite database (import, prepare-share)
query_db.py                 Query the SQLite database (deps, rdeps, search, show)
deps_db.py                  Peewee models and shared DB helpers (Theory, Theorem, DepEdge)
thy_filter.py               Pre-filter: skip .thy files with no supported commands
session.py                  ROOT file parsing and theory-to-session mapping
root_parser.py              Lark LALR grammar for Isabelle ROOT files
ExportDeps/
  ROOT                      Isabelle session definition (Pure + ExportDeps + ExtractFacts)
  BackwardCompatibleAPI.ML  Compatibility shim for Isabelle 2022 to 2025-2 API differences
  ExportDeps.ML             State_Deps structure: TOML helpers, dependency collection
  ExportDeps.thy            Defines the `export_deps` Isar command
  ExtractFacts.ML           Extract_Facts structure: fact scanning, extract_deps command
  ExtractFacts.thy          Declares `extract_facts` / `extract_deps` keywords
examples/                   Sample TOML outputs
pyproject.toml              Python project config
set_afp_env.sh              Helper to set $AFP environment variable
```

## License

MIT
