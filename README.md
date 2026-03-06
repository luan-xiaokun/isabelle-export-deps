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

Or with pip:

```bash
pip install isabelle-client
```

## AFP Environment Variable (Linux)

This repository provides a helper script to configure the AFP root path:

```bash
source ./set_afp_env.sh /path/to/afp
```

If no path is provided, the script prompts you to input the AFP path interactively.

After sourcing, `AFP` points to your AFP root directory and AFP theories are under `$AFP/thys`.

## Usage

### Single theory (`dep_extract.py`)

Extracts dependencies for specific named theorems from one theory file:

```
uv run dep_extract.py \
  --target-session <SESSION> \
  --theory <PATH_TO_THY> \
  --thms <THM1> [<THM2> ...] \
  --out <OUTPUT_FILE> \
  --dir <DIR> [--dir <DIR2> ...] \
  [--verbose]
```

| Option | Description |
|---|---|
| `--target-session` | The Isabelle session containing the target theory (e.g. `HOL-Examples`, `Completeness`) |
| `--theory` | Absolute or relative path to the target `.thy` file |
| `--thms` | One or more theorem/fact names to analyze |
| `--out` | Path where the TOML report will be written (`.toml` or `.toml.zst`) |
| `--dir` | Additional Isabelle root directories (**repeatable**; `ExportDeps/` is added automatically) |
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

### `--dir` Rules (dep_extract.py)

- **Isabelle built-in sessions** (e.g. `HOL-Examples`, `HOL-Library`): `ExportDeps/` is added automatically; no extra `--dir` needed.
- **AFP entries**: pass `--dir $AFP/thys/<EntryName>` (the directory containing the entry's `ROOT` file).
- **Custom projects**: pass the directory containing the project's `ROOT` file.

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

### Output format

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

## Project Structure

```
dep_extract.py              Single-theory extraction (named theorems)
bulk_deps.py                Batch extraction (by session/AFP/Isabelle src)
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
