# isabelle-export-deps

Extract theorem dependency snapshots from Isabelle theories. Given a target theory and theorem names, this tool produces a structured report including:

- Theory import closure (ancestors)
- Theorem dependencies (`thm_deps`) with canonical keys, source positions, etc.
- Proposition text, constants, types, and fingerprints for each theorem

It works by generating a temporary wrapper theory that imports both `ExportDeps` (which provides the `export_deps` command) and the target theory, then runs it via Isabella Server through [isabelle-client](https://pypi.org/project/isabelle-client/).

## Requirements

- **Isabelle 2025** (installed and available in `$PATH`)
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

## Usage

```
uv run dep_extract.py \
  --target-session <SESSION> \
  --theory <PATH_TO_THY> \
  --thms <THM1> [<THM2> ...] \
  --out <OUTPUT_FILE> \
  --dir <DIR> [--dir <DIR2> ...] \
  [--verbose]
```

### Key Options

| Option | Description |
|---|---|
| `--target-session` | The Isabelle session containing the target theory (e.g. `HOL-Examples`, `Completeness`) |
| `--theory` | Absolute or relative path to the target `.thy` file |
| `--thms` | One or more theorem/fact names to analyze |
| `--out` | Path where the output report will be written |
| `--dir` | Additional Isabelle root directories (**repeatable**, see below) |
| `--verbose` | Print Isabelle server diagnostics to stderr |

### `--dir` Rules

The `--dir` option tells Isabelle where to find session ROOT files. You **must** provide:

1. **The directory containing the `ExportDeps` session** (i.e. the `ExportDeps/` folder in this repo, which has its own `ROOT` file).
2. **The directory containing the target session's `ROOT` file**, if it is not part of Isabelle's bundled sessions.

In practice:

- **Isabelle built-in sessions** (e.g. `HOL-Examples`, `HOL-Library`): their ROOT files ship with Isabelle, so you only need `--dir ExportDeps`.
- **AFP entries**: AFP sessions are not built-in, so you must additionally pass `--dir` pointing to the AFP entry's directory (which contains the `ROOT` file). For example, `--dir ~/repositories/afp-2025/thys/Completeness`.

## Examples

### 1. HOL built-in theory (Ackermann)

The `HOL-Examples` session is bundled with Isabelle, so only the `ExportDeps` directory is needed:

```bash
uv run dep_extract.py \
  --target-session HOL-Examples \
  --theory ~/Isabelle2025/src/HOL/Examples/Ackermann.thy \
  --thms ackloop_dom_longer \
  --out examples/ackermann.txt \
  --dir ExportDeps
```

### 2. AFP entry (Completeness)

AFP sessions require an extra `--dir` pointing to the AFP entry folder:

```bash
uv run dep_extract.py \
  --target-session Completeness \
  --theory ~/repositories/afp-2025/thys/Completeness/Completeness.thy \
  --thms validProofTree \
  --out examples/completeness.txt \
  --dir ExportDeps \
  --dir ~/repositories/afp-2025/thys/Completeness \
  --verbose
```

### Output

The generated report looks like:

```
=== THEOREM DEPENDENCIES SNAPSHOT ===
Current theory: Draft.Deps_Wrapper
Theory ancestors (imports closure) (104):
  Draft.Deps_Wrapper
  ExportDeps.ExportDeps
  Main
  ...

Theorem dependencies (thm_deps) (42):
- key: HOL.Nat:Suc_le_mono
  raw: Suc_le_mono
  sel: 0
  pretty: Suc_le_mono
  theory: HOL.Nat
  pos: .../src/HOL/Nat.thy:123:...
...

Has skip proof: false

Theorem: ackloop_dom_longer
  fingerprint: ...
  proposition: ...
  constants: ...
  types: ...
```

See the [examples/](examples/) directory for full sample outputs.

## Project Structure

```
dep_extract.py          Main script
ExportDeps/
  ROOT                  Isabelle session definition
  ExportDeps.thy        ML code providing the `export_deps` command
examples/               Sample outputs
pyproject.toml          Python project config
```

## License

MIT
