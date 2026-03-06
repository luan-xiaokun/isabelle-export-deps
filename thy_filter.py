"""thy_filter.py — Fast Python pre-filter for Isabelle theory files.

Determines whether a .thy file is worth submitting to the Isabelle server
by checking for the presence of supported fact-defining commands after
stripping comments and documentation bodies.

Supported commands
------------------
The set ``SUPPORTED_COMMANDS`` below mirrors ``ExtractFacts.thy``'s
``supported_command`` predicate exactly.

**Maintenance rule**: if you add a new command to ``ExtractFacts.thy``'s
``supported_command`` function, you must add it to ``SUPPORTED_COMMANDS``
here too.  Both lists are the single source of truth for different
layers of the pipeline:

  * ``SUPPORTED_COMMANDS`` (this file) — Python pre-filter
  * ``supported_command`` in ``ExportDeps/ExtractFacts.thy`` — Isabelle/ML extraction

Documentation commands stripped before searching
-------------------------------------------------
Bodies of the following markup commands are stripped because they contain
prose, not Isabelle source, and may contain words like "theorem" or "lemma":

  chapter  section  subsection  subsubsection
  paragraph  subparagraph  text  txt  text_raw

A body is either a ``\\<open>...\\<close>`` cartouche (arbitrarily nested)
or a ``"..."`` string literal (with backslash-escape handling).

``(* ... *)`` block comments (arbitrarily nested) are also stripped.

Conservative design
-------------------
The pre-filter errs on the side of inclusion: when in doubt it returns
``True`` (process the file).  A ``False`` result means the file
*definitely* contains no commands that would produce output.
Read/parse errors also return ``True``.
"""

from __future__ import annotations

import re
from pathlib import Path


# ---------------------------------------------------------------------------
# Supported fact-defining commands.
# THIS LIST MUST MATCH ExportDeps/ExtractFacts.thy's supported_command predicate.
# See README.md § "Supported Fact-Defining Commands" for the full list.
# ---------------------------------------------------------------------------

SUPPORTED_COMMANDS: frozenset[str] = frozenset(
    {
        # Standard proof commands
        "theorem",
        "lemma",
        "corollary",
        "proposition",
        "schematic_goal",
        "lemmas",
        # Definitions
        "definition",
        # Recursive / pattern-matching definitions
        "fun",
        "primrec",
        # Inductive predicates / sets
        "inductive",
        # Algebraic datatypes
        "datatype",
        # Axiomatic declarations
        "axiomatization",
        # Nominal package (syntax for name-binding)
        "nominal_datatype",
        "nominal_primrec",
        "nominal_inductive",
    }
)

# ---------------------------------------------------------------------------
# Documentation/markup commands whose body text is *not* Isabelle source.
# ---------------------------------------------------------------------------

_DOC_COMMANDS: frozenset[str] = frozenset(
    {
        "chapter",
        "section",
        "subsection",
        "subsubsection",
        "paragraph",
        "subparagraph",
        "text",
        "txt",
        "text_raw",
    }
)

# ---------------------------------------------------------------------------
# Compiled regex: keyword at start of line (after optional whitespace),
# followed by a word boundary.  Built from SUPPORTED_COMMANDS automatically.
# ---------------------------------------------------------------------------

_SUPPORTED_RE = re.compile(
    r"(?m)^\s*(?:"
    + "|".join(sorted(SUPPORTED_COMMANDS, key=len, reverse=True))
    + r")\b"
)

# Isabelle cartouche brackets as stored in .thy files (ASCII escape form).
_OPEN = r"\<open>"  # 7 chars: \  <  o  p  e  n  >
_CLOSE = r"\<close>"  # 8 chars: \  <  c  l  o  s  e  >
_LEN_OPEN = len(_OPEN)
_LEN_CLOSE = len(_CLOSE)


# ---------------------------------------------------------------------------
# Pre-processor: strip comments and doc bodies
# ---------------------------------------------------------------------------
def _preprocess(text: str) -> str:
    """Strip ``(* ... *)`` comments and documentation command bodies.

    Returns the processed text with:
    - Block comments replaced by a single space.
    - Doc-command bodies (cartouche or string) removed entirely.
    - Newlines always preserved so the subsequent line-anchored regex works.

    This is a *conservative* scanner: on ambiguity it keeps text.

    State overview
    ~~~~~~~~~~~~~~
    The scanner maintains six mutually-exclusive-ish state flags/depths:

    ``comment_depth``   — nesting depth inside ``(* ... *)``.
    ``string_open``     — inside a normal-level ``"..."`` (kept in output).
    ``cart_depth``      — nesting depth inside a normal-level cartouche (kept).
    ``doc_string``      — inside a doc-body ``"..."`` (stripped).
    ``doc_cart_depth``  — nesting depth inside a doc-body cartouche (stripped).
    ``doc_await``       — just saw a doc keyword; waiting for its body argument.
    """
    out: list[str] = []
    i = 0
    n = len(text)

    comment_depth: int = 0  # > 0 while inside (* ... *)
    string_open: bool = False  # True while inside "..." at normal level
    cart_depth: int = 0  # > 0 while inside \<open>...\<close> at normal level
    doc_string: bool = False  # True while inside "..." doc-body (stripped)
    doc_cart_depth: int = 0  # > 0 while inside \<open>...\<close> doc-body (stripped)
    doc_await: bool = False  # True after a doc keyword, waiting for its body

    while i < n:
        ch = text[i]

        # ── Inside block comment ──────────────────────────────────────────────
        if comment_depth > 0:
            if text[i : i + 2] == "(*":
                comment_depth += 1
                i += 2
            elif text[i : i + 2] == "*)":
                comment_depth -= 1
                i += 2
                if comment_depth == 0:
                    out.append(" ")  # replace comment with a space
            elif ch == "\n":
                out.append("\n")  # preserve newlines for line-anchored regex
                i += 1
            else:
                i += 1
            continue

        # ── Inside doc-body string (stripped) ────────────────────────────────
        if doc_string:
            if ch == "\\" and i + 1 < n:
                # Only newlines in escape sequences are preserved.
                if text[i + 1] == "\n":
                    out.append("\n")
                i += 2
            elif ch == '"':
                doc_string = False
                i += 1
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                i += 1
            continue

        # ── Inside doc-body cartouche (stripped, nested) ──────────────────────
        if doc_cart_depth > 0:
            if text[i : i + _LEN_OPEN] == _OPEN:
                doc_cart_depth += 1
                i += _LEN_OPEN
            elif text[i : i + _LEN_CLOSE] == _CLOSE:
                doc_cart_depth -= 1
                i += _LEN_CLOSE
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                i += 1
            continue

        # ── Inside normal string (kept) ───────────────────────────────────────
        if string_open:
            if ch == "\\" and i + 1 < n:
                out.append(ch)
                out.append(text[i + 1])
                i += 2
            elif ch == '"':
                out.append(ch)
                string_open = False
                i += 1
            else:
                out.append(ch)
                i += 1
            continue

        # ── Inside normal cartouche (kept, nested) ────────────────────────────
        if cart_depth > 0:
            if text[i : i + _LEN_OPEN] == _OPEN:
                cart_depth += 1
                out.append(text[i : i + _LEN_OPEN])
                i += _LEN_OPEN
            elif text[i : i + _LEN_CLOSE] == _CLOSE:
                cart_depth -= 1
                out.append(text[i : i + _LEN_CLOSE])
                i += _LEN_CLOSE
            elif text[i : i + 2] == "(*":
                # Block comments are valid inside cartouches.
                comment_depth += 1
                i += 2
            else:
                out.append(ch)
                i += 1
            continue

        # ── Normal mode ───────────────────────────────────────────────────────

        # Block comment start.
        if text[i : i + 2] == "(*":
            comment_depth += 1
            # A comment interrupting a doc-body wait is unusual; cancel conservatively
            # so we don't accidentally strip whatever comes after the comment.
            doc_await = False
            i += 2
            continue

        # Cartouche open: either starts a doc-body or a normal cartouche.
        if text[i : i + _LEN_OPEN] == _OPEN:
            if doc_await:
                doc_cart_depth = 1
                doc_await = False
            else:
                cart_depth += 1
                out.append(text[i : i + _LEN_OPEN])
            i += _LEN_OPEN
            continue

        # String literal: either starts a doc-body or a normal string.
        if ch == '"':
            if doc_await:
                doc_string = True
                doc_await = False
            else:
                string_open = True
                out.append(ch)
            i += 1
            continue

        # Whitespace while waiting for a doc body.
        if doc_await:
            if ch in " \t\r\n":
                out.append(ch)
                i += 1
                continue
            else:
                # Not a recognised body delimiter (neither \<open> nor ").
                # Cancel conservatively so we don't lose real content.
                doc_await = False
                # Fall through to normal character processing below.

        # Identifier: check for doc-command keywords.
        if ch.isalpha() or ch == "_":
            j = i
            while j < n and (text[j].isalnum() or text[j] == "_"):
                j += 1
            word = text[i:j]
            out.append(word)
            i = j
            if word in _DOC_COMMANDS:
                doc_await = True
            continue

        # Any other character — emit as-is.
        out.append(ch)
        i += 1

    return "".join(out)


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------
def has_supported_commands(thy_path: Path) -> bool:
    """Return ``True`` if *thy_path* may contain supported fact-defining commands.

    Uses a fast Python pre-filter (no Isabelle server required):

      1. Read the file.
      2. Strip block comments and documentation command bodies.
      3. Search for a supported command keyword at the start of a line.

    Conservative: always returns ``True`` on any read or preprocessing error,
    and when the result is ambiguous.  A ``False`` result guarantees the file
    contains no commands that the Isabelle extractor would act on.
    """
    try:
        text = thy_path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return True  # unreadable → assume it might have commands

    try:
        cleaned = _preprocess(text)
        return bool(_SUPPORTED_RE.search(cleaned))
    except Exception:
        return True  # preprocessing failed → conservative fallback
