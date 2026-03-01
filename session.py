from dataclasses import dataclass, field
from pathlib import Path

from lark import Token, Tree
from lark.visitors import Interpreter
from typing import Generator

from root_parser import _parser


@dataclass
class SessionInfo:
    name: str
    main_dir: Path
    parent_session: str | None
    root_file: Path
    directories: list[Path] = field(default_factory=list)


def _token_str(tok: Token) -> str:
    """Extract the string value from a Token, stripping quotes from STRING tokens."""
    s = str(tok)
    if tok.type == "STRING":
        return s[1:-1]
    return s


class RootParser(Interpreter):
    """Walk a Lark parse tree and collect all session_entry nodes
    into a list[SessionInfo]."""

    def __init__(self, root_file: Path) -> None:
        self.root_file = root_file
        self._sessions: list[SessionInfo] = []

    def parse(self, tree: Tree) -> list[SessionInfo]:
        self._sessions = []
        self.visit(tree)
        return self._sessions

    def session_entry(self, tree: Tree) -> None:
        name: str | None = None
        main_dir: Path = self.root_file.parent
        parent_session: str | None = None
        directories: list[Path] = []

        for child in tree.children:
            if isinstance(child, Token):
                # After ?name inlining, the first NAME/STRING token
                # (that isn't a keyword) is the session name.
                if name is None and child.type in ("NAME", "STRING"):
                    name = _token_str(child)
                continue

            # child is a Tree
            match child.data:
                case "dir":
                    # dir: "in" path | — after ?path, 0 or 1 token child
                    if child.children:
                        main_dir = (
                            self.root_file.parent / _token_str(child.children[0])
                        ).resolve()
                case "parent":
                    # parent: name "+" | — after ?name, 0 or 1 token child
                    if child.children:
                        parent_session = _token_str(child.children[0])
                case "directories":
                    # DIRECTORIES path* — keyword token + path tokens
                    for tok in child.children:
                        if isinstance(tok, Token) and tok.type in (
                            "PATH",
                            "STRING",
                        ):
                            directory = main_dir / _token_str(tok)
                            directories.append(directory.resolve())

        assert name is not None, f"session_entry is missing a name: {tree}"
        self._sessions.append(
            SessionInfo(
                name=name,
                main_dir=main_dir,
                parent_session=parent_session,
                root_file=self.root_file,
                directories=directories,
            )
        )


def parse_root_file(root_file: Path) -> list[SessionInfo]:
    """Parse the given ROOT file and return all SessionInfo entries defined in it."""
    tree = _parser.parse(root_file.read_text())
    return RootParser(root_file).parse(tree)


def build_dir_session_map(sessions: list[SessionInfo]) -> dict[Path, SessionInfo]:
    result = {}
    for session in sessions:
        if session.main_dir in result:
            print(
                f"Warning: Main directory {session.main_dir} already mapped to "
                f"session {result[session.main_dir].name}. "
                f"Overwriting with session {session.name}."
            )
        result[session.main_dir] = session
        for directory in session.directories:
            if directory in result:
                print(
                    f"Warning: Directory {directory} already mapped to "
                    f"session {result[directory].name}. "
                    f"Overwriting with session {session.name}."
                )
            result[directory] = session
    return result


def glob_theory_file_with_session(
    theories_dir: Path, verbose: bool = False
) -> Generator[tuple[Path, SessionInfo | None], None, None]:
    """Glob for .thy files in the given theories_dir, find their sessions from ROOT
    files, and yield (thy_file, session) pairs.

    The argument theories_dir is supposed to be the directory containing session
    directories, e.g., the "thys" directory in AFP.
    """
    sessions = []
    for root_file in theories_dir.glob("*/ROOT"):
        sessions.extend(parse_root_file(root_file))
    if verbose:
        print(f"Found {len(sessions)} sessions in {theories_dir}")

    dir_session_map = build_dir_session_map(sessions)
    if verbose:
        print(
            f"Mapped {len(dir_session_map)} directories to sessions in {theories_dir}"
        )

    # Now we can glob for .thy files and find their sessions
    for thy_file in theories_dir.glob("**/*.thy"):
        thy_dir = thy_file.parent
        session = dir_session_map.get(thy_dir)
        if verbose and session is None:
            print(f"Warning: No session found for theory file {thy_file}")
        else:
            yield thy_file, session


def test():
    import os

    afp_root = os.environ.get("AFP")
    if not afp_root:
        raise RuntimeError(
            "Please set AFP environment variable to your AFP root directory"
        )

    afp_thys_dir = Path(afp_root) / "thys"
    count = 0
    for _, _ in glob_theory_file_with_session(afp_thys_dir, verbose=True):
        count += 1
    print(f"Total .thy files found: {count}")


if __name__ == "__main__":
    test()
