"""Shared Lean 4 lexical and import-parsing helpers (Python 3.9+ stdlib only)."""
from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path

IMPORT_LINE_RE = re.compile(
    r"^(\s*)((?:public\s+|private\s+)?)(meta\s+)?import\s+(all\s+)?(.*?)\s*$"
)
IMPORT_LINE_PREFIX_RE = re.compile(r"^\s*(?:(?:public|private)\s+)?(?:meta\s+)?import\b")
OPEN_EXPORT_LINE_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:open|export)\s+(?:scoped\s+)?(.*)$")
IDENT_RE = re.compile(r"[A-Za-z_\u0370-\u03ff][\w.'!?\u2080-\u2089\u0370-\u03ff]*")
OPEN_TOK_RE = re.compile(r"^[A-Za-z_\u0370-\u03ff][\w.'\u2080-\u2089\u0370-\u03ff]*$")


def read_nonempty_lines(path: Path) -> list[str]:
    return [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def write_lines(path: Path, lines: list[str] | tuple[str, ...]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")


@dataclass(frozen=True)
class ImportSpec:
    indent: str
    visibility: str  # "public", "private", or ""
    is_meta: bool
    is_all: bool
    targets: list[str]

    @property
    def is_public(self) -> bool:
        return self.visibility == "public"

    @property
    def prefix(self) -> str:
        vis = f"{self.visibility} " if self.visibility else ""
        meta = "meta " if self.is_meta else ""
        all_tok = "all " if self.is_all else ""
        return f"{vis}{meta}import {all_tok}"


def mod_to_relpath(mod: str) -> str:
    return "src/" + mod.replace(".", "/") + ".lean"


def discover_src_modules(repo: Path) -> dict[str, Path]:
    src_dir = repo / "src"
    mods: dict[str, Path] = {}
    if not src_dir.is_dir():
        return mods
    for path in sorted(src_dir.rglob("*.lean")):
        rel = path.relative_to(src_dir).as_posix()
        mod = rel[:-5].replace("/", ".")
        mods[mod] = path
    return mods


def discover_project_dir_roots(repo: Path) -> set[str]:
    src_dir = repo / "src"
    if not src_dir.is_dir():
        return set()
    return {p.name for p in src_dir.iterdir() if p.is_dir()}


def is_missing_project_module(
    repo: Path,
    mod: str,
    project_dir_roots: set[str],
    dead_mods: set[str] | None = None,
) -> bool:
    """Return True if `mod` is deleted or under a project top-level dir with no file on disk."""
    if dead_mods and mod in dead_mods:
        return True
    if "." in mod and mod.split(".", 1)[0] in project_dir_roots:
        return not (repo / mod_to_relpath(mod)).is_file()
    return False


def strip_lean_comments(text: str) -> str:
    """Replace Lean 4 comments (-- ..., nested /- ... -/) and string literals with spaces.

    Newlines inside comments and strings are preserved so line numbers and
    line-oriented regexes remain aligned with the original source.
    """
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_line = False
    in_str = False
    in_guil = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if in_line:
            if ch == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
            continue

        if block_depth > 0:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.extend((" ", " "))
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.extend((" ", " "))
                i += 2
            elif ch == "\n":
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if in_str:
            if ch == "\\" and i + 1 < n:
                out.append(" ")
                out.append("\n" if nxt == "\n" else " ")
                i += 2
            elif ch == '"':
                in_str = False
                out.append(" ")
                i += 1
            elif ch == "\n":
                in_str = False
                out.append("\n")
                i += 1
            else:
                out.append(" ")
                i += 1
            continue

        if in_guil:
            out.append("\n" if ch == "\n" else ch)
            if ch == "»":
                in_guil = False
            i += 1
            continue

        if ch == "-" and nxt == "-":
            in_line = True
            out.extend((" ", " "))
            i += 2
        elif ch == "/" and nxt == "-":
            block_depth = 1
            out.extend((" ", " "))
            i += 2
        elif ch == '"':
            in_str = True
            out.append(" ")
            i += 1
        elif ch == "«":
            in_guil = True
            out.append(ch)
            i += 1
        else:
            out.append(ch)
            i += 1

    return "".join(out)


def parse_import_line(line: str) -> ImportSpec | None:
    m = IMPORT_LINE_RE.match(line)
    if not m:
        return None
    indent, vis_raw, meta_raw, all_raw, rest = m.groups()
    targets = [tok for tok in rest.split() if tok]
    return ImportSpec(
        indent=indent,
        visibility=vis_raw.strip(),
        is_meta=bool(meta_raw),
        is_all=bool(all_raw),
        targets=targets,
    )


def parse_lean_imports(text: str) -> list[ImportSpec]:
    cleaned = strip_lean_comments(text)
    specs: list[ImportSpec] = []
    for line in cleaned.splitlines():
        spec = parse_import_line(line)
        if spec is not None and spec.targets:
            specs.append(spec)
    return specs


LAKEFILE_ROOTS_RE = re.compile(r"^roots\s*=\s*\[(.*?)\]", re.MULTILINE | re.DOTALL)
LAKEFILE_ROOT_RE = re.compile(r'^root\s*=\s*"([^"]+)"', re.MULTILINE)
LAKEFILE_LEAN_ROOTS_RE = re.compile(r"roots\s*:=\s*#\[(.*?)\]", re.DOTALL)
LAKEFILE_LEAN_ROOT_RE = re.compile(r'root\s*:=\s*(?:`([A-Za-z0-9_.]+)|"([^"]+)")')


def parse_lakefile_roots(repo: Path) -> set[str]:
    """Auto-discover root modules from lakefile.toml / lakefile.lean, defaulting to {'Main'}."""
    roots: set[str] = set()
    toml_path = repo / "lakefile.toml"
    if toml_path.is_file():
        txt = toml_path.read_text(encoding="utf-8", errors="replace")
        for block in LAKEFILE_ROOTS_RE.findall(txt):
            roots.update(re.findall(r'"([^"]+)"', block))
        roots.update(LAKEFILE_ROOT_RE.findall(txt))

    lean_path = repo / "lakefile.lean"
    if lean_path.is_file():
        txt = strip_lean_comments(lean_path.read_text(encoding="utf-8", errors="replace"))
        for block in LAKEFILE_LEAN_ROOTS_RE.findall(txt):
            for tok in re.findall(r'`([A-Za-z0-9_.]+)|"([^"]+)"', block):
                mod = tok[0] or tok[1]
                if mod:
                    roots.add(mod)
        for m in LAKEFILE_LEAN_ROOT_RE.findall(txt):
            mod = m[0] or m[1]
            if mod:
                roots.add(mod)

    return roots or {"Main"}


def resolve_roots(repo: Path, roots_arg: str = "") -> set[str]:
    if roots_arg.strip():
        return {r.strip() for r in roots_arg.split(",") if r.strip()}
    return parse_lakefile_roots(repo)
