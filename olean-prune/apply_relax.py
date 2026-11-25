#!/usr/bin/env python3
"""Strip dead namespace tokens from open/export lines in kept Lean files."""
from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

from lean_syntax import mod_to_relpath, strip_lean_comments

OPEN_EXPORT_RE = re.compile(r"^(\s*(?:@\[[^\]]*\]\s*)?(?:open|export)\s+(?:scoped\s+)?)(.*)$")


def _split_open_clauses(rest: str) -> list[tuple[str, str]]:
    """Split `rest` of an open/export line into `(ns_token, full_clause_text)` pairs."""
    clauses: list[tuple[str, str]] = []
    # Match `NS (a b)`, `NS hiding a b`, `NS renaming a -> b`, or bare `NS`
    tokens = rest.strip()
    if not tokens:
        return clauses

    # First tokenize keeping parenthesized groups intact
    parts = re.findall(r"[^\s(]+(?:\s*\([^)]*\))?|\S+", tokens)
    i = 0
    while i < len(parts):
        tok = parts[i]
        ns = tok.split("(")[0].strip()
        if "(" in tok:
            clauses.append((ns, tok))
            i += 1
            continue
        if i + 1 < len(parts) and parts[i + 1] == "hiding":
            # Consume remaining hidden identifiers until end of clause list
            hidden: list[str] = ["hiding"]
            j = i + 2
            while j < len(parts):
                hidden.append(parts[j])
                j += 1
            clauses.append((ns, f"{ns} " + " ".join(hidden)))
            break
        if i + 1 < len(parts) and parts[i + 1] == "renaming":
            ren: list[str] = ["renaming"]
            j = i + 2
            while j < len(parts):
                ren.append(parts[j])
                j += 1
            clauses.append((ns, f"{ns} " + " ".join(ren)))
            break
        clauses.append((ns, tok))
        i += 1
    return clauses


def relax_open_line(line: str, dead_tokens: set[str]) -> tuple[str | None, bool]:
    """Remove `dead_tokens` from an `open`/`export` line.

    Returns `(replacement_line_or_None, was_modified)`.
    `None` means the entire line became empty and should be deleted.
    """
    mm = OPEN_EXPORT_RE.match(line)
    if not mm:
        return line, False

    head, rest = mm.groups()
    tail = ""
    mt = re.search(r"(\s+in\b.*|\s*--.*)$", rest)
    if mt:
        tail = mt.group(1)
        rest = rest[: mt.start()]

    clauses = _split_open_clauses(rest)
    kept = [clause_txt for ns, clause_txt in clauses if ns not in dead_tokens]
    if len(kept) == len(clauses):
        return line, False

    if kept:
        return head + " ".join(kept) + tail, True

    stripped_tail = tail.strip()
    if stripped_tail.startswith("in"):
        indent = re.match(r"^\s*", head).group(0)
        after_in = re.sub(r"^\s*in\b\s*", "", tail)
        return (f"{indent}{after_in}" if stripped_tail != "in" else ""), True

    if stripped_tail.startswith("--"):
        indent = re.match(r"^\s*", head).group(0)
        return f"{indent}{stripped_tail}", True

    return None, True


def apply_relaxations(repo: Path, relax: dict[str, list[str]]) -> tuple[int, int]:
    relaxed_lines = 0
    touched_files = 0

    for mod, toks in sorted(relax.items()):
        dead_toks = set(toks)
        p = repo / mod_to_relpath(mod)
        if not p.is_file():
            continue
        raw = p.read_text(encoding="utf-8")
        lines = raw.split("\n")
        clean_lines = strip_lean_comments(raw).split("\n")
        out: list[str] = []
        file_changed = False

        for idx, line in enumerate(lines):
            clean_ln = clean_lines[idx] if idx < len(clean_lines) else ""
            if not OPEN_EXPORT_RE.match(clean_ln):
                out.append(line)
                continue
            new_line, changed = relax_open_line(line, dead_toks)
            if changed:
                relaxed_lines += 1
                file_changed = True
            if new_line is not None:
                out.append(new_line)

        if file_changed:
            p.write_text("\n".join(out), encoding="utf-8")
            touched_files += 1

    return relaxed_lines, touched_files


def main() -> int:
    ap = argparse.ArgumentParser(description="Strip dead opened namespaces from kept Lean files.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--relax-json", type=Path, required=True, help="Path to relax JSON from closeD.py")
    args = ap.parse_args()

    relax = json.loads(args.relax_json.read_text(encoding="utf-8"))
    n_lines, n_files = apply_relaxations(args.repo.resolve(), relax)
    print(f"relaxed lines={n_lines} files={n_files}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
