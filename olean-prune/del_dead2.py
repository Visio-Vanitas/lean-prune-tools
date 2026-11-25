#!/usr/bin/env python3
"""Delete dead modules and splice their public imports into remaining importers."""
from __future__ import annotations

import argparse
from pathlib import Path
import sys

from lean_syntax import (
    ImportSpec,
    discover_project_dir_roots,
    is_missing_project_module,
    mod_to_relpath,
    parse_import_line,
    parse_lean_imports,
    read_nonempty_lines,
    strip_lean_comments,
)


def _split_line_comment(line: str) -> tuple[str, str]:
    in_str = False
    i = 0
    while i < len(line):
        ch = line[i]
        if in_str:
            if ch == "\\" and i + 1 < len(line):
                i += 2
                continue
            if ch == '"':
                in_str = False
        else:
            if ch == '"':
                in_str = True
            elif ch == "-" and i + 1 < len(line) and line[i + 1] == "-":
                return line[:i], line[i:]
        i += 1
    return line, ""


def verify_no_dangling_project_imports(
    repo: Path,
    edited_paths: list[Path],
    dead_mods: set[str],
    project_dir_roots: set[str],
) -> list[tuple[str, str]]:
    """Verify edited Lean files contain no imports targeting deleted or absent project modules."""
    dangling: list[tuple[str, str]] = []
    src_dir = repo / "src"
    for path in edited_paths:
        if not path.is_file():
            continue
        mod = path.relative_to(src_dir).as_posix()[:-5].replace("/", ".")
        text = path.read_text(encoding="utf-8", errors="replace")
        for spec in parse_lean_imports(text):
            for tgt in spec.targets:
                if is_missing_project_module(repo, tgt, project_dir_roots, dead_mods):
                    dangling.append((mod, tgt))
    return dangling


def apply_dead_deletions(
    repo: Path,
    dead_mods: set[str],
    clump_exclude: Path | None = None,
    *,
    verify: bool = True,
) -> tuple[int, int, int]:
    pub_cache: dict[str, list[tuple[str, bool, bool]]] = {}
    project_dir_roots = discover_project_dir_roots(repo)
    skipped_missing: list[tuple[str, str]] = []

    def read_pub_imports(mod: str) -> list[tuple[str, bool, bool]]:
        if mod in pub_cache:
            return pub_cache[mod]
        p = repo / mod_to_relpath(mod)
        if not p.is_file():
            pub_cache[mod] = []
            return []
        text = p.read_text(encoding="utf-8", errors="replace")
        out: list[tuple[str, bool, bool]] = []
        for spec in parse_lean_imports(text):
            if spec.is_public:
                for tgt in spec.targets:
                    out.append((tgt, spec.is_meta, spec.is_all))
        pub_cache[mod] = out
        return out

    def expand_public(mod: str, seen: set[str]) -> list[tuple[str, bool, bool]]:
        res: list[tuple[str, bool, bool]] = []
        for tgt, is_meta, is_all in read_pub_imports(mod):
            if tgt in dead_mods:
                if tgt not in seen:
                    seen.add(tgt)
                    for sub_t, sub_meta, sub_all in expand_public(tgt, seen):
                        res.append((sub_t, is_meta or sub_meta, is_all or sub_all))
            elif is_missing_project_module(repo, tgt, project_dir_roots, dead_mods):
                skipped_missing.append((mod, tgt))
            else:
                res.append((tgt, is_meta, is_all))
        return res

    src_dir = repo / "src"
    edited = 0
    added = 0
    edited_paths: list[Path] = []

    for path in sorted(src_dir.rglob("*.lean")):
        rel = path.relative_to(src_dir).as_posix()
        mod = rel[:-5].replace("/", ".")
        if mod in dead_mods:
            continue

        raw_text = path.read_text(encoding="utf-8", errors="replace")
        # Fast prefilter before full comment stripping: skip files with no dead module name on any import line.
        if not any(
            ("import" in ln and any(tok in dead_mods for tok in ln.split()))
            for ln in raw_text.splitlines()
        ):
            continue

        clean_lines = strip_lean_comments(raw_text).splitlines()
        orig_lines = raw_text.split("\n")

        # Determine which line indices actually contain an active import of a dead module
        active_specs: dict[int, ImportSpec] = {}
        has_dead = False
        for idx, cline in enumerate(clean_lines):
            spec = parse_import_line(cline)
            if spec is not None and spec.targets:
                active_specs[idx] = spec
                if any(t in dead_mods for t in spec.targets):
                    has_dead = True

        if not has_dead:
            continue

        keep_direct: list[str] = []
        keep_pub: set[str] = set()
        for spec in active_specs.values():
            surv = [t for t in spec.targets if t not in dead_mods]
            keep_direct.extend(surv)
            if spec.is_public:
                keep_pub.update(surv)

        have_any = set(keep_direct)
        have_pub = set(keep_pub)
        upgrade: set[str] = set()
        out_lines: list[str] = []

        for idx, orig_line in enumerate(orig_lines):
            spec = active_specs.get(idx)
            if spec is None:
                out_lines.append(orig_line)
                continue

            dm = [t for t in spec.targets if t in dead_mods]
            if not dm:
                out_lines.append(orig_line)
                continue

            _, trailing_cmt = _split_line_comment(orig_line)
            rest = [t for t in spec.targets if t not in dead_mods]
            if rest:
                sfx = (" " + trailing_cmt.lstrip()) if trailing_cmt else ""
                out_lines.append(f"{spec.indent}{spec.prefix}{' '.join(rest)}{sfx}")
            elif trailing_cmt:
                out_lines.append(f"{spec.indent}{trailing_cmt.lstrip()}")

            for d in dm:
                for tgt, d_meta, d_all in expand_public(d, {d}):
                    pub = spec.is_public
                    already = (tgt in have_pub) if pub else (tgt in have_any)
                    if not already:
                        if pub and tgt in have_any:
                            upgrade.add(tgt)
                        eff_meta = spec.is_meta or d_meta
                        eff_all = spec.is_all or d_all
                        vis_prefix = f"{spec.visibility} " if spec.visibility else ""
                        meta_prefix = "meta " if eff_meta else ""
                        all_prefix = "all " if eff_all else ""
                        out_lines.append(f"{spec.indent}{vis_prefix}{meta_prefix}import {all_prefix}{tgt}")
                        have_any.add(tgt)
                        if pub:
                            have_pub.add(tgt)
                        added += 1

        if upgrade:
            upgraded_lines: list[str] = []
            for ln in out_lines:
                clean_ln = strip_lean_comments(ln)
                sp = parse_import_line(clean_ln)
                if sp is not None and not sp.is_public:
                    kept_tgts = [t for t in sp.targets if t not in upgrade]
                    if len(kept_tgts) != len(sp.targets):
                        _, trailing_cmt = _split_line_comment(ln)
                        if kept_tgts:
                            sfx = (" " + trailing_cmt.lstrip()) if trailing_cmt else ""
                            upgraded_lines.append(f"{sp.indent}{sp.prefix}{' '.join(kept_tgts)}{sfx}")
                        elif trailing_cmt:
                            upgraded_lines.append(f"{sp.indent}{trailing_cmt.lstrip()}")
                        continue
                upgraded_lines.append(ln)
            out_lines = upgraded_lines

        path.write_text("\n".join(out_lines), encoding="utf-8")
        edited += 1
        edited_paths.append(path)

    removed = 0
    for mod in sorted(dead_mods):
        p = repo / mod_to_relpath(mod)
        if p.is_file():
            p.unlink()
            removed += 1

    if skipped_missing:
        for src_m, miss_t in skipped_missing:
            print(f"WARN skipped missing project public import: {src_m} -> {miss_t}", file=sys.stderr)

    if verify:
        dangling = verify_no_dangling_project_imports(repo, edited_paths, dead_mods, project_dir_roots)
        if dangling:
            sample = ", ".join(f"{m}->{t}" for m, t in dangling[:5])
            raise RuntimeError(f"Post-rewrite check found {len(dangling)} dangling project imports: {sample}")

    if clump_exclude is not None and clump_exclude.is_file():
        lines = clump_exclude.read_text(encoding="utf-8").splitlines()
        filtered = [ln for ln in lines if ln.strip() not in dead_mods]
        clump_exclude.write_text("\n".join(filtered) + ("\n" if lines and filtered else ""), encoding="utf-8")

    return edited, added, removed


def main() -> int:
    ap = argparse.ArgumentParser(description="Delete dead Lean modules and splice their public imports.")
    ap.add_argument("--repo", type=Path, required=True, help="Path to Lean project repository")
    ap.add_argument("--dead-list", type=Path, required=True, help="File listing dead module names (one per line)")
    ap.add_argument(
        "--exclude-file",
        "--clump-exclude",
        dest="exclude_file",
        type=Path,
        default=None,
        help="Optional exclude list file from which deleted modules should also be pruned",
    )
    ap.add_argument("--no-verify", action="store_true", help="Skip post-rewrite missing project import verification")
    args = ap.parse_args()

    dead_mods = set(read_nonempty_lines(args.dead_list))
    edited, added, removed = apply_dead_deletions(
        args.repo.resolve(),
        dead_mods,
        args.exclude_file,
        verify=not args.no_verify,
    )
    print(f"{edited} importers edited, {added} imports added, {removed} files removed")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
