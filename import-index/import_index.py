#!/usr/bin/env python3
"""
import_index.py — Fast, zero-dependency SQLite Lean module & import-graph index.

Works on Linux, macOS, and Windows (Python 3.9+ stdlib + git).
Indexes ALL `.lean` files under `src/` (including Mathlib-only leaf modules!) so
reverse-cone queries, cycle checks, fixed-point orphan peels, and branch diff audits
run in milliseconds locally without slow full-repo `git grep`.

Performance:
  - Full build across ~61,000 Lean files via `git cat-file --batch`: ~4-8 seconds.
  - Incremental `sync` across upstream merges (`git diff --name-status`): <0.5 seconds.
  - Reverse cone / cycle / orphan peel / diff audit: <50 ms.

Subcommands:
  sync       Build (if missing) or incrementally update the SQLite index to `--ref` (default HEAD).
  stats      Show indexed commit, module count, edge count, and Mathlib-only leaf count.
  rev        Show direct importers and full transitive reverse cone of a module or path.
  cycle      Check whether adding an import `src -> dst` would create an import cycle.
  peel       Compute exact fixed-point orphaned modules (incl. leaf files) when dropping imports/cuts.
  audit-diff Audit `base..head` for dangling imports, cycles, protected-file touches, and forbidden patterns.
"""
from __future__ import annotations

import argparse
import collections
import datetime as dt
import json
import re
import sqlite3
import subprocess
import sys
import time
from pathlib import Path
from typing import Any, Iterable

SCHEMA_VERSION = "3"

# Matches `import Foo.Bar`, `public import Foo.Bar`, `private import Foo.Bar`, `import all Foo.Bar`, including Unicode subscripts & guillemets.
IMPORT_RE = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\s\-]+)")

PROTECTED_FILES = {
    "src/Main.lean",
    "src/Statements.lean",
    "src/Challenge.lean",
    "lakefile.toml",
    "lean-toolchain",
    "lake-manifest.json",
    "comparator.json",
    "export-targets.txt",
    "comparator/FormalConjecturesChallenge.lean",
    "comparator/formal-conjectures.json",
    "comparator/formal-conjectures-export-targets.txt",
}


def load_forbidden_patterns(patterns: list[str], forbid_files: list[Path]) -> list[re.Pattern[str]]:
    raw_patterns: list[str] = [p for p in patterns if p]
    for path in forbid_files:
        for line in path.read_text(encoding="utf-8").splitlines():
            s = line.strip()
            if s and not s.startswith("#"):
                raw_patterns.append(s)
    return [re.compile(p, re.IGNORECASE) for p in raw_patterns]

_OUTER_COMMENT_RE = re.compile(r'"(?:\\.|[^"\\])*"|--[^\n]*|/-')
_BLOCK_COMMENT_RE = re.compile(r"/-|-/")


def ensure_utf8_stdio() -> None:
    for stream in (sys.stdout, sys.stderr):
        try:
            if hasattr(stream, "reconfigure"):
                stream.reconfigure(encoding="utf-8", errors="replace")
        except Exception:
            pass


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def path_to_mod(path: str) -> str:
    p = path.replace("\\", "/")
    if p.startswith("src/"):
        p = p[4:]
    if p.endswith(".lean"):
        p = p[:-5]
    return p.replace("/", ".")


def mod_to_path(mod: str) -> str:
    m = mod.strip()
    if m.endswith(".lean"):
        return m.replace("\\", "/")
    return "src/" + m.replace(".", "/") + ".lean"


def normalize_mod(name: str) -> str:
    s = name.strip().replace("\\", "/")
    if s.endswith(".lean") or "/" in s:
        return path_to_mod(s)
    return s


def git_run(repo: Path, args: list[str], binary: bool = False) -> Any:
    r = subprocess.run(
        ["git", "-c", "core.quotepath=false"] + args,
        cwd=str(repo),
        capture_output=True,
        text=not binary,
        encoding=None if binary else "utf-8",
        errors=None if binary else "replace",
    )
    if r.returncode != 0:
        err = r.stderr.decode("utf-8", "replace") if binary else r.stderr
        raise RuntimeError(f"git {' '.join(args[:4])} failed ({r.returncode}): {err[:240]}")
    return r.stdout


def _try_rev_parse(repo: Path, ref_name: str) -> str:
    if not ref_name:
        return ""
    r = subprocess.run(
        ["git", "rev-parse", "--verify", "--quiet", f"{ref_name}^{{commit}}"],
        cwd=str(repo),
        capture_output=True,
        text=True,
    )
    return r.stdout.strip() if r.returncode == 0 else ""


def _is_ancestor(repo: Path, anc: str, desc: str) -> bool:
    if not anc or not desc:
        return False
    r = subprocess.run(
        ["git", "merge-base", "--is-ancestor", anc, desc],
        cwd=str(repo),
        capture_output=True,
    )
    return r.returncode == 0


def init_db(db_path: Path) -> sqlite3.Connection:
    db_path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(str(db_path))
    conn.execute("PRAGMA journal_mode=WAL")
    conn.execute("PRAGMA synchronous=NORMAL")
    conn.execute("PRAGMA temp_store=MEMORY")
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS meta (
            k TEXT PRIMARY KEY,
            v TEXT NOT NULL
        );
        CREATE TABLE IF NOT EXISTS modules (
            mod TEXT PRIMARY KEY,
            path TEXT UNIQUE NOT NULL,
            lines INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS edges (
            src_mod TEXT NOT NULL,
            dst_mod TEXT NOT NULL,
            is_public INTEGER NOT NULL DEFAULT 0
        );
        CREATE INDEX IF NOT EXISTS idx_edges_src ON edges(src_mod);
        CREATE INDEX IF NOT EXISTS idx_edges_dst ON edges(dst_mod);
        """
    )
    return conn


def get_meta(conn: sqlite3.Connection, key: str, default: str = "") -> str:
    row = conn.execute("SELECT v FROM meta WHERE k=?", (key,)).fetchone()
    return row[0] if row else default


def set_meta(conn: sqlite3.Connection, pairs: dict[str, str]) -> None:
    conn.executemany("INSERT OR REPLACE INTO meta (k, v) VALUES (?, ?)", list(pairs.items()))


def strip_lean_comments(text: str) -> str:
    """
    Strip Lean 4 `--` line comments and nested `/- ... -/` block comments while
    preserving exact line counts (newlines are retained). Uses C-backed regex scanning.
    """
    if "/-" not in text and "--" not in text:
        return text
    out: list[str] = []
    pos = 0
    n = len(text)
    while pos < n:
        m = _OUTER_COMMENT_RE.search(text, pos)
        if not m:
            out.append(text[pos:])
            break
        s, e = m.start(), m.end()
        tok = m.group(0)
        if tok.startswith('"'):
            out.append(text[pos:e])
            pos = e
        elif tok.startswith("--"):
            out.append(text[pos:s])
            pos = e
        else:
            out.append(text[pos:s])
            depth = 1
            bpos = e
            while depth > 0:
                mb = _BLOCK_COMMENT_RE.search(text, bpos)
                if not mb:
                    nl_cnt = text.count("\n", s)
                    if nl_cnt:
                        out.append("\n" * nl_cnt)
                    bpos = n
                    break
                if mb.group(0) == "/-":
                    depth += 1
                else:
                    depth -= 1
                bpos = mb.end()
            else:
                nl_cnt = text.count("\n", s, bpos)
                if nl_cnt:
                    out.append("\n" * nl_cnt)
            pos = bpos
    return "".join(out)


def parse_lean_imports(raw_bytes: bytes) -> tuple[int, list[tuple[str, int]]]:
    """Return (line_count, [(dst_mod, is_public), ...]) for a Lean source blob."""
    line_count = raw_bytes.count(b"\n")
    text = raw_bytes.decode("utf-8", errors="replace")
    imports: list[tuple[str, int]] = []
    # Imports in Lean 4 appear before declarations; track nested `/- ... -/` depth cleanly.
    block_depth = 0
    for line in text.splitlines():
        code_chars: list[str] = []
        i = 0
        n = len(line)
        while i < n:
            if block_depth == 0:
                if line[i : i + 2] == "--":
                    break
                if line[i : i + 2] == "/-":
                    block_depth += 1
                    i += 2
                    continue
                code_chars.append(line[i])
                i += 1
            else:
                if line[i : i + 2] == "/-":
                    block_depth += 1
                    i += 2
                    continue
                if line[i : i + 2] == "-/":
                    block_depth -= 1
                    i += 2
                    continue
                i += 1
        s = "".join(code_chars).strip()
        if not s or s == "module" or s.startswith("prelude"):
            continue
        m = IMPORT_RE.match(s)
        if m:
            dst = m.group(1).strip()
            is_pub = 1 if s.startswith("public ") else 0
            imports.append((dst, is_pub))
            continue
        # Stop scanning once the declaration/section body begins (huge speedup on large files!)
        break
    return line_count, imports


def find_clump_header_stale_imports(raw_text: str, stale_mods: set[str]) -> list[dict[str, Any]]:
    """
    Scan `-- clump-header: {...}` JSON metadata lines for embedded `import` references
    to any module in `stale_mods`. Clumped files carry duplicate imports inside these
    comment blobs that `parse_lean_imports` ignores, so editing/dropping a host wrapper
    and its top-level import leaves stale metadata unless cleaned here too.
    """
    if not raw_text or not stale_mods or "-- clump-header:" not in raw_text:
        return []
    hits: list[dict[str, Any]] = []
    for ln_no, ln in enumerate(raw_text.splitlines(), 1):
        s = ln.lstrip()
        if not s.startswith("-- clump-header:"):
            continue
        payload = s[len("-- clump-header:") :].strip()
        clump_member = ""
        try:
            obj = json.loads(payload)
            if isinstance(obj, dict):
                clump_member = str(obj.get("m", ""))
                hdr = obj.get("h", "")
            else:
                hdr = ""
        except Exception:
            hdr = payload
        if not isinstance(hdr, str):
            continue
        found: list[str] = []
        for hln in hdr.splitlines():
            m = IMPORT_RE.match(hln)
            if m:
                dst = m.group(1).strip()
                if dst in stale_mods and dst not in found:
                    found.append(dst)
        if found:
            hits.append({"line": ln_no, "clump_member": clump_member, "stale_imports": found})
    return hits


def stream_git_blobs(repo: Path, obj_specs: list[tuple[str, str]]) -> Iterable[tuple[str, bytes]]:
    """
    Stream many `(path, blob_sha)` pairs in ONE `git cat-file --batch` subprocess.
    """
    if not obj_specs:
        return
    proc = subprocess.Popen(
        ["git", "cat-file", "--batch"],
        cwd=str(repo),
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
    )
    assert proc.stdin is not None and proc.stdout is not None
    # Feed in a background thread or chunked? Writing ~61k 41-byte lines (~2.5 MB) via communicate would buffer all stdout.
    # Use a tiny writer thread to avoid pipe deadlock on large repos.
    import threading

    def writer() -> None:
        try:
            for _, sha in obj_specs:
                proc.stdin.write((sha + "\n").encode("utf-8"))
        except BrokenPipeError:
            pass
        finally:
            try:
                proc.stdin.close()
            except Exception:
                pass

    t = threading.Thread(target=writer, daemon=True)
    t.start()
    stdout = proc.stdout
    try:
        for path, _ in obj_specs:
            hdr = stdout.readline()
            if not hdr:
                break
            parts = hdr.decode("utf-8", "replace").strip().split()
            if len(parts) < 3 or parts[1] == "missing":
                continue
            size = int(parts[2])
            data = stdout.read(size)
            stdout.read(1)  # trailing LF
            yield path, data
    finally:
        try:
            stdout.close()
        except Exception:
            pass
        t.join()
        proc.wait()


def _git_show_blobs(repo: Path, ref: str, paths: list[str]) -> dict[str, str]:
    """Batch-read multiple `<ref>:<path>` blobs in one `git cat-file --batch` invocation."""
    uniq = sorted({p for p in paths if p})
    if not uniq:
        return {}
    specs = [(p, f"{ref}:{p}") for p in uniq]
    out: dict[str, str] = {}
    for p, data in stream_git_blobs(repo, specs):
        out[p] = data.decode("utf-8", errors="replace")
    return out


LEAN_ID_START = r"[^\W\d]"
LEAN_ID_CONT = r"[\w'₀₁₂₃₄₅₆₇₈₉]"
LEAN_IDENT = rf"{LEAN_ID_START}{LEAN_ID_CONT}*"
LEAN_QUAL_IDENT = rf"{LEAN_ID_START}[\w.'₀₁₂₃₄₅₆₇₈₉]*"
LEAN_ID_END = rf"(?!{LEAN_ID_CONT})"
LEAN_ID_PREV = rf"(?<!{LEAN_ID_CONT})"
LEAN_ID_PREV_NODOT = r"(?<![\w.'₀₁₂₃₄₅₆₇₈₉])"

_DECL_EXPORT_RE = re.compile(
    rf"^\s{{0,2}}(?:@\[[^\]]*\]\s*)*"
    rf"((?:(?:public|private|protected|noncomputable|unsafe|partial|scoped|local|meta)\s+)*)"
    rf"(theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom|alias)\s+"
    rf"({LEAN_QUAL_IDENT}){LEAN_ID_END}"
)
_NS_DECL_RE = re.compile(rf"^\s{{0,2}}namespace\s+({LEAN_QUAL_IDENT}){LEAN_ID_END}\s*$")
_SECTION_DECL_RE = re.compile(
    rf"^\s{{0,2}}(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|scoped|local)\s+)*section(?:\s+({LEAN_QUAL_IDENT}))?\s*$"
)
_END_DECL_RE = re.compile(rf"^\s{{0,2}}end(?:\s+({LEAN_QUAL_IDENT}))?\s*$")
_IMPLICIT_ATTR_RE = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:public|private|protected|noncomputable|scoped|local|meta)\s+)*instance\b"
    r"|\battribute\s+\[[^\]]*instance"
    r"|\b(?:infix|infixl|infixr|prefix|postfix|notation|macro|macro_rules|elab|syntax)\b"
)
_LEAN_IDENT_RE = re.compile(LEAN_IDENT)


def _active_ns(scope_stack: list[tuple[str, list[str]]]) -> str:
    segs: list[str] = []
    for kind, parts in scope_stack:
        if kind == "namespace":
            segs.extend(parts)
    return ".".join(segs)


def _step_scope_stack(ln: str, scope_stack: list[tuple[str, list[str]]]) -> str:
    """Update Lean namespace/section `scope_stack` for one comment-stripped line; return 'ns', 'sec', 'end', or ''."""
    m_ns = _NS_DECL_RE.match(ln)
    if m_ns:
        scope_stack.append(("namespace", [s for s in m_ns.group(1).split(".") if s]))
        return "ns"
    m_sec = _SECTION_DECL_RE.match(ln)
    if m_sec:
        sname = m_sec.group(1)
        scope_stack.append(("section", [s for s in sname.split(".") if s] if sname else []))
        return "sec"
    m_end = _END_DECL_RE.match(ln)
    if m_end:
        ename = m_end.group(1)
        if not ename:
            if scope_stack:
                scope_stack.pop()
        else:
            esegs = [s for s in ename.split(".") if s]
            match_pos = -1
            for k in range(len(scope_stack) - 1, -1, -1):
                skind, sparts = scope_stack[k]
                if sparts and len(sparts) >= len(esegs) and sparts[-len(esegs) :] == esegs:
                    match_pos = k
                    break
                if skind == "section" and not sparts:
                    if len(scope_stack) - 1 - k >= 2:
                        break
            if match_pos != -1:
                skind, sparts = scope_stack[match_pos]
                if len(sparts) == len(esegs):
                    del scope_stack[match_pos:]
                else:
                    scope_stack[match_pos] = (skind, sparts[: len(sparts) - len(esegs)])
                    del scope_stack[match_pos + 1 :]
        return "end"
    return ""


def extract_exported_decls(clean_txt: str) -> tuple[list[dict[str, Any]], bool]:
    """
    Extract exported top-level declarations (tracking namespace/section stack) and
    whether the module declares any instances/notations/macros.
    """
    scope_stack: list[tuple[str, list[str]]] = []
    decls: list[dict[str, Any]] = []
    has_implicit = False

    for idx_ln, ln in enumerate(clean_txt.splitlines(), 1):
        if _IMPLICIT_ATTR_RE.search(ln):
            has_implicit = True
        if _step_scope_stack(ln, scope_stack):
            continue

        md = _DECL_EXPORT_RE.match(ln)
        if md:
            mods_kw, kind, raw_name = md.group(1), md.group(2), md.group(3)
            if re.search(r"\bprivate\b", mods_kw):
                continue
            raw_clean = raw_name[len("_root_.") :] if raw_name.startswith("_root_.") else raw_name
            active = _active_ns(scope_stack)
            if active and not raw_name.startswith("_root_."):
                full_name = f"{active}.{raw_clean}"
            else:
                full_name = raw_clean
            short_name = full_name.rsplit(".", 1)[-1]
            decl_ns = full_name.rsplit(".", 1)[0] if "." in full_name else ""
            decls.append(
                {
                    "short_name": short_name,
                    "full_name": full_name,
                    "ns": decl_ns,
                    "kind": kind,
                    "line": idx_ln,
                }
            )
    return decls, has_implicit


def check_host_secondary_symbols(
    host_clean_txt: str,
    dep_clean_by_mod: dict[str, str],
    excluded_line_indices: set[int] | None = None,
) -> dict[str, Any]:
    """
    Check whether a host module's remaining body (after excluding import headers and
    `excluded_line_indices`) STILL references any exported symbol from `dep_clean_by_mod`.
    Prevents false orphan peels when a dropped dependency is still used elsewhere in host!
    """
    excluded = excluded_line_indices or set()
    lines = host_clean_txt.splitlines()
    remaining_lines: list[str] = []
    past_header = False
    scope_stack: list[tuple[str, list[str]]] = []
    host_opened_ns: set[str] = set()

    for i, ln in enumerate(lines):
        st = ln.strip()
        if not past_header:
            if not st or st == "module" or st.startswith("prelude") or IMPORT_RE.match(st):
                remaining_lines.append("")
                continue
            past_header = True
        if i in excluded:
            remaining_lines.append("")
            continue
        remaining_lines.append(ln)
        kind_s = _step_scope_stack(ln, scope_stack)
        if kind_s == "ns":
            active = _active_ns(scope_stack)
            segs = [s for s in active.split(".") if s]
            for idx_s in range(1, len(segs) + 1):
                host_opened_ns.add(".".join(segs[:idx_s]))
        elif not kind_s:
            m_op = re.match(r"^\s*open\s+(?:scoped\s+)?(.+?)(?:\s+in\b.*)?$", st)
            if m_op:
                head_part = re.split(r"\b(?:hiding|renaming|only)\b|\(", m_op.group(1), maxsplit=1)[0]
                active = _active_ns(scope_stack)
                active_segs = [s for s in active.split(".") if s]
                for tok in head_part.split():
                    if tok and re.match(rf"^{LEAN_QUAL_IDENT}$", tok):
                        host_opened_ns.add(tok)
                        for idx_s in range(1, len(active_segs) + 1):
                            host_opened_ns.add(".".join(active_segs[:idx_s]) + "." + tok)

    remaining_text = "\n".join(remaining_lines)
    host_local_decls = {d["short_name"] for d in extract_exported_decls(remaining_text)[0]}
    remaining_tokens = set(_LEAN_IDENT_RE.findall(remaining_text))

    blockers: list[dict[str, Any]] = []
    seen_blocker_keys: set[tuple[str, str]] = set()
    any_implicit = False

    for dmod, dclean in sorted(dep_clean_by_mod.items()):
        if not dclean:
            continue
        decls, has_imp = extract_exported_decls(dclean)
        if has_imp:
            any_implicit = True
        for d in decls:
            short = d["short_name"]
            full = d["full_name"]
            ns = d["ns"]
            if short not in remaining_tokens:
                continue
            key = (dmod, full)
            if key in seen_blocker_keys:
                continue

            hit_lines: list[int] = []
            bare_ok = len(short) >= 4 and short not in host_local_decls and (
                (not ns)
                or (ns in host_opened_ns)
                or (d["kind"] in ("structure", "inductive", "class") and len(short) >= 5)
            )
            qtok_re = re.compile(rf"{LEAN_ID_PREV_NODOT}((?:{LEAN_QUAL_IDENT}\.)?{re.escape(short)}){LEAN_ID_END}")
            for li, rln in enumerate(remaining_lines):
                if short not in rln:
                    continue
                matched_ln = False
                for mq in qtok_re.finditer(rln):
                    tok = mq.group(1)
                    if "." in tok:
                        if tok.startswith("_root_."):
                            if tok[7:] == full:
                                matched_ln = True
                                break
                        elif tok == full:
                            matched_ln = True
                            break
                        elif full.endswith("." + tok):
                            rem_prefix = full[: -len(tok) - 1]
                            if not rem_prefix or rem_prefix in host_opened_ns:
                                matched_ln = True
                                break
                    elif bare_ok:
                        matched_ln = True
                        break
                if matched_ln:
                    hit_lines.append(li + 1)

            if hit_lines:
                seen_blocker_keys.add(key)
                blockers.append(
                    {
                        "dep_mod": dmod,
                        "symbol": full,
                        "short_name": short,
                        "kind": d["kind"],
                        "host_lines": hit_lines[:10],
                    }
                )

    return {
        "blocked": bool(blockers),
        "secondary_symbol_blockers": blockers[:25],
        "total_blocker_symbols": len(blockers),
        "has_instances_or_notations": any_implicit,
        "checked_dep_modules": len(dep_clean_by_mod),
    }


def full_build(conn: sqlite3.Connection, repo: Path, commit_sha: str, include_external: bool = False) -> dict[str, Any]:
    t0 = time.monotonic()
    tree_out = git_run(repo, ["ls-tree", "-r", commit_sha, "--", "src/"])
    specs: list[tuple[str, str]] = []
    all_mods: set[str] = set()
    for line in tree_out.splitlines():
        # Format: "<mode> <type> <sha>\t<path>"
        if "\t" not in line:
            continue
        meta_part, path = line.split("\t", 1)
        if not path.endswith(".lean"):
            continue
        sha = meta_part.split()[2]
        specs.append((path, sha))
        all_mods.add(path_to_mod(path))

    conn.execute("DELETE FROM edges")
    conn.execute("DELETE FROM modules")

    mod_rows: list[tuple[str, str, int]] = []
    edge_rows: list[tuple[str, str, int]] = []
    for path, raw in stream_git_blobs(repo, specs):
        mod = path_to_mod(path)
        lcnt, imps = parse_lean_imports(raw)
        mod_rows.append((mod, path, lcnt))
        for dst, is_pub in imps:
            if include_external or dst in all_mods:
                edge_rows.append((mod, dst, is_pub))

    conn.executemany("INSERT INTO modules (mod, path, lines) VALUES (?, ?, ?)", mod_rows)
    conn.executemany("INSERT INTO edges (src_mod, dst_mod, is_public) VALUES (?, ?, ?)", edge_rows)
    set_meta(
        conn,
        {
            "schema_version": SCHEMA_VERSION,
            "commit": commit_sha,
            "built_at": utc_now(),
            "include_external": "1" if include_external else "0",
        },
    )
    conn.commit()
    return {
        "mode": "full_build",
        "commit": commit_sha[:10],
        "modules": len(mod_rows),
        "edges": len(edge_rows),
        "elapsed_s": round(time.monotonic() - t0, 2),
    }


def incremental_sync(conn: sqlite3.Connection, repo: Path, old_sha: str, new_sha: str, include_external: bool = False) -> dict[str, Any]:
    t0 = time.monotonic()
    if old_sha == new_sha:
        return {
            "mode": "up_to_date",
            "commit": new_sha[:10],
            "modules": conn.execute("SELECT COUNT(*) FROM modules").fetchone()[0],
            "edges": conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0],
            "elapsed_s": round(time.monotonic() - t0, 3),
        }

    diff_out = git_run(repo, ["diff", "--name-status", f"{old_sha}..{new_sha}", "--", "src/"])
    diff_lines = diff_out.splitlines()
    # If >5,000 files changed (e.g. massive re-clump), full_build is cleaner & faster
    if len(diff_lines) > 5000:
        return full_build(conn, repo, new_sha, include_external=include_external)

    to_delete: set[str] = set()
    to_update_paths: set[str] = set()
    for ln in diff_lines:
        parts = ln.split("\t")
        st = parts[0]
        if st.startswith("R") or st.startswith("C"):
            old_p, new_p = parts[1], parts[2]
            if old_p.endswith(".lean"):
                to_delete.add(path_to_mod(old_p))
            if new_p.endswith(".lean"):
                to_update_paths.add(new_p)
        elif st == "D":
            if parts[1].endswith(".lean"):
                to_delete.add(path_to_mod(parts[1]))
        else:
            if parts[1].endswith(".lean"):
                to_update_paths.add(parts[1])

    all_mods = {r[0] for r in conn.execute("SELECT mod FROM modules")}
    all_mods -= to_delete
    for p in to_update_paths:
        all_mods.add(path_to_mod(p))

    for m in to_delete:
        conn.execute("DELETE FROM edges WHERE src_mod=?", (m,))
        if not include_external and m not in all_mods:
            conn.execute("DELETE FROM edges WHERE dst_mod=?", (m,))
        conn.execute("DELETE FROM modules WHERE mod=?", (m,))
    for p in to_update_paths:
        m = path_to_mod(p)
        conn.execute("DELETE FROM edges WHERE src_mod=?", (m,))
        conn.execute("DELETE FROM modules WHERE mod=?", (m,))

    if to_update_paths:
        # Resolve blob SHAs for updated paths
        specs: list[tuple[str, str]] = []
        tree_out = git_run(repo, ["ls-tree", "-r", new_sha, "--"] + sorted(to_update_paths))
        for line in tree_out.splitlines():
            if "\t" not in line:
                continue
            meta_part, path = line.split("\t", 1)
            specs.append((path, meta_part.split()[2]))

        mod_rows = []
        edge_rows = []
        for path, raw in stream_git_blobs(repo, specs):
            mod = path_to_mod(path)
            lcnt, imps = parse_lean_imports(raw)
            mod_rows.append((mod, path, lcnt))
            for dst, is_pub in imps:
                if include_external or dst in all_mods:
                    edge_rows.append((mod, dst, is_pub))
        conn.executemany("INSERT OR REPLACE INTO modules (mod, path, lines) VALUES (?, ?, ?)", mod_rows)
        conn.executemany("INSERT INTO edges (src_mod, dst_mod, is_public) VALUES (?, ?, ?)", edge_rows)

    set_meta(conn, {"commit": new_sha, "built_at": utc_now()})
    conn.commit()
    return {
        "mode": "incremental_sync",
        "old": old_sha[:10],
        "commit": new_sha[:10],
        "deleted": len(to_delete),
        "updated": len(to_update_paths),
        "modules": conn.execute("SELECT COUNT(*) FROM modules").fetchone()[0],
        "edges": conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0],
        "elapsed_s": round(time.monotonic() - t0, 3),
    }


def load_graph(conn: sqlite3.Connection) -> tuple[dict[str, tuple[str, int]], dict[str, set[str]], dict[str, set[str]]]:
    mods = {m: (p, l) for m, p, l in conn.execute("SELECT mod, path, lines FROM modules")}
    fwd: dict[str, set[str]] = collections.defaultdict(set)
    rev: dict[str, set[str]] = collections.defaultdict(set)
    for s, d in conn.execute("SELECT src_mod, dst_mod FROM edges"):
        fwd[s].add(d)
        rev[d].add(s)
    return mods, fwd, rev


def check_remote_main(repo: Path, remote: str = "origin", timeout: int = 8) -> str:
    try:
        r = subprocess.run(
            ["git", "ls-remote", "--heads", remote, "main"],
            cwd=str(repo),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
        if r.returncode == 0 and r.stdout.strip():
            return r.stdout.strip().split()[0]
    except Exception:
        pass
    return ""


def resolve_repo(args_repo: Path | None, db_path: Path | None = None) -> Path:
    if args_repo is not None:
        return args_repo.resolve()
    if db_path is not None and db_path.exists():
        try:
            conn = sqlite3.connect(str(db_path))
            stored = get_meta(conn, "repo_root")
            conn.close()
            if stored and Path(stored).exists():
                return Path(stored).resolve()
        except Exception:
            pass
    return Path(".").resolve()


def cmd_sync(args: argparse.Namespace) -> int:
    if args.repo is not None:
        repo = args.repo.resolve()
    elif (Path(".") / "src").exists() or not args.db.exists():
        repo = Path(".").resolve()
    else:
        repo = resolve_repo(None, args.db)

    if args.fetch:
        git_run(repo, ["fetch", args.remote, "+refs/heads/main:refs/remotes/" + args.remote + "/main"])
    target_sha = git_run(repo, ["rev-parse", args.ref]).strip()
    if args.expect_sha and not target_sha.startswith(args.expect_sha.strip()):
        print(
            json.dumps(
                {
                    "error": "SHA_MISMATCH",
                    "ref": args.ref,
                    "resolved": target_sha[:12],
                    "expected": args.expect_sha.strip(),
                },
                indent=2,
            ),
            file=sys.stderr,
        )
        return 2

    conn = init_db(args.db)
    cur_ver = get_meta(conn, "schema_version")
    old_sha = get_meta(conn, "commit")
    inc_ext = bool(args.include_external)
    if args.rebuild or cur_ver != SCHEMA_VERSION or not old_sha:
        res = full_build(conn, repo, target_sha, include_external=inc_ext)
    else:
        try:
            res = incremental_sync(conn, repo, old_sha, target_sha, include_external=inc_ext)
        except Exception:
            res = full_build(conn, repo, target_sha, include_external=inc_ext)

    set_meta(conn, {"repo_root": str(repo)})
    conn.commit()
    res["repo_root"] = str(repo)

    if not args.no_remote_check:
        rem_sha = check_remote_main(repo, args.remote)
        if rem_sha and rem_sha != target_sha:
            res["stale_vs_remote"] = True
            res["remote_main"] = rem_sha[:10]
            print(
                f"WARNING: Indexed {args.ref} ({target_sha[:10]}) is behind {args.remote}/main ({rem_sha[:10]}). "
                f"Re-run with `--fetch` to sync against live remote!",
                file=sys.stderr,
            )
        elif rem_sha:
            res["stale_vs_remote"] = False
    print(json.dumps(res, indent=2))
    return 0


def cmd_stats(args: argparse.Namespace) -> int:
    conn = init_db(args.db)
    total_mods = conn.execute("SELECT COUNT(*) FROM modules").fetchone()[0]
    total_edges = conn.execute("SELECT COUNT(*) FROM edges").fetchone()[0]
    with_proj_imps = conn.execute("SELECT COUNT(DISTINCT src_mod) FROM edges").fetchone()[0]
    total_lines = conn.execute("SELECT COALESCE(SUM(lines), 0) FROM modules").fetchone()[0]
    commit = get_meta(conn, "commit")
    repo_root = get_meta(conn, "repo_root")
    out: dict[str, Any] = {
        "db": str(args.db),
        "schema_version": get_meta(conn, "schema_version"),
        "commit": commit[:10],
        "built_at": get_meta(conn, "built_at"),
        "repo_root": repo_root,
        "total_modules": total_mods,
        "mathlib_only_leaf_modules": total_mods - with_proj_imps,
        "total_project_edges": total_edges,
        "total_lines": total_lines,
    }
    if args.check_remote:
        check_repo = resolve_repo(args.repo, args.db)
        out["checked_repo"] = str(check_repo)
        if not (check_repo / "src" / "Main.lean").is_file():
            print(
                f"WARNING: checked_repo ({check_repo}) does not appear to be the Lean repo "
                f"(missing src/Main.lean); pass --repo <lean-checkout>.",
                file=sys.stderr,
            )
        rem_sha = check_remote_main(check_repo, args.remote)
        if rem_sha:
            out["remote_main"] = rem_sha[:10]
            out["stale_vs_remote"] = rem_sha != commit
    print(json.dumps(out, indent=2))
    return 0


def cmd_rev(args: argparse.Namespace) -> int:
    conn = init_db(args.db)
    mods, _, rev = load_graph(conn)
    target = normalize_mod(args.module)
    direct = sorted(rev.get(target, set()))
    cone = {target}
    q = [target]
    while q:
        m = q.pop()
        for p in rev.get(m, ()):
            if p not in cone:
                cone.add(p)
                q.append(p)
    cone_sorted = sorted(cone)
    out = {
        "indexed_commit": get_meta(conn, "commit")[:10],
        "module": target,
        "exists": target in mods,
        "lines": mods[target][1] if target in mods else 0,
        "direct_importers_count": len(direct),
        "direct_importers": direct[:50],
        "reverse_cone_count": len(cone_sorted),
        "reaches_Main": "Main" in cone,
        "reaches_Statements": "Statements" in cone,
        "reaches_Challenge": "Challenge" in cone,
        "reverse_cone": cone_sorted if len(cone_sorted) <= 80 else cone_sorted[:40] + [f"... (+{len(cone_sorted)-40} more)"],
    }
    print(json.dumps(out, indent=2))
    return 0


def cmd_cycle(args: argparse.Namespace) -> int:
    conn = init_db(args.db)
    _, fwd, _ = load_graph(conn)
    src = normalize_mod(args.src)
    dst = normalize_mod(args.dst)
    # Adding edge src -> dst creates a cycle iff src is reachable from dst via fwd edges.
    vis = {dst}
    parent: dict[str, str | None] = {dst: None}
    q = collections.deque([dst])
    found = False
    while q:
        cur = q.popleft()
        if cur == src:
            found = True
            break
        for nxt in fwd.get(cur, ()):
            if nxt not in vis:
                vis.add(nxt)
                parent[nxt] = cur
                q.append(nxt)
    path: list[str] = []
    if found:
        cur: str | None = src
        while cur is not None:
            path.append(cur)
            cur = parent[cur]
        path.reverse()
    print(
        json.dumps(
            {
                "indexed_commit": get_meta(conn, "commit")[:10],
                "adding_edge": f"{src} -> {dst}",
                "creates_cycle": found,
                "dst_fwd_closure_size": len(vis),
                "witness_path": path,
            },
            indent=2,
        )
    )
    return 0


def reachable_from(
    roots: Iterable[str],
    mods: dict[str, tuple[str, int]],
    fwd: dict[str, set[str]],
    cut_set: set[tuple[str, str]],
) -> set[str]:
    vis: set[str] = set()
    q: list[str] = []
    for r in roots:
        if r in mods and r not in vis:
            vis.add(r)
            q.append(r)
    while q:
        cur = q.pop()
        for nxt in fwd.get(cur, ()):
            if (cur, nxt) in cut_set or nxt not in mods or nxt in vis:
                continue
            vis.add(nxt)
            q.append(nxt)
    return vis


def compute_multi_peel(
    mods: dict[str, tuple[str, int]],
    fwd: dict[str, set[str]],
    rev: dict[str, set[str]],
    cuts: list[tuple[str, str]],
    drop_mods: set[str] | None = None,
    mode: str = "zero-indegree",
) -> dict[str, Any]:
    """
    Compute fixed-point orphan cascade for cutting `(host, dep)` edges and/or severing `drop_mods`.
    Returns rich dict with zero-indegree orphans, Main-reachability orphans, blockers, and self-cert checks.
    """
    drop_mods = drop_mods or set()
    cut_set = set(cuts)
    rem_rev = {m: set(rev.get(m, ())) for m in mods}
    q: list[str] = []
    for h, d in cuts:
        if d in rem_rev:
            rem_rev[d].discard(h)
            if not rem_rev[d] and d in mods:
                q.append(d)
    for dm in drop_mods:
        if dm in mods and not rem_rev.get(dm):
            q.append(dm)

    zero_dead: set[str] = set()
    while q:
        m = q.pop()
        if m in zero_dead or m not in mods:
            continue
        if not rem_rev.get(m):
            zero_dead.add(m)
            for dep in fwd.get(m, ()):
                if dep in rem_rev:
                    rem_rev[dep].discard(m)
                    if not rem_rev[dep] and dep in mods and dep not in zero_dead:
                        q.append(dep)

    if "Main" in mods:
        reach_before = reachable_from(["Main"], mods, fwd, set())
        reach_after = reachable_from(["Main"], mods, fwd, cut_set)
        if "Main" in drop_mods:
            reach_after.discard("Main")
        main_reach_orphans = reach_before - reach_after
    else:
        reach_before = set()
        reach_after = set()
        main_reach_orphans = set()

    non_main_blocker_mods = sorted(main_reach_orphans - zero_dead)
    non_main_blocker_sample: list[list[str]] = []
    for dep in non_main_blocker_mods:
        for imp in sorted(rev.get(dep, ())):
            if imp not in main_reach_orphans and imp not in zero_dead and (imp, dep) not in cut_set:
                non_main_blocker_sample.append([imp, dep])
                if len(non_main_blocker_sample) >= 20:
                    break
        if len(non_main_blocker_sample) >= 20:
            break

    dead = zero_dead if mode == "zero-indegree" else main_reach_orphans

    # Independent self-certification: verify ZERO surviving modules import any module in `dead`
    survivor_dangling: list[list[str]] = []
    non_main_dangling: list[list[str]] = []
    for s in mods:
        if s in dead:
            continue
        is_main_survivor = True if mode == "zero-indegree" else (s in reach_after)
        for d in fwd.get(s, ()):
            if d in dead and (s, d) not in cut_set:
                if is_main_survivor:
                    survivor_dangling.append([s, d])
                else:
                    non_main_dangling.append([s, d])

    hosts_set = {h for h, _ in cuts}
    host_cone = set(hosts_set)
    hq = list(hosts_set)
    while hq:
        cur = hq.pop()
        for imp in rev.get(cur, ()):
            if imp not in host_cone:
                host_cone.add(imp)
                hq.append(imp)

    return {
        "dead": dead,
        "zero_dead": zero_dead,
        "main_reach_orphans": main_reach_orphans,
        "non_main_blocker_mods": non_main_blocker_mods,
        "non_main_blocker_sample": non_main_blocker_sample,
        "survivor_dangling": survivor_dangling,
        "non_main_dangling": non_main_dangling,
        "hosts": sorted(hosts_set),
        "union_rev_cone_of_hosts": len(host_cone),
    }


def cmd_peel(args: argparse.Namespace) -> int:
    conn = init_db(args.db)
    mods, fwd, rev = load_graph(conn)

    host_mod = normalize_mod(args.host) if args.host else ""
    raw_drops = args.drop if isinstance(args.drop, list) else [args.drop]
    drops = [normalize_mod(x) for item in raw_drops for x in str(item).split(",") if x.strip()]
    explicit_cuts: list[tuple[str, str]] = []
    if host_mod:
        for d in drops:
            explicit_cuts.append((host_mod, d))
    for cut_spec in args.cut:
        h_raw, sep, deps_raw = cut_spec.partition(":")
        if not sep or not h_raw.strip() or not deps_raw.strip():
            print(json.dumps({"error": "INVALID_CUT_FORMAT", "value": cut_spec, "expected": "HOST:DEP1[,DEP2]"}, indent=2), file=sys.stderr)
            return 2
        h_mod = normalize_mod(h_raw)
        for d_raw in deps_raw.split(","):
            if d_raw.strip():
                explicit_cuts.append((h_mod, normalize_mod(d_raw)))

    raw_drop_mods = args.drop_modules if isinstance(args.drop_modules, list) else [args.drop_modules]
    drop_mods_list = [normalize_mod(x) for item in raw_drop_mods for x in str(item).split(",") if x.strip()]
    drop_mods_set = set(drop_mods_list)

    if not explicit_cuts and not drop_mods_set:
        print(json.dumps({"error": "NO_CUTS_SPECIFIED", "hint": "Pass <host> --drop <deps>, --cut HOST:DEP, or --drop-modules <mods>"}, indent=2), file=sys.stderr)
        return 2

    referenced = ({host_mod} if host_mod else set()) | {h for h, _ in explicit_cuts} | {d for _, d in explicit_cuts} | drop_mods_set
    missing = sorted(m for m in referenced if m not in mods)
    missing_hints: dict[str, list[str]] = {}
    for miss in missing:
        suf = "." + miss.rsplit(".", 1)[-1]
        matches = [m for m in mods if m.endswith(suf) or m == miss][:5]
        if matches:
            missing_hints[miss] = matches

    raw_non_existent: list[list[str]] = []
    for h, d in explicit_cuts:
        if h in mods and d in mods and d not in fwd.get(h, ()):
            raw_non_existent.append([h, d])

    required_host_cuts: list[list[str]] = []
    all_cuts = list(explicit_cuts)
    seen_cuts = set(all_cuts)
    for dm in sorted(drop_mods_set):
        for imp in sorted(rev.get(dm, ())):
            if imp not in drop_mods_set:
                required_host_cuts.append([imp, dm])
                if (imp, dm) not in seen_cuts:
                    all_cuts.append((imp, dm))
                    seen_cuts.add((imp, dm))

    res = compute_multi_peel(mods, fwd, rev, all_cuts, drop_mods=drop_mods_set, mode=args.mode)
    dead: set[str] = res["dead"]
    dead_lines = sum(mods[m][1] for m in dead)
    leaf_dead = sorted(m for m in dead if not fwd.get(m))
    m_reach: set[str] = res["main_reach_orphans"]
    survivor_dangling = res["survivor_dangling"]

    transitive_drops_not_direct = [[h, d] for h, d in raw_non_existent if d in dead]
    non_existent_edges = [[h, d] for h, d in raw_non_existent if d not in dead]

    if non_existent_edges:
        print(
            f"WARNING: {len(non_existent_edges)} specified cut edge(s) do not exist in indexed graph: {non_existent_edges[:5]}",
            file=sys.stderr,
        )

    out: dict[str, Any] = {
        "indexed_commit": get_meta(conn, "commit")[:10],
        "mode": args.mode,
        "host": host_mod,
        "hosts": res["hosts"],
        "union_rev_cone_of_hosts": res["union_rev_cone_of_hosts"],
        "dropped_imports": drops if drops else [d for _, d in all_cuts],
        "cuts": [[h, d] for h, d in all_cuts],
        "orphan_module_count": len(dead),
        "mathlib_only_leaf_orphans": len(leaf_dead),
        "orphan_total_lines": dead_lines,
        "main_reach_orphan_count": len(m_reach),
        "main_reach_orphan_lines": sum(mods[m][1] for m in m_reach),
        "non_main_blockers_count": len(res["non_main_blocker_mods"]),
        "survivor_dangling_edges": len(survivor_dangling),
        "sample_orphans": sorted(dead)[:20],
        "leaf_orphans": leaf_dead,
        "edge_direction_note": "A -> B means A imports B; peel walks forward from cut edges and prunes dependencies that lose all paths.",
    }
    if transitive_drops_not_direct:
        out["transitive_drops_not_direct"] = transitive_drops_not_direct
    if non_existent_edges:
        out["non_existent_edges"] = non_existent_edges
    if required_host_cuts:
        out["required_host_cuts"] = required_host_cuts
    if res["non_main_blocker_sample"]:
        out["non_main_blockers_sample"] = res["non_main_blocker_sample"]
    if res["non_main_dangling"]:
        out["non_main_dangling_edges"] = len(res["non_main_dangling"])
        out["non_main_dangling_sample"] = res["non_main_dangling"][:20]
    if missing:
        out["missing_modules"] = missing
        if missing_hints:
            out["missing_hints"] = missing_hints
    if survivor_dangling:
        out["survivor_dangling_sample"] = survivor_dangling[:20]
    if args.out_list:
        Path(args.out_list).write_text("\n".join(mods[m][0] for m in sorted(dead)) + "\n", encoding="utf-8")
        out["written_list"] = str(args.out_list)
    if args.check_symbols:
        repo = resolve_repo(args.repo, args.db)
        indexed_sha = get_meta(conn, "commit")
        if args.ref:
            ref = args.ref
            ref_sha = _try_rev_parse(repo, ref)
            if not ref_sha:
                print(json.dumps({"error": "INVALID_REF", "ref": ref, "repo": str(repo)}, indent=2), file=sys.stderr)
                return 2
            if indexed_sha and ref_sha != indexed_sha:
                if _is_ancestor(repo, ref_sha, indexed_sha) and not args.allow_stale:
                    print(
                        json.dumps(
                            {
                                "error": "STALE_REF_VS_INDEX",
                                "ref": ref,
                                "ref_sha": ref_sha[:12],
                                "indexed_commit": indexed_sha[:12],
                                "hint": "Pass a newer --ref, re-run sync, or pass --allow-stale.",
                            },
                            indent=2,
                        ),
                        file=sys.stderr,
                    )
                    return 2
                warn_msg = (
                    f"Indexed DB ({indexed_sha[:10]}) differs from --ref {ref} ({ref_sha[:10]}); "
                    f"run sync for 1:1 alignment."
                )
                out["stale_index_vs_ref_warning"] = warn_msg
                print(f"WARNING: {warn_msg}", file=sys.stderr)
        else:
            ref = ""
            ref_sha = ""
            for cand in ("upstream/main", "origin/main"):
                csha = _try_rev_parse(repo, cand)
                if csha:
                    ref = cand
                    ref_sha = csha
                    break
            if not ref:
                if indexed_sha and _try_rev_parse(repo, indexed_sha):
                    ref = indexed_sha
                    ref_sha = indexed_sha
                else:
                    ref = "HEAD"
                    ref_sha = _try_rev_parse(repo, "HEAD")
            if indexed_sha and ref_sha and ref_sha != indexed_sha:
                warn_msg = (
                    f"Indexed DB ({indexed_sha[:10]}) differs from default check ref {ref} ({ref_sha[:10]}); "
                    f"run sync to refresh the graph."
                )
                out["stale_index_vs_ref_warning"] = warn_msg
                print(f"WARNING: {warn_msg}", file=sys.stderr)

        check_specs: list[tuple[str, str, list[str]]] = []
        all_sym_paths: set[str] = set()
        for h, d in all_cuts:
            if h not in mods or d not in mods:
                continue
            sub_reach = reachable_from([d], mods, fwd, set())
            check_mods = [d] + sorted((dead & sub_reach) - {d})[:299]
            all_sym_paths.add(mods[h][0])
            for cm in check_mods:
                all_sym_paths.add(mods[cm][0])
            check_specs.append((h, d, check_mods))
        raw_blobs = _git_show_blobs(repo, ref, sorted(all_sym_paths))
        clean_blobs = {p: strip_lean_comments(txt) for p, txt in raw_blobs.items()}
        host_symbol_checks: list[dict[str, Any]] = []
        for h, d, check_mods in check_specs:
            hclean = clean_blobs.get(mods[h][0], "")
            dmap = {cm: clean_blobs.get(mods[cm][0], "") for cm in check_mods}
            sres = check_host_secondary_symbols(hclean, dmap)
            host_symbol_checks.append(
                {
                    "host": h,
                    "dep": d,
                    "blocked": sres["blocked"],
                    "total_blocker_symbols": sres["total_blocker_symbols"],
                    "secondary_symbol_blockers": sres["secondary_symbol_blockers"],
                    "has_instances_or_notations": sres["has_instances_or_notations"],
                    "checked_dep_modules": sres["checked_dep_modules"],
                }
            )
        out["symbol_check_ref"] = ref[:12] if len(ref) == 40 else ref
        if ref_sha:
            out["symbol_check_sha"] = ref_sha[:12]
        out["host_symbol_checks"] = host_symbol_checks
    print(json.dumps(out, indent=2))
    return 2 if (missing or survivor_dangling) else 0


def find_introduced_cycles(
    touched_mods: set[str],
    del_mods: set[str],
    fwd: dict[str, set[str]],
    head_imports: dict[str, set[str]],
) -> list[list[str]]:
    """Iterative 3-color DFS from touched modules to detect any cycle in post-diff graph."""
    color: dict[str, int] = {}
    cycles: list[list[str]] = []
    path: list[str] = []
    for start in sorted(touched_mods):
        if color.get(start, 0) != 0:
            continue
        color[start] = 1
        path.append(start)
        nbrs = sorted(d for d in head_imports.get(start, fwd.get(start, ())) if d not in del_mods)
        stack: list[tuple[str, list[str], int]] = [(start, nbrs, 0)]
        while stack:
            node, adj, idx_i = stack[-1]
            if idx_i >= len(adj):
                color[node] = 2
                path.pop()
                stack.pop()
                continue
            nxt = adj[idx_i]
            stack[-1] = (node, adj, idx_i + 1)
            c = color.get(nxt, 0)
            if c == 1:
                pos = path.index(nxt)
                cycles.append(path[pos:] + [nxt])
                if len(cycles) >= 5:
                    return cycles
            elif c == 0:
                color[nxt] = 1
                path.append(nxt)
                nxt_adj = sorted(d for d in head_imports.get(nxt, fwd.get(nxt, ())) if d not in del_mods)
                stack.append((nxt, nxt_adj, 0))
    return cycles


def cmd_audit_diff(args: argparse.Namespace) -> int:
    repo = args.repo.resolve() if args.repo is not None else resolve_repo(None, args.db)
    base = args.base
    head = args.head
    base_sha = git_run(repo, ["rev-parse", base]).strip()
    head_sha = git_run(repo, ["rev-parse", head]).strip()

    conn = init_db(args.db)
    idx_sha = get_meta(conn, "commit")
    if idx_sha != base_sha:
        # Auto-sync index to base_sha first!
        if not idx_sha or get_meta(conn, "schema_version") != SCHEMA_VERSION:
            full_build(conn, repo, base_sha)
        else:
            incremental_sync(conn, repo, idx_sha, base_sha)

    mods, fwd, rev = load_graph(conn)
    shortstat = git_run(repo, ["diff", "--shortstat", f"{base_sha}...{head_sha}"]).strip()
    ns_lines = git_run(repo, ["diff", "--name-status", f"{base_sha}...{head_sha}"]).splitlines()
    mod_paths, del_paths, add_paths = [], [], []
    for ln in ns_lines:
        parts = ln.split("\t")
        st = parts[0]
        if st == "M":
            mod_paths.append(parts[1])
        elif st == "D":
            del_paths.append(parts[1])
        elif st == "A":
            add_paths.append(parts[1])
        elif st.startswith("R"):
            del_paths.append(parts[1])
            add_paths.append(parts[2])

    del_mods = {path_to_mod(p) for p in del_paths if p.endswith(".lean")}
    touched_mods = {path_to_mod(p) for p in mod_paths + add_paths if p.endswith(".lean")}

    # 1. Check 0 dangling imports across ALL remaining modules in the repo
    dangling: list[tuple[str, str]] = []
    for dm in del_mods:
        for importer in rev.get(dm, ()):
            if importer in del_mods or importer in touched_mods:
                continue
            dangling.append((importer, dm))

    # 2. Check modified/added files' actual imports on HEAD + added lines for forbidden patterns / sorry
    forbidden_res = load_forbidden_patterns(
        getattr(args, "forbid_pattern", []),
        getattr(args, "forbid_file", []),
    )
    protected_files = PROTECTED_FILES | set(getattr(args, "protected_file", []))
    forbidden_hits: list[str] = []
    bad_tokens: list[str] = []
    clump_warnings: list[dict[str, Any]] = []
    head_imports: dict[str, set[str]] = {}
    all_valid_mods = (set(mods) - del_mods) | touched_mods
    project_dir_roots = {m.split(".")[0] for m in (set(mods) | del_mods | touched_mods) if "." in m}
    for p in mod_paths + add_paths:
        if not p.endswith(".lean"):
            continue
        raw = git_run(repo, ["show", f"{head_sha}:{p}"], binary=True)
        _, imps = parse_lean_imports(raw)
        pmod = path_to_mod(p)
        head_imports[pmod] = {dst for dst, _ in imps if dst in all_valid_mods}
        for dst, _ in imps:
            if dst in del_mods or (
                "." in dst and dst.split(".")[0] in project_dir_roots and dst not in all_valid_mods
            ):
                dangling.append((pmod, dst))
        if del_mods and b"-- clump-header:" in raw:
            for ch in find_clump_header_stale_imports(raw.decode("utf-8", errors="replace"), del_mods):
                clump_warnings.append({"mod": pmod, "path": p, **ch})
        diff_txt = git_run(repo, ["diff", f"{base_sha}...{head_sha}", "--", p])
        for ln in diff_txt.splitlines():
            if ln.startswith("+") and not ln.startswith("+++"):
                for rx in forbidden_res:
                    if rx.search(ln):
                        forbidden_hits.append(f"{p}: {ln[:120]}")
                        break
                if re.search(r"\b(sorry|admit|axiom)\b", ln):
                    bad_tokens.append(f"{p}: {ln[:120]}")

    cycles = find_introduced_cycles(touched_mods, del_mods, fwd, head_imports)

    commit_msg = git_run(repo, ["log", "--format=%B", f"{base_sha}..{head_sha}"])
    for rx in forbidden_res:
        if rx.search(commit_msg):
            forbidden_hits.append(f"COMMIT_MSG: {rx.findall(commit_msg)}")

    protected_hits = sorted((set(mod_paths) | set(del_paths) | set(add_paths)) & protected_files)
    mt = subprocess.run(["git", "merge-tree", "--write-tree", base_sha, head_sha], cwd=str(repo), capture_output=True)

    passed = (
        mt.returncode == 0
        and len(dangling) == 0
        and len(cycles) == 0
        and len(protected_hits) == 0
        and len(forbidden_hits) == 0
        and len(bad_tokens) == 0
    )
    out = {
        "verdict": "PASS" if passed else "FAIL",
        "base": base_sha[:10],
        "head": head_sha[:10],
        "merge_tree_clean": mt.returncode == 0,
        "cycle_free": len(cycles) == 0,
        "introduced_cycles": cycles,
        "shortstat": shortstat,
        "counts": {"M": len(mod_paths), "D": len(del_paths), "A": len(add_paths)},
        "dangling_imports_count": len(dangling),
        "dangling_sample": dangling[:10],
        "clump_header_warnings_count": len(clump_warnings),
        "clump_header_warnings": clump_warnings[:20],
        "protected_file_hits": protected_hits,
        "forbidden_pattern_hits": forbidden_hits[:10],
        "bad_tokens": bad_tokens[:10],
    }
    print(json.dumps(out, indent=2))
    return 0 if passed else 1


def main() -> int:
    ensure_utf8_stdio()
    ap = argparse.ArgumentParser(description="Fast local SQLite import-graph index & verifier for Lean repos.")
    ap.add_argument("--repo", type=Path, default=None, help="Path to local riemann-hypothesis git checkout (defaults to indexed repo_root or cwd)")
    ap.add_argument("--db", type=Path, default=Path.home() / ".cache" / "rh-import-index" / "import_index.db")
    sub = ap.add_subparsers(dest="cmd", required=True)

    p_sync = sub.add_parser("sync", help="Build or incrementally sync SQLite index to --ref")
    p_sync.add_argument("--ref", default="HEAD")
    p_sync.add_argument("--remote", default="origin", help="Git remote to fetch/check against (default: origin)")
    p_sync.add_argument("--fetch", action="store_true", help="Run `git fetch <remote> +refs/heads/main:refs/remotes/<remote>/main` before syncing")
    p_sync.add_argument("--expect-sha", default="", help="Fail closed (exit 2) if resolved --ref does not start with this SHA prefix")
    p_sync.add_argument("--no-remote-check", action="store_true", help="Skip live remote staleness check")
    p_sync.add_argument("--rebuild", action="store_true")
    p_sync.add_argument("--include-external", action="store_true", help="Also store Mathlib/Std imports (larger DB)")

    p_stats = sub.add_parser("stats", help="Print index metadata & health")
    p_stats.add_argument("--check-remote", action="store_true", help="Compare indexed commit against live remote main")
    p_stats.add_argument("--remote", default="origin")

    p_rev = sub.add_parser("rev", help="Show direct importers & full reverse cone of a module")
    p_rev.add_argument("module")

    p_cyc = sub.add_parser("cycle", help="Check if adding src -> dst creates an import cycle")
    p_cyc.add_argument("src")
    p_cyc.add_argument("dst")

    p_peel = sub.add_parser("peel", help="Compute exact fixed-point orphan modules when dropping imports or cutting module subtrees")
    p_peel.add_argument("host", nargs="?", default=None, help="Host module dropping imports (optional if using --cut or --drop-modules)")
    p_peel.add_argument("--drop", action="append", default=[], help="Comma-separated or repeatable dropped module names from <host>")
    p_peel.add_argument("--cut", action="append", default=[], help="Additional edge cut HOST:DEP1[,DEP2,...] (repeatable)")
    p_peel.add_argument("--drop-modules", action="append", default=[], help="Comma-separated or repeatable target modules whose all incoming edges are severed")
    p_peel.add_argument("--mode", choices=["zero-indegree", "reach-main"], default="zero-indegree", help="Orphan definition mode")
    p_peel.add_argument("--check-symbols", action="store_true", help="Inspect host Lean source for secondary exported symbols of dropped deps")
    p_peel.add_argument("--ref", default="", help="Git ref for --check-symbols (defaults to upstream/main -> origin/main -> indexed commit)")
    p_peel.add_argument("--allow-stale", action="store_true", help="Allow --check-symbols against a --ref strictly older than indexed_commit")
    p_peel.add_argument("--out-list", type=Path, help="Optional file to write deleted paths")

    p_aud = sub.add_parser("audit-diff", help="Full <1s diff audit (dangling imports, cycles, merge-tree, protected files, forbidden patterns)")
    p_aud.add_argument("base")
    p_aud.add_argument("head", nargs="?", default="HEAD")
    p_aud.add_argument("--forbid-pattern", action="append", default=[], help="Case-insensitive regex forbidden in added lines or commit messages (repeatable)")
    p_aud.add_argument("--forbid-file", type=Path, action="append", default=[], help="File of forbidden regexes (one per line, # comments ignored)")
    p_aud.add_argument("--protected-file", action="append", default=[], help="Additional repo-relative path that must remain untouched (repeatable)")

    args = ap.parse_args()
    return {
        "sync": cmd_sync,
        "stats": cmd_stats,
        "rev": cmd_rev,
        "cycle": cmd_cycle,
        "peel": cmd_peel,
        "audit-diff": cmd_audit_diff,
    }[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
