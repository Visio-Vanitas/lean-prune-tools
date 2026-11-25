#!/usr/bin/env python3
"""Zero-dependency unit test suite for lean-dead-modules (Python 3.9+ stdlib only)."""
from __future__ import annotations

import json
import sqlite3
import sys
import tempfile
import unittest
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS_DIR))

import apply_relax  # noqa: E402
import closeD  # noqa: E402
import del_dead2  # noqa: E402
import lean_syntax as ls  # noqa: E402
import load as ld  # noqa: E402
import quickcheck as qc  # noqa: E402
import reach  # noqa: E402
import split as sp  # noqa: E402


def _write_repo_files(repo: Path, files: dict[str, str]) -> None:
    for rel, content in files.items():
        p = repo / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")


def _build_synthetic_graph(
    repo: Path,
    work_dir: Path,
    *,
    files: dict[str, str],
    names_rows: list[tuple[str, str, str]],
    deps_rows: list[tuple[str, str, str, str, list[str]]],
    ext_ns: list[str] | None = None,
) -> tuple[Path, Path]:
    _write_repo_files(repo, files)
    mods = ls.discover_src_modules(repo)
    g_before: dict[str, list[str]] = {}
    mod_set = set(mods)
    for mod, path in mods.items():
        imps: list[str] = []
        for spec in ls.parse_lean_imports(path.read_text(encoding="utf-8")):
            imps.extend(t for t in spec.targets if t in mod_set)
        g_before[mod] = imps

    work_dir.mkdir(parents=True, exist_ok=True)
    (work_dir / "G_before.json").write_text(json.dumps(g_before), encoding="utf-8")

    names_p = work_dir / "names.txt"
    names_p.write_text(
        "".join(f"{m}\t{k}\t{n}\n" for m, k, n in names_rows),
        encoding="utf-8",
    )

    deps_dir = work_dir / "olean" / "deps"
    deps_dir.mkdir(parents=True, exist_ok=True)
    (deps_dir / "r0000.tsv").write_text(
        "".join(f"{m}\t{tag}\t{k}\t{n}\t{' '.join(ds)}\n" for m, tag, k, n, ds in deps_rows),
        encoding="utf-8",
    )

    if ext_ns:
        (work_dir / "ext_ns.txt").write_text("\n".join(ext_ns) + "\n", encoding="utf-8")

    db_path = work_dir / "olean" / "decl_graph.db"
    ld.load_tsv_to_db(deps_dir, db_path)
    reach.compute_reach(db_path, {"Main", "Statements"})

    con = sqlite3.connect(str(db_path))
    try:
        live_mods = {
            m for (m,) in con.execute("SELECT DISTINCT d.mod FROM decls d JOIN live l ON l.id = d.id")
        }
    finally:
        con.close()

    keep_roots = ls.parse_lakefile_roots(repo) | {"Main", "Statements", "Challenge"}
    cands = sorted(m for m in mods if m not in live_mods and m not in keep_roots)
    cand_file = work_dir / "cand.txt"
    cand_file.write_text("\n".join(cands) + ("\n" if cands else ""), encoding="utf-8")
    return db_path, cand_file


class TestLeanSyntaxAndLoader(unittest.TestCase):
    def test_nested_comments_and_imports(self):
        src = "\n".join(
            [
                "/- outer /- inner",
                "import FakeGhost",
                "open FakeNS",
                "-/ still comment",
                "public import GhostTwo",
                "-/",
                'def strLit := "/- not comment -/ import Nope"',
                "-- import CommentedOut",
                "public meta import all Real.Sub₂ -- trailing",
                "private import Helper.One Helper.Two",
            ]
        )
        cleaned = ls.strip_lean_comments(src)
        self.assertNotIn("FakeGhost", cleaned)
        self.assertNotIn("GhostTwo", cleaned)
        self.assertNotIn("CommentedOut", cleaned)
        specs = ls.parse_lean_imports(src)
        self.assertEqual(len(specs), 2)
        self.assertTrue(specs[0].is_public and specs[0].is_meta and specs[0].is_all)
        self.assertEqual(specs[0].targets, ["Real.Sub₂"])
        self.assertEqual(specs[1].visibility, "private")
        self.assertEqual(specs[1].targets, ["Helper.One", "Helper.Two"])

    def test_load_and_reach(self):
        with tempfile.TemporaryDirectory() as td:
            work = Path(td)
            deps_dir = work / "olean" / "deps"
            deps_dir.mkdir(parents=True)
            (deps_dir / "r0000.tsv").write_text(
                "\n".join(
                    [
                        "Main\tfull\tthm\tMain.mainThm\tLiveMod.helper",
                        "LiveMod\tfull\tdef\tLiveMod.helper\t",
                        "LiveMod\tfull\tdef\tLiveMod.deadCode\tDeadDep.unused",
                        "DeadDep\tfull\tdef\tDeadDep.unused\t",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            db_path = work / "olean" / "decl_graph.db"
            n_decls, n_edges, n_files = ld.load_tsv_to_db(deps_dir, db_path)
            self.assertEqual((n_decls, n_edges, n_files), (4, 2, 1))
            n_roots, n_seen, n_total = reach.compute_reach(db_path, {"Main", "Statements"})
            self.assertEqual((n_roots, n_seen, n_total), (1, 2, 4))


class TestCloseD(unittest.TestCase):
    def test_close_d_all_soft_edges_and_unicode_and_nesting(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            repo = root / "repo"
            work = root / "work"

            files = {
                "lakefile.toml": 'roots = ["Main", "Statements", "Challenge"]\n',
                "src/Main.lean": "\n".join(
                    [
                        "import KeptLive",
                        "import UnreachedLive",
                        "theorem mainThm : True := UnreachedLive.liveUsed KeptLive.k",
                    ]
                ),
                "src/Statements.lean": "theorem stmt : True := trivial\n",
                "src/Challenge.lean": "theorem chal : True := sorry\n",
                "src/KeptLive.lean": "\n".join(
                    [
                        "import PolyApproxCut",
                        "import PolyApproxLive",
                        "import InertStub",
                        "import AttrStub",
                        "import OpenRelaxMod",
                        "import ExtNsUser",
                        "import UnicodeProvider₂",
                        "import ScopedProvider",
                        "import ExportProvider",
                        "import RelNsMod",
                        "import HideRenMod",
                        "/- nested /- open GhostCand -/ -/",
                        "open PolyNS (Ch PolyApproxAt)",
                        "open PolyNS hiding HiddenItem",
                        "open PolyNS renaming RenamedSrc → RenamedDst",
                        "open RelaxNS",
                        "open MathlibExt",
                        "open scoped ScopedNS",
                        "namespace Outer",
                        "open Inner (relItem)",
                        "end Outer",
                        "variable (x : AttrStub) (u : Uni₂.item)",
                        "def k : True := trivial",
                    ]
                ),
                "src/UnreachedLive.lean": "\n".join(
                    [
                        "import HardConstCand",
                        "import TextRefCand",
                        "def liveUsed (_ : True) : True := trivial",
                        "def deadInLive : True := HardConstCand.hc",
                        "variable (y : TextRefCand.Ty)",
                    ]
                ),
                "src/PolyApproxCut.lean": "def PolyNS.Ch : Nat := 1\ndef PolyNS.PolyApproxAt : Nat := 2\n",
                "src/PolyApproxLive.lean": "def PolyNS.alive : Nat := 3\n",
                "src/InertStub.lean": "import InertTarget\nopen SomeNS\nset_option pp.all true\n",
                "src/InertTarget.lean": "def targetVal : Nat := 4\n",
                "src/AttrStub.lean": "attribute [simp] Nat.add_zero\n",
                "src/OpenRelaxMod.lean": "def RelaxNS.r : Nat := 5\n",
                "src/ExtNsUser.lean": "def MathlibExt.m : Nat := 6\n",
                "src/UnicodeProvider₂.lean": "def Uni₂.item : Nat := 7\n",
                "src/ScopedProvider.lean": "scoped notation \"⟪x⟫\" => x\n",
                "src/ExportProvider.lean": "export PolyNS (alive)\n",
                "src/RelNsMod.lean": "def Outer.Inner.relItem : Nat := 8\n",
                "src/HideRenMod.lean": "def PolyNS.HiddenItem : Nat := 9\ndef PolyNS.RenamedSrc : Nat := 10\n",
                "src/HardConstCand.lean": "def HardConstCand.hc : True := trivial\n",
                "src/TextRefCand.lean": "def TextRefCand.Ty : Type := Unit\n",
                "src/PureDead.lean": "def PureDead.dead : Nat := 0\n",
                "src/GhostCand.lean": "def GhostNS.g : Nat := 0\n",
            }

            names_rows = [
                ("Main", "thm", "Main.mainThm"),
                ("Statements", "thm", "Statements.stmt"),
                ("Challenge", "thm", "Challenge.chal"),
                ("KeptLive", "def", "KeptLive.k"),
                ("UnreachedLive", "def", "UnreachedLive.liveUsed"),
                ("UnreachedLive", "def", "UnreachedLive.deadInLive"),
                ("PolyApproxCut", "def", "PolyNS.Ch"),
                ("PolyApproxCut", "def", "PolyNS.PolyApproxAt"),
                ("PolyApproxLive", "def", "PolyNS.alive"),
                ("InertTarget", "def", "InertTarget.targetVal"),
                ("OpenRelaxMod", "def", "RelaxNS.r"),
                ("ExtNsUser", "def", "MathlibExt.m"),
                ("UnicodeProvider₂", "def", "Uni₂.item"),
                ("RelNsMod", "def", "Outer.Inner.relItem"),
                ("HideRenMod", "def", "PolyNS.HiddenItem"),
                ("HideRenMod", "def", "PolyNS.RenamedSrc"),
                ("HardConstCand", "def", "HardConstCand.hc"),
                ("TextRefCand", "def", "TextRefCand.Ty"),
                ("PureDead", "def", "PureDead.dead"),
                ("GhostCand", "def", "GhostNS.g"),
            ]
            deps_rows = [
                ("Main", "full", "thm", "Main.mainThm", ["KeptLive.k", "UnreachedLive.liveUsed"]),
                ("Statements", "full", "thm", "Statements.stmt", []),
                ("Challenge", "full", "thm", "Challenge.chal", []),
                ("KeptLive", "full", "def", "KeptLive.k", []),
                ("UnreachedLive", "full", "def", "UnreachedLive.liveUsed", []),
                ("UnreachedLive", "full", "def", "UnreachedLive.deadInLive", ["HardConstCand.hc"]),
                ("PolyApproxCut", "full", "def", "PolyNS.Ch", []),
                ("PolyApproxCut", "full", "def", "PolyNS.PolyApproxAt", []),
                ("PolyApproxLive", "full", "def", "PolyNS.alive", []),
                ("InertTarget", "full", "def", "InertTarget.targetVal", []),
                ("OpenRelaxMod", "full", "def", "RelaxNS.r", []),
                ("ExtNsUser", "full", "def", "MathlibExt.m", []),
                ("UnicodeProvider₂", "full", "def", "Uni₂.item", []),
                ("RelNsMod", "full", "def", "Outer.Inner.relItem", []),
                ("HideRenMod", "full", "def", "PolyNS.HiddenItem", []),
                ("HideRenMod", "full", "def", "PolyNS.RenamedSrc", []),
                ("HardConstCand", "full", "def", "HardConstCand.hc", []),
                ("TextRefCand", "full", "def", "TextRefCand.Ty", []),
                ("PureDead", "full", "def", "PureDead.dead", []),
                ("GhostCand", "full", "def", "GhostNS.g", []),
            ]

            _, cand_file = _build_synthetic_graph(
                repo,
                work,
                files=files,
                names_rows=names_rows,
                deps_rows=deps_rows,
                ext_ns=["MathlibExt"],
            )

            out_set = work / "v3b_set.txt"
            out_relax = work / "v3b_relax.json"
            final_set, relax_dict = closeD.run_close_d(
                repo=repo,
                work_dir=work,
                cand_file=cand_file,
                out_set=out_set,
                out_relax=out_relax,
                policy_name="conservative",
            )
            final_s = set(final_set)

            # Must KEEP all modules protected by hard edges, selective open, relative open,
            # hiding/renaming, non-inert zero-const, export, scoped, and live open+textref providers.
            for must_keep in (
                "Main",
                "Statements",
                "Challenge",
                "HardConstCand",
                "TextRefCand",
                "PolyApproxCut",
                "HideRenMod",
                "RelNsMod",
                "AttrStub",
                "ScopedProvider",
                "ExportProvider",
                "PolyApproxLive",
                "UnicodeProvider₂",  # referenced via text outside open (`UnicodeProvider₂` token) or kept
            ):
                self.assertNotIn(must_keep, final_s, f"{must_keep} should be KEPT")

            # Must DELETE inert stub (+ its unreached target), relaxed-open provider, external-ns shadow cand, unreferenced PureDead & GhostCand
            for must_del in ("PureDead", "GhostCand", "InertStub", "InertTarget", "OpenRelaxMod", "ExtNsUser"):
                self.assertIn(must_del, final_s, f"{must_del} should be DELETED")

            # RelaxNS was opened only by KeptLive and provided only by OpenRelaxMod -> must be in relax_dict
            self.assertIn("RelaxNS", relax_dict.get("KeptLive", []))
            # MathlibExt is external -> IGNORE (never stripped)
            self.assertNotIn("MathlibExt", relax_dict.get("KeptLive", []))


class TestDelDeadAndApplyRelax(unittest.TestCase):
    def test_del_dead2_splicing_upgrades_and_meta_all(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _write_repo_files(
                repo,
                {
                    "src/Dead1.lean": (
                        "/- /- public import Ignored -/ -/\n"
                        "public meta import Dead2\n"
                        "private import SecretHelper\n"
                        "def d1 : Nat := 1\n"
                    ),
                    "src/Dead2.lean": "public import all LeafA\ndef d2 : Nat := 2\n",
                    "src/LeafA.lean": "def la : Nat := 3\n",
                    "src/SecretHelper.lean": "def sh : Nat := 4\n",
                    "src/Host.lean": (
                        "private import LeafA\n"
                        "public import Dead1\n"
                        "theorem h : True := trivial\n"
                    ),
                },
            )
            edited, added, removed = del_dead2.apply_dead_deletions(repo, {"Dead1", "Dead2"})
            self.assertEqual(removed, 2)
            self.assertEqual(edited, 1)
            self.assertGreaterEqual(added, 1)
            host_txt = (repo / "src/Host.lean").read_text(encoding="utf-8")
            self.assertNotIn("Dead1", host_txt)
            self.assertNotIn("SecretHelper", host_txt)
            self.assertNotIn("Ignored", host_txt)
            # Public import of Dead1 splices Dead2's public import LeafA as `public meta import all LeafA`
            # and removes the redundant `private import LeafA`.
            self.assertIn("public meta import all LeafA", host_txt)
            self.assertNotIn("private import LeafA", host_txt)

    def test_apply_relax_hiding_in_and_comments(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _write_repo_files(
                repo,
                {
                    "src/Sample.lean": "\n".join(
                        [
                            "open DeadA LiveB hiding keepHidden",
                            "open DeadA hiding droppedHidden",
                            "open DeadA (foo bar) LiveB",
                            "  open DeadA in theorem keepCmd : True := trivial",
                            "open DeadA",
                            "/- open DeadA -/",
                        ]
                    )
                    + "\n",
                },
            )
            n_lines, n_files = apply_relax.apply_relaxations(repo, {"Sample": ["DeadA"]})
            self.assertEqual((n_lines, n_files), (5, 1))
            lines = (repo / "src/Sample.lean").read_text(encoding="utf-8").splitlines()
            self.assertEqual(
                lines,
                [
                    "open LiveB hiding keepHidden",
                    "open LiveB",
                    "  theorem keepCmd : True := trivial",
                    "/- open DeadA -/",
                ],
            )

    def test_del_dead2_skips_absent_upstream_public_import_and_guards_existing_dangling(self):
        with tempfile.TemporaryDirectory() as td:
            repo = Path(td)
            _write_repo_files(
                repo,
                {
                    "src/Dev/DeadMod.lean": "\n".join(
                        [
                            "public import Dev.RemovedUpstream",
                            "public import Dev.ExistingLeaf",
                            "public import Mathlib.Tactic",
                            "def dm : Nat := 1",
                        ]
                    ),
                    "src/Dev/ExistingLeaf.lean": "def el : Nat := 2\n",
                    "src/Dev/Host.lean": "import Dev.DeadMod\ntheorem ok : True := trivial\n",
                },
            )
            edited, _, removed = del_dead2.apply_dead_deletions(repo, {"Dev.DeadMod"})
            self.assertEqual((edited, removed), (1, 1))
            host_txt = (repo / "src/Dev/Host.lean").read_text(encoding="utf-8")
            self.assertNotIn("Dev.RemovedUpstream", host_txt)
            self.assertIn("import Dev.ExistingLeaf", host_txt)
            self.assertIn("import Mathlib.Tactic", host_txt)

        # If a kept file already carries an untouched missing project import, verification must fail.
        with tempfile.TemporaryDirectory() as td2:
            repo2 = Path(td2)
            _write_repo_files(
                repo2,
                {
                    "src/Dev/DeadMod.lean": "def dm : Nat := 1\n",
                    "src/Dev/Host.lean": "import Dev.DeadMod\nimport Dev.AlreadyGone\n",
                },
            )
            with self.assertRaises(RuntimeError):
                del_dead2.apply_dead_deletions(repo2, {"Dev.DeadMod"})


class TestSplitAndQuickcheck(unittest.TestCase):
    def test_split_colocates_relaxed_providers_and_adaptive_depth(self):
        with tempfile.TemporaryDirectory() as td:
            root = Path(td)
            repo = root / "repo"
            work = root / "work"

            files = {
                "src/Main.lean": "import KeptUser\ntheorem m : True := trivial\n",
                "src/KeptUser.lean": "import Dev.Mod1\nimport Dev.Mod2\nopen SharedNS\n",
                "src/Dev/AreaX/A.lean": "def ax : Nat := 1\n",
                "src/Dev/AreaY/B.lean": "def ay : Nat := 2\n",
                "src/Dev/Mod1.lean": "def SharedNS.x : Nat := 1\n",
                "src/Dev/Mod2.lean": "def SharedNS.y : Nat := 2\n",
            }
            names_rows = [
                ("Main", "thm", "Main.m"),
                ("Dev.AreaX.A", "def", "AreaX.ax"),
                ("Dev.AreaY.B", "def", "AreaY.ay"),
                ("Dev.Mod1", "def", "SharedNS.x"),
                ("Dev.Mod2", "def", "SharedNS.y"),
            ]
            deps_rows = [(m, "full", k, n, []) for m, k, n in names_rows]
            _build_synthetic_graph(repo, work, files=files, names_rows=names_rows, deps_rows=deps_rows)

            set_file = work / "dead.txt"
            set_file.write_text("Dev.AreaX.A\nDev.AreaY.B\nDev.Mod1\nDev.Mod2\n", encoding="utf-8")
            relax_file = work / "relax.json"
            relax_file.write_text(json.dumps({"KeptUser": ["SharedNS"]}), encoding="utf-8")
            out_dir = work / "chunks"

            manifest = sp.split_dead_set(
                repo=repo,
                work_dir=work,
                set_file=set_file,
                relax_file=relax_file,
                out_dir=out_dir,
                max_chunk=2,
                area_depth=1,
                adaptive_depth=True,
            )

            # Dev.Mod1 and Dev.Mod2 both provide SharedNS, so relax_coloc MUST place them in the SAME chunk.
            chunk_map = {m: c["id"] for c in manifest["chunks"] for m in c["modules"]}
            self.assertEqual(chunk_map["Dev.Mod1"], chunk_map["Dev.Mod2"])
            relax_files = list(out_dir.glob("relax*.json"))
            self.assertEqual(len(relax_files), 1)
            self.assertEqual(relax_files[0].name, f"relax{chunk_map['Dev.Mod1']:02d}.json")

            # Adaptive depth refined Dev.AreaX and Dev.AreaY into sub-areas.
            areas = {c["area"] for c in manifest["chunks"]}
            self.assertIn("Dev.AreaX", areas)
            self.assertIn("Dev.AreaY", areas)

    def test_clopper_pearson_ci_matches_exact_values(self):
        self.assertEqual(qc.clopper_pearson_ci(0, 0), (0.0, 1.0))
        lo0, hi0 = qc.clopper_pearson_ci(0, 396, alpha=0.05)
        self.assertEqual(lo0, 0.0)
        self.assertAlmostEqual(hi0, 1.0 - 0.025 ** (1.0 / 396), places=10)

        lo4, hi4 = qc.clopper_pearson_ci(4, 400, alpha=0.05)
        self.assertAlmostEqual(lo4, 0.002731, places=5)
        self.assertAlmostEqual(hi4, 0.025403, places=5)

        lo_all, hi_all = qc.clopper_pearson_ci(20, 20, alpha=0.05)
        self.assertAlmostEqual(lo_all, 0.025 ** (1.0 / 20), places=10)
        self.assertEqual(hi_all, 1.0)


if __name__ == "__main__":
    unittest.main()
