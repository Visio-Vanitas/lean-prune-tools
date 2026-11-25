#!/usr/bin/env python3
"""Zero-dependency unit test suite for import_index.py, big_pr_hunter.py, and strip_planner.py."""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parent
sys.path.insert(0, str(TOOLS_DIR))

import big_pr_hunter as bph  # noqa: E402
import import_index as idx  # noqa: E402


def _git(repo: Path, *args: str) -> str:
    r = subprocess.run(
        ["git"] + list(args),
        cwd=str(repo),
        capture_output=True,
        text=True,
        check=True,
    )
    return r.stdout


def _init_git_repo(root: Path, files: dict[str, str], msg: str = "init") -> str:
    _git(root, "init", "-b", "main")
    _git(root, "config", "user.name", "Test User")
    _git(root, "config", "user.email", "test@example.com")
    for rel, content in files.items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-m", msg)
    return _git(root, "rev-parse", "HEAD").strip()


def _commit_changes(root: Path, updates: dict[str, str] | None = None, deletes: list[str] | None = None, msg: str = "update") -> str:
    for rel in deletes or []:
        p = root / rel
        if p.exists():
            p.unlink()
    for rel, content in (updates or {}).items():
        p = root / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(content, encoding="utf-8")
    _git(root, "add", "-A")
    _git(root, "commit", "-m", msg)
    return _git(root, "rev-parse", "HEAD").strip()


def _run_cli(script: Path, *args: str, cwd: Path | None = None) -> tuple[int, str, str]:
    p = subprocess.run(
        [sys.executable, str(script), *args],
        cwd=str(cwd) if cwd else None,
        capture_output=True,
        text=True,
    )
    return p.returncode, p.stdout, p.stderr


class TestParseLeanImports(unittest.TestCase):
    def test_imports_and_nested_comments(self):
        src = (
            "module\n"
            "prelude\n"
            "/- outer comment\n"
            "   /- nested comment with -- fake\n"
            "      import Fake.Mod\n"
            "   -/\n"
            "   import StillComment.Mod -/\n"
            "import Foo.Bar -- trailing comment\n"
            "public import Baz.Qux\n"
            "private import Secret.Mod\n"
            "meta import Meta.Mod\n"
            "import all All.Mod\n"
            "/- inline -/ import AfterInline.Mod\n"
            "theorem realDecl : True := trivial\n"
            "import NotAfterDecl\n"
        ).encode("utf-8")
        lcnt, imps = idx.parse_lean_imports(src)
        self.assertGreater(lcnt, 10)
        self.assertEqual(
            imps,
            [
                ("Foo.Bar", 0),
                ("Baz.Qux", 1),
                ("Secret.Mod", 0),
                ("Meta.Mod", 0),
                ("All.Mod", 0),
                ("AfterInline.Mod", 0),
            ],
        )


class TestImportIndexAndAudit(unittest.TestCase):
    def setUp(self):
        self.td = tempfile.TemporaryDirectory()
        self.root = Path(self.td.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.db = self.root / "idx.db"
        self.files = {
            "src/Main.lean": "import HostA\nimport HostB\nimport DiamondHost\ntheorem main_t : True := trivial\n",
            "src/HostA.lean": "import SharedLeaf\nimport DeadBranchA\n",
            "src/HostB.lean": "import SharedLeaf\nimport MultiCutLeaf\n",
            "src/SharedLeaf.lean": "theorem shared : True := trivial\n",
            "src/DeadBranchA.lean": "import DeepLeaf\ntheorem da : True := trivial\n",
            "src/DeepLeaf.lean": "theorem dl : True := trivial\n",
            "src/MultiCutLeaf.lean": "theorem mc : True := trivial\n",
            "src/DiamondHost.lean": "import DiamLeft\nimport DiamRight\n",
            "src/DiamLeft.lean": "import DiamBottom\n",
            "src/DiamRight.lean": "import DiamBottom\n",
            "src/DiamBottom.lean": "theorem db : True := trivial\n",
            "src/UnreachableBlocker.lean": "import BlockedByNonMain\n",
            "src/BlockedByNonMain.lean": "theorem bnm : True := trivial\n",
        }
        # Connect BlockedByNonMain under HostA as well so Main reaches it only via HostA
        self.files["src/HostA.lean"] += "import BlockedByNonMain\n"
        self.base_sha = _init_git_repo(self.repo, self.files)

    def tearDown(self):
        self.td.cleanup()

    def test_sync_stats_repo_root_and_incremental_ghost_cleanup(self):
        rc, out, err = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "sync", "--ref", "HEAD", "--no-remote-check",
        )
        self.assertEqual(rc, 0, err)
        res = json.loads(out)
        self.assertEqual(res["modules"], len(self.files))

        # Expect-sha fail-closed check
        rc_fail, _, err_fail = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "sync", "--expect-sha", "deadbeef", "--no-remote-check",
        )
        self.assertEqual(rc_fail, 2)
        self.assertIn("SHA_MISMATCH", err_fail)

        # Stats --check-remote remembers stored repo_root even from unrelated cwd
        other_cwd = self.root / "other"
        other_cwd.mkdir()
        rc_s, out_s, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--db", str(self.db),
            "stats", "--check-remote",
            cwd=other_cwd,
        )
        self.assertEqual(rc_s, 0)
        sdata = json.loads(out_s)
        self.assertEqual(Path(sdata["checked_repo"]).resolve(), self.repo.resolve())

        # Stats --check-remote explicitly pointed at non-Lean dir warns on stderr
        non_lean = self.root / "nonlean"
        non_lean.mkdir()
        _init_git_repo(non_lean, {"README.md": "hi\n"})
        rc_w, _, err_w = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(non_lean),
            "--db", str(self.db),
            "stats", "--check-remote",
        )
        self.assertEqual(rc_w, 0)
        self.assertIn("missing src/Main.lean", err_w)

        # Incremental delete cleans ghost dst_mod edges too
        _commit_changes(
            self.repo,
            updates={"src/HostA.lean": "import SharedLeaf\nimport BlockedByNonMain\n"},
            deletes=["src/DeadBranchA.lean", "src/DeepLeaf.lean"],
            msg="remove DeadBranchA",
        )
        rc_inc, out_inc, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "sync", "--ref", "HEAD", "--no-remote-check",
        )
        self.assertEqual(rc_inc, 0)
        self.assertEqual(json.loads(out_inc)["mode"], "incremental_sync")
        conn = idx.init_db(self.db)
        ghost = conn.execute("SELECT COUNT(*) FROM edges WHERE dst_mod='DeadBranchA'").fetchone()[0]
        self.assertEqual(ghost, 0)

    def test_multi_peel_modes_and_audit_diff_checks(self):
        _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "sync", "--ref", "HEAD", "--no-remote-check",
        )

        # Multi-host --cut peels SharedLeaf across HostA and HostB
        rc, out, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--db", str(self.db),
            "peel",
            "--cut", "HostA:SharedLeaf",
            "--cut", "HostB:SharedLeaf,MultiCutLeaf",
        )
        self.assertEqual(rc, 0)
        pdata = json.loads(out)
        self.assertEqual(pdata["survivor_dangling_edges"], 0)
        self.assertEqual(pdata["orphan_module_count"], 2)
        self.assertEqual(set(pdata["sample_orphans"]), {"SharedLeaf", "MultiCutLeaf"})

        # Non-existent edge genuinely outside peel emits loud warning field
        rc_ne, out_ne, err_ne = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--db", str(self.db),
            "peel", "HostA", "--drop", "MultiCutLeaf",
        )
        self.assertEqual(rc_ne, 0)
        self.assertIn("non_existent_edges", json.loads(out_ne))
        self.assertIn("WARNING", err_ne)

        # Passing both direct dep DeadBranchA and its transitive orphan DeepLeaf MUST NOT warn on stderr
        rc_tr, out_tr, err_tr = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--db", str(self.db),
            "peel", "HostA", "--drop", "DeadBranchA,DeepLeaf",
        )
        self.assertEqual(rc_tr, 0)
        self.assertNotIn("WARNING", err_tr)
        d_tr = json.loads(out_tr)
        self.assertNotIn("non_existent_edges", d_tr)
        self.assertEqual(d_tr.get("transitive_drops_not_direct"), [["HostA", "DeepLeaf"]])
        self.assertEqual(d_tr["orphan_module_count"], 2)

        # Non-Main blocker reported, and --mode reach-main peels it
        rc_nm0, out_nm0, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--db", str(self.db),
            "peel", "HostA", "--drop", "BlockedByNonMain",
        )
        d0 = json.loads(out_nm0)
        self.assertEqual(d0["orphan_module_count"], 0)
        self.assertEqual(d0["main_reach_orphan_count"], 1)
        self.assertEqual(d0["non_main_blockers_count"], 1)
        self.assertEqual(d0["non_main_blockers_sample"], [["UnreachableBlocker", "BlockedByNonMain"]])

        rc_nm1, out_nm1, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--db", str(self.db),
            "peel", "HostA", "--drop", "BlockedByNonMain", "--mode", "reach-main",
        )
        self.assertEqual(rc_nm1, 0)
        d1 = json.loads(out_nm1)
        self.assertEqual(d1["orphan_module_count"], 1)
        self.assertEqual(d1["non_main_dangling_edges"], 1)

        # --drop-modules DiamBottom discovers DiamLeft & DiamRight as required host cuts
        rc_dm, out_dm, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--db", str(self.db),
            "peel", "--drop-modules", "DiamBottom",
        )
        self.assertEqual(rc_dm, 0)
        dm_data = json.loads(out_dm)
        self.assertEqual(sorted(dm_data["required_host_cuts"]), [["DiamLeft", "DiamBottom"], ["DiamRight", "DiamBottom"]])
        self.assertEqual(dm_data["orphan_module_count"], 1)

        # audit-diff cycle FAIL & configurable forbidden-pattern check
        _git(self.repo, "checkout", "-b", "bad-cycle")
        _commit_changes(
            self.repo,
            updates={
                "src/DeepLeaf.lean": "import HostA\n-- FORBIDDEN_TEST_TOKEN\ntheorem dl : True := trivial\n",
            },
            msg="introduce cycle and forbidden token",
        )
        rc_default, out_default, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "audit-diff", self.base_sha, "HEAD",
        )
        self.assertEqual(rc_default, 1)
        aud_default = json.loads(out_default)
        self.assertEqual(aud_default["forbidden_pattern_hits"], [])

        rc_aud, out_aud, _ = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "audit-diff", self.base_sha, "HEAD",
            "--forbid-pattern", "FORBIDDEN_TEST_TOKEN",
        )
        self.assertEqual(rc_aud, 1)
        aud = json.loads(out_aud)
        self.assertEqual(aud["verdict"], "FAIL")
        self.assertFalse(aud["cycle_free"])
        self.assertTrue(len(aud["introduced_cycles"]) >= 1)
        self.assertTrue(len(aud["forbidden_pattern_hits"]) >= 1)

    def test_audit_diff_missing_project_module_vs_external(self):
        base_with_dev = _commit_changes(
            self.repo,
            updates={"src/Dev/ValidMod.lean": "def validMod : Nat := 1\n"},
            msg="add Dev namespace root",
        )
        _git(self.repo, "checkout", "-b", "missing-proj-imp")
        head_bad = _commit_changes(
            self.repo,
            updates={
                "src/HostA.lean": "import SharedLeaf\nimport Dev.MissingOnBase\nimport Mathlib.Data.Nat.Basic\n",
            },
            msg="splice absent project import alongside external import",
        )
        rc, out, err = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "audit-diff", base_with_dev, head_bad,
        )
        self.assertEqual(rc, 1, err)
        aud = json.loads(out)
        self.assertEqual(aud["verdict"], "FAIL")
        self.assertEqual(aud["dangling_imports_count"], 1)
        self.assertEqual(aud["dangling_sample"], [["HostA", "Dev.MissingOnBase"]])


class TestHunterAndPlanner(unittest.TestCase):
    def setUp(self):
        self.td = tempfile.TemporaryDirectory()
        self.root = Path(self.td.name)
        self.repo = self.root / "repo"
        self.repo.mkdir()
        self.db = self.root / "idx.db"

        dup_body = "\n".join(f"  have h{i} : True := trivial" for i in range(18)) + "\n  exact trivial\n"
        self.files = {
            "src/Main.lean": (
                "import BundleUse\n"
                "import DiamondHost\n"
                "import DupAlphaA\n"
                "import DupAlphaB\n"
                "import InstUser\n"
                "theorem main_thm : True := trivial\n"
            ),
            "src/ProviderUnused.lean": (
                "theorem unusedWitness : True := trivial\n"
            ),
            "src/ProviderIgnored.lean": (
                "theorem ignoredWitness : True := trivial\n"
            ),
            "src/ProviderUsed.lean": (
                "theorem usedWitness : True := trivial\n"
            ),
            "src/BaseStruct.lean": (
                "structure BaseS where\n"
                "  b0 : Prop\n"
            ),
            # Multi-line extends structure, 4-space indentation, parameterized field, same-file forwarder!
            "src/Local/CustomDictionary.lean": (
                "import BaseStruct\n"
                "structure CustomBundle (k : Type)\n"
                "    extends BaseS where\n"
                "    /-- docstring comment with .fUnused -/\n"
                "    fUnused : True\n"
                "    fParam (n : Nat) : n = n\n"
                "    fIgnored : True\n"
                "    fForwarded : True\n"
                "    fUsed : True\n"
                "\n"
                "theorem CustomBundle.forward {k : Type} (h : CustomBundle k) : True :=\n"
                "  h.fForwarded\n"
            ),
            "src/HelperConsumer.lean": (
                "theorem consumeHelper : True → True → True :=\n"
                "  fun _ usedArg => usedArg\n"
                "\n"
                "theorem introConsumer : True → True → True := by\n"
                "  intro _ usedB\n"
                "  exact usedB\n"
            ),
            "src/BundleUse.lean": (
                "import Local.CustomDictionary\n"
                "import HelperConsumer\n"
                "import ProviderUnused\n"
                "import ProviderIgnored\n"
                "import ProviderUsed\n"
                "def mkBundle : CustomBundle Nat :=\n"
                "  { b0 := True\n"
                "    fUnused := unusedWitness\n"
                "    fParam := fun _ => rfl\n"
                "    fIgnored := ignoredWitness\n"
                "    fForwarded := trivial\n"
                "    fUsed := usedWitness }\n"
                "theorem useIt : True := by\n"
                "  -- comment mentioning mkBundle.fUnused\n"
                "  have h1 := consumeHelper mkBundle.fIgnored mkBundle.fUsed\n"
                "  have h2 := introConsumer mkBundle.fIgnored h1\n"
                "  have h3 := mkBundle.fParam 0\n"
                "  exact mkBundle.forward\n"
            ),
            # Diamond DAG for dom-pillars
            "src/DiamondHost.lean": (
                "import DiamLeft\n"
                "import DiamRight\n"
                "theorem dh : True := trivial\n"
            ),
            "src/DiamLeft.lean": "import DiamBottom\n" + "\n".join(f"-- l{i}" for i in range(12)),
            "src/DiamRight.lean": "import DiamBottom\n" + "\n".join(f"-- r{i}" for i in range(12)),
            "src/DiamBottom.lean": "import DiamTail\n" + "\n".join(f"-- b{i}" for i in range(25)),
            "src/DiamTail.lean": "\n".join(f"-- t{i}" for i in range(30)),
            # Cross-filename alpha-equivalent & body-hash duplicates + published-dups test
            "src/GlobalTheory/PublishedDefs.lean": "def GlobalTheory.Published.Target : Prop := True\n",
            "src/DupAlphaA.lean": (
                "import GlobalTheory.PublishedDefs\n"
                "theorem proofA (x y : Nat) : x + y = y + x := by\n"
                + dup_body
                + "theorem pubA : GlobalTheory.Published.Target := by\n"
                "  have a : True := trivial\n"
                "  exact a\n"
            ),
            "src/DupAlphaB.lean": (
                "import GlobalTheory.PublishedDefs\n"
                "theorem proofB (a b : Nat) : a + b = b + a := by\n"
                + dup_body
                + "theorem pubB : GlobalTheory.Published.Target := by\n"
                "  have b : True := trivial\n"
                "  exact b\n"
                "theorem pubForwarder (h : GlobalTheory.Published.Target) : GlobalTheory.Published.Target :=\n"
                "  h\n"
            ),
            # attribute [-instance] test
            "src/InstUser.lean": (
                "-- comment attribute [-instance] FakeInst\n"
                "attribute [-instance] Foo.instA Bar.instB in\n"
                "theorem instUser : True := trivial\n"
            ),
        }
        # Connect DiamondHost with enough small modules for min-files check in test
        self.sha = _init_git_repo(self.repo, self.files)
        rc, _, err = _run_cli(
            TOOLS_DIR / "import_index.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "sync", "--ref", "HEAD", "--no-remote-check",
        )
        self.assertEqual(rc, 0, err)

    def tearDown(self):
        self.td.cleanup()

    def test_unused_fields_and_ignored_bundle_args(self):
        # unused-fields: finds CustomBundle even though module name is Local.CustomDictionary!
        # fForwarded has readers_count=1 (same-file forwarder), NOT 0!
        # fUnused has readers_count=0 (comment mention ignored!).
        rc, out, err = _run_cli(
            TOOLS_DIR / "big_pr_hunter.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "--ref", "HEAD",
            "unused-fields",
            "--min-fields", "3",
            "--max-readers", "0",
            "--struct-filter", "Bundle",
        )
        self.assertEqual(rc, 0, err)
        data = json.loads(out)
        self.assertEqual(len(data["structures"]), 1)
        st = data["structures"][0]
        self.assertEqual(st["structure"], "CustomBundle")
        self.assertEqual(st["total_fields"], 5)
        zero_names = {f["field"] for f in st["low_reader_fields"]}
        self.assertEqual(zero_names, {"fUnused"})
        self.assertEqual(st["low_reader_fields"][0].get("estimated_peel_seed"), "ProviderUnused")

        # With --max-readers 1, fForwarded shows same_file_readers=["CustomBundle.forward"]
        rc1, out1, _ = _run_cli(
            TOOLS_DIR / "big_pr_hunter.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "--ref", "HEAD",
            "unused-fields",
            "--min-fields", "3",
            "--max-readers", "1",
            "--struct-filter", "Bundle",
        )
        self.assertEqual(rc1, 0)
        d1 = json.loads(out1)["structures"][0]["low_reader_fields"]
        fwd_entry = [x for x in d1 if x["field"] == "fForwarded"][0]
        self.assertEqual(fwd_entry["readers_count"], 1)
        self.assertIn("CustomBundle.forward", fwd_entry.get("same_file_readers", []))

        # ignored-bundle-args catches BOTH fun _ and by intro _ on fIgnored!
        rc_i, out_i, err_i = _run_cli(
            TOOLS_DIR / "big_pr_hunter.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "--ref", "HEAD",
            "ignored-bundle-args",
            "--min-fields", "3",
            "--max-readers", "2",
            "--struct-filter", "Bundle",
        )
        self.assertEqual(rc_i, 0, err_i)
        idata = json.loads(out_i)
        ignored_fields = {x["field"]: x for x in idata["ignored_bundle_fields"]}
        self.assertIn("fIgnored", ignored_fields)
        self.assertTrue(ignored_fields["fIgnored"]["all_reads_discarded"])
        self.assertEqual(ignored_fields["fIgnored"].get("estimated_peel_seed"), "ProviderIgnored")

    def test_dom_pillars_decl_dups_published_dups_and_neg_instances(self):
        # dom-pillars catches DiamondHost dominating DiamLeft, DiamRight, DiamBottom, DiamTail
        rc_dp, out_dp, err_dp = _run_cli(
            TOOLS_DIR / "big_pr_hunter.py",
            "--db", str(self.db),
            "dom-pillars", "--min-lines", "50", "--min-files", "3", "--only-multi-edge", "--min-multi-gain", "20",
        )
        self.assertEqual(rc_dp, 0, err_dp)
        dp = json.loads(out_dp)
        hosts = {x["host_mod"]: x for x in dp["pillars"]}
        self.assertIn("DiamondHost", hosts)
        self.assertEqual(hosts["DiamondHost"]["dom_files"], 4)
        self.assertGreater(hosts["DiamondHost"]["multi_edge_gain_lines"], 20)

        # decl-dups catches alpha-equivalent proofA vs proofB in different-stem files
        rc_dd, out_dd, err_dd = _run_cli(
            TOOLS_DIR / "big_pr_hunter.py",
            "--db", str(self.db),
            "--ref", "HEAD",
            "decl-dups", "--min-mod-lines", "5", "--min-body-lines", "10", "--min-sig-len", "10",
        )
        self.assertEqual(rc_dd, 0, err_dd)
        dd = json.loads(out_dd)
        self.assertTrue(any(c["different_stems"] and {cp["mod"] for cp in c["copies"]} == {"DupAlphaA", "DupAlphaB"} for c in dd["clusters"]))

        # published-dups filters out pubForwarder wrapper and keeps pubA + pubB
        rc_pd, out_pd, err_pd = _run_cli(
            TOOLS_DIR / "big_pr_hunter.py",
            "--db", str(self.db),
            "--ref", "HEAD",
            "published-dups",
        )
        self.assertEqual(rc_pd, 0, err_pd)
        pd = json.loads(out_pd)["duplicate_published_types"][0]
        self.assertEqual(pd["occurrences"], 2)
        self.assertEqual(pd["filtered_forwarder_count"], 1)

        # neg-instances skips comments and `in`
        rc_ni, out_ni, _ = _run_cli(
            TOOLS_DIR / "big_pr_hunter.py",
            "--db", str(self.db),
            "--ref", "HEAD",
            "neg-instances",
        )
        self.assertEqual(rc_ni, 0)
        ni = json.loads(out_ni)
        inst_map = {x["instance"]: x["count"] for x in ni["top_disabled_instances"]}
        self.assertEqual(inst_map, {"Foo.instA": 1, "Bar.instB": 1})

    def test_strip_planner_all_subcommands(self):
        # bundle-field
        rc_bf, out_bf, err_bf = _run_cli(
            TOOLS_DIR / "strip_planner.py",
            "--db", str(self.db),
            "--ref", "HEAD",
            "bundle-field", "--struct", "CustomBundle", "--fields", "fUnused,fIgnored",
        )
        self.assertEqual(rc_bf, 0, err_bf)
        bf = json.loads(out_bf)
        self.assertEqual(bf["survivor_dangling_edges"], 0)
        self.assertEqual(set(bf["orphan_files"]), {"src/ProviderUnused.lean", "src/ProviderIgnored.lean"})

        # subtree-replace on DiamLeft + DiamRight (excluding DiamondHost), cascading to DiamBottom + DiamTail
        rc_sr, out_sr, err_sr = _run_cli(
            TOOLS_DIR / "strip_planner.py",
            "--db", str(self.db),
            "--ref", "HEAD",
            "subtree-replace", "--drop-mods", "DiamLeft,DiamRight",
        )
        self.assertEqual(rc_sr, 0, err_sr)
        sr = json.loads(out_sr)
        self.assertEqual(sr["survivor_dangling_edges"], 0)
        self.assertEqual(sr["total_orphan_files"], 4)
        self.assertEqual(sr["cascading_outside_files_count"], 2)
        self.assertEqual(sr["external_boundary_importers"][0]["importer_mod"], "DiamondHost")

        # unused-imports detects BaseStruct unused in Local.CustomDictionary? Let's test a dedicated file with unused import
        _commit_changes(
            self.repo,
            updates={"src/BundleUse.lean": self.files["src/BundleUse.lean"].replace("unusedWitness", "trivial")},
            msg="stop referencing ProviderUnused",
        )
        rc_ui, out_ui, err_ui = _run_cli(
            TOOLS_DIR / "strip_planner.py",
            "--repo", str(self.repo),
            "--db", str(self.db),
            "unused-imports", "--base", self.sha, "--head", "HEAD",
        )
        self.assertEqual(rc_ui, 0, err_ui)
        ui = json.loads(out_ui)
        cands = {c["imported_mod"]: c for c in ui["files"][0]["candidate_unused_imports"]}
        self.assertIn("ProviderUnused", cands)
        self.assertEqual(cands["ProviderUnused"]["bonus_peel_files"], 1)

    def test_host_secondary_symbol_guard(self):
        td2 = tempfile.TemporaryDirectory()
        try:
            r2 = Path(td2.name) / "repo"
            r2.mkdir()
            db2 = Path(td2.name) / "idx.db"
            files2 = {
                "src/Main.lean": "import EveryChar\ntheorem m_main : True := by exact EveryChar.use_all\n",
                "src/PublishedDefs.lean": (
                    "def GlobalTheory.Published.PrismaticDieudonneHodge : Prop := True\n"
                    "def GlobalTheory.Published.StrongApproxSU : Prop := True\n"
                    "def GlobalTheory.Published.VolGe : Prop := True\n"
                    "structure PublishedHodgeBundleTheorems where\n"
                    "  q4 : GlobalTheory.Published.PrismaticDieudonneHodge\n"
                    "  p13 : GlobalTheory.Published.StrongApproxSU\n"
                    "  p2 : GlobalTheory.Published.VolGe\n"
                ),
                "src/PrismaticDieudonneHodge.lean": (
                    "namespace UpperTheory.Lit\n"
                    "theorem prismaticDieudonneHodge : True := trivial\n"
                    "theorem farguesExact : True := trivial\n"
                    "end UpperTheory.Lit\n"
                ),
                "src/ImportsTailTer.lean": (
                    "namespace GlobalTheory.StrongApproxSUProof\n"
                    "theorem strongApproxSU : True := trivial\n"
                    "end GlobalTheory.StrongApproxSUProof\n"
                ),
                "src/VolGeOfHilbertSamuel.lean": (
                    "import VolGe₂\n"
                    "namespace GlobalTheory.VolBr\n"
                    "theorem volGe_of_hilbertSamuel : True := trivial\n"
                    "end GlobalTheory.VolBr\n"
                ),
                "src/VolGe₂.lean": "theorem volSub₂ : True := trivial\n",
                "src/EveryChar.lean": (
                    "import PublishedDefs\n"
                    "import PrismaticDieudonneHodge\n"
                    "import ImportsTailTer\n"
                    "import VolGeOfHilbertSamuel\n"
                    "theorem prismatic_of_lit (n : Nat) : GlobalTheory.Published.PrismaticDieudonneHodge :=\n"
                    "  UpperTheory.Lit.prismaticDieudonneHodge\n"
                    "theorem strong_approx_of_lit (n : Nat) : GlobalTheory.Published.StrongApproxSU :=\n"
                    "  GlobalTheory.StrongApproxSUProof.strongApproxSU\n"
                    "theorem vol_ge_of_lit (n : Nat) : GlobalTheory.Published.VolGe :=\n"
                    "  GlobalTheory.VolBr.volGe_of_hilbertSamuel\n"
                    "theorem fargues_thm : True :=\n"
                    "  UpperTheory.Lit.farguesExact\n"
                    "def published_eigen (n : Nat) : True :=\n"
                    "  strong_approx_of_lit n\n"
                    "def hodge_arith (n : Nat) : PublishedHodgeBundleTheorems :=\n"
                    "  {\n"
                    "    q4 := (prismatic_of_lit n),\n"
                    "    p13 := (strong_approx_of_lit n),\n"
                    "    p2 := (vol_ge_of_lit n)\n"
                    "  }\n"
                    "theorem use_all : True := by\n"
                    "  have _ := (hodge_arith 0).p2\n"
                    "  have _ := published_eigen 0\n"
                    "  exact fargues_thm\n"
                ),
            }
            _init_git_repo(r2, files2)
            rc_s, _, err_s = _run_cli(TOOLS_DIR / "import_index.py", "--repo", str(r2), "--db", str(db2), "sync", "--ref", "HEAD", "--no-remote-check")
            self.assertEqual(rc_s, 0, err_s)

            # bundle-field MUST block PrismaticDieudonneHodge (farguesExact) and ImportsTailTer (wrapper reused in published_eigen),
            # while cleanly peeling ONLY VolGeOfHilbertSamuel!
            rc_b, out_b, err_b = _run_cli(
                TOOLS_DIR / "strip_planner.py",
                "--repo", str(r2),
                "--db", str(db2),
                "--ref", "HEAD",
                "bundle-field",
                "--struct", "PublishedHodgeBundleTheorems",
                "--fields", "q4,p13,p2",
            )
            self.assertEqual(rc_b, 0, err_b)
            bd = json.loads(out_b)
            self.assertEqual(bd["orphan_module_count"], 2)
            self.assertEqual(set(bd["orphan_files"]), {"src/VolGeOfHilbertSamuel.lean", "src/VolGe₂.lean"})
            self.assertEqual(bd["candidate_import_cuts"], [["EveryChar", "VolGeOfHilbertSamuel"]])
            self.assertIn("vol_ge_of_lit", {w["wrapper"] for w in bd.get("required_host_wrapper_removals", [])})
            self.assertIn("precondition_note", bd)
            blocked = {b["dep"]: b for b in bd["blocked_import_cuts"]}
            self.assertEqual(set(blocked), {"PrismaticDieudonneHodge", "ImportsTailTer"})
            self.assertIn("farguesExact", {s["short_name"] for s in blocked["PrismaticDieudonneHodge"]["secondary_symbol_blockers"]})
            self.assertIn("strong_approx_of_lit", {w["wrapper"] for w in blocked["ImportsTailTer"]["wrapper_reuse_blockers"]})
            self.assertIn("src/VolGe₂.lean", idx._git_show_blobs(r2, "HEAD", ["src/VolGe₂.lean"]))

            # import_index.py peel --check-symbols reports host secondary symbols
            rc_p, out_p, err_p = _run_cli(
                TOOLS_DIR / "import_index.py",
                "--repo", str(r2),
                "--db", str(db2),
                "peel", "EveryChar", "--drop", "PrismaticDieudonneHodge", "--check-symbols", "--ref", "HEAD",
            )
            self.assertEqual(rc_p, 0, err_p)
            pd_chk = json.loads(out_p)["host_symbol_checks"][0]
            self.assertTrue(pd_chk["blocked"])
            self.assertIn("farguesExact", {s["short_name"] for s in pd_chk["secondary_symbol_blockers"]})

            # Regression test: bare peel of VolGeOfHilbertSamuel without removing wrapper MUST block
            rc_v, out_v, err_v = _run_cli(
                TOOLS_DIR / "import_index.py",
                "--repo", str(r2),
                "--db", str(db2),
                "peel", "EveryChar", "--drop", "VolGeOfHilbertSamuel", "--check-symbols", "--ref", "HEAD",
            )
            self.assertEqual(rc_v, 0, err_v)
            v_chk = json.loads(out_v)["host_symbol_checks"][0]
            self.assertTrue(v_chk["blocked"])
            self.assertIn("volGe_of_hilbertSamuel", {s["short_name"] for s in v_chk["secondary_symbol_blockers"]})

            # Fail-closed check when --ref is strictly older than indexed_commit unless --allow-stale
            _commit_changes(r2, updates={"src/VolGe₂.lean": "theorem volSub₂ : True := trivial\n-- v2\n"}, msg="advance")
            _run_cli(TOOLS_DIR / "import_index.py", "--repo", str(r2), "--db", str(db2), "sync", "--ref", "HEAD", "--no-remote-check")
            rc_st, _, err_st = _run_cli(
                TOOLS_DIR / "import_index.py",
                "--repo", str(r2),
                "--db", str(db2),
                "peel", "EveryChar", "--drop", "VolGeOfHilbertSamuel", "--check-symbols", "--ref", "HEAD~1",
            )
            self.assertEqual(rc_st, 2)
            self.assertIn("STALE_REF_VS_INDEX", err_st)
            rc_al, _, err_al = _run_cli(
                TOOLS_DIR / "import_index.py",
                "--repo", str(r2),
                "--db", str(db2),
                "peel", "EveryChar", "--drop", "VolGeOfHilbertSamuel", "--check-symbols", "--ref", "HEAD~1", "--allow-stale",
            )
            self.assertEqual(rc_al, 0, err_al)

            # Namespace collision regression (qualified vs local symbol resolution):
            # Dropped dep exports `GlobalTheory.GKPort.KFinLink.isLieStable_of`, while host calls
            # `_root_.GlobalTheory.CompanionTheory.KFinLink.isLieStable_of`, relative
            # `CompanionTheory.KFinLink.isLieStable_of`, and defines local `isLieStable_of`.
            host_ns = "\n".join([
                "import Companion",
                "import GK",
                "namespace GlobalTheory.KFinLinkPort",
                "theorem isLieStable_of : True := by",
                "  exact _root_.GlobalTheory.CompanionTheory.KFinLink.isLieStable_of",
                "theorem rel_other : True := by",
                "  exact CompanionTheory.KFinLink.isLieStable_of",
                "end GlobalTheory.KFinLinkPort",
            ])
            dep_gk = "\n".join([
                "namespace GlobalTheory.GKPort.KFinLink",
                "theorem isLieStable_of : True := trivial",
                "end GlobalTheory.GKPort.KFinLink",
            ])
            ns_res = idx.check_host_secondary_symbols(host_ns, {"GK": dep_gk})
            self.assertFalse(ns_res["blocked"], ns_res)

            # Direct `_root_` or opened-namespace reference MUST still block!
            host_hit = "\n".join([
                "import GK",
                "theorem direct_root : True := _root_.GlobalTheory.GKPort.KFinLink.isLieStable_of",
            ])
            self.assertTrue(idx.check_host_secondary_symbols(host_hit, {"GK": dep_gk})["blocked"])

            # Relative strict suffix without `open GKPort` must NOT block; WITH `open GlobalTheory.GKPort` MUST block!
            host_rel_miss = "namespace GlobalTheory.CompanionTheory\ntheorem r : True := KFinLink.isLieStable_of\nend GlobalTheory.CompanionTheory\n"
            self.assertFalse(idx.check_host_secondary_symbols(host_rel_miss, {"GK": dep_gk})["blocked"])
            host_rel_hit = "open GlobalTheory.GKPort\ntheorem r : True := KFinLink.isLieStable_of\n"
            self.assertTrue(idx.check_host_secondary_symbols(host_rel_hit, {"GK": dep_gk})["blocked"])

            # Named section balancing (`section Abstract ... end Abstract`) must not leak enclosing namespace
            clump_txt = "\n".join([
                "namespace GlobalTheory.SUWeakApprox",
                "section Abstract",
                "theorem a1 : True := trivial",
                "end Abstract",
                "end GlobalTheory.SUWeakApprox",
                "namespace GlobalTheory.StrongApproxSUProof",
                "theorem strongApproxSU : True := trivial",
                "end GlobalTheory.StrongApproxSUProof",
            ])
            cdecls, _ = idx.extract_exported_decls(clump_txt)
            self.assertEqual([d["full_name"] for d in cdecls], ["GlobalTheory.SUWeakApprox.a1", "GlobalTheory.StrongApproxSUProof.strongApproxSU"])
        finally:
            td2.cleanup()

    def test_vacuous_defs_and_unreferenced_decls(self):
        td3 = tempfile.TemporaryDirectory()
        try:
            r3 = Path(td3.name) / "repo"
            r3.mkdir()
            db3 = Path(td3.name) / "idx.db"
            files3 = {
                "src/Main.lean": "import LeafMod\nimport ExtMod\ntheorem main_t : True := by exact ExtMod.live_ext\n",
                "src/BaseMod.lean": "structure BaseS where\n  x : Nat\n",
                "src/AliasedMod.lean": (
                    "theorem real_inner : True := trivial\n"
                    "alias exported_alias := real_inner\n"
                ),
                "src/PrimedMod.lean": (
                    "structure Hypotheses'' : Prop where\n"
                    "  p1 : True\n"
                    "theorem poleSolve' : True := trivial\n"
                ),
                "src/LeafMod.lean": (
                    "import BaseMod\n"
                    "def TrivialCond : Prop := True\n"
                    "def TrivialFn : Nat → Prop := fun _ => True\n"
                    "structure EmptyPlaceholder (n : Nat) : Type\n"
                    "structure EmptyPropBox : Prop where\n"
                    "structure GoodExt extends BaseS where\n"
                    "structure GreekFrame where\n"
                    "  β : Nat\n"
                    "  γ : Nat\n"
                    "structure Prm where\n"
                    "  x : Nat\n"
                    "def GeoCl (p : Prop) : Prop := p\n"
                    "theorem dead_lem : True := by\n"
                    "  have h := True.intro\n"
                    "  exact h\n"
                    "theorem live_lem : True := trivial\n"
                    "@[simp] theorem simp_lem : True := trivial\n"
                    "instance : Inhabited Nat := ⟨0⟩\n"
                ),
                "src/ExtMod.lean": (
                    "import LeafMod\n"
                    "import AliasedMod\n"
                    "import PrimedMod\n"
                    "theorem caller1 (_ : TrivialCond) (f : GreekFrame) (h : Hypotheses'') : Nat := f.β + f.γ\n"
                    "theorem caller2 (tc : TrivialCond) : Prop := GeoCl TrivialCond\n"
                    "theorem live_ext (f : GreekFrame) (h : Hypotheses'') : True := by\n"
                    "  have h0 := caller1 trivial f h\n"
                    "  have h1 := exported_alias\n"
                    "  have h2 := poleSolve'\n"
                    "  have _ := caller2 trivial\n"
                    "  have h3 := live_lem\n"
                    "  exact h1\n"
                ),
            }
            _init_git_repo(r3, files3)
            _run_cli(TOOLS_DIR / "import_index.py", "--repo", str(r3), "--db", str(db3), "sync", "--ref", "HEAD", "--no-remote-check")

            rc_v, out_v, err_v = _run_cli(
                TOOLS_DIR / "big_pr_hunter.py", "--repo", str(r3), "--db", str(db3), "--ref", "HEAD", "vacuous-defs"
            )
            self.assertEqual(rc_v, 0, err_v)
            vd = json.loads(out_v)
            hits_by_name = {h["name"]: h for h in vd["hits"]}
            self.assertIn("TrivialCond", hits_by_name)
            self.assertIn("TrivialFn", hits_by_name)
            self.assertIn("EmptyPlaceholder", hits_by_name)
            self.assertIn("EmptyPropBox", hits_by_name)
            self.assertNotIn("GoodExt", hits_by_name)
            self.assertNotIn("GreekFrame", hits_by_name)
            self.assertEqual(hits_by_name["TrivialCond"]["unused_binder_callers_count"], 2)
            self.assertTrue(any(c["callee"] == "GeoCl" for c in hits_by_name["TrivialCond"].get("only_trivial_param_candidates", [])))

            rc_u, out_u, err_u = _run_cli(
                TOOLS_DIR / "big_pr_hunter.py", "--repo", str(r3), "--db", str(db3), "--ref", "HEAD", "unreferenced-decls"
            )
            self.assertEqual(rc_u, 0, err_u)
            ud = json.loads(out_u)
            dead_names = {d["name"] for d in ud["unreferenced_decls"]}
            self.assertEqual(dead_names, {"TrivialFn", "EmptyPlaceholder", "EmptyPropBox", "GoodExt", "Prm", "dead_lem"})
            dead_mods = {m["mod"] for m in ud["dead_module_candidates"]}
            self.assertNotIn("AliasedMod", dead_mods)
            self.assertNotIn("PrimedMod", dead_mods)
        finally:
            td3.cleanup()

    def test_scoped_destructuring_detector(self):
        # Negative cases: none of these destructure or positionally construct CustomBundle
        clean_lean = "\n".join([
            "namespace TestNs",
            "structure CustomBundle : Prop where",
            "  fUsed : Prop",
            "  fDead : Prop",
            "",
            "section",
            "variable (vSec : CustomBundle)",
            "theorem no_fp_obtain (hP2 : _root_.TestNs.CustomBundle) (hT : OtherRec) : ∃ x : Prop, True := by",
            "  obtain ⟨-, q, hv⟩ := some_lem (toOther hP2) hP2.fUsed",
            "  rcases hP2.fUsed with ⟨a, b⟩",
            "  have nested : Prop := hT.pins.2.1.1",
            "  have nested2 : Prop := hP2.fUsed.1",
            "  exact ⟨q, trivial⟩",
            "",
            "theorem shadowed_var (vSec : OtherRec) : Prop := by",
            "  exact vSec.1",
            "end",
            "",
            "theorem ret_subgoal_ok (h : OtherRec) : CustomBundle := by",
            "  have hsub : A ∧ B := by",
            "    exact ⟨h.a, h.b⟩",
            "  exact { fUsed := h.a, fDead := h.b }",
            "theorem subgoal_rintro_ok : CustomBundle → ∀ (X : Prop), (A ∧ B) → Prop := by",
            "  intro _ _",
            "  refine trivial_imp ?_",
            "  · rintro ⟨a, b⟩",
            "    exact a",
            "end TestNs",
        ])
        self.assertEqual(bph.find_struct_destructuring_hits(clean_lean, "CustomBundle", skip_range=(1, 4)), [])

        # Positive cases: all true positional destructures / constructors must trigger
        pos_lean = "\n".join([
            "theorem p_rcases (h : CustomBundle) : Prop := by",
            "  rcases h with ⟨a, _⟩",
            "  exact a",
            "theorem p_obtain (h : ns.CustomBundle) : Prop := by",
            "  obtain ⟨a, b⟩ := (h : ns.CustomBundle)",
            "  exact a",
            "theorem p_proj (h : CustomBundle) : Prop := by",
            "  exact h.1",
            "theorem p_fun (f : CustomBundle → Prop) : Prop := by",
            "  have g := fun (⟨a, b⟩ : CustomBundle) => a",
            "  exact f (CustomBundle.mk True False)",
            "theorem p_rintro : CustomBundle → Prop := by",
            "  rintro ⟨a, b⟩",
            "  exact a",
            "theorem p_ret_ctor (h : Other) : _root_.ns.CustomBundle := by",
            "  refine ⟨h.a, h.b⟩",
            "section",
            "variable (vSec : CustomBundle)",
            "theorem p_sec_var : Prop := vSec.2",
            "end",
        ])
        hits = bph.find_struct_destructuring_hits(pos_lean, "CustomBundle")
        kinds = {h["kind"] for h in hits}
        self.assertIn("rcases_destructure", kinds)
        self.assertIn("obtain_let_destructure", kinds)
        self.assertIn("positional_projection", kinds)
        self.assertIn("typed_fun_destructure", kinds)
        self.assertIn("explicit_mk", kinds)
        self.assertIn("domain_rintro_destructure", kinds)
        self.assertIn("positional_constructor", kinds)
        self.assertEqual(sum(1 for h in hits if h["kind"] == "positional_projection"), 2)

        # Primed structure name boundary test (`Hypotheses''`)
        primed_lean = "\n".join([
            "theorem mkHyp (h : Published) : _root_.CovTop.Hypotheses'' := by",
            "  have x := helper h.p1",
            "  refine ⟨h.p1, h.p2⟩",
        ])
        phits = bph.find_struct_destructuring_hits(primed_lean, "Hypotheses''")
        self.assertEqual(len(phits), 1)
        self.assertEqual(phits[0]["kind"], "positional_constructor")
        self.assertEqual(phits[0]["decl"], "mkHyp")

    def test_clump_header_cleanups_and_sibling_structs(self):
        td = tempfile.TemporaryDirectory()
        try:
            root = Path(td.name) / "repo"
            root.mkdir(parents=True, exist_ok=True)
            db = Path(td.name) / "idx.db"
            header_json = json.dumps({
                "m": "ClumpMember",
                "h": "module\n\npublic import Bundle\npublic import DeadLeaf\n",
            })
            base_files = {
                "src/Bundle.lean": "\n".join([
                    "module",
                    "structure PublishedBundle : Prop where",
                    "  p1 : Published.Keep",
                    "  p2 : Published.VolGe",
                ]),
                "src/Sibling.lean": "\n".join([
                    "module",
                    "structure Sibling₂ : Prop where",
                    "  p1 : Published.Keep",
                    "  p2 : _root_.Published.VolGe",
                ]),
                "src/Unrelated.lean": "\n".join([
                    "module",
                    "structure RecNums : Prop where",
                    "  p2 : 0 < eps",
                ]),
                "src/DeadLeaf.lean": "\n".join([
                    "module",
                    "theorem dead_volge : Published.VolGe := trivial",
                ]),
                "src/Host.lean": "\n".join([
                    "module",
                    "public import Bundle",
                    "public import DeadLeaf",
                    "theorem keepUse (b : Bundle.PublishedBundle) : Published.Keep := b.p1",
                    "def wrapDead : Published.VolGe := DeadLeaf.dead_volge",
                    f"-- clump-header: {header_json}",
                    "def buildBundle : Bundle.PublishedBundle where",
                    "  p1 := keepUse buildBundle",
                    "  p2 := wrapDead",
                ]),
                "src/Main.lean": "\n".join([
                    "module",
                    "import Host",
                ]),
            }
            base_sha = _init_git_repo(root, base_files)
            subprocess.run(
                [sys.executable, str(TOOLS_DIR / "import_index.py"), "--repo", str(root), "--db", str(db), "sync", "--ref", "main", "--no-remote-check"],
                check=True,
                capture_output=True,
            )

            plan_proc = subprocess.run(
                [
                    sys.executable,
                    str(TOOLS_DIR / "strip_planner.py"),
                    "--repo", str(root),
                    "--db", str(db),
                    "--ref", "main",
                    "bundle-field",
                    "--module", "Bundle",
                    "--struct", "PublishedBundle",
                    "--fields", "p2",
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            plan = json.loads(plan_proc.stdout)
            self.assertEqual(plan["orphan_files"], ["src/DeadLeaf.lean"])
            self.assertEqual(len(plan["clump_header_cleanups"]), 1)
            self.assertEqual(plan["clump_header_cleanups"][0]["mod"], "Host")
            self.assertEqual(plan["clump_header_cleanups"][0]["stale_imports"], ["DeadLeaf"])

            sib_names = [s["structure"] for s in plan["sibling_field_structures"]]
            self.assertIn("Sibling₂", sib_names)
            self.assertNotIn("RecNums", sib_names)
            self.assertNotIn("PublishedBundle", sib_names)

            # Audit-diff detects remaining `-- clump-header` import reference when live import & leaf deleted
            head_sha = _commit_changes(
                root,
                updates={
                    "src/Host.lean": "\n".join([
                        "module",
                        "public import Bundle",
                        f"-- clump-header: {header_json}",
                        "def keepOnly : Published.Keep := trivial",
                    ])
                },
                deletes=["src/DeadLeaf.lean"],
                msg="drop dead leaf leaving clump header",
            )
            aud_proc = subprocess.run(
                [sys.executable, str(TOOLS_DIR / "import_index.py"), "--repo", str(root), "--db", str(db), "audit-diff", base_sha, head_sha],
                check=True,
                capture_output=True,
                text=True,
            )
            aud = json.loads(aud_proc.stdout)
            self.assertEqual(aud["verdict"], "PASS")
            self.assertEqual(aud["clump_header_warnings_count"], 1)
            self.assertEqual(aud["clump_header_warnings"][0]["stale_imports"], ["DeadLeaf"])
        finally:
            td.cleanup()


if __name__ == "__main__":
    unittest.main()
