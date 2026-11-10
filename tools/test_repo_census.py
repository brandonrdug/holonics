"""Checks of the trunk contract's census on a synthetic repository; every write stays in a temporary directory."""

import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

TOOL = Path(__file__).with_name("repo_census.py")
OLD = "2026-01-01T00:00:00Z"


def sh(*args, cwd, env=None, check=True):
    e = dict(os.environ, GIT_AUTHOR_NAME="t", GIT_AUTHOR_EMAIL="t@example.invalid", GIT_COMMITTER_NAME="t",
             GIT_COMMITTER_EMAIL="t@example.invalid", **(env or {}))
    r = subprocess.run(list(args), cwd=str(cwd), capture_output=True, text=True, env=e)
    if check and r.returncode:
        raise AssertionError(f"{args}: {r.stderr}")
    return r.stdout.strip()


class CensusTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        t = Path(self.tmp.name)
        self.origin, self.repo = t / "origin.git", t / "repo"
        sh("git", "init", "-q", "--bare", "-b", "main", str(self.origin), cwd=t)
        sh("git", "init", "-q", "-b", "main", str(self.repo), cwd=t)
        g = self.g
        (self.repo / ".gitignore").write_text("/.local/\n/target/\n")
        (self.repo / "a.txt").write_text("a\n")
        g("add", "."), g("commit", "-qm", "first")
        g("remote", "add", "origin", str(self.origin))
        first = g("rev-parse", "HEAD")
        # A merged branch on both sides, and one that only stands here.
        g("checkout", "-qb", "claude/merged-pushed"), self.commit("b.txt"), g("push", "-q", "origin", "claude/merged-pushed")
        g("checkout", "-q", "main"), g("merge", "-q", "--no-ff", "-m", "merge", "claude/merged-pushed")
        g("push", "-q", "origin", "main")
        g("branch", "claude/merged-local", first)
        # Open branches a long time ahead of main: one pushed, two that never left, one protected.
        for name, push in (("claude/open-pushed", True), ("claude/open-local", False), ("claude/open-local-2", False),
                           ("codex/apple-silicon", True)):
            g("checkout", "-qb", name, "main"), self.commit(name.replace("/", "_"), old=True)
            if push:
                g("push", "-q", "origin", name)
        # The main checkout left on a detached head while another worktree holds main.
        g("checkout", "-q", "--detach", first)
        g("worktree", "add", "-q", ".local/wt/canon", "main")
        # A fresh task with no commit yet, a detached read with work in it, and a nested pair.
        g("worktree", "add", "-q", "-b", "claude/fresh", ".local/wt/fresh", "origin/main")
        g("worktree", "add", "-q", "--detach", ".local/wt/old-read", "origin/main")
        r = self.repo / ".local/wt/old-read"
        self.commit("c.txt", cwd=r)
        self.read_head = sh("git", "rev-parse", "HEAD", cwd=r)
        (r / ".local/run").mkdir(parents=True), (r / ".local/run/x.bin").write_text("state")
        (r / "notes.txt").write_text("untracked"), (r / "a.txt").write_text("changed\n")
        (r / "target").mkdir(), (r / "target/big.o").write_text("o")
        g("worktree", "add", "-q", "-b", "claude/outer", ".local/wt/outer", "origin/main")
        sh("git", "worktree", "add", "-q", "--detach", ".local/wt/inner", "origin/main", cwd=self.repo / ".local/wt/outer")
        g("fetch", "-q", "origin")

    def g(self, *args, **kw):
        return sh("git", *args, cwd=self.repo, **kw)

    def commit(self, name, old=False, cwd=None):
        cwd = cwd or self.repo
        (cwd / name).write_text(name)
        env = {"GIT_AUTHOR_DATE": OLD, "GIT_COMMITTER_DATE": OLD} if old else None
        sh("git", "add", name, cwd=cwd), sh("git", "commit", "-qm", name, cwd=cwd, env=env)

    def tool(self, *args, repo=None):
        r = subprocess.run([sys.executable, str(TOOL), "--repo", str(repo or self.repo), *args], capture_output=True, text=True)
        return r.returncode, r.stdout + r.stderr

    def snapshot(self, repo=None):
        return sh("git", "for-each-ref", cwd=repo or self.repo), sh("git", "worktree", "list", "--porcelain", cwd=repo or self.repo)

    def test_census_reads_and_changes_nothing(self):
        before = self.snapshot()
        code, out = self.tool()
        self.assertEqual(code, 1, out)
        self.assertEqual(before, self.snapshot())
        violations = out.split("VIOLATIONS")[1].split("STEPS THAT LOSE NOTHING")[0]
        for want in ("the main checkout is on a detached head", "main is checked out in another worktree",
                     "claude/merged-pushed: merged, the local branch still stands",
                     "claude/merged-pushed: merged, the remote branch still stands",
                     "claude/merged-local: merged, the local branch still stands",
                     "claude/open-pushed: 1 commits not on main", "claude/open-local: 1 commits not on main",
                     "nested inside the worktree"):
            self.assertIn(want, violations)
        for absent in ("claude/fresh", "apple-silicon", "claude/outer:"):
            self.assertNotIn(absent, violations)

    def test_apply_does_only_what_loses_nothing(self):
        code, out = self.tool("--apply")
        self.assertNotIn("FAILED", out)
        self.assertEqual(self.g("branch", "--show-current"), "main")
        self.assertEqual(self.g("rev-parse", "HEAD"), self.g("rev-parse", "origin/main"))
        self.assertEqual(sh("git", "branch", "--show-current", cwd=self.repo / ".local/wt/canon"), "")
        local = self.g("for-each-ref", "--format=%(refname:short)", "refs/heads").split()
        remote = sh("git", "for-each-ref", "--format=%(refname:short)", "refs/heads", cwd=self.origin).split()
        self.assertNotIn("claude/merged-pushed", local), self.assertNotIn("claude/merged-local", local)
        self.assertNotIn("claude/merged-pushed", remote)
        for kept in ("claude/open-pushed", "claude/open-local", "claude/fresh", "claude/outer", "codex/apple-silicon"):
            self.assertIn(kept, local)
        self.assertIn("claude/open-pushed", remote), self.assertIn("codex/apple-silicon", remote)

    def test_archive_keeps_every_commit_and_pushes_only_what_was_pushed(self):
        tips = {n: self.g("rev-parse", n) for n in ("claude/open-pushed", "claude/open-local", "claude/open-local-2")}
        code, out = self.tool("--archive", "claude/open-pushed", "claude/open-local", "codex/apple-silicon", "claude/fresh")
        self.assertIn("codex/apple-silicon: protected", out), self.assertIn("claude/fresh: held by the worktree", out)
        self.assertEqual(self.g("rev-parse", "archive/claude/open-pushed"), tips["claude/open-pushed"])
        self.assertEqual(self.g("rev-parse", "archive/claude/open-local"), tips["claude/open-local"])
        on_origin = sh("git", "for-each-ref", "--format=%(refname)", cwd=self.origin).split()
        self.assertIn("refs/tags/archive/claude/open-pushed", on_origin)
        self.assertNotIn("refs/heads/claude/open-pushed", on_origin)
        self.assertNotIn("refs/tags/archive/claude/open-local", on_origin)
        local = self.g("for-each-ref", "--format=%(refname:short)", "refs/heads").split()
        self.assertNotIn("claude/open-pushed", local), self.assertNotIn("claude/open-local", local)
        self.assertIn("codex/apple-silicon", local)
        code, out = self.tool("--archive-idle", "30", "--push-local")
        on_origin = sh("git", "for-each-ref", "--format=%(refname)", cwd=self.origin).split()
        self.assertIn("refs/tags/archive/claude/open-local-2", on_origin)
        self.assertIn("refs/heads/codex/apple-silicon", on_origin)
        self.assertIn("claude/outer", self.g("for-each-ref", "--format=%(refname:short)", "refs/heads").split())

    def test_retire_moves_every_file_and_leaves_live_worktrees(self):
        r = self.repo / ".local/wt/old-read"
        code, out = self.tool("--retire", "old-read")
        self.assertIn("live (a file under .local/ written in the last day)", out)
        self.assertTrue(r.exists())
        old = time.time() - 5 * 86400
        os.utime(r / ".local/run/x.bin", (old, old))
        reg = self.repo / ".local/dispatch"
        reg.mkdir(parents=True)
        (reg / "lap.json").write_text(json.dumps({"name": "lap", "backend": "colab", "cwd": str(r)}))
        code, out = self.tool("--retire", "old-read")
        self.assertIn("live (run lap)", out)
        (reg / "lap.exit").write_text("0 2026-11-10T00:00:00Z")
        code, out = self.tool("--retire", str(r))
        self.assertNotIn("FAILED", out)
        self.assertFalse(r.exists())
        dest = next((self.repo / ".local/archive/wt").glob("*-old-read"))
        self.assertEqual((dest / ".local/run/x.bin").read_text(), "state")
        self.assertEqual((dest / "untracked/notes.txt").read_text(), "untracked")
        self.assertIn("+changed", (dest / "tracked-changes.patch").read_text())
        manifest = (dest / "MANIFEST.txt").read_text()
        self.assertIn("retired by name: target", manifest), self.assertIn("tag archive/wt/old-read", manifest)
        self.assertEqual(self.g("rev-parse", "archive/wt/old-read"), self.read_head)

    def test_a_worktree_that_a_run_or_a_process_only_reads_is_live(self):
        r, elsewhere = self.repo / ".local/wt/old-read", self.repo / ".local/wt/fresh"
        old = time.time() - 5 * 86400
        os.utime(r / ".local/run/x.bin", (old, old))
        reader = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(120)", f"--units={r}/.local/run/x.bin"])
        self.addCleanup(reader.kill)
        code, out = self.tool("--retire", "old-read")
        self.assertRegex(out, r"live \(process \d+\)")
        reader.kill(), reader.wait()
        reg, script = self.repo / ".local/dispatch", elsewhere / "lap.sh"
        reg.mkdir(parents=True)
        (reg / "lap.json").write_text(json.dumps({"name": "lap", "backend": "colab", "cwd": str(elsewhere),
                                                  "script": str(script)}))
        for spelling in (f"{r}/.local/run/x.bin", ".local/wt/old-read/.local/run/x.bin", "../old-read/.local/run/x.bin"):
            script.write_text(f"learner --units {spelling}\n")
            code, out = self.tool("--retire", "old-read")
            self.assertIn("live (run lap reads it)", out, spelling)
            self.assertTrue(r.exists())
        script.write_text("bash chain.sh\n")  # the registered script is often one line that calls another
        (elsewhere / "chain.sh").write_text(f"bash {elsewhere}/lap_inner.sh\n")
        (elsewhere / "lap_inner.sh").write_text(f"learner --units {r}/.local/run/x.bin\n")
        code, out = self.tool("--retire", "old-read")
        self.assertIn("live (run lap reads it)", out)
        self.assertTrue(r.exists())
        (elsewhere / "lap_inner.sh").write_text("learner --units ../old-read-2/x.bin .local/wt/old-reading/x\n")  # others' names
        code, out = self.tool("--retire", "old-read")
        self.assertNotIn("FAILED", out)
        self.assertFalse(r.exists(), out)

    def test_retire_takes_the_inner_worktree_first(self):
        outer = self.repo / ".local/wt/outer"
        code, out = self.tool("--retire", "outer")
        self.assertTrue(outer.exists())
        self.assertRegex(out, r"left .*outer: (live|it contains the worktree)")
        for f in (outer / ".local/wt/inner").rglob("*"):
            pass
        code, out = self.tool("--retire", "outer", "inner")
        self.assertNotIn("FAILED", out)
        self.assertFalse(outer.exists(), out)
        self.assertIn("claude/outer", self.g("for-each-ref", "--format=%(refname:short)", "refs/heads").split())

    def test_dry_run_changes_nothing_and_keep_is_honoured(self):
        old = time.time() - 5 * 86400
        os.utime(self.repo / ".local/wt/old-read/.local/run/x.bin", (old, old))
        before = self.snapshot()
        for flags in (["--apply"], ["--archive-idle", "30"], ["--retire", "old-read", "outer", "inner"]):
            code, out = self.tool(*flags, "--dry-run")
            self.assertIn("would", out), self.assertIn("nothing was changed", out)
        self.assertEqual(before, self.snapshot())
        self.assertTrue((self.repo / ".local/wt/old-read/notes.txt").exists())
        self.assertFalse((self.repo / ".local/archive").exists())
        code, out = self.tool("--retire-idle", "0", "--keep", "old-read", "canon", "fresh")
        self.assertTrue((self.repo / ".local/wt/old-read").exists())
        self.assertTrue((self.repo / ".local/wt/fresh").exists())
        self.assertFalse((self.repo / ".local/wt/outer").exists(), out)
        code, out = self.tool("--archive-idle", "30", "--keep", "claude/open-local")
        local = self.g("for-each-ref", "--format=%(refname:short)", "refs/heads").split()
        self.assertIn("claude/open-local", local), self.assertNotIn("claude/open-local-2", local)

    def test_a_dirty_holder_of_main_is_detached_with_its_changes(self):
        canon = self.repo / ".local/wt/canon"
        (canon / "a.txt").write_text("uncommitted\n")
        code, out = self.tool("--apply")
        self.assertNotIn("FAILED", out)
        self.assertEqual(self.g("branch", "--show-current"), "main")
        self.assertEqual(self.g("rev-parse", "HEAD"), self.g("rev-parse", "origin/main"))
        self.assertEqual((canon / "a.txt").read_text(), "uncommitted\n")

    def test_a_remote_branch_that_moved_is_left(self):
        other = self.repo.with_name("other")
        sh("git", "clone", "-q", str(self.origin), str(other), cwd=self.repo.parent)
        sh("git", "checkout", "-q", "claude/merged-pushed", cwd=other)
        self.commit("late.txt", cwd=other)
        sh("git", "push", "-q", "origin", "claude/merged-pushed", cwd=other)
        late = sh("git", "rev-parse", "HEAD", cwd=other)
        code, out = self.tool("--apply", "--no-fetch")  # stale refs still read the branch as merged
        self.assertIn("FAILED  delete on origin: claude/merged-pushed", out)
        self.assertEqual(sh("git", "rev-parse", "refs/heads/claude/merged-pushed", cwd=self.origin), late)
        self.g("checkout", "-q", "--detach")
        code, out = self.tool("--apply")  # with the fetch it reads as unmerged and is not in the plan
        self.assertNotIn("delete on origin: claude/merged-pushed", out)
        self.assertEqual(sh("git", "rev-parse", "refs/heads/claude/merged-pushed", cwd=self.origin), late)

    def test_a_failed_fetch_stops_every_change(self):
        self.g("remote", "set-url", "origin", str(self.origin) + "-gone")
        before = self.snapshot()
        code, out = self.tool("--apply")
        self.assertNotEqual(code, 0)
        self.assertIn("refused: the fetch failed", out)
        self.assertEqual(before, self.snapshot())

    def test_a_shallow_clone_is_read_only(self):
        canon = self.repo / ".local/wt/canon"  # it holds main
        for name in ("d.txt", "e.txt"):
            self.commit(name, cwd=canon)
        sh("git", "push", "-q", "origin", "main", cwd=canon)
        shallow = self.repo.with_name("shallow")
        sh("git", "clone", "-q", "--depth", "1", "--no-single-branch", "file://" + str(self.origin), str(shallow),
           cwd=self.repo.parent)
        code, out = self.tool(repo=shallow)
        self.assertIn("THIS CLONE IS SHALLOW", out)
        code, out = self.tool("--apply", repo=shallow)
        self.assertNotEqual(code, 0)
        self.assertIn("refused: this clone is shallow", out)
        remote = sh("git", "for-each-ref", "--format=%(refname:short)", "refs/heads", cwd=self.origin).split()
        self.assertIn("claude/merged-pushed", remote)

    def test_a_mounted_view_is_read_only(self):
        moved = self.repo.with_name("mounted")
        self.repo.rename(moved)
        before = self.snapshot(moved)
        code, out = self.tool(repo=moved)
        self.assertIn("THE WORKTREES' PATHS DO NOT RESOLVE HERE", out)
        for flag in (["--apply"], ["--retire-idle", "0"], ["--archive", "claude/open-local"], ["--fetch"]):
            code, out = self.tool(*flag, repo=moved)
            self.assertNotEqual(code, 0)
            self.assertIn("refused", out)
        self.assertEqual(before, self.snapshot(moved))


if __name__ == "__main__":
    unittest.main()
