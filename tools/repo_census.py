#!/usr/bin/env python3
"""The census of the trunk contract (CLAUDE.md and AGENTS.md, "Git: the trunk contract").

It prints the main checkout's state, every branch against `origin/main`, every worktree, each violation of the
contract, and the steps that would repair them. With no flag it changes nothing and needs no network.

  repo_census.py                      the census and its plan (read-only; exit 1 when a violation stands)
  repo_census.py --fetch              the same, after `git fetch --prune origin`
  ... --no-fetch                      with any change below: skip the fetch (a remote deletion still carries its lease)
  repo_census.py --apply              fetch, then do the steps that lose nothing:
                                        prune worktree entries whose directory is gone,
                                        put the main checkout on `main` at `origin/main` (fast-forward only),
                                        delete local and remote branches already merged into `origin/main`
  repo_census.py --archive B [B ...]  set a branch aside: tag `archive/<B>` at its tip, push the tag, delete the branch
  repo_census.py --archive-idle DAYS  the same for every unmerged branch whose tip is older than DAYS days and that
                                      no worktree holds
  repo_census.py --retire W [W ...]   end a worktree (a path, or its directory's name) without losing a file
  repo_census.py --retire-idle DAYS   the same for every worktree untouched for DAYS days
  ... --keep NAME [NAME ...]          leave these worktrees and branches out of the two idle sweeps
  ... --dry-run                       with any of the above: fetch, print each step and do none of them

"Untouched" is read from modification times, and a worktree whose states or binaries are only read by a run elsewhere
looks idle. Retiring it loses nothing but moves its `.local/` to the archive, so a script that names the old path
breaks. Before an idle sweep, name such worktrees with `--keep`, and read the sweep with `--dry-run` first.

What "loses nothing" means, clause by clause:
- A merged branch's commits are on `origin/main`, so deleting the name loses nothing.
- An archived branch keeps every commit under its tag. A branch that never left this machine is tagged locally and its
  tag is pushed only with `--push-local`, after its content has been read against the publication rule (the repository
  is public, and an unpushed branch was never checked for private material).
- A retired worktree's `.local/` is moved whole to `<main>/.local/archive/wt/<date>-<name>/`, with every other
  untracked or ignored file, a patch of its uncommitted changes and a manifest. Build products (BUILD_PRODUCTS) are
  retired by name. A detached head that no ref reaches is tagged `archive/wt/<name>` first.
- A worktree with a live run is never touched: a run in the registry of `tools/runs.py` that has not ended, a process
  whose directory is inside the worktree, or a file under its `.local/` written in the last day.

Housekeeping runs on the host. Through a mount, a container or a VM the worktrees' recorded paths do not resolve and
git reads every one of them as prunable (all 89 did on November 10, 2026); pruning there would cut live worktrees from
the repository. The tool detects that view, prints the census read-only and refuses every change.

A change is made only on what was verified:
- Every change starts with a fetch, and a failed fetch stops it: the remote's branches would be read from stale refs.
- A remote branch is deleted with a lease on the tip that was read as merged, so a branch that moved since is left.
- A shallow clone (a cloud session's) cannot tell ancestry: on November 10, 2026 one read five merged branches as
  "no history shared with main" with thousands of commits ahead. The census says so there and every change is refused.

"Untouched" is also reset by any mass maintenance (a move of old folders touched some sixty worktrees at once on
November 9, 2026), so an idle sweep is a listing to read, never a judgment of use.

Protected names are never deleted: `main`, `archive/*` and `codex/apple-silicon`.

The clauses about the main checkout are the PC's (`/home/b/Workspaces/holonics`). A disposable clone that works on its
task branch (a cloud session's) reads "not on main" for itself, and that line is expected there.
"""
import argparse
import json
import os
import shutil
import signal
import subprocess
import sys
import time
from pathlib import Path

PROTECTED = {"main", "codex/apple-silicon"}
PROTECTED_PREFIXES = ("archive/",)
BUILD_PRODUCTS = ("target", "lean/.lake", "__pycache__", ".pytest_cache", "node_modules")
DAY = 86400
ROOT = None  # the main checkout, set in main()
DRY = False  # --dry-run: print each step, do none


def git(*args, cwd=None, check=True, write=False):
    env = dict(os.environ)
    if not write:
        env["GIT_OPTIONAL_LOCKS"] = "0"  # a read never takes a lock or refreshes an index
    r = subprocess.run(["git", *args], cwd=str(cwd or ROOT), capture_output=True, text=True, env=env)
    if check and r.returncode:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip() or r.stdout.strip()}")
    return r.stdout.rstrip("\n") if check else r


def protected(name):
    return name in PROTECTED or name.startswith(PROTECTED_PREFIXES)


def days(seconds):
    return f"{seconds / DAY:.1f} d"


def find_root(start):
    r = subprocess.run(["git", "-C", str(start), "rev-parse", "--path-format=absolute", "--git-common-dir"],
                       capture_output=True, text=True)
    if r.returncode or not r.stdout.strip():
        sys.exit(f"{start} is not inside a git repository")
    return Path(r.stdout.strip()).parent


# ---------------------------------------------------------------------------------------------------------------------
# Reading
# ---------------------------------------------------------------------------------------------------------------------

def read_worktrees():
    out, cur = [], None
    for ln in git("worktree", "list", "--porcelain").splitlines():
        if ln.startswith("worktree "):
            cur = {"path": Path(ln[9:]), "branch": None, "head": None, "missing": False, "locked": False}
            out.append(cur)
        elif ln.startswith("HEAD "):
            cur["head"] = ln[5:]
        elif ln.startswith("branch "):
            cur["branch"] = ln[7:].removeprefix("refs/heads/")
        elif ln.startswith("prunable"):
            cur["missing"] = True
        elif ln.startswith("locked"):
            cur["locked"] = True
    for w in out[1:]:
        w["missing"] = w["missing"] or not w["path"].exists()
    return out


def shallow():
    return git("rev-parse", "--is-shallow-repository") == "true"


def foreign_view(worktrees):
    """True when the repository is seen through a mount: a recorded path is absent, yet the same directory exists
    under the root we see. Also true when most linked worktrees are absent at once, which no ordinary deletion does."""
    linked = worktrees[1:]
    gone = [w for w in linked if w["missing"]]
    for w in gone:
        parts = w["path"].parts
        for i in range(1, len(parts)):
            if (ROOT.joinpath(*parts[i:]) / ".git").exists():
                return True
    return len(gone) >= 3 and 2 * len(gone) > len(linked)


def read_refs():
    refs = {"heads": {}, "remotes": {}, "tags": {}}
    fmt = "%(refname)%09%(objectname)%09%(committerdate:unix)%09%(*objectname)"
    for ln in git("for-each-ref", f"--format={fmt}", "refs/heads", "refs/remotes/origin", "refs/tags").splitlines():
        name, sha, when, peeled = (ln.split("\t") + [""])[:4]
        when = int(when) if when else 0
        if name.startswith("refs/heads/"):
            refs["heads"][name[11:]] = (sha, when)
        elif name.startswith("refs/remotes/origin/") and name != "refs/remotes/origin/HEAD":
            refs["remotes"][name[20:]] = (sha, when)
        elif name.startswith("refs/tags/"):
            refs["tags"][name[10:]] = peeled or sha
    return refs


def merged_set(base, namespace):
    out = git("for-each-ref", "--format=%(refname)", "--merged", base, namespace)
    return set(out.split())


def unmerged_facts(base, tip):
    """(commits not on base, age of the oldest of them in seconds, shares history with base)."""
    stamps = git("log", "--format=%ct", f"{base}..{tip}").split()
    shares = git("merge-base", base, tip, check=False).returncode == 0
    return len(stamps), (time.time() - min(int(s) for s in stamps)) if stamps else 0, shares


def reachable(sha):
    return bool(git("for-each-ref", "--contains", sha, "--count=1", "--format=%(refname)"))


def on_remote(sha):
    return bool(git("for-each-ref", "--contains", sha, "--count=1", "--format=%(refname)", "refs/remotes/origin"))


def dirty(path):
    return bool(git("status", "--porcelain", "--untracked-files=no", cwd=path))


def unit_active(unit):
    try:
        r = subprocess.run(["systemctl", "--user", "is-active", unit], capture_output=True, text=True)
    except OSError:
        return None
    return r.stdout.strip() in ("active", "activating", "deactivating")


def live_reasons(path):
    """Why a worktree must not be touched now."""
    path, why = path.resolve(), []
    reg = ROOT / ".local" / "dispatch"
    for j in sorted(reg.glob("*.json")) if reg.is_dir() else []:
        try:
            e = json.loads(j.read_text())
        except (OSError, ValueError):
            continue
        inside = any(str(e.get(k, "")).startswith(str(path) + os.sep) or e.get(k) == str(path)
                     for k in ("cwd", "out", "log", "script"))
        if not inside:
            continue
        ended = (reg / f"{e.get('name')}.exit").exists()
        active = unit_active(e["unit"]) if e.get("backend") == "local" and e.get("unit") else None
        if active or (active is None and not ended):
            why.append(f"run {e.get('name')}")
    mine = set()
    pid = os.getpid()
    while pid > 1:  # this process and its ancestors may stand inside the worktree
        mine.add(pid)
        try:
            pid = int(Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()[1])
        except (OSError, ValueError, IndexError):
            break
    for p in Path("/proc").glob("[0-9]*"):
        if int(p.name) in mine:
            continue
        try:
            cwd = os.readlink(p / "cwd")
        except OSError:
            continue
        if cwd == str(path) or cwd.startswith(str(path) + os.sep):
            why.append(f"process {p.name}")
            break
    local = path / ".local"
    if local.is_dir():
        r = subprocess.run(["find", str(local), "-type", "f", "-mmin", "-1440", "-print", "-quit"],
                           capture_output=True, text=True)
        if r.stdout.strip():
            why.append("a file under .local/ written in the last day")
    return why


def last_touch(w):
    """The newest of: the worktree's git state, its top-level entries, and its `.local/` to three levels."""
    newest = 0
    admin = git("rev-parse", "--path-format=absolute", "--git-dir", cwd=w["path"], check=False)
    spots = []
    if admin.returncode == 0:
        g = Path(admin.stdout.strip())
        spots += [g / "HEAD", g / "index", g / "logs" / "HEAD"]
    spots += list(w["path"].glob("*")) + list(w["path"].glob(".local/*")) + list(w["path"].glob(".local/*/*")) \
        + list(w["path"].glob(".local/*/*/*"))
    for s in spots:
        try:
            newest = max(newest, s.lstat().st_mtime)
        except OSError:
            pass
    return newest


def census():
    """Read everything once. Returns the state, the violations and the lossless plan."""
    wts = read_worktrees()
    refs = read_refs()
    foreign = foreign_view(wts)
    base = "refs/remotes/origin/main" if "main" in refs["remotes"] else "refs/heads/main"
    if "main" not in refs["remotes"] and "main" not in refs["heads"]:
        sys.exit("neither origin/main nor main exists")
    merged = merged_set(base, "refs/heads") | merged_set(base, "refs/remotes/origin")
    held = {}
    for w in wts:
        if w["branch"]:
            held.setdefault(w["branch"], []).append(w)
    S = {"wts": wts, "refs": refs, "foreign": foreign, "shallow": shallow(), "base": base, "held": held,
         "branches": {}, "violations": [], "plan": []}
    V, P = S["violations"], S["plan"]

    # The main checkout.
    m = wts[0]
    m_dirty = False if foreign and not m["path"].exists() else dirty(m["path"])
    base_sha = git("rev-parse", base)
    S["main"] = {"branch": m["branch"], "head": m["head"], "dirty": m_dirty, "base_sha": base_sha}
    others_on_main = [w for w in wts[1:] if w["branch"] == "main"]
    if m_dirty:
        V.append("the main checkout has uncommitted changes")
    if m["branch"] != "main":
        V.append(f"the main checkout is on {m['branch'] or 'a detached head ' + m['head'][:9]}, not on main")
        if not m_dirty:
            P.append(("checkout-main", None))
    for w in others_on_main:
        V.append(f"main is checked out in another worktree: {w['path']}")
        if not m_dirty:
            P.append(("detach", w))  # at the same commit: its files and index stay as they are
    if "main" in refs["heads"] and "main" in refs["remotes"]:
        local_main = refs["heads"]["main"][0]
        if local_main != base_sha:
            if git("merge-base", "--is-ancestor", local_main, base_sha, check=False).returncode == 0:
                V.append(f"local main {local_main[:9]} is behind origin/main {base_sha[:9]}")
                if not m_dirty:
                    P.append(("ff-main", None))
            else:
                V.append(f"local main {local_main[:9]} holds commits that origin/main does not")
    elif "main" not in refs["heads"] and not m_dirty:
        P.append(("ff-main", None))

    # Branches.
    for name in sorted(set(refs["heads"]) | set(refs["remotes"])):
        loc, rem = refs["heads"].get(name), refs["remotes"].get(name)
        b = {"local": loc, "remote": rem, "held": held.get(name, []), "protected": protected(name)}
        b["local_merged"] = loc is not None and f"refs/heads/{name}" in merged
        b["remote_merged"] = rem is not None and f"refs/remotes/origin/{name}" in merged
        S["branches"][name] = b
        if b["protected"]:
            continue
        tip = (loc or rem)[0]
        b["tagged"] = refs["tags"].get(f"archive/{name}") == tip
        live_local = loc is not None and not b["local_merged"]
        if b["local_merged"] and not b["held"]:
            V.append(f"{name}: merged, the local branch still stands")
            P.append(("del-local", name))
        if b["remote_merged"] and not b["held"]:  # a held branch is its worktree's matter, judged below
            if live_local:
                V.append(f"{name}: the remote branch is merged while the local one holds commits not on main")
            else:
                V.append(f"{name}: merged, the remote branch still stands")
                P.append(("del-remote", name))
        if (loc and not b["local_merged"]) or (rem and not b["remote_merged"] and not loc):
            n, age, shares = unmerged_facts(base, tip)
            b["ahead"], b["age"], b["shares"] = n, age, shares
            if age > DAY:
                what = "merge what is verified, or archive it" if shares else "no history shared with main: archive it"
                V.append(f"{name}: {n} commits not on main, the oldest {days(age)} old ({what})")

    # Worktrees.
    linked = [w for w in wts[1:]]
    home = ROOT / ".local" / "wt"
    for w in linked:
        w["name"] = w["path"].name
        if w["missing"]:
            if not foreign:
                V.append(f"worktree {w['path']}: its directory is gone")
            continue
        w["dirty"] = dirty(w["path"])
        w["touch"] = last_touch(w)
        inner = [o for o in linked if o is not w and not o["missing"] and w["path"] in o["path"].parents]
        outer = [o for o in linked if o is not w and o["path"] in w["path"].parents]
        w["inner"], w["outer"] = inner, outer
        if w["path"].parent != home:
            V.append(f"worktree {w['path']}: not directly under .local/wt/")
        if outer:
            V.append(f"worktree {w['path']}: nested inside the worktree {outer[0]['path']}")
        stale = time.time() - w["touch"] > DAY  # a fresh task has no commit yet, and a read lasts a session
        if not w["branch"]:
            if stale:
                V.append(f"worktree {w['path']}: detached at {w['head'][:9]} and untouched "
                         f"{days(time.time() - w['touch'])} (a read that should have ended)")
        elif not protected(w["branch"]) and S["branches"].get(w["branch"], {}).get("local_merged") and stale:
            V.append(f"worktree {w['path']}: its branch {w['branch']} is merged (end the worktree)")
    if not foreign and any(w["missing"] for w in linked):
        P.append(("prune", None))
    return S


# ---------------------------------------------------------------------------------------------------------------------
# Printing
# ---------------------------------------------------------------------------------------------------------------------

def show(S):
    now = time.time()
    m = S["main"]
    print(f"MAIN CHECKOUT {ROOT}")
    print(f"  on {S['wts'][0]['branch'] or 'a detached head'} at {m['head'][:9]}, "
          f"{'uncommitted changes' if m['dirty'] else 'clean'}; {S['base'].removeprefix('refs/remotes/')} is "
          f"{m['base_sha'][:9]}")
    fh = Path(git("rev-parse", "--path-format=absolute", "--git-common-dir")) / "FETCH_HEAD"
    if fh.exists():
        print(f"  the remote's branches as of the last fetch, {days(now - fh.stat().st_mtime)} ago")
    if S["foreign"]:
        print("  THE WORKTREES' PATHS DO NOT RESOLVE HERE: this is a mount, a container or a VM. Read-only.")
    if S["shallow"]:
        print("  THIS CLONE IS SHALLOW: a branch below may read as not merged, or as sharing no history, when it is "
              "merged. Read-only.")

    B = S["branches"]
    print(f"\nBRANCHES {len(S['refs']['heads'])} local, {len(S['refs']['remotes'])} on origin")
    for name, b in B.items():
        where = "local+origin" if b["local"] and b["remote"] else ("local" if b["local"] else "origin")
        if b["local"] and b["remote"] and b["local"][0] != b["remote"][0]:
            where += " (tips differ)"
        tip, when = (b["local"] or b["remote"])
        if b["protected"]:
            state = "protected"
        elif "ahead" in b:
            state = f"{b['ahead']} not on main, oldest {days(b['age'])}"
            if not b["shares"]:
                state += ", no shared history"
            if b.get("tagged"):
                state += ", archive tag at its tip"
        else:
            state = "merged"
        hold = f"  held by {b['held'][0]['path'].name}" if b["held"] else ""
        print(f"  {name:<52} {where:<26} {tip[:9]} tip {days(now - when):>8}  {state}{hold}")

    linked = S["wts"][1:]
    print(f"\nWORKTREES {len(linked)} besides the main checkout")
    for w in linked:
        if w["missing"]:
            print(f"  {str(w['path']):<70} {'directory not found here' if S['foreign'] else 'directory gone'}  "
                  f"{w['branch'] or 'detached'} {w['head'][:9]}")
            continue
        notes = [w["branch"] or "detached", w["head"][:9], "dirty" if w["dirty"] else "clean",
                 f"untouched {days(now - w['touch'])}"]
        if w["locked"]:
            notes.append("locked")
        print(f"  {str(w['path']):<70} {'  '.join(notes)}")

    print(f"\nVIOLATIONS {len(S['violations'])}")
    for v in S["violations"]:
        print(f"  {v}")
    print(f"\nSTEPS THAT LOSE NOTHING {len(S['plan'])}" + (" (refused in this view)" if S["foreign"] or S["shallow"]
                                                          else " (run with --apply)"))
    for kind, arg in S["plan"]:
        print("  " + describe(kind, arg))


def describe(kind, arg):
    if kind == "detach":
        return f"detach the worktree that holds main: {arg['path']}"
    return {"prune": "prune worktree entries whose directory is gone",
            "checkout-main": "put the main checkout on main",
            "ff-main": "fast-forward main to origin/main",
            "del-local": f"delete the merged local branch {arg}",
            "del-remote": f"delete the merged remote branch {arg}"}[kind]


# ---------------------------------------------------------------------------------------------------------------------
# Changing
# ---------------------------------------------------------------------------------------------------------------------

def refuse_foreign(S):
    if S["foreign"]:
        sys.exit("refused: the worktrees' paths do not resolve here. Housekeeping runs on the host.")
    if S["shallow"]:
        sys.exit("refused: this clone is shallow, so which branches are merged cannot be told here. Housekeeping "
                 "runs on the host's full clone.")


def delete_remote(name, sha):
    """Delete a branch on origin only if its tip is still the one that was read."""
    git("push", "origin", f"--force-with-lease={name}:{sha}", f":refs/heads/{name}", write=True)


def step(text, fn):
    if DRY:
        print(f"  would   {text}")
        return True
    try:
        fn()
        print(f"  done    {text}")
        return True
    except RuntimeError as e:
        print(f"  FAILED  {text}: {e}")
        return False


def apply(S):
    refuse_foreign(S)
    plan = S["plan"]
    if ("prune", None) in plan:
        step(describe("prune", None), lambda: git("worktree", "prune", write=True))
    freed = True
    for kind, w in plan:
        if kind == "detach":
            why = live_reasons(w["path"])
            if why:
                print(f"  left    {w['path']} holds main and is live ({'; '.join(why)})")
                freed = False
            else:
                freed = step(describe(kind, w), lambda w=w: git("checkout", "--detach", cwd=w["path"], write=True)) \
                    and freed
    main_free = freed if DRY else not any(w["branch"] == "main" for w in read_worktrees()[1:])
    if any(k == "checkout-main" for k, _ in plan) and main_free:
        head = S["main"]["head"]
        if not reachable(head):  # a detached head of the main checkout that nothing else names
            tag = f"archive/wt/main-checkout-{head[:9]}"
            step(f"tag {tag}", lambda: git("tag", tag, head, write=True))
        heads, remotes = S["refs"]["heads"], S["refs"]["remotes"]
        if "main" in heads and "main" in remotes and git("merge-base", "--is-ancestor", heads["main"][0],
                                                          remotes["main"][0], check=False).returncode == 0:
            step("put the main checkout on main at origin/main",
                 lambda: git("checkout", "-B", "main", "origin/main", write=True))
        elif "main" in heads:
            step(describe("checkout-main", None), lambda: git("checkout", "main", write=True))
        else:
            step(describe("checkout-main", None), lambda: git("checkout", "-b", "main", "--track", "origin/main",
                                                             write=True))
    wts = read_worktrees()
    if DRY:
        if any(k == "ff-main" for k, _ in plan):
            step(describe("ff-main", None), None)
    elif wts[0]["branch"] == "main" and "main" in S["refs"]["remotes"] and not dirty(ROOT):
        if git("rev-parse", "HEAD") != git("rev-parse", "origin/main"):
            step(describe("ff-main", None), lambda: git("merge", "--ff-only", "origin/main", write=True))
    for kind, name in plan:
        if kind == "del-local":
            step(describe(kind, name), lambda name=name: git("branch", "-D", name, write=True))
    for kind, name in plan:
        if kind == "del-remote":
            sha = S["refs"]["remotes"][name][0]
            step(f"delete on origin: {name} (at {sha[:9]})", lambda name=name, sha=sha: delete_remote(name, sha))


def tag_name(S, wanted, sha):
    tags = S["refs"]["tags"]
    if wanted not in tags or tags[wanted] == sha:
        return wanted
    return f"{wanted}-{sha[:9]}"


def archive(S, names, push_local):
    refuse_foreign(S)
    for name in names:
        b = S["branches"].get(name)
        if b is None:
            print(f"  left    {name}: no such branch")
            continue
        if b["protected"]:
            print(f"  left    {name}: protected")
            continue
        if b["held"]:
            print(f"  left    {name}: held by the worktree {b['held'][0]['path']} (end the worktree first)")
            continue
        has_origin = bool(S["refs"]["remotes"])
        loc = b["local"][0] if b["local"] else None
        rem = b["remote"][0] if b["remote"] else None
        tips = [(f"archive/{name}", loc or rem)]
        if loc and rem and git("merge-base", "--is-ancestor", rem, loc, check=False).returncode:
            tips.append((f"archive/origin/{name}", rem))  # the remote tip holds commits the local one lacks
        ok, pushed = True, []
        for wanted, sha in tips:
            tag = tag_name(S, wanted, sha)
            if S["refs"]["tags"].get(tag) != sha:
                ok = ok and step(f"tag {tag} at {sha[:9]}", lambda: git("tag", tag, sha, write=True))
                S["refs"]["tags"][tag] = sha
            if has_origin and ok:
                if on_remote(sha) or push_local:
                    if step(f"push the tag {tag}", lambda: git("push", "origin", f"refs/tags/{tag}", write=True)):
                        pushed.append(sha)
                    else:
                        ok = False
                else:
                    print(f"  kept    {tag} stays on this machine: its commits were never pushed. Read them against "
                          f"the publication rule, then push the tag (--push-local).")
        if not ok:
            print(f"  left    {name}: a tag was not made or pushed, so the branch stands")
            continue
        if rem:
            covered = any(git("merge-base", "--is-ancestor", rem, sha, check=False).returncode == 0 for sha in pushed)
            if not covered:  # the local tag stays here, so the remote tip gets a pushed tag of its own
                tag = tag_name(S, f"archive/origin/{name}", rem)
                made = S["refs"]["tags"].get(tag) == rem or \
                    step(f"tag {tag} at {rem[:9]}", lambda: git("tag", tag, rem, write=True))
                covered = made and \
                    step(f"push the tag {tag}", lambda: git("push", "origin", f"refs/tags/{tag}", write=True))
            if covered:
                step(f"delete {name} on origin (at {rem[:9]})", lambda: delete_remote(name, rem))
            else:
                print(f"  left    {name} on origin: no pushed tag reaches its tip")
        if loc:
            step(f"delete the local branch {name}", lambda: git("branch", "-D", name, write=True))


def find_worktree(S, key):
    for w in S["wts"][1:]:
        if str(w["path"]) == str(Path(key).resolve()) or str(w["path"]) == key or w["path"].name == key:
            return w
    return None


def retire(S, targets):
    refuse_foreign(S)
    stamp = time.strftime("%Y-%m-%d")
    todo = sorted(targets, key=lambda w: -len(w["path"].parts))  # innermost first
    chosen = {str(w["path"]) for w in todo}
    would = set()
    for w in todo:
        path, name = w["path"], w["path"].name
        if w["missing"]:
            print(f"  left    {path}: its directory is gone (--apply prunes the entry)")
            continue
        if w["locked"]:
            print(f"  left    {path}: locked")
            continue
        why = live_reasons(path)
        if why:
            print(f"  left    {path}: live ({'; '.join(why)})")
            continue
        inner = [o for o in read_worktrees()[1:] if path in o["path"].parents and o["path"].exists()
                 and not (DRY and str(o["path"]) in would)]
        if inner:
            print(f"  left    {path}: it contains the worktree {inner[0]['path']}"
                  + ("" if str(inner[0]["path"]) in chosen else " (retire that one first)"))
            continue
        if DRY:
            would.add(str(path))
            print(f"  would   retire {path} ({w['branch'] or 'detached'} {w['head'][:9]}, "
                  f"untouched {days(time.time() - w['touch'])}{', uncommitted changes' if w['dirty'] else ''})")
            continue
        dest = ROOT / ".local" / "archive" / "wt" / f"{stamp}-{name}"
        n = 1
        while dest.exists():
            n += 1
            dest = dest.with_name(f"{stamp}-{name}-{n}")
        try:
            lines = [f"worktree {path}", f"branch {w['branch'] or 'detached'}", f"head {w['head']}",
                     f"retired {time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}"]
            if not w["branch"] and not reachable(w["head"]):
                tag = tag_name(S, f"archive/wt/{name}", w["head"])
                git("tag", tag, w["head"], write=True)
                S["refs"]["tags"][tag] = w["head"]
                lines.append(f"tag {tag}")
            dest.mkdir(parents=True)
            patch = subprocess.run(["git", "diff", "--binary", "HEAD"], cwd=str(path), capture_output=True)
            if patch.stdout:
                (dest / "tracked-changes.patch").write_bytes(patch.stdout)
                lines.append("tracked-changes.patch: the uncommitted changes to tracked files")
            for flags, sub in ((["--exclude-standard"], "untracked"), (["--ignored", "--exclude-standard"], "ignored")):
                listed = subprocess.run(["git", "ls-files", "--others", "--directory", "-z", *flags], cwd=str(path),
                                        capture_output=True, text=True).stdout.split("\0")
                for rel in filter(None, listed):
                    rel = rel.rstrip("/")
                    src = path / rel
                    if not (src.exists() or src.is_symlink()):
                        continue
                    if any(rel == p or rel.endswith("/" + p) or rel.startswith(p + "/") for p in BUILD_PRODUCTS) \
                            or rel.endswith(".pyc"):
                        lines.append(f"retired by name: {rel}")
                        continue
                    to = dest / ".local" if rel == ".local" else dest / sub / rel
                    to.parent.mkdir(parents=True, exist_ok=True)
                    shutil.move(str(src), str(to))
                    lines.append(f"moved: {rel}")
            (dest / "MANIFEST.txt").write_text("\n".join(lines) + "\n")
            git("worktree", "remove", "--force", str(path), write=True)
            print(f"  done    retired {path}; its files are in {dest}")
        except (RuntimeError, OSError) as e:
            print(f"  FAILED  {path}: {e}")


def main():
    global ROOT
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)  # `| head` ends the print quietly
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--repo", help="a path inside the repository (default: this tool's own repository)")
    ap.add_argument("--fetch", action="store_true")
    ap.add_argument("--no-fetch", action="store_true")
    ap.add_argument("--apply", action="store_true")
    ap.add_argument("--archive", nargs="+", metavar="BRANCH")
    ap.add_argument("--archive-idle", type=float, metavar="DAYS")
    ap.add_argument("--push-local", action="store_true", help="also push archive tags of branches that never left "
                                                             "this machine, after reading them")
    ap.add_argument("--retire", nargs="+", metavar="WORKTREE")
    ap.add_argument("--retire-idle", type=float, metavar="DAYS")
    ap.add_argument("--keep", nargs="+", default=[], metavar="NAME", help="worktrees (path or directory name) and "
                                                                          "branches the idle sweeps leave alone")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args()
    global DRY
    DRY = a.dry_run
    ROOT = find_root(a.repo or Path(__file__).resolve().parent)
    changing = a.apply or a.archive or a.archive_idle is not None or a.retire or a.retire_idle is not None
    S = census()
    if a.fetch or changing:
        if S["foreign"] or (S["shallow"] and changing):
            show(S)
            refuse_foreign(S)
        if not a.no_fetch and git("remote").strip():
            r = git("fetch", "--prune", "origin", check=False, write=True)
            if r.returncode and changing and not DRY:
                sys.exit(f"refused: the fetch failed, so the remote's branches are not known ({r.stderr.strip()}). "
                         f"Nothing was changed.")
            if r.returncode:
                print(f"fetch failed: {r.stderr.strip()}", file=sys.stderr)
            S = census()
    if not changing:
        show(S)
        return 1 if S["violations"] else 0
    now = time.time()
    if a.apply:
        print("APPLY")
        apply(S)
        S = census()
    if a.retire or a.retire_idle is not None:
        print("RETIRE")
        targets = []
        for key in a.retire or []:
            w = find_worktree(S, key)
            if w is None:
                print(f"  left    {key}: no such worktree")
            else:
                targets.append(w)
        if a.retire_idle is not None:
            targets += [w for w in S["wts"][1:] if not w["missing"] and w not in targets
                        and now - w["touch"] > a.retire_idle * DAY
                        and w["path"].name not in a.keep and str(w["path"]) not in a.keep]
        retire(S, targets)
        S = census()
    if a.archive or a.archive_idle is not None:
        print("ARCHIVE")
        names = list(a.archive or [])
        if a.archive_idle is not None:
            for name, b in S["branches"].items():
                tip_when = (b["local"] or b["remote"])[1]
                if "ahead" in b and not b["held"] and name not in names and name not in a.keep \
                        and now - tip_when > a.archive_idle * DAY:
                    names.append(name)
        archive(S, names, a.push_local)
        S = census()
    if DRY:
        print("\nDRY RUN: nothing was changed.")
        return 0
    print()
    show(S)
    return 1 if S["violations"] else 0


if __name__ == "__main__":
    sys.exit(main())
