#!/usr/bin/env python3
"""Every path a governing document names must resolve in the body that document describes.

This is the falsifier for the roadmap movement "The record names the body it has"
(`blueprint/THE_ROADMAP.md`, Part one). It is also the mechanical form of
`canon/THE_DOCUMENT_LAW.md` section 4: *"A link that does not resolve is a defect at the
same level as a wrong claim, because it produces the same outcome: a reader who cannot
check."*

    python3 tools/resolve_named_paths.py            summary and failures
    python3 tools/resolve_named_paths.py --all      also the archive-document notes
    python3 tools/resolve_named_paths.py --json     machine-readable

Exit status is 0 only when every live document resolves every path it names.

WHAT IS SCANNED. The two operating contracts, the position record, `README.md`, all of
`canon/`, and all of `blueprint/`. Not `research/records/` — a record is dated evidence
and is never edited except to add a supersession banner, so a stale path inside one is
its own provenance. Not `archive/` — it governs nothing.

FOUR WAYS A NAMED PATH RESOLVES.

  LIVE        it exists in the live tree, outside `archive/` and `reference/`
  PROVENANCE  the token itself begins with `archive/` or `reference/` — the reader is
              told where they are going — or it resolves under `reference/`, the
              provenance mirror, or in the frozen laboratory at `a07ff376`
  ARCHIVE     it resolves ONLY under `archive/` and the token does not say so. This is
              the movement's stated failure: a live document silently naming an owner
              of the archived body as though it were the present one
  MISSING     nowhere

A bare basename with no slash is resolved by searching the tree, because that is what a
reader does with it. A path with a slash is resolved against the repository root, then
against the naming document's own directory, then against the archive prefixes.

TWO CLASSES OF DOCUMENT, TWO RULES.

A document whose opening carries a SUPERSEDED or ARCHIVE banner is archived-body
provenance. Its prose is historical, so ARCHIVE is a correct resolution there and is not
rewritten. Only MISSING is reported, and as a note rather than a failure.

Every other document is live and its prose is present tense. ARCHIVE is then exactly the
movement's stated failure — *"any path that resolves only under `archive/` while its
surrounding prose is in the present tense fails this movement"* — and so is MISSING.

DECLARED ABSENCES. A live document may name a path in order to say it does not exist
(`canon/THE_DOCUMENT_LAW.md` section 1.11 does this deliberately, and reporting absence
is required conduct). Each such token is declared once in
`tools/resolve_named_paths.allow`, with its reason, so the exemption is auditable rather
than inferred from tone.
"""

from __future__ import annotations

import argparse
import functools
import json
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
ALLOWFILE = os.path.join(ROOT, "tools", "resolve_named_paths.allow")

LABORATORY = "/home/b/Workspaces/laboratory"
LABORATORY_COMMIT = "a07ff376"

SCANNED_DIRS = ("canon", "blueprint")

# Prefixes under which an archived C++ path is expected to resolve.
ARCHIVE_PREFIXES = (
    "archive/cpp-engine",
    "archive/cpp-engine/src",
    "archive/cpp-engine/src/include",
    "archive/cpp-engine/src/include/holonics",
    "archive/cpp-engine/tests",
    "archive/cpp-engine/evidence",
    "archive/cpp-engine/standing",
)

EXTENSIONS = (
    ".md", ".rs", ".hpp", ".cpp", ".cu", ".cuh", ".h", ".py", ".sh", ".toml",
    ".lock", ".cmake", ".txt", ".tsv", ".csv", ".json", ".lean", ".typ", ".pdf",
    ".spv", ".ptx", ".png", ".svg", ".card", ".yaml", ".yml", ".wav", ".bib",
)

PLACEHOLDER_MARKERS = ("<", ">", "*", "?", "$", "|", "YYYY", "MM-DD", "...", "…", "NN_", "-NN")

PLACEHOLDER_TOKENS = {
    "canon/NN_NAME.md",
    "canon/THE_NAME.md",
    "blueprint/THE_NAME.md",
    "blueprint/NAME.md",
    "research/records/YYYY-MM-DD_THE_SENTENCE.md",
}

BANNER_RE = re.compile(
    r"^>\s*\*\*(SUPERSEDED|ARCHIVE|ACTIVE SUPERSESSION)", re.MULTILINE | re.IGNORECASE
)

# The banner exempts a WHOLE DOCUMENT, so where it may appear has to be tight. Searching the
# leading 4000 characters made the exemption reachable by ordinary prose: a document that QUOTES an
# example banner switches its own checking off. A line window is not enough either — a quotation
# planted at line 9 is still inside any window wide enough for the real ones.
#
# So the test is structural: a document's own banner is FRONT MATTER, and nothing but front matter
# may precede it. Blank lines, the title, a horizontal rule, `**Key:** value` metadata, and the
# banner's own continuation lines are front matter. An ordinary prose paragraph is not, and a
# quoted example always has prose above it introducing the quotation.
BANNER_LINES = 12
FRONT_MATTER_RE = re.compile(r"^\s*(#{1,3}\s|>|---+\s*$|\*\*[^*]+\*\*\s*[:.]?)")


def is_archive_bannered(text: str) -> bool:
    """True when the document's OWN banner opens it, false for a banner it merely quotes."""
    for index, line in enumerate(text.splitlines()[:BANNER_LINES]):
        if BANNER_RE.match(line):
            return True
        if line.strip() and not FRONT_MATTER_RE.match(line):
            return False  # ordinary prose reached first: any banner below it is a quotation
        del index
    return False
TICK_RE = re.compile(r"`([^`\n]+)`")
LINK_RE = re.compile(r"\]\(([^)\s]+)\)")
BRACE_RE = re.compile(r"\{([^{}]*)\}")
TRAILING_RE = re.compile(r"(::[A-Za-z_][A-Za-z0-9_:]*|:\d+(-\d+)?|#L?\d+(-\d+)?)$")


# (the working-tree walk that needed a prune list is gone; `git ls-files --others
# --exclude-standard` does the same job with git's own ignore rules)


@functools.lru_cache(maxsize=None)
def is_ignored(rel: str) -> bool:
    """Does git ignore this path? An ignored artifact is not part of the body.

    `git check-ignore` exits 0 when the path IS ignored, 1 when it is not, and 128 on error;
    an error is read as not-ignored so a broken git never suppresses a resolution.
    """
    # `git check-ignore` refuses to descend through a symbolic link.  Release worktrees use an
    # `output -> <main-worktree>/output` link so an expensive, already-addressed deed can be
    # inspected without replay.  Without this lexical check the same commit consequently sees an
    # ignored runtime path as MISSING in the main tree and LIVE in the release worktree.  Anchored
    # ignored directory roots are repository policy, not a statement about the current inode kind;
    # honour them before asking git about the concrete path.  A tracked exception remains live
    # because Resolver._here checks the index before consulting this predicate.
    head = rel.strip("/").split("/", 1)[0]
    try:
        with open(os.path.join(ROOT, ".gitignore"), encoding="utf-8") as ignored:
            for line in ignored:
                match = re.fullmatch(r"/([A-Za-z0-9_.-]+)/", line.strip())
                if match and match.group(1) == head:
                    return True
    except OSError:
        pass

    return (
        subprocess.run(
            ["git", "-C", ROOT, "check-ignore", "-q", "--", rel],
            capture_output=True,
        ).returncode
        == 0
    )


def tracked_files() -> list[str]:
    """Every file a reader could find: git's index plus the untracked working tree.

    Both are needed. A file staged but not committed, or written this session and not
    yet added, still resolves for a reader — and a document that names it is correct.

    **Ignored files are not the body.** `--exclude-standard` is what makes the verdict a property
    of the commit rather than of the machine: `runs/`, `output/` and `target/` exist wherever a
    driver has been run and nowhere else, so counting them would make the same commit pass here and
    fail on a clean clone.
    """
    def git(*arguments: str) -> set[str]:
        out = subprocess.run(
            ["git", "-C", ROOT, *arguments], capture_output=True, text=True, check=True
        ).stdout
        return set(out.splitlines())

    return sorted(git("ls-files") | git("ls-files", "--others", "--exclude-standard"))


def laboratory_index() -> set[str]:
    try:
        out = subprocess.run(
            ["git", "-C", LABORATORY, "ls-tree", "-r", "--name-only", LABORATORY_COMMIT],
            capture_output=True, text=True, check=True,
        ).stdout
    except (subprocess.CalledProcessError, FileNotFoundError):
        return set()
    return set(out.splitlines())


def expand_braces(token: str) -> list[str]:
    m = BRACE_RE.search(token)
    if not m:
        return [token]
    if ".." in m.group(1):
        return []  # `formal_carry-0000{0..6}.lean` is a range pattern, not a path
    out: list[str] = []
    for part in m.group(1).split(","):
        part = part.strip()
        if not part:
            continue
        out.extend(expand_braces(token[: m.start()] + part + token[m.end():]))
    return out


def normalize(token: str) -> str | None:
    token = token.strip().strip("\"'").rstrip(",;:)]")
    if not token.endswith("/"):
        token = token.rstrip(".")
    while True:
        stripped = TRAILING_RE.sub("", token)
        if stripped == token:
            break
        token = stripped
    if token.startswith(ROOT + "/"):
        token = token[len(ROOT) + 1:]
    elif token == ROOT or token == ROOT + "/":
        return None
    if token.startswith("./"):
        token = token[2:]
    return token or None


_TOP_LEVEL: set[str] | None = None


def top_level_directories() -> set[str]:
    """Top-level directory names, live and inside each archive prefix.

    The archived roots matter: `src/` is not a directory of this body, but it is the root every
    archived C++ path is written against, and those are precisely the tokens a live document must
    not name in the present tense. Anchored gitignored roots matter for the complementary reason:
    `output/` and `target/` may be absent in a clean clone, but a document which names a runtime
    path below either root is still making a path claim. Reading those root names from `.gitignore`
    keeps this verdict independent of whether a local deed happened to materialize the directory.
    """
    global _TOP_LEVEL
    if _TOP_LEVEL is None:
        names: set[str] = set()
        for base in ("",) + ARCHIVE_PREFIXES:
            directory = os.path.join(ROOT, base) if base else ROOT
            try:
                entries = os.listdir(directory)
            except OSError:
                continue
            names.update(
                name for name in entries
                if not name.startswith(".")
                and os.path.isdir(os.path.join(directory, name))
            )
        try:
            with open(os.path.join(ROOT, ".gitignore"), encoding="utf-8") as ignored:
                for line in ignored:
                    match = re.fullmatch(r"/([A-Za-z0-9_.-]+)/", line.strip())
                    if match:
                        names.add(match.group(1))
        except OSError:
            pass
        _TOP_LEVEL = names
    return _TOP_LEVEL


def is_path_claim(token: str) -> bool:
    if any(marker in token for marker in PLACEHOLDER_MARKERS):
        return False
    if " " in token or "\t" in token:
        return False
    if token.startswith(("http://", "https://", "mailto:", "git@")):
        return False
    if token.startswith("/") and not token.startswith(ROOT):
        return False
    for ext in EXTENSIONS:
        # A bare extension is prose about a file kind: "282 `.rs` files", "`.card` files".
        if token == ext:
            return False
    # A trailing slash is a directory claim, at any depth. `formal/` is as checkable as
    # `soma/formal/` and was silently skipped until 2026-08-07, hiding three dead README links.
    if token.endswith(EXTENSIONS) or (token.endswith("/") and len(token) > 1):
        return True
    # A directory written WITHOUT its trailing slash — `src/include/holonics/event` — carried no
    # extension and no slash to end on, so it was skipped and the gate reported zero failures on a
    # planted dead path. The discriminator is the first segment: it must name a real top-level
    # directory, live or archived. That admits `research/records` and `soma/formal` while leaving
    # the mathematics alone, because `Z/p`, `dx/x`, `C/d`, `1/2` and `RIDE/FOUND` have no
    # first segment that is a directory in this repository.
    head = token.split("/", 1)[0]
    return "/" in token and head in top_level_directories()


def extract(text: str) -> list[str]:
    seen: dict[str, None] = {}
    for item in TICK_RE.findall(text) + LINK_RE.findall(text):
        for expanded in expand_braces(item):
            token = normalize(expanded)
            if token is None or token in PLACEHOLDER_TOKENS or not is_path_claim(token):
                continue
            seen.setdefault(token, None)
    return list(seen)


def is_archived_path(rel: str) -> bool:
    """Resolved under the archived C++ body — the class the movement targets."""
    return rel.startswith("archive/")


def is_provenance_path(rel: str) -> bool:
    """`reference/` is the provenance mirror of prior repository states (document law §1.10)."""
    return rel.startswith("reference/")


def names_its_own_provenance(token: str) -> bool:
    """The token itself says `archive/` or `reference/`, so no reader is misled."""
    return token.startswith("archive/") or token.startswith("reference/")


def classify(rel: str) -> str:
    if is_archived_path(rel):
        return "ARCHIVE"
    if is_provenance_path(rel):
        return "PROVENANCE"
    return "LIVE"


class Resolver:
    def __init__(self) -> None:
        self.tracked = set(tracked_files())
        self.dirs: set[str] = set()
        self.by_base: dict[str, list[str]] = {}
        for path in self.tracked:
            self.by_base.setdefault(os.path.basename(path), []).append(path)
            parent = os.path.dirname(path)
            while parent:
                self.dirs.add(parent)
                parent = os.path.dirname(parent)
        self.lab = laboratory_index()
        self.lab_dirs: set[str] = set()
        for path in self.lab:
            parent = os.path.dirname(path)
            while parent:
                self.lab_dirs.add(parent)
                parent = os.path.dirname(parent)

    def _here(self, rel: str) -> bool:
        rel = rel.rstrip("/")
        if rel in self.tracked or rel in self.dirs:
            return True
        # An untracked file in the working tree still resolves for a reader — but a GITIGNORED one
        # does not. `runs/`, `output/` and `target/` are driver artifacts: present on the machine
        # that ran a driver, absent on a clean clone of the same commit. Honouring them makes the
        # verdict depend on local state rather than on the body, which is the absolute-frame defect
        # this checker exists to catch. A document naming `runs/` to say it is GONE was being told
        # its own absence declaration was false, on one machine only.
        return os.path.exists(os.path.join(ROOT, rel)) and not is_ignored(rel)

    def _there(self, rel: str) -> bool:
        rel = rel.rstrip("/")
        return rel in self.lab or rel in self.lab_dirs

    def resolve(self, token: str, doc_dir: str) -> tuple[str, str | None]:
        # A token that names its own provenance misleads nobody. It still has to exist.
        declared = names_its_own_provenance(token)

        def verdict(rel: str) -> str:
            return "PROVENANCE" if declared else classify(rel)

        if token.endswith("/"):
            # A directory claim. Resolve it as a path even when it is one segment long:
            # `canon/` is a directory, not a basename, and `by_base` holds only filenames.
            bare = token.rstrip("/")
            if self._here(bare):
                return verdict(bare), bare
            ranked = sorted(
                (d for d in self.dirs if d == bare or d.endswith("/" + bare)),
                key=lambda d: (is_archived_path(d), is_provenance_path(d), d.count("/")),
            )
            if ranked:
                return verdict(ranked[0]), ranked[0]
            if bare in self.lab_dirs or any(
                d == bare or d.endswith("/" + bare) for d in self.lab_dirs
            ):
                return "PROVENANCE", f"{LABORATORY_COMMIT}:{bare}"
            return "MISSING", None

        if "/" not in token.rstrip("/"):
            matches = self.by_base.get(token.rstrip("/"), [])
            ranked = sorted(matches, key=lambda m: (is_archived_path(m), is_provenance_path(m)))
            if ranked:
                return verdict(ranked[0]), ranked[0]
            lab = [p for p in self.lab if os.path.basename(p) == token]
            if lab:
                return "PROVENANCE", f"{LABORATORY_COMMIT}:{lab[0]}"
            return "MISSING", None

        candidates = [token]
        if doc_dir:
            sibling = os.path.normpath(os.path.join(doc_dir, token))
            if not sibling.startswith(".."):
                candidates.append(sibling)
        candidates += [f"{prefix}/{token}" for prefix in ARCHIVE_PREFIXES]

        for candidate in candidates:
            if self._here(candidate):
                return verdict(candidate), candidate

        # A path written against another root — `life/src/x.rs` for `soma/life/src/x.rs`,
        # `holonic-engine/src/y.rs` for `crates/holonic-engine/src/y.rs`. A reader can
        # follow it, so it resolves; the suffix must break on a path separator.
        suffix = "/" + token.rstrip("/")
        hits = [p for p in self.tracked if p.endswith(suffix)]
        if not hits:
            hits = [d for d in self.dirs if d.endswith(suffix)]
        ranked = sorted(hits, key=lambda h: (is_archived_path(h), is_provenance_path(h)))
        if ranked:
            return verdict(ranked[0]), ranked[0]

        if self._there(token):
            return "PROVENANCE", f"{LABORATORY_COMMIT}:{token.rstrip('/')}"
        lab_hits = [p for p in self.lab if p.endswith(suffix)]
        if lab_hits:
            return "PROVENANCE", f"{LABORATORY_COMMIT}:{lab_hits[0]}"
        return "MISSING", None


def load_allow() -> dict[tuple[str, str], str]:
    allow: dict[tuple[str, str], str] = {}
    if not os.path.exists(ALLOWFILE):
        return allow
    with open(ALLOWFILE, encoding="utf-8") as fh:
        for line in fh:
            line = line.strip()
            if not line or line.startswith("#"):
                continue
            parts = [p.strip() for p in line.split("::")]
            if len(parts) < 2:
                continue
            reason = parts[2] if len(parts) > 2 else ""
            allow[(parts[0], parts[1])] = reason
    return allow


def scan_files() -> list[str]:
    docs = [n for n in sorted(os.listdir(ROOT)) if n.endswith(".md")]
    for sub in SCANNED_DIRS:
        base = os.path.join(ROOT, sub)
        if os.path.isdir(base):
            docs += [f"{sub}/{n}" for n in sorted(os.listdir(base)) if n.endswith(".md")]
    return docs


def main() -> int:
    ap = argparse.ArgumentParser(description="resolve every path the governing documents name")
    ap.add_argument("--all", action="store_true", help="also list archive-document notes")
    ap.add_argument("--json", action="store_true", help="machine-readable output")
    args = ap.parse_args()

    resolver = Resolver()
    allow = load_allow()
    failures: list[dict] = []
    notes: list[dict] = []
    contradicted: list[dict] = []
    used_allow: set[tuple[str, str]] = set()
    tallies = {
        "docs": 0, "archived_docs": 0, "tokens": 0,
        "live": 0, "provenance": 0, "archive": 0, "missing": 0, "declared_absent": 0,
    }

    for doc in scan_files():
        with open(os.path.join(ROOT, doc), encoding="utf-8") as fh:
            text = fh.read()
        archived = is_archive_bannered(text)
        tallies["docs"] += 1
        if archived:
            tallies["archived_docs"] += 1
        doc_dir = os.path.dirname(doc)
        for token in extract(text):
            tallies["tokens"] += 1
            verdict, where = resolver.resolve(token, doc_dir)
            tallies[verdict.lower()] += 1
            if (doc, token) in allow:
                used_allow.add((doc, token))
                # An allow entry CLAIMS the path does not resolve live. When it does, the entry is
                # simply false, and honouring it would suppress a check on a path that exists —
                # the allow file's own header says it "is NOT for stale references". ARCHIVE and
                # MISSING are the verdicts an absence declaration is FOR; LIVE contradicts it.
                if verdict == "LIVE":
                    contradicted.append({
                        "doc": doc, "token": token, "verdict": verdict, "resolved_at": where,
                        "reason": allow[(doc, token)],
                    })
                    continue
                tallies["declared_absent"] += 1
                continue
            entry = {"doc": doc, "token": token, "verdict": verdict, "resolved_at": where}
            if archived:
                if verdict == "MISSING":
                    notes.append(entry)
            elif verdict in ("ARCHIVE", "MISSING"):
                failures.append(entry)

    stale_allow = sorted(set(allow) - used_allow)

    # The allow file is the one place this checker can be talked out of a check, so its own
    # contract is enforced rather than described. An entry that no document names any more has
    # rotted; an entry whose path resolves LIVE was never an absence. Both used to print and
    # return zero, which made the file a silent off switch for exactly the checks that matter.
    refused = bool(failures) or bool(contradicted) or bool(stale_allow)

    if args.json:
        print(json.dumps({
            "tallies": tallies, "failures": failures, "notes": notes,
            "contradicted_allow": contradicted,
            "stale_allow": [{"doc": d, "token": t} for d, t in stale_allow],
        }, indent=2))
        return 1 if refused else 0

    print(f"scanned {tallies['docs']} documents ({tallies['archived_docs']} archive-bannered)")
    print(
        f"path tokens {tallies['tokens']}: {tallies['live']} live, "
        f"{tallies['provenance']} declared-provenance, {tallies['archive']} silently-archived, "
        f"{tallies['missing']} missing, {tallies['declared_absent']} declared-absent"
    )
    print(f"FAILURES (live document names a path that does not resolve in the live tree): {len(failures)}")
    for f in failures:
        at = f" -> {f['resolved_at']}" if f["resolved_at"] else ""
        print(f"  {f['verdict']:10} {f['doc']}: {f['token']}{at}")
    if args.all:
        print(f"NOTES (archive document, path resolves nowhere): {len(notes)}")
        for n in notes:
            print(f"  {n['verdict']:10} {n['doc']}: {n['token']}")
    else:
        print(f"notes (archive document, path resolves nowhere): {len(notes)}  [--all to list]")
    if contradicted:
        print(f"CONTRADICTED ALLOW ENTRIES (declared absent, resolves live): {len(contradicted)}")
        for c in contradicted:
            print(f"  {c['doc']}: {c['token']} -> {c['resolved_at']}")
    if stale_allow:
        print(f"STALE ALLOW ENTRIES (declared absent but no longer named): {len(stale_allow)}")
        for doc, token in stale_allow:
            print(f"  {doc}: {token}")
    return 1 if refused else 0


if __name__ == "__main__":
    sys.exit(main())
