#!/usr/bin/env python3
"""Generate `THE_CLAIM_INDEX.md` from the tree, so the table of contents cannot drift.

    python3 tools/claim_index.py            # rewrite THE_CLAIM_INDEX.md
    python3 tools/claim_index.py --check    # exit 1 if the file disagrees with the tree

# Why this exists, and it is a defect in the file it generates

`THE_CLAIM_INDEX.md` was deposited 2026-08-10 carrying, in its own bounds section, *"Generated
2026-08-10 by scanning canon/, blueprint/, the repository root, research/records/ and tools/"* and
*"Regenerate rather than edit; a hand-edited index drifts from the tree, which is the defect this
file exists to prevent."*

**No generator was committed.** The file was produced by a one-off shell pipeline that is gone. That
is precisely the shape `CLAUDE.md` §0 lesson 1 convicts and that `tools/closure_manifest.py` exists
to detect: a return whose producer is not in the tree. An index claiming to be regenerable, with
nothing able to regenerate it, is an orphan wearing a provenance line.

# The extraction, and why the first one was wrong

The lost pipeline took *"each file's own first descriptive line"*, which on a hard-wrapped corpus is
a **continuation line**. Twenty of forty document rows began mid-sentence — `canon/THE_MILLENNIUM_FRAME.md`
was described as *"any Millennium problem**, and no deed may be graded by resemblance to one."*

Two fields are taken instead, both of which the document law already guarantees exist:

- **subject** — the `# ` title. `canon/THE_DOCUMENT_LAW.md` requires a declarative title, so for most
  files the title *is* the claim and needs no summarizing.
- **gloss** — the first complete sentence of the document's **preamble**, meaning what stands before
  its first `## ` heading. Preamble is preferred because a paragraph inside the body is a *section's*
  opening claim, not the file's. Headings, blockquotes, tables, lists, fences and horizontal rules
  are skipped; so are metadata blocks (`**Truth status:**`, `**Genre:**`, `**Provenance**`), except
  that where a preamble is *entirely* metadata the sentence following the key's own value is taken —
  `**Genre:** canon (…). It states the spine the roadmap is ordered by.` A body paragraph is the last
  resort. Paragraphs are joined across wrapped lines before the sentence is cut, which is the step
  the lost pipeline did not have; and a sentence boundary landing inside an open `**` or backtick
  span is skipped, so no gloss begins or ends mid-emphasis.

Nothing is summarized. Every string in the output is copied from the file it describes. The one
thing removed is a link **target**: a relative link copied out of `canon/` or `blueprint/` resolves
nowhere from the repository root, so the link text is kept and the address dropped —
`tools/resolve_named_paths.py` caught that on the first run.

# The gate column is measured, not declared

§5 lists each verifier under `tools/` and reports whether anything invokes it, by searching the tree
outside `tools/` and outside the generated index. A verifier nobody invokes detects nothing, and
that column is the measurement rather than an assertion. **It measures naming, not execution** — a
document that discusses a verifier in prose counts the same as a script that runs it, and §6 of the
generated file says so.
"""

from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
INDEX = ROOT / "THE_CLAIM_INDEX.md"

# A paragraph opening with one of these is a metadata block, not a description.
METADATA = re.compile(
    r"^\*\*(genre|truth status|date|deposited|evidence|provenance|ratified|currency|status|"
    r"superseded|occasion|source|read this|supersedes|withdrawn|corrected)\b",
    re.IGNORECASE,
)
# A block, a quote, a table or a list is structure rather than description. `*` alone is NOT a list
# marker — `**bold**` opens most of this corpus's descriptive paragraphs, and treating the bare
# asterisk as structure is what skipped `CONSTRUCTION_STATE.md`'s own one-line self-description.
STRUCTURAL = ("#", ">", "|", "```")
LIST_MARKER = re.compile(r"^([-*+]\s|\d+[.)]\s|\[)")
RULE = re.compile(r"^([-*_])\1{2,}$")
GLOSS_LIMIT = 190

# The governing spine, in `CLAUDE.md` §0's reading order. Order is authority here, so it is declared
# rather than sorted: an alphabetical pickup order would be a different claim.
SPINE = [
    "CLAUDE.md",
    "canon/THE_HOLOBROCHOS_SPINE.md",
    "canon/THE_DOCUMENT_LAW.md",
    "canon/THE_DIALECT.md",
    "canon/THE_QUOTE_NETWORK.md",
    "canon/THE_EXPLORATIVE_FAILURE.md",
    "canon/THE_MEASURED_CAPABILITIES.md",
    # Inserted 2026-08-13. It was added to CLAUDE.md's pickup table the same day and omitted here,
    # and `--check` could not catch it: the check compares the index against this list, never this
    # list against CLAUDE.md. A generator that declares itself a copy of another file's order and is
    # never compared to it is exactly the receipt-versus-implementation gap the contract convicts.
    "canon/THE_TIMELINE.md",
    "blueprint/THE_ROADMAP.md",
    "CONSTRUCTION_STATE.md",
    "THE_CLAIM_INDEX.md",
    "canon/THE_CORRESPONDENCE_ATLAS.md",
    "canon/THE_MILLENNIUM_FRAME.md",
    "canon/TABLET_THE_MANIFOLD.md",
]


def paragraphs(text: str) -> list[list[str]]:
    """Maximal runs of non-blank lines."""
    blocks: list[list[str]] = []
    current: list[str] = []
    for line in text.splitlines():
        if line.strip():
            current.append(line.rstrip())
        elif current:
            blocks.append(current)
            current = []
    if current:
        blocks.append(current)
    return blocks


def delink(fragment: str) -> str:
    """Strip markdown link targets, keeping the link text.

    A gloss is copied out of a file in `canon/` or `blueprint/`, so any relative link inside it is
    written from *that* directory and resolves nowhere from the repository root. Keeping the target
    would make this file name a path that does not exist — `tools/resolve_named_paths.py` caught
    exactly that on the first run. The words are copied; the broken address is not.
    """
    return re.sub(r"\[([^\]]+)\]\([^)]*\)", r"\1", fragment)


def balance(fragment: str) -> str:
    """Remove an unmatched emphasis marker so a cut sentence cannot unbalance the table cell.

    The marker is deleted, never the text after it. Truncating at the marker instead is what
    reduced `CONSTRUCTION_STATE.md`'s description to the empty string on the first attempt: its
    opening sentence ends *inside* a bold span, so cutting there left one `**` and no content.
    """
    for marker in ("**", "`"):
        if fragment.count(marker) % 2:
            index = fragment.rfind(marker)
            fragment = fragment[:index] + fragment[index + len(marker) :]
    return delink(fragment).strip().replace("|", "\\|")


def closed(prefix: str) -> bool:
    """True when every emphasis span opened in `prefix` is also closed there."""
    return prefix.count("**") % 2 == 0 and prefix.count("`") % 2 == 0


def first_sentence(joined: str) -> str:
    """The first complete sentence, cut at a word boundary if it runs past the limit.

    A sentence ends at `.`, `?` or `!` followed by whitespace and a capital, a backtick or a bold
    marker — never after a digit (`4.27`, `§1.1`) or a single initial. A boundary landing **inside**
    an open emphasis span is not a top-level boundary and is skipped, so a gloss never begins or
    ends mid-emphasis.
    """
    sentence = joined
    for match in re.finditer(r"(?<![0-9A-Z])[.?!](?=\s+(?:[A-Z`*\[]|$))", joined):
        if closed(joined[: match.end()]):
            sentence = joined[: match.end()]
            break
    if len(sentence) > GLOSS_LIMIT:
        sentence = sentence[:GLOSS_LIMIT].rsplit(" ", 1)[0] + "…"
    return balance(sentence.strip())


def after_metadata_key(joined: str) -> str:
    """Drop a leading `**Key:** value.` clause, keeping the sentence that follows it.

    `canon/THE_DOCUMENT_LAW.md` puts the genre on the first line, and several files put their only
    self-description in the *second* sentence of that same paragraph — `**Genre:** canon (…). It
    states the spine the roadmap is ordered by.` The description is there; it is just behind a key.
    """
    match = re.match(r"^\*\*[^*]+:\*\*\s*", joined)
    if not match:
        return ""
    rest = joined[match.end() :]
    # Drop the key's own value clause — the first top-level sentence — and keep what follows it.
    for boundary in re.finditer(r"(?<![0-9A-Z])[.?!](?=\s+(?:[A-Z`*\[]|$))", rest):
        if closed(rest[: boundary.end()]):
            return rest[boundary.end() :].strip()
    return ""


def describe(path: Path) -> tuple[str, str]:
    """(title, gloss) — both copied from the file, neither summarized.

    A document's self-description lives in its **preamble**: what stands before the first `## `
    heading. That is preferred over anything later, because the first qualifying paragraph inside
    the body is a section's opening claim rather than the file's.
    """
    text = path.read_text(errors="replace")
    title = ""
    preamble: list[str] = []
    body: list[str] = []
    metadata: list[str] = []
    in_preamble = True
    fenced = False

    for block in paragraphs(text):
        head = block[0].lstrip()
        if head.startswith("```"):
            fenced = not fenced
            continue
        if fenced:
            continue
        if head.startswith("# ") and not title:
            title = head[2:].strip()
            continue
        if head.startswith("## "):
            in_preamble = False
            continue
        if head.startswith(STRUCTURAL) or LIST_MARKER.match(head) or RULE.match(head):
            continue
        joined = " ".join(line.strip() for line in block)
        if METADATA.match(head):
            if in_preamble:
                trailing = after_metadata_key(joined)
                if trailing:
                    metadata.append(trailing)
            continue
        (preamble if in_preamble else body).append(joined)

    for source in (preamble, metadata, body):
        if source:
            return title or path.name, first_sentence(source[0])
    return title or path.name, ""


def title_only(path: Path) -> str:
    for line in path.read_text(errors="replace").splitlines():
        if line.startswith("# "):
            return balance(line[2:].strip())
    return path.stem


def row(relative: str) -> str:
    path = ROOT / relative
    if not path.is_file():
        return f"| `{relative}` | **MISSING FROM THE TREE** |\n"
    title, gloss = describe(path)
    body = f"**{balance(title)}** — {gloss}" if gloss else f"**{balance(title)}**"
    return f"| `{relative}` | {body} |\n"


def directory_rows(directory: str, skip: set[str]) -> str:
    out = ""
    for path in sorted((ROOT / directory).glob("*.md")):
        relative = f"{directory}/{path.name}"
        if relative in skip:
            continue
        out += row(relative)
    return out


def gate_users(tool: str) -> list[str]:
    """Every tracked file outside `tools/` that names this verifier."""
    try:
        found = subprocess.run(
            ["git", "grep", "-l", "--", tool],
            cwd=ROOT,
            capture_output=True,
            text=True,
            check=False,
        ).stdout.split()
    except OSError:
        return []
    return sorted(
        name
        for name in found
        if not name.startswith("tools/") and name != "THE_CLAIM_INDEX.md"
    )


def verifier_rows() -> str:
    out = ""
    for path in sorted((ROOT / "tools").iterdir()):
        if path.suffix not in {".py", ".sh"} or path.name.startswith("_"):
            continue
        first = ""
        for line in path.read_text(errors="replace").splitlines():
            stripped = line.strip().lstrip("#").strip()
            if stripped.startswith('"""'):
                stripped = stripped.strip('"').strip()
            if not stripped or stripped.startswith(("!", "-*-", "set -")):
                continue
            first = stripped
            break
        users = gate_users(f"tools/{path.name}")
        shown = ", ".join(f"`{name}`" for name in users[:3])
        if len(users) > 3:
            shown += f", and {len(users) - 3} more"
        named = shown if users else "**nothing names it**"
        out += f"| `tools/{path.name}` | {balance(first_sentence(first))} | {named} |\n"
    return out


def record_rows() -> tuple[str, int]:
    records = sorted((ROOT / "research" / "records").glob("2026-08-*.md"))
    out = ""
    for path in records:
        out += f"| `{path.name}` | {title_only(path)} |\n"
    return out, len(records)


def render() -> str:
    records, record_count = record_rows()
    total = len(list((ROOT / "research" / "records").glob("*.md")))
    canon_skip: set[str] = set()
    blueprint_skip = {"blueprint/THE_ROADMAP.md"}

    return f"""# The claim index

**Truth status:** `index` — this file asserts nothing. It routes. `canon/THE_DOCUMENT_LAW.md` §1
names this genre. **Generated by `tools/claim_index.py`; run it rather than editing this file.**

**What it is for.** Four partial indexes existed and none knew about the others: `CLAUDE.md` §0's
pickup order, `THE_MATHEMATICS_TABLET` §3's tablet list, `research/README.md` (records only), and
`papers/source/holonics/registry.typ` (mathematical objects by id). **Nothing indexed across
genres**, so the corpus could be entered by filename or by code symbol and by nothing else — which
is how three false absences were deposited on 2026-08-10 alone.

**How to use it.** Enter by concept through `canon/THE_CORRESPONDENCE_ATLAS.md` (168 cards, what
other fields call the same face). Enter by mathematical object through
`papers/source/holonics/registry.typ`. Enter by document through this file. Enter by date through
`research/README.md`.

**Grade nothing from this file.** Every claim belongs to the document it points at and is graded
there. Every description below is **copied** from the file it describes — its title, and the first
complete sentence of its first non-metadata paragraph. Nothing here is summarized.

---

## 1 · The governing documents, in reading order

`CLAUDE.md` §0's pickup order. The order is the authority; it is declared here rather than sorted.

| file | what it is |
|---|---|
{"".join(row(name) for name in SPINE)}
---

## 2 · Canon

| file | what it is |
|---|---|
{directory_rows("canon", canon_skip)}
---

## 3 · Blueprint and position

`blueprint/THE_ROADMAP.md` is in §1 and is the only file that says what is open.

| file | what it is |
|---|---|
{directory_rows("blueprint", blueprint_skip)}
---

## 4 · The 2026-08 record line ({record_count} deposits of {total})

Each row is the record's own title, which under `canon/THE_DOCUMENT_LAW.md` is a declarative
sentence — so this table is the month's claims, not a file listing. Full chronological atlas:
`research/README.md`.

| record | the claim in its title |
|---|---|
{records}
---

## 5 · Verifiers, and which of them are invoked

**A verifier nobody invokes detects nothing.** The last column is measured — every tracked file
outside `tools/` that names the verifier — not declared.

| tool | what it checks | invoked by |
|---|---|---|
{verifier_rows()}
`cargo test --workspace` is the gate that is actually run alongside these.

---

## 6 · Bounds

- Generated by `tools/claim_index.py` over `canon/`, `blueprint/`, `research/records/`, `tools/` and
  the files `CLAUDE.md` §0 names. **Run the tool rather than editing this file.**
- A gloss is the first sentence of the first non-metadata paragraph. Where a document opens on a
  measurement rather than a description, that is what appears — the tool does not write prose.
- The `invoked by` column measures **naming**, not execution. A file that names a verifier in prose
  counts the same as a script that runs it; read the cited file to tell which.
- This file routes and asserts nothing.
"""


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate THE_CLAIM_INDEX.md from the tree.")
    parser.add_argument("--check", action="store_true", help="exit 1 if the index is stale")
    arguments = parser.parse_args()

    rendered = render()

    if arguments.check:
        if not INDEX.is_file():
            print("missing THE_CLAIM_INDEX.md; run without --check to write it")
            return 1
        if INDEX.read_text() != rendered:
            print("THE_CLAIM_INDEX.md disagrees with the tree; run tools/claim_index.py")
            return 1
        print("claim index current")
        return 0

    INDEX.write_text(rendered)
    print(f"wrote {INDEX.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
