#!/usr/bin/env python3
"""Check every quotation the repository attributes to Brandon against the session transcripts.

Occasioned 2026-08-08. A subagent deposited a research record whose `**Provenance:**` line carried
a direct quotation attributed to Brandon and dated to that day, requesting research into Wolfram
Mathematica. He never said it; the sentence occurs in no transcript of either project. It was
composed out of two things he *did* say — "reference Wolfram's MathWorld" and "refer to MorphoHDL
again" — and placed on the one line the operating contract reserves for his direct rulings.

That is the worst species of contamination this corpus admits, because CLAUDE.md section 10 makes
the provenance line govern: *"Distinguish his direct rulings from assistant interpretation in every
deposit. His corrections are provenance and they govern."* A fabricated ruling manufactures
authority, and no later reader re-checks it. So it gets a verifier, the way section 0 says every
deposit should have had one.

WHAT THIS CAN AND CANNOT SAY. CERTIFIED means the quotation occurs verbatim in a genuine user
message. UNCERTIFIABLE does NOT mean fabricated: transcripts rotate and are deleted, and most of
`canon/THE_QUOTE_NETWORK.md` predates every surviving one. Brandon appears to have ruled on that
condition himself --

    "I think that the historical record contains many things that I have never directly stated,
     but rather it is filled with interpretations you or Claude had made in the past from my
     analogies."

-- and note that THAT sentence is itself uncertifiable by this tool, which is the honest state to
report rather than to suppress. An uncertifiable quote from the laboratory era is expected and is
not a finding.

The claim this tool CAN adjudicate is narrow and decisive: a quotation deposited during a session
whose transcript survives, absent from that transcript, is fabricated. Run it before depositing
anything that quotes him.

KNOWN FALSE POSITIVE, since a check that overstates is the defect this tool exists to catch:
attribution is inferred from proximity -- a quotation counts as his if his name stands within 260
characters before it. A document quoting a SOURCE FILE's doc comment in a paragraph that also
mentions him therefore scores as an uncertifiable quote of his. The count over-reports and does not
under-report. Read it as an upper bound.
"""
import glob
import json
import re
import sys
from pathlib import Path

REPO = Path("/home/b/Workspaces/holonics")
# THE CORPUS. Corrected 2026-08-08 after a dialect survey measured what was actually here: the
# per-project Claude Code transcripts hold only ~298 genuine user messages, because Claude Code
# prunes them — the hundreds of megabytes in those directories are `tool-results/` and `subagents/`.
# An earlier form of this tool read only those and reported 130 quotations "uncertifiable", which
# was a property of the corpus and not of the quotations.
#
# The real corpus is 8,935 messages over 2026-05-11 → 2026-08-08:
#   ~/.claude/history.jsonl            7,895   one JSON object per line, text at `display`
#   ~/.codex/sessions/**/rollout-*     1,050   the Codex month; text at payload.content[].text
#   the surviving per-project transcripts, which are almost entirely subsumed
#
# The Codex rollouts are not optional. They are the densest month of the current project and are
# exactly what he means by "refer to the Codex conversation log"; without them the corpus has a
# three-week hole at maximum recency.
CLAUDE_HISTORY = "/home/b/.claude/history.jsonl"
CODEX_ROLLOUTS = "/home/b/.codex/sessions/**/rollout-*.jsonl"
TRANSCRIPTS = sorted(
    glob.glob("/home/b/.claude/projects/-home-b-Workspaces-holonics/*.jsonl")
    + glob.glob("/home/b/.claude/projects/-home-b-Workspaces-laboratory/*.jsonl")
)

MACHINE_PREFIXES = (
    "<task-notification",
    "<local-command",
    "<system-reminder",
    "[SYSTEM NOTIFICATION",
    "<environment_context",
    "<permissions instructions",
    "<user_instructions",
)


def _is_machine(text):
    """Machine-authored blocks. Including them would let the assistant certify its own words."""
    if text.lstrip().startswith(MACHINE_PREFIXES):
        return True
    return "This session is being continued from a previous conversation" in text[:300]


DOCS = ["CLAUDE.md", "CONSTRUCTION_STATE.md", "AGENTS.md"]
DIRS = ["canon", "blueprint", "research/records", "standing"]


def normalize(text):
    """Markdown wraps lines; transcripts do not. Compare on collapsed whitespace."""
    text = text.replace("’", "'").replace("‘", "'")
    text = text.replace("“", '"').replace("”", '"')
    text = text.replace("—", "--").replace("–", "-")
    text = re.sub(r"\*\*", "", text)
    return re.sub(r"\s+", " ", text).strip()


def load_user_text():
    """Every genuine message he wrote, from all three sources.

    Excludes task notifications, environment blocks and compaction summaries, which are
    machine-authored — including them would let the assistant's own words certify themselves.
    """
    blobs = []

    # 1. The Claude Code history: every prompt typed at the CLI, across every project.
    if Path(CLAUDE_HISTORY).exists():
        for line in open(CLAUDE_HISTORY, errors="replace"):
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            text = record.get("display") or ""
            if text and not _is_machine(text):
                blobs.append(normalize(text))

    # 2. The Codex rollouts: the densest month of this project.
    for path in glob.glob(CODEX_ROLLOUTS, recursive=True):
        for line in open(path, errors="replace"):
            if '"role": "user"' not in line and '"role":"user"' not in line:
                continue
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            payload = record.get("payload") or {}
            if payload.get("type") != "message" or payload.get("role") != "user":
                continue
            parts = payload.get("content") or []
            text = " ".join(
                part.get("text", "")
                for part in parts
                if isinstance(part, dict) and part.get("type") in ("input_text", "text")
            )
            if text and not _is_machine(text):
                blobs.append(normalize(text))

    # 3. The surviving per-project transcripts, mostly subsumed but cheap to include.
    for path in TRANSCRIPTS:
        for line in open(path, errors="replace"):
            try:
                record = json.loads(line)
            except json.JSONDecodeError:
                continue
            if record.get("type") != "user":
                continue
            content = record.get("message", {}).get("content")
            if isinstance(content, str):
                text = content
            elif isinstance(content, list):
                text = " ".join(
                    part.get("text", "")
                    for part in content
                    if isinstance(part, dict) and part.get("type") == "text"
                )
            else:
                continue
            if text and not _is_machine(text):
                blobs.append(normalize(text))

    return blobs


# `*"..."*`, `> *"..."*`, and bare `"..."` runs long enough to be a quotation rather than a term.
QUOTE_PATTERNS = [
    re.compile(r'\*"(.+?)"\*', re.S),
    re.compile(r'\*“(.+?)”\*', re.S),
    re.compile(r'^>\s*\*?["“](.+?)["”]\*?\s*$', re.M | re.S),
]

MIN_FRAGMENT = 32


def fragments(quote):
    """A quotation may elide with ... or …; each surviving run is checked on its own.

    Blockquote markers and emphasis are the document's, not his: a multi-line `> *"..."*` carries
    a `>` at every continuation line, and `**bold**` is the depositor's stress. Both must come off
    BEFORE the whitespace collapse, or every wrapped quote reads as absent.
    """
    quote = re.sub(r"(?m)^\s*>\s?", " ", quote)
    quote = quote.replace("**", "").replace("`", "")
    quote = normalize(quote)
    parts = re.split(r"…|\.\.\.|\[[^\]]*\]", quote)
    return [p.strip(" ,;:-—\"'") for p in parts if len(p.strip()) >= MIN_FRAGMENT]


def main():
    corpus = load_user_text()
    if not corpus:
        print("NO TRANSCRIPTS READABLE — cannot certify anything", file=sys.stderr)
        return 2
    print(f"corpus: {len(corpus)} genuine user messages from {len(TRANSCRIPTS)} transcripts\n")

    files = [REPO / d for d in DOCS if (REPO / d).exists()]
    for directory in DIRS:
        files.extend(sorted((REPO / directory).rglob("*.md")))

    found = absent = 0
    absent_rows = []
    for path in files:
        text = path.read_text(errors="replace")
        # THE_QUOTE_NETWORK is entirely his words by construction; elsewhere a quote counts as
        # attributed only if his name, or a provenance/ruling marker, stands close before it.
        whole_file_is_his = path.name == "THE_QUOTE_NETWORK.md"
        seen = set()
        for pattern in QUOTE_PATTERNS:
            for match in pattern.finditer(text):
                quote = match.group(1)
                if not whole_file_is_his:
                    lead = text[max(0, match.start() - 260) : match.start()]
                    if not re.search(r"Brandon|his own words|direct ruling|\*\*Provenance", lead):
                        continue
                key = normalize(quote)[:120]
                if key in seen:
                    continue
                seen.add(key)
                pieces = fragments(quote)
                if not pieces:
                    continue
                missing = [p for p in pieces if not any(p in blob for blob in corpus)]
                if missing:
                    absent += 1
                    absent_rows.append((path.relative_to(REPO), normalize(quote)[:300], missing))
                else:
                    found += 1

    for rel, quote, missing in absent_rows:
        print(f"ABSENT  {rel}")
        print(f"        quote:   {quote}")
        for piece in missing[:2]:
            print(f"        missing: {piece[:200]}")
        print()

    print(f"\ncertified against a genuine user message: {found}")
    print(f"not found in any transcript:               {absent}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
