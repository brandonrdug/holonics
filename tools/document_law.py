#!/usr/bin/env python3
"""Three laws the corpus states about its own governing documents, made executable.

    python3 tools/document_law.py            the failures
    python3 tools/document_law.py --all      also every absence claim that passes
    python3 tools/document_law.py --json     machine-readable

Exit status is 0 only when both laws hold.

LAW ONE — AN ABSENCE CLAIM CARRIES THE COMMAND THAT MEASURED IT, AND ITS DATE.

`canon/THE_OWNER_ATLAS.md` already states the discipline:

    A measured absence decays and carries its command. Every absence below is dated and states the
    command that measured it. Re-run it; do not cite it.

Ten files carry that motto and one file carries the practice. An audit on 2026-08-15 measured the
consequence: of the absence claims made about this repository across three sessions, **roughly one
in three was false**, and the population that survived into governing documents was not the loud
kind — it was the quiet kind, a name-grep or a dated census, *because both look like measurements*.

So the law is not "do not claim absence". Absence is a first-class finding here. The law is that a
claim of absence must be **re-runnable**: the paragraph carrying it names the command, and says
when. Then a later reader re-measures instead of inheriting.

**AND IT ONLY BINDS CLAIMS ABOUT THIS TREE.** The corpus is full of sentences that carry an absence
word and assert nothing about the repository — a theorem (*"an oriented loop enclosing nothing
returns zero"*), a normative rule (*"a receipt that could not have come out otherwise carries no
evidence"*), a statement about the conversation corpus, or an ontological position. Re-measuring
those is meaningless and demanding a command for them would push commands into prose that has
nothing to run.

The test is whether the paragraph names a **repository object**: a backticked path with a source
extension, or a backticked Rust identifier. A claim about a file or a construct is a claim this
tree can settle; a claim about mathematics is not. The first full run flagged 75 paragraphs and the
re-measurement found a large share of them to be exactly this kind, which is what motivated the
condition.

A claim passes when its SECTION — from the nearest preceding heading to the next — contains BOTH a
backticked command (a `grep`/`rg`/`find`/`ls`/`cargo`/`python3`/`git` invocation, or a `tools/`
script) AND an ISO date. It also passes if the paragraph marks the claim as already withdrawn,
struck, or corrected: a recorded correction is provenance, not a live claim.

**The section, not the paragraph, and that is a calibration rather than a loosening.** A reader who
meets an absence claim scans its section for what measured it; requiring both in the same paragraph
would force a command and a date into every sentence and make the documents worse to read. What the
law is protecting is re-runnability, and a command one paragraph up is re-runnable.

LAW TWO — ONE ROADMAP, AND EVERY OTHER PLAN STATES ITS SUBORDINATION TO IT.

`blueprint/THE_ROADMAP.md` opens *"This is the single active roadmap"*, and `CLAUDE.md` calls it
that too. On 2026-08-15 five of thirteen blueprints carried an active-plan declaration, three of
them added the same day.

**The law is not that the phrase may appear once.** A repository builds subordinate plans and should;
what a reader cannot survive is a plan that declares itself active without saying what it is active
*under*. So: `THE_ROADMAP.md` may declare itself the roadmap, and any other `blueprint/` document
declaring itself an active plan must name `THE_ROADMAP.md` in the same paragraph.

The first form of this check flagged `THE_PRESENTATION_ORGAN.md`, whose sentence reads *"It schedules
nothing. `blueprint/THE_ROADMAP.md` remains the single active roadmap"* — a document deferring
correctly, failed by a reader that matched the phrase and not the claim. Fixed by reading the
paragraph rather than the phrase.

A document escapes the law by carrying an archive or supersession banner, which is what a
superseded plan is supposed to carry.

WHAT IS SCANNED. The operating contract, the position record, all of `canon/`, all of `blueprint/`.
Not `research/records/` — a record is dated evidence whose absence claims are their own provenance,
the same boundary `resolve_named_paths.py` and `resolve_line_citations.py` draw.

LAW THREE — THE POSITION RECORD AND ROADMAP NAME ONE IDENTICAL SOLE NEXT DEED.

`CONSTRUCTION_STATE.md` is the sole current-position record and `THE_ROADMAP.md` is the sole ordered
construction authority. Each must contain exactly one explicit declaration of the form
`<PHASE> ... IS THE SOLE NEXT DEED`, and the phase identifiers must agree. No subordinate live
blueprint may contain that declaration. Historical evidence can say what was once next only after it
has been moved under an archive/supersession banner or rewritten without live scheduling language.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

SCANNED_FILES = ["CLAUDE.md", "CONSTRUCTION_STATE.md", "README.md"]
SCANNED_DIRS = ["canon", "blueprint"]

#: An assertion that something is not there. Deliberately narrow: these are the forms that read as
#: measurements. Softer prose ("we do not yet", "remains open") is a position, not a measurement.
ABSENCE = re.compile(
    r"\b(no owner|has no owner|zero owners|nothing implements|nothing reaches|"
    r"never (?:been )?(?:run|driven|called|invoked)|has never|"
    r"reaches nothing|is absent|are absent|appears nowhere|occurs nowhere|"
    r"does not exist|do not exist|is not built|is unbuilt|not implemented anywhere|"
    r"returns? zero|no live callers?|zero live callers?|no driver|zero drivers?)\b",
    re.IGNORECASE,
)

#: A command a later reader can re-run. `lake` is Lean's project/build apparatus in the same
#: exterior-command class as Cargo; omitting it falsely rejects a section that supplies `lake
#: build` and a date.
COMMAND = re.compile(
    r"`[^`]*\b(grep|rg|find|ls|wc|cargo|lake|python3|git|bash|tools/[a-z_]+\.(?:py|sh))\b[^`]*`"
)

DATE = re.compile(r"\b20\d\d-\d\d-\d\d\b")

#: A claim already marked as retired is provenance, not a live assertion.
RETIRED = re.compile(
    r"~~|\b(withdrawn|struck|superseded|CORRECTED|corrected in place|was false|stale|"
    r"no longer|retired|refuted)\b"
)

ACTIVE_PLAN = re.compile(
    r"\b(the (?:single )?active (?:construction )?(?:plan|roadmap)|"
    r"this is the active|the present deed)\b",
    re.IGNORECASE,
)

#: A repository object — a source path or a Rust identifier, in backticks. Its presence is what
#: makes an absence claim a claim about THIS TREE rather than about mathematics or conduct.
REPO_OBJECT = re.compile(
    r"`[^`]*\.(?:rs|cu|toml|py|sh|tsv|typ|lean|spv|ptx)\b[^`]*`"
    r"|`[a-z][a-z0-9]*_[a-z0-9_]*(?:\(\))?`"
    r"|`[A-Z][A-Za-z0-9]*(?:::[A-Za-z0-9_]+)+`"
)

BANNERED = re.compile(
    r"\*\*SUPERSEDED\b|\bARCHIVE BANNER\b|\*\*ARCHIVED\b|\bARCHIVED-BODY PROVENANCE\b"
)

CURRENT_FRONTIER = re.compile(
    r"^\*\*Current frontier:\*\*\s+(?P<phase>[A-Z][A-Z0-9]*(?:-[A-Z0-9]+)*)\s*$",
    re.MULTILINE,
)

SUBORDINATE_SCHEDULING = re.compile(
    r"\b(sole active|active\s+(?:corrective\s+)?construction\s+authority|"
    r"sole\s+(?:current\s+)?frontier|sole\s+next\s+deed|current\s+deed|next\s+deed)\b",
    re.IGNORECASE,
)

NON_SCHEDULING_STATUS = re.compile(
    r"\*\*Status:\*\*[^\n]*(PARKED|COMPLETED|SUPERSEDED|ARCHIVED)\b",
    re.IGNORECASE,
)


@dataclass
class Claim:
    document: str
    line: int
    text: str
    has_command: bool
    has_date: bool
    retired: bool

    @property
    def passes(self) -> bool:
        return self.retired or (self.has_command and self.has_date)


def scanned_documents() -> list[Path]:
    found = [ROOT / n for n in SCANNED_FILES if (ROOT / n).is_file()]
    for directory in SCANNED_DIRS:
        base = ROOT / directory
        if base.is_dir():
            found.extend(sorted(base.rglob("*.md")))
    return found


def sections(text: str) -> list[tuple[int, str, str]]:
    """(first line number, section text, ancestor headings), split on Markdown headings.

    A section is what a reader takes in around a claim: from the heading above it to the next
    heading. The command that measured an absence is very often a code block a paragraph away.
    A ratification date in a parent heading governs its nested subsections, while a command in a
    parent section does not discharge the child's measurement.
    """
    out: list[tuple[int, str, str]] = []
    start = 1
    buffer: list[str] = []
    ancestors: dict[int, str] = {}
    inherited = ""
    for number, line in enumerate(text.splitlines(), start=1):
        heading = re.match(r"^(#{1,6})\s", line)
        if heading and buffer:
            out.append((start, "\n".join(buffer), inherited))
            buffer = []
            start = number
        if heading:
            level = len(heading.group(1))
            ancestors = {depth: title for depth, title in ancestors.items() if depth < level}
            inherited = "\n".join(ancestors[depth] for depth in sorted(ancestors))
            ancestors[level] = line
        if not buffer:
            start = number
        buffer.append(line)
    if buffer:
        out.append((start, "\n".join(buffer), inherited))
    return out


def paragraphs(text: str) -> list[tuple[int, str]]:
    """(first line number, paragraph text), splitting on blank lines."""
    out: list[tuple[int, str]] = []
    start = 1
    buffer: list[str] = []
    for number, line in enumerate(text.splitlines(), start=1):
        if line.strip():
            if not buffer:
                start = number
            buffer.append(line)
        elif buffer:
            out.append((start, "\n".join(buffer)))
            buffer = []
    if buffer:
        out.append((start, "\n".join(buffer)))
    return out


def read() -> tuple[list[Claim], list[str], list[str]]:
    claims: list[Claim] = []
    active: list[str] = []
    subordinate_frontiers: list[str] = []

    for document in scanned_documents():
        body = document.read_text(errors="replace")
        relative = str(document.relative_to(ROOT))
        # A banner is a DECLARATION at the top. The first form of this test searched
        # 2000 chars case-insensitively and skipped THE_ROADMAP.md entirely, because its
        # twelfth line says "the eleven documents this roadmap superseded". The gate that
        # counts active plans was blind to the one document that is supposed to be active.
        if BANNERED.search(body[:800]):
            continue

        for section_start, section, ancestor_headings in sections(body):
            section_has_command = bool(COMMAND.search(section))
            section_has_date = bool(DATE.search(section) or DATE.search(ancestor_headings))
            for offset, block in paragraphs(section):
                if not ABSENCE.search(block):
                    continue
                if not REPO_OBJECT.search(block):
                    continue
                claims.append(
                    Claim(
                        document=relative,
                        line=section_start + offset - 1,
                        text=" ".join(block.split())[:150],
                        has_command=section_has_command,
                        has_date=section_has_date,
                        retired=bool(RETIRED.search(block)),
                    )
                )

        if relative.startswith("blueprint/") and relative != "blueprint/THE_ROADMAP.md":
            for _, block in paragraphs(body):
                if ACTIVE_PLAN.search(block) and "THE_ROADMAP" not in block:
                    active.append(relative)
                    break
            if (
                not NON_SCHEDULING_STATUS.search(body[:1000])
                and SUBORDINATE_SCHEDULING.search(body)
            ):
                subordinate_frontiers.append(relative)

    expected_frontiers: dict[str, list[str]] = {}
    for relative in ("CONSTRUCTION_STATE.md", "blueprint/THE_ROADMAP.md"):
        body = (ROOT / relative).read_text(errors="replace")
        expected_frontiers[relative] = [
            match.group("phase").upper() for match in CURRENT_FRONTIER.finditer(body)
        ]

    frontier_failures = list(subordinate_frontiers)
    state = expected_frontiers["CONSTRUCTION_STATE.md"]
    roadmap = expected_frontiers["blueprint/THE_ROADMAP.md"]
    if len(state) != 1:
        frontier_failures.append(
            f"CONSTRUCTION_STATE.md declares {len(state)} sole next deeds: {state}"
        )
    if len(roadmap) != 1:
        frontier_failures.append(
            f"blueprint/THE_ROADMAP.md declares {len(roadmap)} sole next deeds: {roadmap}"
        )
    if len(state) == 1 and len(roadmap) == 1 and state[0] != roadmap[0]:
        frontier_failures.append(
            f"position/roadmap frontier mismatch: {state[0]} != {roadmap[0]}"
        )

    return claims, active, frontier_failures


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="also list the claims that pass")
    parser.add_argument("--json", action="store_true", help="machine-readable")
    arguments = parser.parse_args()

    claims, active, frontier_failures = read()
    unmeasured = [c for c in claims if not c.passes]

    if arguments.json:
        print(
            json.dumps(
                {
                    "claims": [c.__dict__ for c in claims],
                    "active_plans": active,
                    "frontier_failures": frontier_failures,
                },
                indent=2,
            )
        )
        return 1 if unmeasured or active or frontier_failures else 0

    for claim in unmeasured:
        missing = ", ".join(
            part
            for part, present in (("command", claim.has_command), ("date", claim.has_date))
            if not present
        )
        print(f"UNMEASURED  {claim.document}:{claim.line}  (no {missing})  {claim.text}")

    if active:
        print()
        for name in active:
            print(
                f"ACTIVE-PLAN {name} declares itself an active plan without naming "
                "blueprint/THE_ROADMAP.md as what it is active under"
            )

    if frontier_failures:
        print()
        for failure in frontier_failures:
            if failure.startswith("blueprint/"):
                print(f"SUBORDINATE-FRONTIER {failure} declares a sole next deed")
            else:
                print(f"FRONTIER {failure}")

    if arguments.all:
        for claim in (c for c in claims if c.passes):
            mark = "retired" if claim.retired else "measured"
            print(f"OK ({mark})  {claim.document}:{claim.line}  {claim.text}")

    print(
        f"FAILURES (a governing document asserts an absence it cannot re-measure, or "
        f"a subordinate plan does not name the roadmap, or frontier declarations disagree): "
        f"{len(unmeasured) + len(active) + len(frontier_failures)}; "
        f"absence claims {len(claims)}: {len(claims) - len(unmeasured)} carry command and date, "
        f"{len(unmeasured)} do not; unsubordinated plans {len(active)}; "
        f"frontier failures {len(frontier_failures)}"
    )
    return 1 if unmeasured or active or frontier_failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
