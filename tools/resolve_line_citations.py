#!/usr/bin/env python3
"""Every `file.rs:NNN` a governing document names must still point at the construct it claims.

`tools/resolve_named_paths.py` verifies the path. Nothing verified the number on the end of it, and
`CLAUDE.md` says in its own text why that matters:

    A line number is the most perishable thing a document can carry: it is invalidated by any edit
    above it, and this one has now been wrong twice in four days. Cite the construct, and let the
    line be a hint.

Written after an audit on 2026-08-15 found 265 such citations across the operating contract, `canon/`
and `blueprint/` with no verifier of any kind, and `analytic_field.rs:1142` stale in three governing
documents while a research record deposited the same day already cited `:1359-1379` correctly. The
correction had been made and never propagated, which is the exact failure a gate exists to stop.

    python3 tools/resolve_line_citations.py           summary and failures
    python3 tools/resolve_line_citations.py --all     also the citations that carry no anchor
    python3 tools/resolve_line_citations.py --json    machine-readable

Exit status is 0 only when no citation is DRIFTED, ABSENT or PAST_EOF.

WHAT IS SCANNED. The operating contract, the position record, all of `canon/`, all of `blueprint/`.
Not `research/records/` — a record is dated evidence and a stale line inside one is its own
provenance, the same rule `resolve_named_paths.py` applies. Not `archive/`, which governs nothing.

HOW A CITATION IS CHECKED. A citation is only checkable if the document says WHAT it is pointing at.
So the reader looks on the citation's own line for a backticked Rust identifier — `positive_form`,
`ExactRatMatrix`, `fn without_stem` — and asks whether that identifier occurs at the cited line.

  OK          the anchor occurs on the cited line, or inside the cited range
  NEAR        the anchor occurs within the declared window of the cited line
  DRIFTED     the anchor occurs in the file, but outside the window — the true line is reported
  ABSENT      the anchor occurs nowhere in the file
  PAST_EOF    the file is shorter than the cited line
  UNANCHORED  the document names no identifier on that line, so only existence can be checked
  UNRESOLVED  the path does not resolve; `resolve_named_paths.py` owns that failure, not this one
  AMBIGUOUS   a bare basename matching several live files, so no verdict is founded

THE WINDOW IS A DECLARED APERTURE, not a tolerance. A document may cite the line a construct's doc
comment opens on rather than its `pub fn`, and that is a correct citation of the same construct. The
window is the largest such gap this reader will call the same construct; `NEAR` is reported so the
population is visible rather than silently accepted, and it does not fail the gate. What would
derive it from the material is the distance from each `pub fn`/`pub struct` to the top of its own
doc comment; until that is measured the window is declared here and nowhere else.

WHY `UNANCHORED` DOES NOT FAIL. A bare `file.rs:NNN` with no identifier beside it is weaker
citation practice, but it is not a false statement, and a gate that failed on it would convert a
style preference into a build break. The count is reported so the practice is visible.
"""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

#: The declared window. See the module docstring — an aperture, stated once, nowhere else.
WINDOW = 12

SCANNED_FILES = ["CLAUDE.md", "AGENTS.md", "CONSTRUCTION_STATE.md", "README.md", "THE_CLAIM_INDEX.md"]
SCANNED_DIRS = ["canon", "blueprint"]

#: `path.rs:120` and `path.rs:120-140`. The path may be repository-relative or a bare basename.
CITATION = re.compile(r"(?P<path>[A-Za-z0-9_./-]+\.rs):(?P<line>\d+)(?:-(?P<end>\d+))?")

#: A backticked token. The anchor is drawn only from these — prose words are not identifiers.
BACKTICKED = re.compile(r"`([^`]+)`")

#: What counts as a Rust identifier worth anchoring on: snake_case with an underscore, or CamelCase.
#: The length floor kills mathematical subscripts written in backticks — `n_v`, `a_i`, `d_k` — which
#: match snake_case and are not constructs. Five is the shortest real identifier in this corpus's
#: public surface; below it the reader was anchoring on notation.
SNAKE = re.compile(r"^[a-z][a-z0-9_]*_[a-z0-9_]*$")
CAMEL = re.compile(r"^[A-Z][A-Za-z0-9]*[a-z][A-Za-z0-9]*$")
MINIMUM_ANCHOR = 5

#: A span that is a shell command is a record of a past measurement, not a claim about a construct.
#: `THE_ROADMAP.md` carries grep alternations whose terms would otherwise be read as anchors.
COMMANDLIKE = re.compile(r"\b(grep|rg|find|ls|wc|cargo|python3|git|bash)\b|--include|\s-[a-zA-Z]")


@dataclass
class Citation:
    document: str
    document_line: int
    path: str
    line: int
    end: int | None
    anchors: list[str]
    verdict: str = ""
    detail: str = ""


@dataclass
class Reading:
    citations: list[Citation] = field(default_factory=list)

    def by_verdict(self, *verdicts: str) -> list[Citation]:
        return [c for c in self.citations if c.verdict in verdicts]


def scanned_documents() -> list[Path]:
    found: list[Path] = []
    for name in SCANNED_FILES:
        path = ROOT / name
        if path.is_file():
            found.append(path)
    for directory in SCANNED_DIRS:
        base = ROOT / directory
        if base.is_dir():
            found.extend(sorted(base.rglob("*.md")))
    return found


#: A banner is a DECLARATION at the top, in caps. Matching the word anywhere in the first 2000
#: characters skips `THE_ROADMAP.md`, whose twelfth line reads "the eleven documents this roadmap
#: superseded" — so the reader would exempt the live roadmap from its own gate.
BANNERED = re.compile(
    r"\*\*SUPERSEDED\b|\bARCHIVE BANNER\b|\*\*ARCHIVED\b|\bARCHIVED-BODY PROVENANCE\b"
)


def is_archived(document: Path) -> bool:
    """A document opening with an archive or supersession banner is provenance, not law."""
    return bool(BANNERED.search(document.read_text(errors="replace")[:800]))


def resolve(token: str) -> Path | None | str:
    """Repository-relative first, then by basename — which is what a reader does with it.

    Returns the string `"AMBIGUOUS"` when a bare basename matches more than one live file. `lib.rs`
    is the standing case: it matches every crate root, so picking the first is an authored choice
    the reader has no basis for, and a verdict founded on it would be about the wrong file.
    """
    direct = ROOT / token
    if direct.is_file():
        return direct
    # A crate-relative token — `relational-geometry/src/model.rs` — is how these documents commonly
    # write a path. Try it under the two workspace roots before falling back to a basename search,
    # which would otherwise resolve it to an unrelated file of the same name.
    for prefix in ("crates", "soma"):
        under = ROOT / prefix / token
        if under.is_file():
            return under
    name = Path(token).name
    matches: list[Path] = []
    for candidate in ROOT.rglob(name):
        parts = candidate.relative_to(ROOT).parts
        if parts and parts[0] in {"archive", "reference", "target", ".git"}:
            continue
        if candidate.is_file():
            matches.append(candidate)
    if len(matches) > 1 and "/" not in token:
        return "AMBIGUOUS"
    return matches[0] if matches else None


def anchors_on(text: str, citation_span: tuple[int, int]) -> list[str]:
    """Backticked Rust identifiers belonging to THIS citation.

    Anchors are drawn from the backtick span that contains the citation, or failing that from the
    single nearest span. **Not from every span on the line** — the first form of this reader took
    all of them, so a line carrying two citations cross-assigned their anchors and reported both as
    ABSENT. That is a scope error in the instrument of exactly the kind this gate exists to catch,
    and it was caught by reading its own first output rather than by trusting the count.
    """
    spans = [(m.start(), m.end(), m.group(1)) for m in BACKTICKED.finditer(text)]
    if not spans:
        return []
    # Stems of every OTHER `.rs` path on the line. A list item naming three files would otherwise
    # lend its neighbour's filename as an anchor, and the reader would ask whether `leader_quadrature`
    # appears inside `contact_gluing.rs`. It is a filename, not a construct at that citation.
    other_stems = {
        Path(m.group("path")).stem
        for m in CITATION.finditer(text)
        if (m.start(), m.end()) != citation_span
    }
    other_stems |= {Path(m).stem for m in re.findall(r"`([A-Za-z0-9_./-]+\.rs)`", text)}

    def identifiers(raw: str) -> list[str]:
        if COMMANDLIKE.search(raw):
            return []
        out: list[str] = []
        token = CITATION.sub("", raw).strip(" `:")
        # `Type::method` — the document names the type and cites the METHOD's line, which is the
        # correct citation and the reader must not fail it for the type sitting at its `impl`. A
        # plain lowercase segment is admitted only in this form, where the `::` says it is a path
        # into a type and not an English word in backticks.
        if "::" in token:
            for segment in token.split("::"):
                segment = segment.strip()
                if (
                    len(segment) >= MINIMUM_ANCHOR
                    and segment not in out
                    and segment not in other_stems
                    and re.fullmatch(r"[a-z][a-z0-9_]*", segment)
                ):
                    out.append(segment)
        for piece in re.split(r"[^A-Za-z0-9_]+", token):
            if not piece or piece in out or piece in other_stems:
                continue
            if len(piece) < MINIMUM_ANCHOR:
                continue
            if SNAKE.match(piece) or CAMEL.match(piece):
                out.append(piece)
        return out

    containing = [s for s in spans if s[0] <= citation_span[0] and s[1] >= citation_span[1]]
    found: list[str] = []
    for _, _, raw in containing:
        found.extend(i for i in identifiers(raw) if i not in found)
    if found:
        return found

    # The citation sits alone in its own backticks — the common form in this corpus, where the
    # construct is named in the span beside it. Take the NEAREST other span, one only, so a line
    # carrying two citations still cannot cross-assign.
    #
    # **And the span must be in the same clause.** A sentence boundary or a table-cell pipe between
    # the two means the neighbour is talking about something else, which produced four false ABSENT
    # verdicts on the first full run — a doc saying "…already `ExposedPolarity`. Mass is … and
    # `arrow.rs:18`" had the reader asking whether `ExposedPolarity` lives in `arrow.rs`.
    others = [s for s in spans if s not in containing]
    if not others:
        return []
    nearest = min(
        others,
        key=lambda s: min(abs(s[0] - citation_span[1]), abs(citation_span[0] - s[1])),
    )
    low, high = sorted([(nearest[0], nearest[1]), citation_span])
    between = text[low[1] : high[0]]
    if re.search(r"[.;!?]\s|\|", between):
        return []
    return identifiers(nearest[2])


def occurrences(source_lines: list[str], anchor: str) -> list[int]:
    pattern = re.compile(rf"\b{re.escape(anchor)}\b")
    return [n for n, line in enumerate(source_lines, start=1) if pattern.search(line)]


def read() -> Reading:
    reading = Reading()
    cache: dict[str, list[str] | None | str] = {}

    for document in scanned_documents():
        if is_archived(document):
            continue
        relative = str(document.relative_to(ROOT))
        for number, text in enumerate(document.read_text(errors="replace").splitlines(), start=1):
            for match in CITATION.finditer(text):
                token = match.group("path")
                cited = int(match.group("line"))
                end = int(match.group("end")) if match.group("end") else None
                anchors = [a for a in anchors_on(text, match.span()) if a not in token]
                citation = Citation(relative, number, token, cited, end, anchors)

                if token not in cache:
                    resolved = resolve(token)
                    if isinstance(resolved, str):
                        cache[token] = "AMBIGUOUS"
                    else:
                        cache[token] = (
                            resolved.read_text(errors="replace").splitlines() if resolved else None
                        )
                source_lines = cache[token]

                if source_lines == "AMBIGUOUS":
                    citation.verdict = "AMBIGUOUS"
                    citation.detail = "a bare basename matching several live files"
                elif source_lines is None:
                    citation.verdict = "UNRESOLVED"
                elif cited > len(source_lines):
                    citation.verdict = "PAST_EOF"
                    citation.detail = f"file has {len(source_lines)} lines"
                elif not anchors:
                    citation.verdict = "UNANCHORED"
                else:
                    citation.verdict, citation.detail = judge(
                        source_lines, anchors, cited, end or cited
                    )
                reading.citations.append(citation)
    return reading


def judge(source_lines: list[str], anchors: list[str], cited: int, end: int) -> tuple[str, str]:
    """The best verdict any named anchor achieves.

    Best-of rather than all-of: a line may name several identifiers and the citation is correct if
    it points at any one of them. Requiring all would fail a sentence for mentioning a second name.
    """
    best = ("ABSENT", "")
    order = {"OK": 0, "NEAR": 1, "DRIFTED": 2, "ABSENT": 3}
    for anchor in anchors:
        at = occurrences(source_lines, anchor)
        if not at:
            continue
        if any(cited <= n <= end for n in at):
            return "OK", ""
        nearest = min(at, key=lambda n: min(abs(n - cited), abs(n - end)))
        gap = min(abs(nearest - cited), abs(nearest - end))
        verdict = "NEAR" if gap <= WINDOW else "DRIFTED"
        detail = f"`{anchor}` is at :{nearest}" + (f" (+{len(at) - 1} more)" if len(at) > 1 else "")
        if order[verdict] < order[best[0]]:
            best = (verdict, detail)
    if best[0] == "ABSENT":
        best = ("ABSENT", "named " + ", ".join(f"`{a}`" for a in anchors))
    return best


TRUE_LINE = re.compile(r"is at :(?P<line>\d+)")


def repair(reading: Reading) -> int:
    """Rewrite every DRIFTED citation to the line its anchor is actually on.

    Only DRIFTED — the verdict where the anchor was found in the same file, so the construct is
    known and only the number moved. ABSENT and PAST_EOF are left alone: there the document may be
    naming the wrong file or a construct that has gone, and a reader has to decide which.

    A repair is skipped when the same `path:line` pair occurs more than once on the document line,
    because a blind textual substitution could then rewrite the wrong one.
    """
    edits: dict[str, list[Citation]] = {}
    for citation in reading.by_verdict("DRIFTED"):
        edits.setdefault(citation.document, []).append(citation)

    repaired = 0
    skipped = 0
    for document, citations in sorted(edits.items()):
        path = ROOT / document
        lines = path.read_text(errors="replace").splitlines(keepends=True)
        for citation in citations:
            match = TRUE_LINE.search(citation.detail)
            if not match:
                skipped += 1
                continue
            true_line = match.group("line")
            index = citation.document_line - 1
            was = f"{citation.path}:{citation.line}"
            now = f"{citation.path}:{true_line}"
            if lines[index].count(was) != 1:
                print(f"SKIPPED  {document}:{citation.document_line}  {was} is not unique on the line")
                skipped += 1
                continue
            lines[index] = lines[index].replace(was, now)
            print(f"REPAIRED {document}:{citation.document_line}  {was} -> {now}")
            repaired += 1
        path.write_text("".join(lines))
    print(f"\nrepaired {repaired} drifted citation(s); skipped {skipped}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--all", action="store_true", help="also list UNANCHORED and UNRESOLVED")
    parser.add_argument("--json", action="store_true", help="machine-readable")
    parser.add_argument(
        "--repair",
        action="store_true",
        help="rewrite DRIFTED citations to the line the anchor is actually on",
    )
    arguments = parser.parse_args()

    reading = read()
    if arguments.repair:
        return repair(reading)
    failures = reading.by_verdict("DRIFTED", "ABSENT", "PAST_EOF")

    if arguments.json:
        print(json.dumps([c.__dict__ for c in reading.citations], indent=2))
        return 1 if failures else 0

    for citation in failures:
        print(
            f"{citation.verdict:<9} {citation.document}:{citation.document_line}"
            f"  cites {citation.path}:{citation.line}"
            + (f"-{citation.end}" if citation.end else "")
            + (f"   {citation.detail}" if citation.detail else "")
        )
    if arguments.all:
        for citation in reading.by_verdict("UNANCHORED", "UNRESOLVED", "AMBIGUOUS", "NEAR"):
            print(
                f"{citation.verdict:<9} {citation.document}:{citation.document_line}"
                f"  cites {citation.path}:{citation.line}"
                + (f"   {citation.detail}" if citation.detail else "")
            )

    counts = {v: len(reading.by_verdict(v)) for v in
              ("OK", "NEAR", "DRIFTED", "ABSENT", "PAST_EOF", "UNANCHORED", "UNRESOLVED",
               "AMBIGUOUS")}
    print(
        f"FAILURES (a governing document cites a line the construct has left): {len(failures)}; "
        f"citations {len(reading.citations)}: "
        + ", ".join(f"{n} {v.lower()}" for v, n in counts.items() if n)
    )
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
