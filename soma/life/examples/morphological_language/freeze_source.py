#!/usr/bin/env python3
"""Freeze this repository's own heterogeneous language corpus without invoking any model.

PROVENANCE
==========
This file is a PORT. Its ancestor is the frozen laboratory's
`experiments/causal-language/sidecar/freeze_source.py`, recoverable with

    git -C /home/b/Workspaces/laboratory show \\
        a07ff376:experiments/causal-language/sidecar/freeze_source.py

The laboratory's `SOURCE.json` for `eros_morphological_language_generation` was written under
its untracked `runs/`, so it is gone at every commit in either repository -- the same loss
`CLAUDE.md` §0 records for the tiger figures. What survives is this extractor, and the extractor
is the honest recovery surface: it reads real files and computes every number from their bytes.

WHAT CHANGED IN THE PORT, EXACTLY
---------------------------------
The receiver constants, the paragraph rule, the >=6-word passage filter, the four prompts, the
control prompt, the comparison stanza, and the emitted schema are byte-for-byte the laboratory's.
Only `SOURCES` moved, because the paths moved:

  * 15 of the laboratory's 17 named files exist VERBATIM in this repository and are named here
    at their holonics paths -- eight `research/records/*.md` (the laboratory's
    `src/soma/RESEARCH/`), `soma/life/src/synchronized_occurrence.rs`,
    `crates/holonic-engine/src/algebraic.rs`, four `papers/source/mathematics/definitions/*.typ`
    (the laboratory's `src/soma/PAPERS/mathematics/definitions/`), and the operating contract
    (`AGENTS.md` there, `CLAUDE.md` here -- `CLAUDE.md` is the Claude-facing authority and
    `AGENTS.md` is explicitly not authority here).
  * 2 of the 17 were laboratory `runs/` artifacts and are UNRECOVERABLE. They carried the
    OBSERVATION receiver. They are replaced by two tracked observation-class documents of this
    repository, named below with `SUBSTITUTED` beside them. Nothing else was substituted, and no
    number in the emitted source is authored -- `sha256`, `bytes` and `passages` are all computed
    from the files on disk at the moment of the run.

There is no model, no network, no tokenizer, and no float anywhere in this file. It is a boundary
codec in the declared apparatus role.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from pathlib import Path


RECEIVER_RESEARCH = 0x5245534541524348
RECEIVER_CODE = 0x434F44455F525843
RECEIVER_MATHEMATICS = 0x4D4154485F525843
RECEIVER_OBSERVATION = 0x4F4253565F525843
RECEIVER_CONTRACT = 0x434F4E5452414354

# (relative path, receiver, lineage). `lineage` is carried into the emitted source so a reader
# can tell a recovered name from a substituted one without leaving the file.
SOURCES = (
    ("CLAUDE.md", RECEIVER_CONTRACT, "recovered:AGENTS.md"),
    (
        "research/records/2026-07-29_THE_DELIVERY_WORD_IS_GAUGE_THE_CAUSAL_CONFIGURATION_CARRIES_THE_SOURCE_FIBER.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    (
        "research/records/2026-07-29_THE_INFORMANT_CHARGES_THE_GERM_THE_LEADER_RETURNS_THE_RESONANT_COMPONENT.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    (
        "research/records/2026-07-29_THE_SUFFIX_DILATES_THE_CONTEXT_THE_EMANATED_BRANCH_RETURNS_AS_CAUSE.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    (
        "research/records/2026-07-29_THE_DIFFERENCE_EMITS_THE_PATH_CARRIES_THE_SPECTRUM_IS_THE_RECEIVER_PHASE_FACE.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    (
        "research/records/2026-07-29_THE_RECEIVER_IS_NOT_THE_FRAME_THE_PROJECTION_IS_ONLY_A_MEMBRANE.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    (
        "research/records/2026-07-27_THE_CURRENT_CROSSES_THE_LOCAL_FRONT_THE_FRAME_CANNOT_SCHEDULE_THE_EVENT.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    (
        "research/records/2026-07-26_THE_TUBE_CARRIES_THE_EXTERIOR_FACE_THE_DISTANT_FIELD_RETURNS_THROUGH_REBASE.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    (
        "research/records/2026-07-28_THE_PHASE_CARRIES_ACROSS_THE_CELL_THE_SCALAR_RECEIVER_IS_NOT_CLOSED_UNDER_PROPAGATION.md",
        RECEIVER_RESEARCH,
        "recovered",
    ),
    ("soma/life/src/synchronized_occurrence.rs", RECEIVER_CODE, "recovered"),
    ("crates/holonic-engine/src/algebraic.rs", RECEIVER_CODE, "recovered"),
    (
        "papers/source/mathematics/definitions/receiver-indexed-holonic-system.typ",
        RECEIVER_MATHEMATICS,
        "recovered",
    ),
    (
        "papers/source/mathematics/definitions/holonic-process-double-category.typ",
        RECEIVER_MATHEMATICS,
        "recovered",
    ),
    (
        "papers/source/mathematics/definitions/receiver-configuration-calculus.typ",
        RECEIVER_MATHEMATICS,
        "recovered",
    ),
    (
        "papers/source/mathematics/definitions/contextual-tangle-compression.typ",
        RECEIVER_MATHEMATICS,
        "recovered",
    ),
    # SUBSTITUTED. The laboratory named
    # `runs/synchronized-grid-factorized-structural-fiber-information-flow/RESULTS.md`, which was
    # never tracked and does not exist at any commit in either repository.
    (
        "CONSTRUCTION_STATE.md",
        RECEIVER_OBSERVATION,
        "SUBSTITUTED:runs/synchronized-grid-factorized-structural-fiber-information-flow/RESULTS.md",
    ),
    # SUBSTITUTED. The laboratory named
    # `runs/resonant-corpus-current-information-flow/REPORT.json`, likewise untracked and gone.
    (
        "standing/README.md",
        RECEIVER_OBSERVATION,
        "SUBSTITUTED:runs/resonant-corpus-current-information-flow/REPORT.json",
    ),
)

# The laboratory's declared generation aperture, in tokens per prompt.
LABORATORY_GENERATION_APERTURE = 256

PROMPTS = (
    (
        "training-and-uncertainty",
        "How does training condition morphology while unresolved uncertainty remains open?",
    ),
    (
        "suffix-and-lineage",
        "How does the exact suffix frontier conduct retained source lineage?",
    ),
    (
        "emission-and-reuse",
        "What does emission carry through phase transport, and when may a receiver tube be reused?",
    ),
    (
        "multimodal-return",
        "How does multimodal co-presence enter one ecology? How can returned consequence change later conduct?",
    ),
)


def sha256(body: bytes) -> str:
    return hashlib.sha256(body).hexdigest()


def paragraph_occurrences(text: str) -> list[str]:
    # Paragraphs are inherited presentation boundaries from the source. They are not resized into
    # a host-selected maximum extent: the conditioned language ecology retains document lineage,
    # exact internal chronology, recurrent spans, clauses, and these delivery occurrences
    # simultaneously.
    occurrences = [
        re.sub(r"[ \t]+", " ", paragraph.strip())
        for paragraph in re.split(r"\n\s*\n", text)
        if paragraph.strip()
    ]
    return [
        occurrence
        for occurrence in occurrences
        if len(re.findall(r"[A-Za-z0-9_']+", occurrence)) >= 6
    ]


def freeze(
    workspace: Path,
    aperture: int = LABORATORY_GENERATION_APERTURE,
    schema: str = "soma.morphological-language.source.v2",
) -> dict[str, object]:
    passages: list[dict[str, object]] = []
    files: list[dict[str, object]] = []
    for relative, receiver, lineage in SOURCES:
        path = workspace / relative
        body = path.read_bytes()
        text = body.decode("utf-8")
        chunks = paragraph_occurrences(text)
        files.append(
            {
                "path": relative,
                "receiver": receiver,
                "sha256": sha256(body),
                "bytes": len(body),
                "passages": len(chunks),
                "lineage": lineage,
            }
        )
        for ordinal, chunk in enumerate(chunks):
            passages.append(
                {
                    "identity": f"{relative}#{ordinal:04d}",
                    "receiver": receiver,
                    "source_path": relative,
                    "source_sha256": sha256(body),
                    "text": chunk,
                }
            )
    return {
        "provenance": {
            "kind": "CONSTRUCTED",
            "constructed_by": "soma/life/examples/morphological_language/freeze_source.py",
            "ported_from_repository": "/home/b/Workspaces/laboratory (frozen)",
            "ported_from_commit": "a07ff376",
            "ported_from_path": "experiments/causal-language/sidecar/freeze_source.py",
            "laboratory_source_json": (
                "UNRECOVERABLE -- written under the laboratory's untracked `runs/`; zero files "
                "exist under it at any commit, so the original SOURCE.json is gone. The extractor "
                "survived and this file is its output."
            ),
            "material": (
                "Every passage below is verbatim text of a file tracked in this repository. "
                "Every sha256, byte count and passage count was computed from those bytes at "
                "extraction time. No measurement was authored and no model was executed."
            ),
            "generation_aperture": aperture,
            "laboratory_generation_aperture": LABORATORY_GENERATION_APERTURE,
            "generation_aperture_note": (
                "`maximum_generated_tokens` per prompt. 256 is the laboratory's declared value and "
                "is what `--maximum-generated-tokens` defaults to. MEASURED HERE 2026-08-08 on a "
                "23-passage corpus with one of these prompts, release build: 1 token 57 ms, "
                "2 tokens 403 ms, 4 tokens 55,098 ms, 8 tokens did not return inside 200,000 ms. "
                "`MorphologicalLanguageEcology::generate` branches super-exponentially in this "
                "parameter, so the laboratory's 256 is not reachable by this implementation at any "
                "corpus size and a run at 256 does not return. A source emitted with a smaller "
                "aperture is BOUNDED, not falsified: the aperture is a declared receiver parameter "
                "and it is recorded here so no reader mistakes the bound for the law."
            ),
            "recovered_file_names": 15,
            "substituted_file_names": 2,
            "substitution_reason": (
                "Two of the laboratory's seventeen named files were `runs/` artifacts that were "
                "never tracked. Their receiver (OBSERVATION) is carried by two tracked "
                "observation-class documents of this repository instead. Each file below carries "
                "a `lineage` member reading `recovered` or `SUBSTITUTED:<the laboratory path>`."
            ),
        },
        "schema": schema,
        "question": (
            "Can simultaneous recurrent mark, lexical, phrase, clause, occurrence, and source "
            "receivers condition one exact response ecology which composes several caused source "
            "phases, returns every emitted transition, and closes only when its query fibers rest?"
        ),
        "files": files,
        "passages": passages,
        "prompts": [
            {
                "identity": identity,
                "text": text,
                "maximum_generated_tokens": aperture,
            }
            for identity, text in PROMPTS
        ],
        "control_prompt": "xylophonic quasar zephyr",
        "comparison": {
            "role": "architectural evidence only; no external model is executed",
            "kimi_k3": [
                "recurrent sequence mixing",
                "periodic global interaction",
                "selective transport across depth",
                "shared plus sparse routed width",
                "native multimodal conditioning",
            ],
            "gemma_4": [
                "local and global context transport",
                "dense and mixture-of-experts realizations",
                "unified and encoder-mediated multimodal realizations",
                "multi-token prediction",
            ],
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("workspace", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument(
        "--schema",
        default="soma.morphological-language.source.v2",
        help=(
            "the emitted `schema` string. `eros_morphological_language_generation` validates "
            "`soma.morphological-language.source.v2`; `eros_causal_language_generation` validates "
            "`soma.causal-language.source.v1`. The two drivers deserialize the SAME field "
            "structure -- verified by diffing their `struct Source` -- so one extractor feeds "
            "both and only this string differs."
        ),
    )
    parser.add_argument(
        "--maximum-generated-tokens",
        type=int,
        default=LABORATORY_GENERATION_APERTURE,
        help=(
            "generation aperture per prompt; defaults to the laboratory's declared 256, which "
            "this implementation cannot reach (see `generation_aperture_note` in the output)"
        ),
    )
    arguments = parser.parse_args()
    if arguments.maximum_generated_tokens < 1:
        parser.error("the generation aperture is at least one token")
    source = freeze(
        arguments.workspace.resolve(),
        arguments.maximum_generated_tokens,
        arguments.schema,
    )
    arguments.output.parent.mkdir(parents=True, exist_ok=True)
    arguments.output.write_text(
        json.dumps(source, indent=2, ensure_ascii=False) + "\n",
        encoding="utf-8",
    )
    print(
        f"froze {len(source['passages'])} heterogeneous passages "
        f"from {len(source['files'])} files to {arguments.output}"
    )


if __name__ == "__main__":
    main()
