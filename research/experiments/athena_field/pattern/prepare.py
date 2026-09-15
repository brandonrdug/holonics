"""Prepare exterior data for the joint-regions partial-field fixture.

The native field receives a three-slot section with observed and unobserved
regions.  This script owns the task relation and target text: it generates the
complete pattern ``[a, b, a]`` (and the explicit composition controls), then
exposes only the requested partial view to the session.  A non-null partial
entry is an observation; a null entry is unobserved.  The native receiver is
responsible for its declared affine observation ``y = P given + Q raw_field``.

Usage::

    python prepare.py [epochs]

The default is four epochs.  Comparison IDs are the exterior stream's
monotone source IDs: every development target gets one ID, and the final
development request intentionally leaves the next ID pending.  Evaluation
starts by observing that pending ID after a resume.
"""

from __future__ import annotations

import itertools
import json
import pathlib
import sys
from typing import Any, Iterable, Sequence


ROOT = pathlib.Path(__file__).resolve().parent
SYMBOLS = ["red", "blue", "green"]
SPEC = {
    "symbols": SYMBOLS,
    "section_symbols": 3,
    "context_symbols": 1,
    "source_chart": "joint-regions",
    "codec": "whitespace-words",
    "fractional_bits": 48,
}


def command(action: str, **fields: Any) -> dict[str, Any]:
    return {
        "schema": "org.holonics.hna.stream-request.v1",
        "command": {"action": action, **fields},
    }


def request(
    partial: Sequence[str | None],
    context: Sequence[str],
    *,
    commit: bool,
    retain: bool,
    omit_text: bool,
    output_symbols: int | None = None,
) -> dict[str, Any]:
    fields: dict[str, Any] = {
        "context": list(context),
        "partial": list(partial),
        "commit": commit,
        "retain_comparison": retain,
    }
    # Both forms are part of the public request contract.  Empty text keeps
    # this input on the existing text field while omission exercises its
    # default; neither form supplies a target or native answer.
    if not omit_text:
        fields["text"] = ""
    if output_symbols is not None:
        fields["output_symbols"] = output_symbols
    return command("field-request", request=fields)


def observe(source: int, text: str) -> dict[str, Any]:
    return command("observe-field", source=source, text=text, step_bits=1)


def prefix_text(pattern: Sequence[str], output_symbols: int | None = None) -> str:
    extent = len(pattern) if output_symbols is None else output_symbols
    if not 0 < extent <= len(pattern):
        raise ValueError(f"output extent {extent} is outside pattern {pattern}")
    return " ".join(pattern[:extent])


def views(a: str, b: str) -> list[list[str | None]]:
    return [[a, None, None], [None, None, a], [a, b, None], [None, b, a]]


def write_jsonl(path: pathlib.Path, rows: Iterable[dict[str, Any]]) -> None:
    path.write_text("".join(json.dumps(row) + "\n" for row in rows))


def main() -> None:
    epochs = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    if epochs < 1:
        raise SystemExit("epochs must be positive")
    ROOT.mkdir(parents=True, exist_ok=True)
    (ROOT / "spec.json").write_text(json.dumps(SPEC, indent=2) + "\n")

    development: list[dict[str, Any]] = []
    development_cases: list[dict[str, Any]] = []
    comparison = 0
    complete_cases = list(itertools.permutations(SYMBOLS, 2))
    for epoch in range(epochs):
        for a, b in complete_cases:
            pattern = [a, b, a]
            for view_index, partial in enumerate(views(a, b)):
                development.append(
                    request(
                        partial,
                        [b],
                        commit=True,
                        retain=True,
                        omit_text=False,
                    )
                )
                target = prefix_text(pattern)
                development.append(observe(comparison, target))
                development_cases.append(
                    {
                        "split": "development",
                        "epoch": epoch,
                        "comparison": comparison,
                        "a": a,
                        "b": b,
                        "pattern": pattern,
                        "context": [b],
                        "partial": partial,
                        "target": target,
                        "view_index": view_index,
                    }
                )
                comparison += 1

    # Keep a real producing comparison outstanding across the process boundary.
    pending_a, pending_b = complete_cases[0]
    pending_pattern = [pending_a, pending_b, pending_a]
    pending_partial = views(pending_a, pending_b)[0]
    pending_comparison = comparison
    development.append(
        request(
            pending_partial,
            [pending_b],
            commit=True,
            retain=True,
            omit_text=True,
        )
    )
    pending_case = {
        "split": "development-pending",
        "comparison": pending_comparison,
        "a": pending_a,
        "b": pending_b,
        "pattern": pending_pattern,
        "context": [pending_b],
        "partial": pending_partial,
        "target": prefix_text(pending_pattern),
    }

    evaluation: list[dict[str, Any]] = [
        # This must be the first evaluation event so a resumed process proves
        # that the producing comparison survived the development boundary.
        observe(pending_comparison, pending_case["target"])
    ]
    withheld: list[dict[str, Any]] = []
    for a in SYMBOLS:
        b = a
        pattern = [a, b, a]
        for view_index, partial in enumerate(views(a, b)):
            evaluation.append(
                request(
                    partial,
                    [b],
                    commit=False,
                    retain=False,
                    omit_text=True,
                )
            )
            withheld.append(
                {
                    "split": "withheld-equal",
                    "a": a,
                    "b": b,
                    "pattern": pattern,
                    "context": [b],
                    "partial": partial,
                    "target": prefix_text(pattern),
                    "view_index": view_index,
                }
            )

    # These controls are kept separate from the 12-case diagonal score.  They
    # test joining independent received regions and variable output extent;
    # they are not a claim that the native session has been given a universal
    # pattern rule or a target-derived decoder.
    composition: list[dict[str, Any]] = []
    for a, b, c in itertools.product(SYMBOLS, repeat=3):
        if a == c:
            continue
        pattern = [a, b, c]
        partial = [a, None, c]
        evaluation.append(
            request(
                partial,
                [b],
                commit=False,
                retain=False,
                omit_text=False,
            )
        )
        composition.append(
            {
                "split": "composition-control",
                "a": a,
                "b": b,
                "c": c,
                "pattern": pattern,
                "context": [b],
                "partial": partial,
                "target": prefix_text(pattern),
            }
        )

    shorter: list[dict[str, Any]] = []
    for a, b in itertools.product(SYMBOLS, repeat=2):
        pattern = [a, b, a]
        partial = [a, None]
        evaluation.append(
            request(
                partial,
                [b],
                commit=False,
                retain=False,
                omit_text=True,
                output_symbols=2,
            )
        )
        shorter.append(
            {
                "split": "shorter-output-control",
                "a": a,
                "b": b,
                "pattern": pattern,
                "context": [b],
                "partial": partial,
                "output_symbols": 2,
                "target": prefix_text(pattern, 2),
            }
        )

    write_jsonl(ROOT / "development.jsonl", development)
    write_jsonl(ROOT / "evaluation.jsonl", evaluation)
    expected = {
        "schema": "org.holonics.hna.field-pattern.v1",
        "source_chart": "joint-regions",
        "codec": "whitespace-words",
        "fractional_bits": 48,
        "symbols": SYMBOLS,
        "section_capacity": 3,
        "context_capacity": 1,
        "target_authority": "exterior-generated-source-data",
        "partial_observation": {
            "non_null_entries": "held observations through y = P given + Q raw_field",
            "null_entries": "unobserved regions",
            "zero_seed": "chosen seed only; never an observation",
        },
        "epochs": epochs,
        "development": {
            "base_cases": 24,
            "observed_targets": len(development_cases),
            "pending_comparison": pending_comparison,
            "pending": pending_case,
            "cases": development_cases,
        },
        "evaluation": {
            "resume_first_event": "observe-field",
            "resume_source": pending_comparison,
            "withheld_equal_cases": len(withheld),
            "withheld_equal": withheld,
            "composition_control_cases": len(composition),
            "composition_controls": composition,
            "shorter_output_control_cases": len(shorter),
            "shorter_output_controls": shorter,
        },
    }
    (ROOT / "expected.json").write_text(json.dumps(expected, indent=2) + "\n")
    print(
        json.dumps(
            {
                "epochs": epochs,
                "development_cases": len(development_cases),
                "pending_comparison": pending_comparison,
                "withheld_equal_cases": len(withheld),
                "composition_control_cases": len(composition),
                "shorter_output_control_cases": len(shorter),
            }
        )
    )


if __name__ == "__main__":
    main()
