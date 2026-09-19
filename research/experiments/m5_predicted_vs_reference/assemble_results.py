#!/usr/bin/env python3
"""Assemble one `results.json` out of the three things this experiment produced.

[definition] This script computes nothing. It concatenates the Rust example's receiver readings
(exact, over Q), the record of what the predictor actually ran, and the predictor's own confidence
self-report (exterior float). Keeping the three apart in the file makes it impossible to read a
float statistic as a library verdict.

    python3 assemble_results.py
"""
import json
import pathlib

HERE = pathlib.Path(__file__).parent


def main() -> int:
    results = {
        "schema": "holonics.m5-predicted-vs-reference.assembled.v1",
        "predictor_runs": json.loads((HERE / "predictor_runs.json").read_text()),
        "receiver_readings_exact_over_Q": json.loads(
            (HERE / "receiver_readings.json").read_text()
        ),
        "exterior_predictor_confidence_float": json.loads(
            (HERE / "predictor_confidence.json").read_text()
        ),
    }
    (HERE / "results.json").write_text(json.dumps(results, indent=2) + "\n")
    print(f"wrote {HERE / 'results.json'}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
