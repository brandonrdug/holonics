#!/usr/bin/env python3
"""Cold comparison of an independently executed text run and a remounted continuation.

This reads diagnostic reports, never mounts or develops a native ecology. Wire equality is
evidence for this particular continuation; it is not semantic identity or language quality.
"""
import argparse
import json
import os
from pathlib import Path


def compare(reference, resumed):
    keys = (
        "body", "generation", "development_records", "development_native_until",
        "emission_current_history", "utf8", "utf8_error", "prompt", "prompt_error",
        "fractional_bits", "junction_solver", "has_material_transport",
    )
    if reference["all_currents_requested"] or resumed["all_currents_requested"]:
        keys += ("all_currents_requested", "junction_history")
    checks = {key: reference[key] == resumed[key] for key in keys}
    checks["remount_enacts_no_native_occurrence"] = resumed["remount_native_deeds"] == 0
    checks["no_native_or_development_error"] = all(
        run[key] is None
        for run in (reference, resumed)
        for key in ("native_error", "development_error")
    )
    checks["source_position"] = all(
        reference["exposure_cursor"][key] == resumed["exposure_cursor"][key]
        for key in ("byte_offset", "next_sequence")
    )
    # A different absolute source path is permitted in this comparison, but its wire pin
    # remains part of each actual checkpoint. Continued development authenticates that pin.
    assert all(checks.values()), checks
    return {
        "schema": "holonics.text-rest-comparison.v1",
        "scope": "exact declared report/current/lineage and emission equality",
        "checks": checks,
        "development_families": len(resumed["development_records"]),
        "development_native_until": resumed["development_native_until"],
        "final_native_until": resumed["body"]["occurrences"],
        "resumed_native_from": resumed["resume_native_from"],
        "generation_disposition": resumed["generation"]["disposition"],
        "emitted_octets": resumed["generation"]["emitted_octets"],
        "language_quality_established": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("reference", type=Path)
    parser.add_argument("resumed", type=Path)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    receipt = compare(json.loads(args.reference.read_text()), json.loads(args.resumed.read_text()))
    receipt["reference"] = str(args.reference)
    receipt["resumed"] = str(args.resumed)
    with args.output.open("x") as out:
        os.fchmod(out.fileno(), 0o600)
        json.dump(receipt, out, indent=2)
        out.write("\n")
    print(json.dumps(receipt))


if __name__ == "__main__":
    main()
