#!/usr/bin/env python3
"""Render and observe the completed AS4 acoustic controls through the public CLI.

This is a cold observer: it invokes ``holonics-acoustic render`` for each completed checkpoint,
compares the retained exact native current before any PCM summary, and then plots a small receiver
face. It does not classify the source, manufacture current, or treat a digest as semantic identity.
"""

from __future__ import annotations

import argparse
import json
from fractions import Fraction
import subprocess
import wave
from pathlib import Path


def wire_int(value: list) -> int:
    """Decode the serde BigInt [sign, little-endian u32 limbs] representation."""
    sign, limbs = value
    magnitude = sum(int(limb) << (32 * index) for index, limb in enumerate(limbs))
    return int(sign) * magnitude


def phase_cells(production: dict) -> list[list[Fraction]]:
    denominator = sum(int(limb) << (32 * index) for index, limb in enumerate(production["common_denominator"]))
    if denominator <= 0:
        raise ValueError("production denominator must be positive")
    section = production["exact_phase_current"]
    cells = [[Fraction(wire_int(value), denominator) for value in cell] for cell in section["cells"]]
    if not cells or any(len(cell) != section["phase_extent"] for cell in cells):
        raise ValueError("incomplete current cell population")
    # Independently reconstruct the same section from the retained rational port fibre.
    orders = production["causal_orders"]
    fibre = production["complete_port_quadrature_fibre"]
    ports = sorted({(entry[1], entry[2]) for entry in fibre})
    if len(cells) != len(orders) or len(ports) * 2 != section["phase_extent"]:
        raise ValueError("phase/fibre incidence differs")
    expected = [(order, port) for order in orders for port in ports]
    if len(fibre) != len(expected):
        raise ValueError("incomplete port fibre")
    for index, (entry, (order, port)) in enumerate(zip(fibre, expected)):
        if (entry[0], (entry[1], entry[2])) != (order, port):
            raise ValueError("phase/fibre chronology differs")
        coordinates = [Fraction(wire_int(entry[3][key][0]), wire_int(entry[3][key][1]))
                       for key in ["real", "imaginary"]]
        at, slot = divmod(index, len(ports))
        if cells[at][2 * slot:2 * slot + 2] != coordinates:
            raise ValueError("rational phase reconstruction differs from complete port fibre")
    return cells


def phase_metrics(production: dict) -> dict:
    cells = phase_cells(production)
    return {
        "cell_count": len(cells), "phase_extent": len(cells[0]),
        "nonzero_coordinates": sum(bool(v) for cell in cells for v in cell),
        "absolute_rational_current_sum": sum(abs(v) for cell in cells for v in cell),
        "oriented_rational_sums_by_phase": [sum(c[i] for c in cells) for i in range(len(cells[0]))],
    }


def phase_difference(left: dict, right: dict) -> dict:
    for key in ["origin", "sample_step", "phase_extent", "raw_extent"]:
        if left["exact_phase_current"][key] != right["exact_phase_current"][key]:
            raise ValueError("incomparable source clock or phase extent: " + key)
    a, b = phase_cells(left), phase_cells(right)
    if len(a) != len(b):
        raise ValueError("different causal populations")
    delta = [[x - y for x, y in zip(c, d)] for c, d in zip(a, b)]
    return {
        "changed_cells": sum(any(c) for c in delta),
        "changed_coordinates": sum(bool(v) for c in delta for v in c),
        "absolute_oriented_rational_difference_sum": sum(abs(v) for c in delta for v in c),
        "oriented_rational_difference_sums_by_phase": [sum(c[i] for c in delta) for i in range(len(delta[0]))],
        "all_coordinates_negate_original": all(x == -y for c, d in zip(a, b) for x, y in zip(c, d)),
    }


def read_pcm16(path: Path) -> list[int]:
    with wave.open(str(path), "rb") as stream:
        if stream.getnchannels() != 1 or stream.getsampwidth() != 2:
            raise ValueError(f"observer requires mono PCM16 WAV: {path}")
        raw = stream.readframes(stream.getnframes())
    return [int.from_bytes(raw[index : index + 2], "little", signed=True) for index in range(0, len(raw), 2)]


def pcm_difference(left: list[int], right: list[int]) -> dict:
    if len(left) != len(right):
        raise ValueError("compared PCM controls have different frame counts")
    differences = [a - b for a, b in zip(left, right)]
    return {
        "equal": not any(differences),
        "all_samples_negate_original": all(a == -b for a, b in zip(left, right)),
        "changed_samples": sum(bool(value) for value in differences),
        "absolute_oriented_difference_sum": sum(abs(value) for value in differences),
        "oriented_difference_sum": sum(differences),
    }


def receiver_summary(production: dict, potential: dict, inspection: dict) -> dict:
    first, last = inspection["first_native_return"], inspection["last_native_return"]
    return {
        "initial_successor_rank": first["successor_rank"],
        "final_successor_rank": last["successor_rank"],
        "initial_native_receiver": first["receiver"],
        "final_native_receiver": last["receiver"],
        "final_received_difference": last["received_difference"],
        "final_root_currents": last["root_source_currents"],
        "next_sample": inspection["next_sample"], "complete": inspection["complete"],
        "pending": inspection["pending"],
        "declared_port_coordinates": sorted({(int(item[1]), int(item[2])) for item in production["complete_port_quadrature_fibre"]}),
        "complete_port_current_fibre_entries": len(production["complete_port_quadrature_fibre"]),
        "complete_port_current_fibre_retained": potential["complete_production_fibre_retained"],
    }


def fibre_difference(left: list, right: list) -> dict:
    if len(left) != len(right):
        raise ValueError("compared complete port fibres have different extents")
    changed = [index for index, (a, b) in enumerate(zip(left, right)) if a != b]
    current_changed = [
        index for index, (a, b) in enumerate(zip(left, right)) if a[3] != b[3]
    ]
    return {
        "entry_count": len(left),
        "changed_entries": len(changed),
        "changed_current_entries": len(current_changed),
        "changed_entry_indices_sample": changed[:16],
    }


def plot_report(report: dict, output: Path) -> None:
    import matplotlib.pyplot as plt
    rows = report["cases"]
    fig, axes = plt.subplots(len(rows), 3, figsize=(14, 2.8 * len(rows)), squeeze=False)
    for row_index, row in enumerate(rows):
        source_ax, current_ax, rendered_ax = axes[row_index]
        for variant in row["variants"]:
            source = read_pcm16(Path(variant["wav"]))
            rendered = read_pcm16(Path(variant["render_dir"]) / "sound.wav")
            production = json.loads((Path(variant["render_dir"]) / "production.json").read_text())
            # A plotting projection of one named oriented coordinate; all coordinates remain in JSON.
            current = [float(cell[0]) for cell in phase_cells(production)]
            label = variant["variant"]
            source_ax.plot(source, linewidth=0.5, label=label)
            current_ax.plot(current, linewidth=0.5, label=label)
            rendered_ax.plot(rendered, linewidth=0.5, label=label)
        source_ax.set_title(row["source"] + " — source PCM")
        current_ax.set_title("Actual emitted current: port 0 real")
        rendered_ax.set_title("Generated PCM: fixed receiver")
        source_ax.set_ylabel("PCM16")
        current_ax.set_ylabel("rational current (plot projection)")
        rendered_ax.set_ylabel("PCM16")
        for ax in axes[row_index]:
            ax.grid(alpha=0.2)
        source_ax.legend(fontsize=7)
    for ax in axes[-1]:
        ax.set_xlabel("sample / causal arrival ordinal")
    fig.tight_layout()
    fig.savefig(output, dpi=150)
    plt.close(fig)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runs", type=Path, default=Path(".local/artifacts/acoustic/controls/runs.json"))
    parser.add_argument("--receiver", type=Path, default=Path(".local/artifacts/acoustic/receiver.json"))
    parser.add_argument("--binary", type=Path, default=Path("target/debug/holonics-acoustic"))
    parser.add_argument("--output", type=Path, default=Path(".local/artifacts/acoustic/controls/observed"))
    parser.add_argument("--render-root", type=Path, help="reuse completed render directories without invoking the CLI")
    args = parser.parse_args()
    runs = json.loads(args.runs.read_text())["runs"]
    declared_receiver = json.loads(args.receiver.read_text())
    if args.output.exists():
        raise SystemExit(f"refusing existing observer output: {args.output}")
    args.output.mkdir(parents=True)
    report = {
        "schema": "holonics.apple.as4.acoustic-observer-report.v1",
        "runs": str(args.runs),
        "receiver": str(args.receiver),
        "render_binary": str(args.binary),
        "comparison": "all rational phase coordinates (including each production denominator) and complete port fibre are compared before generated PCM; rational JSON values are exact strings",
        "pcm_interpretation": "cold sonification receiver face; it is not a waveform-copy or speech result",
        "cases": [],
    }
    grouped: dict[str, list[dict]] = {}
    for item in runs:
        grouped.setdefault(item["source"], []).append(item)
    for source, items in grouped.items():
        baseline = None
        baseline_pcm = None
        case = {"source": source, "variants": []}
        for item in items:
            checkpoint = Path(item["checkpoint"])
            render_dir = (args.render_root / checkpoint.stem) if args.render_root else (args.output / checkpoint.stem)
            command = [str(args.binary), "render", str(checkpoint), "--receiver", str(args.receiver), "--output", str(render_dir)]
            completed = None if args.render_root else subprocess.run(command, check=True, capture_output=True, text=True)
            production = json.loads((render_dir / "production.json").read_text())
            potential = json.loads((render_dir / "potential.json").read_text())
            projection = json.loads((render_dir / "projection.json").read_text())
            scope = json.loads((render_dir / "scope.json").read_text())
            if potential["receiver"] != declared_receiver:
                raise ValueError("reused render has a different fixed receiver")
            if scope["source_checkpoint"] != str(checkpoint) or not scope["input_complete"]:
                raise ValueError("render scope differs from the completed input checkpoint")
            if potential["production_identity_sha256"] != production["identity_sha256"]:
                raise ValueError("serialized production/potential wire mismatch")
            inspection = json.loads(subprocess.run([str(args.binary), "inspect", str(checkpoint)],
                check=True, capture_output=True, text=True).stdout)
            if item["variant"] == "original":
                baseline = production
                baseline_pcm = read_pcm16(render_dir / "sound.wav")
            if baseline is None:
                raise ValueError(f"original must precede comparison variant for {source}")
            difference = phase_difference(production, baseline)
            pcm = read_pcm16(render_dir / "sound.wav")
            fibre_equal = production["complete_port_quadrature_fibre"] == baseline["complete_port_quadrature_fibre"]
            entry = {
                "variant": item["variant"],
                "wav": item["wav"],
                "checkpoint": str(checkpoint),
                "render_dir": str(render_dir),
                "render_stdout": None if completed is None else completed.stdout.strip(),
                "exact_phase_metrics": phase_metrics(production),
                "exact_phase_difference_from_original": difference,
                "complete_port_quadrature_fibre_equal_to_original": fibre_equal,
                "complete_port_quadrature_fibre_difference_from_original": fibre_difference(
                    production["complete_port_quadrature_fibre"], baseline["complete_port_quadrature_fibre"]
                ),
                "pcm_difference_from_original": pcm_difference(pcm, baseline_pcm),
                "receiver_and_rank": receiver_summary(production, potential, inspection),
                "production_flags": {
                    "source_samples_accessible": production["source_samples_accessible"],
                    "waveform_template_applied": production["waveform_template_applied"],
                    "complete_port_quadrature_fibre_retained": bool(production["complete_port_quadrature_fibre"]),
                },
                "pcm_projection": {
                    "samples": len(projection["samples"]),
                    "nonzero_sample_population": projection["nonzero_sample_population"],
                    "clipped_sample_population": projection["clipped_sample_population"],
                    "cold_renderer_only": projection["cold_renderer_only"],
                },
            }
            case["variants"].append(entry)
        report["cases"].append(case)
    report_path = args.output / "report.json"
    report_path.write_text(json.dumps(report, indent=2, default=str) + "\n")
    plot_report(report, args.output / "waveform_current_comparison.png")
    print(json.dumps({"report": str(report_path), "plot": str(args.output / 'waveform_current_comparison.png'), "cases": len(report['cases']), "renders": sum(len(c['variants']) for c in report['cases'])}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
