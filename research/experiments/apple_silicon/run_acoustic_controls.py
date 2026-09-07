#!/usr/bin/env python3
"""Run prepared exterior sound controls through the public native application only."""
import argparse
import json
from pathlib import Path
import subprocess
import time


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--controls", type=Path, default=Path(".local/datasets/esc50-as4-controls"))
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--count", type=int, default=3)
    parser.add_argument("--binary", type=Path, default=Path("target/debug/holonics-acoustic"))
    args = parser.parse_args()
    manifest = json.loads((args.controls / "listening_manifest.json").read_text())
    if not 0 < args.count <= len(manifest["controls"]):
        parser.error("count must select a nonempty available prefix of the prepared family")
    args.output.mkdir(parents=True, exist_ok=False)
    report = {"schema": "holonics.apple.acoustic-control-run.v1", "source_manifest": str(args.controls / "listening_manifest.json"),
              "selection": "first declared count of prepared sources; original, reversed and polarity-inverted quarter-second windows",
              "runs": []}
    for source in manifest["controls"][:args.count]:
        for variant in source["variants"]:
            if variant["variant"] == "base-original":
                continue
            wav = args.controls / variant["path"]
            checkpoint = args.output / (wav.stem + ".hna")
            command = [str(args.binary), "run", "--seed",
                       "applications/holonics-workbench/examples/native/acoustic-seed.json",
                       "--wav", str(wav), "--occurrence", "esc50-control:" + wav.stem,
                       "--return-couplings", "applications/holonics-workbench/examples/native/acoustic-digital-return.json",
                       "--checkpoint", str(checkpoint)]
            start = time.monotonic_ns()
            result = subprocess.run(command, capture_output=True, text=True)
            row = {"source": source["source_filename"], "variant": variant["variant"],
                   "source_sample_from": source["window_sample_from"], "source_sample_to": source["window_sample_to"],
                   "wav": str(wav), "checkpoint": str(checkpoint), "command": command,
                   "elapsed_ns": time.monotonic_ns() - start, "exit_code": result.returncode,
                   "return": json.loads(result.stdout) if result.stdout.strip() else None,
                   "stderr": result.stderr}
            report["runs"].append(row)
            (args.output / "runs.json").write_text(json.dumps(report, indent=2) + "\n")
            print(json.dumps({"wav": str(wav), "exit_code": result.returncode,
                              "return": row["return"]}), flush=True)
            if result.returncode or not row["return"] or not row["return"]["complete"]:
                raise SystemExit("control stopped at its explicit refusal; artifacts preserved")


if __name__ == "__main__":
    main()
