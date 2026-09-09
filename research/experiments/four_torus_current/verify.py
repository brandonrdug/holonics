#!/usr/bin/env python3
"""Compare source-qualified continuations of the exterior exact current example.

This driver mounts experiment arguments, executes the public example in fresh
processes, and compares its returned receivers. It supplies no mathematical solver.
Pass the built example path and a new output directory; evidence is never overwritten.
"""
import json
import os
from pathlib import Path
import subprocess
import sys
import time


def main():
    binary, root = Path(sys.argv[1]).resolve(), Path(sys.argv[2]).resolve()
    root.mkdir(parents=True, exist_ok=False)
    commands = []

    def run(name, *arguments):
        output = root / name
        # wait4 observes this complete child, including decoder, all receiver
        # checks, inverse certificates, allocation and durable I/O.
        command = [str(binary), *map(str, arguments), str(output)]
        if arguments[-1:] == ("blind",):
            command[-2:] = [str(output), "blind"]
        commands.append(command)
        started = time.perf_counter_ns()
        with subprocess.Popen(command) as child:
            _, status, usage = os.wait4(child.pid, 0)
            child.returncode = os.waitstatus_to_exitcode(status)
            process = {"command": command, "exit_code": child.returncode,
                       "wall_ns": time.perf_counter_ns() - started,
                       "user_seconds": usage.ru_utime, "system_seconds": usage.ru_stime,
                       "maximum_resident_kib_linux": usage.ru_maxrss,
                       "major_page_faults": usage.ru_majflt,
                       "minor_page_faults": usage.ru_minflt}
            (root / f"{name}.process.json").write_text(json.dumps(process, indent=2) + "\n")
            if child.returncode:
                raise subprocess.CalledProcessError(child.returncode, command)
        return output

    def load(path, file):
        return json.loads((path / file).read_text())

    direct = run("side2-direct", "run", 2, 12)
    prefix = run("side2-prefix", "run", 2, 5)
    resumed = run("side2-resumed", "resume", prefix / "state.json", 7)
    blind = run("side2-blind", "run", 2, 12, "blind")
    blind_prefix = run("side2-blind-prefix", "run", 2, 5, "blind")
    blind_resumed = run("side2-blind-resumed", "resume", blind_prefix / "state.json", 7)
    larger = run("side3-direct", "run", 3, 6)

    for full, split in [(direct, resumed), (blind, blind_resumed)]:
        assert load(full, "state.json") == load(split, "state.json")
        assert load(full, "full-current.json") == load(split, "full-current.json")

    direct_state, blind_state = [load(p, "state.json") for p in (direct, blind)]
    for key in ["cuts", "faces", "clock", "step"]:
        assert direct_state[key] == blind_state[key]
    assert not direct_state["blind_residual"] and blind_state["blind_residual"]
    full, shifted = [load(p, "full-current.json") for p in (direct, blind)]
    separating_edge = next(i for i, pair in enumerate(zip(full, shifted)) if pair[0] != pair[1])

    small_steps, large_steps, blind_steps = [load(p, "receipt.json")["steps"]
                                           for p in (direct, larger, blind)]
    for left, right in zip(small_steps, large_steps):
        for key in ["input", "clock_before", "clock_after", "cuts", "face_readings", "active_material_energy"]:
            assert left[key] == right[key]
    for left, right in zip(small_steps, blind_steps):
        for key in ["input", "clock_before", "clock_after", "cuts", "face_readings", "active_material_energy"]:
            assert left[key] == right[key]

    result = {
        "grade": "established-bounded",
        "evidence": ["computational-witness", "implemented-exact"],
        "source": "crates/holonic-engine/examples/four_torus_current.rs",
        "commands": commands,
        "resume": "fresh processes reproduce uninterrupted 12-event state and full current, with and without cold residual",
        "scale": "six matching clocked events on side 2 and 3 preserve four cuts, active face readings and declared material energy",
        "retained_fibre": "12 matching events preserve joint readings while full currents remain separated",
        "separating_edge": separating_edge,
        "unshifted_edge_codeword": full[separating_edge],
        "shifted_edge_codeword": shifted[separating_edge],
        "boundary": "two active faces, declared source/material sequence, rational current chart; no arbitrary geometric refinement or HNN execution",
    }
    (root / "comparison.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "commands"}, indent=2))


if __name__ == "__main__":
    main()
