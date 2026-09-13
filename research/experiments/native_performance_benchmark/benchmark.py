#!/usr/bin/env python3
"""Measure bounded current HNN workloads on one declared host.

This is exterior timing apparatus.  It reports exact resident work, integer clocks, transfer and
residency counters, and rational delivered-face/state-update rates.  Rates describe these
workloads at their declared apertures; they are not semantic quality, physical power, or an
acceptance gate.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path


SCHEMA = "org.holonics.hna.stream-request.v1"
MATH_OPERATION = "mathematical-request"


def rat(value: int) -> dict[str, str]:
    return {"numerator": str(value), "denominator": "1"}


def matrix_wire(matrix: list[list[int]]) -> list[list[dict[str, str]]]:
    return [[rat(value) for value in row] for row in matrix]


def request(action: str, **body: object) -> dict[str, object]:
    command = {"action": action}
    if action == MATH_OPERATION:
        command["request"] = body
    else:
        command.update(body)
    return {"schema": SCHEMA, "command": command}


def c5_laplacian() -> list[list[int]]:
    return [
        [2, -1, 0, 0, -1],
        [-1, 2, -1, 0, 0],
        [0, -1, 2, -1, 0],
        [0, 0, -1, 2, -1],
        [-1, 0, 0, -1, 2],
    ]


def matrix_mul(a: list[list[int]], b: list[list[int]]) -> list[list[int]]:
    return [[sum(left * right for left, right in zip(row, column)) for column in zip(*b)] for row in a]


def matrix_power(a: list[list[int]], exponent: int) -> list[list[int]]:
    result = [[int(row == column) for column in range(len(a))] for row in range(len(a))]
    base = a
    while exponent:
        if exponent & 1:
            result = matrix_mul(result, base)
        base = matrix_mul(base, base)
        exponent >>= 1
    return result


def vector_apply(a: list[list[int]], vector: list[int]) -> list[int]:
    return [sum(value * coordinate for value, coordinate in zip(row, vector)) for row in a]


def math_input(index: int) -> list[int]:
    values = [2, -1, 3, 5, -4]
    return [value + ((index * 3 + axis) % 7) - 3 for axis, value in enumerate(values)]


def math_requests(steps: int) -> tuple[list[dict[str, object]], list[str]]:
    l5 = c5_laplacian()
    requests = [
        request(MATH_OPERATION, operation="construct-linear", coefficients=matrix_wire(l5)),
        request(MATH_OPERATION, operation="power", operator=0, exponent=16),
        request(
            MATH_OPERATION,
            operation="apply",
            operator=1,
            left=[rat(value) for value in [0, 0, 0, 0, 0]],
            retain_product=False,
        ),
    ]
    labels = ["construct", "power", "warmup"]
    for index in range(steps):
        current = math_input(index)
        requests.append(
            request(
                MATH_OPERATION,
                operation="apply",
                operator=1,
                left=[rat(value) for value in current],
                retain_product=index == 0,
            )
        )
        labels.append("apply")
    requests.append(
        request(MATH_OPERATION, operation="read-product", operator=1, product=0)
    )
    labels.append("readout")
    return requests, labels


def wave_requests(steps: int) -> tuple[list[dict[str, object]], list[str]]:
    requests = [request("receive-next-symbol", text="a")]
    requests.extend(
        request("receive-next-symbol", text="a" if index % 2 == 0 else "b")
        for index in range(steps)
    )
    return requests, ["warmup"] + ["state-update"] * steps


def line_events(stdout: str) -> list[dict[str, object]]:
    return [json.loads(line) for line in stdout.splitlines() if line.strip()]


def receipt(stderr: str) -> dict[str, object]:
    for line in reversed(stderr.splitlines()):
        if line.strip():
            return json.loads(line)
    raise RuntimeError("native process returned no receipt")


def percentile(values: list[int], numerator: int, denominator: int) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    rank = max(1, (len(ordered) * numerator + denominator - 1) // denominator)
    return ordered[rank - 1]


def latency_summary(values: list[int], stall_deadline_ns: int | None = None) -> dict[str, object]:
    if not values:
        return {"count": 0, "unit": "nanoseconds", "percentiles": {}}
    p50 = percentile(values, 50, 100)
    p95 = percentile(values, 95, 100)
    p99 = percentile(values, 99, 100)
    return {
        "count": len(values),
        "unit": "nanoseconds",
        "percentiles": {"p50": p50, "p95": p95, "p99": p99, "max": max(values)},
        "tail_scope": "requests at or above empirical p95 are reported as tail observations",
        "tail_count_at_or_above_p95": sum(value >= p95 for value in values),
        "stall_scope": "explicit deadline only; no scheduler attribution",
        "stall_deadline_ns": stall_deadline_ns,
        "stall_count": None if stall_deadline_ns is None else sum(value >= stall_deadline_ns for value in values),
    }


def rate(count: int, elapsed_ns: int, unit: str) -> dict[str, str]:
    if elapsed_ns <= 0:
        raise ValueError("rate requires positive elapsed nanoseconds")
    value = Fraction(count * 1_000_000_000, elapsed_ns)
    return {"numerator": str(value.numerator), "denominator": str(value.denominator), "unit": unit}


def selected_samples(values: list[int], labels: list[str], selected: str) -> list[int]:
    if len(values) != len(labels):
        raise ValueError("samples and labels must have equal lengths")
    return [value for value, label in zip(values, labels) if label == selected]


def validate_math_events(
    events: list[dict[str, object]], labels: list[str], measured_steps: int
) -> dict[str, object]:
    if len(events) != len(labels):
        raise AssertionError(f"mathematical event count {len(events)} != labels {len(labels)}")
    values = []
    for event, label in zip(events, labels):
        if event.get("event") != "mathematical-return":
            raise AssertionError(f"mathematical {label} was not returned: {event}")
        value = event.get("value")
        if not isinstance(value, dict):
            raise AssertionError(f"mathematical {label} has no value")
        values.append(value)
    if values[0].get("status") != "constructed" or values[1].get("status") != "constructed":
        raise AssertionError("C5 construction/Power did not complete")
    l16 = matrix_power(c5_laplacian(), 16)
    expected_outputs: list[list[int]] = []
    actual_outputs: list[list[int]] = []
    for index, (value, label) in enumerate(zip(values, labels)):
        if label not in ("warmup", "apply"):
            continue
        if value.get("status") != "applied":
            raise AssertionError(f"C5 {label} did not apply: {value}")
        output = [Fraction(int(item["numerator"]), int(item["denominator"]))
                  for item in value.get("output", [])]
        expected = [0] * 5 if label == "warmup" else vector_apply(l16, math_input(index - 3))
        if output != expected:
            raise AssertionError(f"C5 {label} output mismatch: {output} != {expected}")
        actual_outputs.append([int(coordinate) for coordinate in output])
        expected_outputs.append(expected)
    if labels.count("apply") != measured_steps:
        raise AssertionError("requested measured C5 apply count was not represented")
    if values[-1].get("status") != "read":
        raise AssertionError("C5 readout did not complete")
    readback = [Fraction(int(item["numerator"]), int(item["denominator"]))
                for item in values[-1].get("output", [])]
    if readback != expected_outputs[1]:
        raise AssertionError("retained first C5 product differs on readback")
    return {
        "actual_outputs": actual_outputs,
        "expected_outputs": expected_outputs,
        "measured_apply_count": labels.count("apply"),
        "warmup_count": labels.count("warmup"),
    }


def validate_wave_events(events: list[dict[str, object]], labels: list[str], measured_steps: int) -> dict[str, object]:
    if len(events) != len(labels):
        raise AssertionError(f"wave event count {len(events)} != labels {len(labels)}")
    committed = []
    for event, label in zip(events, labels):
        if event.get("event") != "next-symbol-received":
            raise AssertionError(f"wave {label} was not returned: {event}")
        value = event.get("value", {})
        if value.get("observation_committed") is not True:
            raise AssertionError(f"wave {label} was not committed: {event}")
        committed.append(value)
    if labels.count("state-update") != measured_steps:
        raise AssertionError("requested measured wave update count was not represented")
    return {
        "committed_epochs": [value.get("epoch") for value in committed],
        "measured_update_count": labels.count("state-update"),
        "warmup_count": labels.count("warmup"),
    }


def clock_info() -> dict[str, object]:
    clock = time.get_clock_info("perf_counter")
    resolution = Fraction(str(clock.resolution)) * 1_000_000_000
    return {
        "name": clock.implementation,
        "monotonic": clock.monotonic,
        "adjustable": clock.adjustable,
        "resolution_ns": {"numerator": str(resolution.numerator), "denominator": str(resolution.denominator)},
    }


def binary_sha256(binary: Path) -> str:
    digest = hashlib.sha256()
    with binary.open("rb") as handle:
        for block in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def workstation_snapshot() -> dict[str, object]:
    snapshot: dict[str, object] = {}
    try:
        load = Path("/proc/loadavg").read_text().split()
        snapshot["load_average"] = load[:3]
    except FileNotFoundError:
        pass
    temperatures: dict[str, int] = {}
    for path in sorted(Path("/sys/class/thermal").glob("thermal_zone*/temp")):
        try:
            temperatures[path.parent.name] = int(path.read_text().strip())
        except (OSError, ValueError):
            continue
    if temperatures:
        snapshot["thermal_millidegrees_celsius"] = temperatures
    try:
        gpu = subprocess.run(
            ["nvidia-smi", "--query-gpu=temperature.gpu", "--format=csv,noheader,nounits"],
            capture_output=True,
            text=True,
            check=False,
            timeout=5,
        )
        if gpu.returncode == 0 and gpu.stdout.strip():
            snapshot["gpu_temperature_celsius"] = [int(value.strip()) for value in gpu.stdout.splitlines()]
    except (FileNotFoundError, subprocess.TimeoutExpired, ValueError):
        pass
    return snapshot


def host_info(binary: Path) -> dict[str, object]:
    info: dict[str, object] = {
        "declared": {
            "cpu": "AMD Ryzen 9 7900X",
            "ram": "32 GB",
            "gpu": "NVIDIA RTX 4080 SUPER 16 GB",
            "ssd_read": "7300 MB/s",
            "ssd_write": "6300 MB/s",
        },
        "observed": {"platform": platform.platform()},
        "binary": {"path": str(binary), "sha256": binary_sha256(binary)},
    }
    try:
        revision = subprocess.run(
            ["git", "rev-parse", "HEAD"], capture_output=True, text=True, check=True
        ).stdout.strip()
        info["source_revision"] = revision
    except (OSError, subprocess.CalledProcessError):
        pass
    try:
        info["observed"]["cpu_model"] = next(
            line.split(":", 1)[1].strip()
            for line in Path("/proc/cpuinfo").read_text().splitlines()
            if line.lower().startswith("model name")
        )
    except (FileNotFoundError, StopIteration):
        pass
    try:
        memory = next(
            line.split()[1]
            for line in Path("/proc/meminfo").read_text().splitlines()
            if line.startswith("MemTotal:")
        )
        info["observed"]["memory_kib"] = int(memory)
    except (FileNotFoundError, StopIteration, ValueError):
        pass
    try:
        gpu = subprocess.run(
            ["nvidia-smi", "--query-gpu=name,memory.total", "--format=csv,noheader"],
            capture_output=True,
            text=True,
            check=False,
            timeout=5,
        )
        if gpu.returncode == 0 and gpu.stdout.strip():
            info["observed"]["gpu"] = gpu.stdout.strip()
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pass
    return info


def interactive(
    binary: Path,
    mode: str,
    source: Path | None,
    requests: list[dict[str, object]],
    labels: list[str],
    checkpoint: Path,
) -> dict[str, object]:
    command = [str(binary), "hna"]
    if mode == "math":
        command += ["mathematical-session", "--input", "-"]
    else:
        command += ["wave-session", str(source), "--seed", "--input", "-", "--checkpoint", str(checkpoint)]
    process_start = time.perf_counter_ns()
    child = subprocess.Popen(command, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    roundtrips: list[int] = []
    events: list[dict[str, object]] = []
    assert child.stdin and child.stdout and child.stderr
    for payload, label in zip(requests, labels):
        start = time.perf_counter_ns()
        child.stdin.write((json.dumps(payload, separators=(",", ":")) + "\n").encode())
        child.stdin.flush()
        line = child.stdout.readline()
        roundtrips.append(time.perf_counter_ns() - start)
        if not line:
            raise RuntimeError(f"{mode} process ended during {label}")
        events.append(json.loads(line))
    child.stdin.close()
    stdout_tail = child.stdout.read()
    stderr = child.stderr.read().decode()
    child.wait()
    if stdout_tail.strip():
        events.extend(line_events(stdout_tail.decode()))
    if child.returncode:
        raise RuntimeError(f"{mode} process failed: {stderr}")
    return {
        "events": events,
        "receipt": receipt(stderr),
        "process_wall_ns": time.perf_counter_ns() - process_start,
        "roundtrips_ns": roundtrips,
    }


def cold_run(
    binary: Path,
    mode: str,
    source: Path | None,
    requests: list[dict[str, object]],
    checkpoint: Path,
) -> dict[str, object]:
    if mode == "math":
        command = [str(binary), "hna", "mathematical-session", "--input", "-"]
    else:
        command = [str(binary), "hna", "wave-session", str(source), "--seed", "--input", "-", "--checkpoint", str(checkpoint)]
    payload = "\n".join(json.dumps(item, separators=(",", ":")) for item in requests) + "\n"
    completed, wall, resources = measured_process(command, payload)
    if completed.returncode:
        raise RuntimeError(f"cold {mode} process failed: {completed.stderr}")
    return {"wall_ns": wall, "events": line_events(completed.stdout), "receipt": receipt(completed.stderr),
            "process_resources": resources}


def measured_process(command: list[str], payload: str | None = None):
    """One fresh Unix observer waits for one child and reads its resource return.

    Isolating RUSAGE_CHILDREN per wrapper avoids the parent's cumulative RSS maximum.
    Decimal CPU seconds are observer measurements, not exact semantic coefficients.
    """
    with tempfile.TemporaryDirectory(prefix="holonics-resource-") as temporary:
        output = Path(temporary) / "time.json"
        observer = """
import json, resource, subprocess, sys, time
from pathlib import Path
start = time.perf_counter_ns()
child = subprocess.run(sys.argv[2:])
elapsed = time.perf_counter_ns() - start
r = resource.getrusage(resource.RUSAGE_CHILDREN)
Path(sys.argv[1]).write_text(json.dumps({
    'child_wall_ns': elapsed,
    'user_seconds': r.ru_utime, 'system_seconds': r.ru_stime,
    'max_rss_kib': r.ru_maxrss, 'major_page_faults': r.ru_majflt,
    'minor_page_faults': r.ru_minflt, 'voluntary_context_switches': r.ru_nvcsw,
    'involuntary_context_switches': r.ru_nivcsw}))
sys.exit(child.returncode)
"""
        actual = [sys.executable, "-c", observer, str(output), *command]
        start = time.perf_counter_ns()
        completed = subprocess.run(actual, input=payload, capture_output=True, text=True, check=False)
        wall = time.perf_counter_ns() - start
        resources = json.loads(output.read_text()) if output.exists() else None
        return completed, wall, resources


def cold_summary(runs: list[dict[str, object]], mode: str, labels: list[str]) -> dict[str, object]:
    walls = [int(run["wall_ns"]) for run in runs]
    if mode == "math":
        validations = [validate_math_events(run["events"], labels, labels.count("apply")) for run in runs]
        count = sum(int(item["measured_apply_count"]) for item in validations)
        return {
            "latency": latency_summary(walls),
            "rates": {"end_to_end_delivered_faces": rate(count, sum(walls), "faces/second")},
            "samples_unit": "nanoseconds/process",
            "samples": walls,
            "process_resources": [run["process_resources"] for run in runs],
            "raw": {
                "labels": labels,
                "actual_outputs": [output for item in validations for output in item["actual_outputs"]],
                "expected_outputs": [output for item in validations for output in item["expected_outputs"]],
            },
            "scope": "construct + Power(C5,16) + warmup + one resident apply in each fresh process",
        }
    validations = [validate_wave_events(run["events"], labels, labels.count("state-update")) for run in runs]
    count = sum(int(item["measured_update_count"]) for item in validations)
    return {
        "latency": latency_summary(walls),
        "rates": {"end_to_end_completed_state_updates": rate(count, sum(walls), "state-updates/second")},
        "samples_unit": "nanoseconds/process",
        "samples": walls,
        "process_resources": [run["process_resources"] for run in runs],
        "raw": {
            "labels": labels,
            "committed_epochs": [epoch for item in validations for epoch in item["committed_epochs"]],
        },
        "scope": "seed + warmup + one receive-next-symbol in each fresh process",
    }


def process_metrics(run: dict[str, object], mode: str, labels: list[str]) -> dict[str, object]:
    events = run["events"]
    process_receipt = run["receipt"]
    if mode == "math":
        validation = validate_math_events(events, labels, labels.count("apply"))
        steady_roundtrips = selected_samples(run.get("roundtrips_ns", []), labels, "apply")
        values = [event["value"] for event in events]
        apply_values = [value for value, label in zip(values, labels) if label == "apply"]
        readouts = [value for value, label in zip(values, labels) if label == "readout"]
        request_us = [int(value["cost"]["elapsed_microseconds"]) for value in values if "cost" in value]
        apply_us = [int(value["cost"]["elapsed_microseconds"]) for value in apply_values]
        readout_us = [int(value["cost"]["elapsed_microseconds"]) for value in readouts]
        census = process_receipt["inspect"]["census"]
        constructed = {
            label: value
            for value, label in zip(values, labels)
            if label in ("construct", "power")
        }
        return {
            "delivered_faces": len(apply_values),
            "completed_state_updates": None,
            "latency": latency_summary(steady_roundtrips),
            "boundary_latencies": {label: latency_summary(selected_samples(run["roundtrips_ns"], labels, label))
                                   for label in ("construct", "power", "warmup", "readout")},
            "rates": {
                "steady_delivered_faces": rate(len(apply_values), sum(steady_roundtrips), "faces/second"),
                "end_to_end_delivered_faces": rate(len(apply_values), run["process_wall_ns"], "faces/second"),
            },
            "partition": {
                "process_wall_ns": run.get("process_wall_ns"),
                "receipt_elapsed_microseconds": process_receipt.get("elapsed_microseconds"),
                "request_cost_microseconds": sum(request_us),
                "apply_request_cost_microseconds": sum(apply_us),
                "readout_cost_microseconds": sum(readout_us),
                "receipt_minus_request_cost_microseconds": int(process_receipt.get("elapsed_microseconds", 0)) - sum(request_us),
                "process_wall_minus_receipt_nanoseconds": int(run.get("process_wall_ns", 0)) - int(process_receipt.get("elapsed_microseconds", 0)) * 1000,
            },
            "memory_transfer": {key: census.get(key) for key in ("resident_octets_now", "resident_octets_peak", "ingress_octets", "egress_receipt_octets", "egress_section_octets")},
            "exact_work": {
                "construct_rank_factorization": constructed["construct"].get("construction_work"),
                "power_source_reconstruction": constructed["power"].get("source_reconstruction_work"),
                "power_minimal_polynomial": constructed["power"].get("power_construction_work"),
                "power_rank_factorization": constructed["power"].get("construction_work"),
                "unit": "ExactWork coordinate vectors; integer counts and exact bit widths",
            },
            "raw": {
                "roundtrips_ns": run.get("roundtrips_ns", []),
                "labels": labels,
                "actual_outputs": validation["actual_outputs"],
                "expected_outputs": validation["expected_outputs"],
                "events": events,
            },
            "native_census": census,
            "scope": "apply returns one exact delivered face; apply does not claim a continuing state update",
        }
    validation = validate_wave_events(events, labels, labels.count("state-update"))
    steady_roundtrips = selected_samples(run.get("roundtrips_ns", []), labels, "state-update")
    updates = [
        event
        for event, label in zip(events, labels)
        if label == "state-update"
        and event.get("event") == "next-symbol-received"
        and event.get("value", {}).get("observation_committed") is True
    ]
    receipt_elapsed = int(process_receipt.get("epochs", {}).get("after", 0)) - int(process_receipt.get("epochs", {}).get("before", 0))
    inspect = process_receipt.get("inspect", {})
    return {
        "delivered_faces": len(updates),
        "completed_state_updates": len(updates),
        "latency": latency_summary(steady_roundtrips),
        "setup_and_warmup_latency": latency_summary(
            [dt for dt, label in zip(run.get("roundtrips_ns", []), labels) if label != "state-update"]
        ),
        "rates": {
            "steady_completed_state_updates": rate(len(updates), sum(steady_roundtrips), "state-updates/second"),
            "end_to_end_completed_state_updates": rate(len(updates), run["process_wall_ns"], "state-updates/second"),
        },
        "partition": {
            "process_wall_ns": run.get("process_wall_ns"),
            "receipt_epoch_before": process_receipt.get("epochs", {}).get("before"),
            "receipt_epoch_after": process_receipt.get("epochs", {}).get("after"),
            "receipt_elapsed_microseconds": None,
            "native_epoch_delta": receipt_elapsed,
            "process_wall_is_end_to_end_with_setup_and_transport": True,
        },
        "memory_transfer": {"status": "not exposed by the current wave process receipt"},
        "native_census": inspect,
        "raw": {
            "roundtrips_ns": run.get("roundtrips_ns", []),
            "labels": labels,
            "committed_epochs": validation["committed_epochs"],
            "events": events,
        },
        "scope": "receive-next-symbol returns one committed native observation and state update",
    }


def code_cost(binary: Path, runs: int) -> dict[str, object]:
    executable = binary.parent / "examples" / "receiver_code_cost"
    samples: list[int] = []
    resource_samples = []
    last: dict[str, object] | None = None
    for _ in range(runs):
        completed, wall, resources = measured_process([str(executable)])
        completed.check_returncode()
        samples.append(wall)
        resource_samples.append(resources)
        last = json.loads(completed.stdout)
    assert last is not None
    return {
        "runs": runs,
        "latency": latency_summary(samples),
        "samples_unit": "nanoseconds/process",
        "samples": samples,
        "process_resources": resource_samples,
        "binary": {"path": str(executable), "sha256": binary_sha256(executable)},
        "metrics": {
            "cross_entropy_bits_form": last["zeta_information"]["cross_entropy_bits"],
            "entropy_bits_per_step_form": last["stationary_entropy_bits_per_step"],
            "cost_units_per_step_form": last["stationary_cost_per_step"],
            "checked_histories": last["checked_histories"],
        },
        "units": {"cross_entropy": "bits (exact symbolic log2 form)", "stationary_entropy": "bits/step (exact symbolic form)", "stationary_cost": "declared dimensionless cost units/step; not bits"},
        "scope": last["scope"],
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--binary", type=Path, default=Path("target/debug/holonics"))
    parser.add_argument("--out-dir", type=Path, default=Path("research/experiments/native_performance_benchmark"))
    parser.add_argument("--warm-steps", type=int, default=128)
    parser.add_argument("--cold-runs", type=int, default=8)
    parser.add_argument("--code-runs", type=int, default=8)
    args = parser.parse_args()
    if min(args.warm_steps, args.cold_runs, args.code_runs) <= 0:
        raise SystemExit("all workload apertures must be positive")
    args.out_dir.mkdir(parents=True, exist_ok=True)
    suite_start = time.perf_counter_ns()
    co_load_before = workstation_snapshot()
    wave_seed = args.out_dir / "wave-seed.json"
    wave_seed.write_text(json.dumps({"schema": "org.holonics.hna.applied-wave-seed.v1", "symbols": ["a", "b"], "seed": "ab", "grain": 64}) + "\n")

    math_warm_requests, math_labels = math_requests(args.warm_steps)
    wave_warm_requests, wave_labels = wave_requests(args.warm_steps)
    with tempfile.TemporaryDirectory(prefix="holonics-bench-") as temporary:
        temp = Path(temporary)
        math_warm = interactive(args.binary, "math", None, math_warm_requests, math_labels, temp / "math.checkpoint")
        validate_math_events(math_warm["events"], math_labels, args.warm_steps)
        wave_warm = interactive(args.binary, "wave", wave_seed, wave_warm_requests, wave_labels, temp / "wave.checkpoint")
        validate_wave_events(wave_warm["events"], wave_labels, args.warm_steps)
        math_cold = []
        wave_cold = []
        for index in range(args.cold_runs):
            cold_requests, cold_labels = math_requests(1)
            math_cold.append(cold_run(args.binary, "math", None, cold_requests, temp / f"math-{index}.checkpoint"))
            validate_math_events(math_cold[-1]["events"], cold_labels, 1)
            cold_requests, cold_labels = wave_requests(1)
            wave_cold.append(cold_run(args.binary, "wave", wave_seed, cold_requests, temp / f"wave-{index}.checkpoint"))
            validate_wave_events(wave_cold[-1]["events"], cold_labels, 1)
    code_result = code_cost(args.binary, args.code_runs)
    co_load_after = workstation_snapshot()
    result = {
        "schema": "org.holonics.performance-benchmark.v1",
        "host": host_info(args.binary),
        "clock": clock_info(),
        "co_load_snapshot": {"before": co_load_before, "after": co_load_after},
        "aperture": {"warm_steps_per_session": args.warm_steps, "cold_process_runs": args.cold_runs, "code_cost_process_runs": args.code_runs},
        "workloads": {
            "mathematical_c5_power_apply": {
                "warm": process_metrics(math_warm, "math", math_labels),
                "cold": cold_summary(math_cold, "math", math_requests(1)[1]),
            },
            "wave_receive_next_symbol": {
                "warm": process_metrics(wave_warm, "wave", wave_labels),
                "cold": cold_summary(wave_cold, "wave", wave_requests(1)[1]),
            },
            "receiver_code_cost": code_result,
        },
        "measurement_contract": {
            "clock": "integer monotonic nanoseconds from Python perf_counter_ns; no float conversion",
            "rate": "exact rational count per elapsed second; numerator/denominator retained; nonpositive elapsed time is an error",
            "warm_scope": "one native process with explicit setup and one warmup request; steady samples exclude setup/warmup and end-to-end rates include them",
            "cold_scope": "fresh process per sample; includes process and native setup",
            "partition": "request ExactWork/cost, process receipt and census are retained; subtraction fields are residual estimates, not independent clocks",
            "state_update": "counted only where the native receive return declares observation_committed=true",
            "stall": "null unless an explicit deadline is supplied; p95/p99 are latency tails, not stall attribution",
            "semantic_boundary": "rates and code/cross-entropy faces characterize declared workloads and do not establish usefulness, intelligence, physical power, or model quality",
            "storage": "SSD values are the supplied device ratings; no separate disk-throughput test is part of this native workload benchmark",
            "co_load": "before/after load averages and GPU temperature are ordinary workstation snapshots; timings are not isolated machine calibration",
            "process_resources": "fresh Unix observer per cold/code child; RUSAGE_CHILDREN CPU seconds and peak RSS (Linux KiB), child wall plus outer wrapper wall; native payload peak is not process/GPU memory peak",
        },
    }
    result["suite_elapsed_ns"] = time.perf_counter_ns() - suite_start
    (args.out_dir / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
