"""Bounded native output forks. No training, targets, shell, remote model or fallback.

Plan, executable, checkpoint, prompts and keys are SHA-pinned before any child.
Every arm gets a durable terminal receipt in canonical order, including refusal or
deadline. ALL_ARMS_TERMINAL is never a success claim for missing/incomplete output.
"""
import hashlib
import ctypes
import json
import os
from pathlib import Path
import re
import resource
import signal
import subprocess
import sys
import time


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def pins_valid(plan_path, plan_sha, pins):
    try:
        return sha(plan_path) == plan_sha and all(sha(pin["path"]) == pin["sha256"] for pin in pins)
    except OSError:
        return False


def successful(stop, results, all_pins_valid):
    return stop is None and all_pins_valid and bool(results) and all(record["complete"] for record in results)


def durable(path, value):
    data = (json.dumps(value, indent=2) + "\n").encode()
    with path.open("xb") as file:
        file.write(data)
        file.flush()
        os.fsync(file.fileno())
    fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def execute(plan_path, plan_sha, output):
    assert sha(plan_path) == plan_sha, "plan digest"
    plan = json.loads(Path(plan_path).read_text())
    assert plan["workers"] in (1, 4)
    assert plan["cells"] in (128, 512)
    assert 0 < plan["deadline_ns"] <= 3_600_000_000_000
    assert plan["aggregate_host_bytes"] == 8 * 1024**3
    assert plan["aggregate_cpus"] == 4
    assert 0 < len(plan["arms"]) <= 16
    identities = [arm["id"] for arm in plan["arms"]]
    assert len(set(identities)) == len(identities)
    assert all(re.fullmatch(r"[a-z0-9-]{1,40}", name) for name in identities)
    assert all(arm["policy"] in ("native", "native-zero-M", "native-context-zero", "founding-R", "tree") for arm in plan["arms"])
    pins = [plan["binary"], plan["checkpoint"], plan["keys"],
            {"path": str(Path(__file__).resolve()), "sha256": plan["controller_sha256"]}] + [arm["prompt"] for arm in plan["arms"]]

    def integrity():
        return pins_valid(plan_path, plan_sha, pins)

    assert integrity(), "input or executable digest"
    output = Path(output)
    output.mkdir()
    cpus = sorted(os.sched_getaffinity(0))[:4]
    assert len(cpus) == 4
    os.sched_setaffinity(0, cpus)
    resource.setrlimit(resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3))
    start = time.monotonic_ns()
    running = {}
    results = {}
    samples = []
    next_arm = 0
    stop = None
    controller_pid = os.getpid()

    def limits():
        # Owned native processes must not outlive a killed controller. This is
        # per-child lifecycle cleanup, not a machine/driver/security setting.
        if ctypes.CDLL(None).prctl(1, signal.SIGKILL, 0, 0, 0) != 0:
            raise OSError("PR_SET_PDEATHSIG")
        if os.getppid() != controller_pid:
            os.kill(os.getpid(), signal.SIGKILL)
        os.sched_setaffinity(0, cpus)
        resource.setrlimit(resource.RLIMIT_AS, (8 * 1024**3, 8 * 1024**3))

    def own(pid):
        try:
            return os.getpgid(pid) in running
        except ProcessLookupError:
            return False

    def finish(pid, forced=None):
        process, index, log, opened = running[pid]
        process.wait()
        try:
            os.killpg(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        log.flush()
        os.fsync(log.fileno())
        log.close()
        arm = plan["arms"][index]
        folder = output / arm["id"]
        # A killed child's flush is not a durability claim. Seal its own partial
        # output/progress bytes before writing the durable terminal receipt.
        if folder.exists():
            for artifact in folder.rglob("*"):
                if artifact.is_file():
                    with artifact.open("rb") as file:
                        os.fsync(file.fileno())
        record = {"index": index, "id": arm["id"], "policy": arm["policy"],
                  "prompt_sha256": arm["prompt"]["sha256"], "checkpoint_sha256": plan["checkpoint"]["sha256"],
                  "binary_sha256": plan["binary"]["sha256"], "exit": process.returncode,
                  "elapsed_ns": time.monotonic_ns() - opened, "stop": forced,
                  "complete": False, "terminal": True}
        manifest = folder / "OUTPUT.json"
        try:
            if manifest.exists():
                reading = json.loads(manifest.read_text())
                assert reading["output_cells_requested"] == plan["cells"]
                assert reading["prompt_sha256"] == arm["prompt"]["sha256"]
                assert reading["key_schedule_sha256"] == plan["keys"]["sha256"]
                assert reading["actual_rayon_workers"] == 1
                frozen = json.loads((folder / "FROZEN_MATERIAL.json").read_text())
                assert frozen["native_laws_unchanged"] and frozen["empirical_material_unchanged"]
                if arm["policy"] == "native-zero-M" and Path(arm["prompt"]["path"]).stat().st_size:
                    first = json.loads((folder / "CONDITIONING_FIRST.json").read_text())
                    assert first["mode"] == "ForecastZeroControl" and first["added_and_work_zero"]
                record.update({"output_sha256": sha(folder / "OUTPUT.bin"),
                               "output_manifest_sha256": sha(manifest), "cells": len(reading["classes"]),
                               "native_stop": reading["stop"], "final_state_sha256": reading["final_state_sha256"],
                               "final_crib_sha256": reading["final_crib_sha256"],
                               "cold_continuation": reading["cold_continuation"]})
                record["complete"] = process.returncode == 0 and forced is None and reading["stop"] == "DeclaredLength" and len(reading["classes"]) == plan["cells"]
            else:
                progress = folder / "classes.jsonl"
                record["durable_progress_lines"] = len(progress.read_text().splitlines()) if progress.exists() else 0
        except (OSError, ValueError, KeyError, AssertionError) as error:
            record["complete"] = False
            record["output_manifest_refusal"] = f"{type(error).__name__}:{error}"
        remaining=[]
        for child in Path("/proc").glob("[0-9]*"):
            try:
                if os.getpgid(int(child.name)) == pid:
                    state=next((line for line in child.joinpath("status").read_text().splitlines() if line.startswith("State:")),"")
                    if "Z (zombie)" not in state:
                        remaining.append(int(child.name))
            except (OSError,ValueError):
                pass
        record["owned_cleanup_remaining"] = remaining
        record["complete"] = record["complete"] and not remaining
        durable(output / f"attempt-{index:02}.json", record)
        results[index] = record
        del running[pid]

    try:
        while next_arm < len(plan["arms"]) or running:
            while not stop and next_arm < len(plan["arms"]) and len(running) < plan["workers"]:
                assert integrity(), "integrity before child"
                arm = plan["arms"][next_arm]
                command = "sample-prepared-retained-512-v1" if plan["cells"] == 512 else "sample-prepared-retained-fibre-v1"
                args = [plan["binary"]["path"], "complete-language", command, "host-reference",
                        plan["checkpoint"]["path"], arm["prompt"]["path"], arm["prompt"]["sha256"],
                        plan["keys"]["path"], plan["keys"]["sha256"], arm["policy"],
                        "cold-replay" if arm["cold"] else "no-replay", str(output / arm["id"])]
                log = (output / f"child-{next_arm:02}.log").open("xb")
                env = dict(os.environ, RAYON_NUM_THREADS="1")
                process = subprocess.Popen(args, stdout=log, stderr=subprocess.STDOUT, env=env,
                                           preexec_fn=limits, start_new_session=True)
                running[process.pid] = (process, next_arm, log, time.monotonic_ns())
                next_arm += 1
            for pid, (process, _, _, _) in list(running.items()):
                if process.poll() is not None:
                    finish(pid)
                    if not integrity():
                        stop = "integrity_after_child"
            rss = 0
            owned = []
            for status in Path("/proc").glob("[0-9]*/status"):
                try:
                    pid = int(status.parent.name)
                    if own(pid) or pid == os.getpid():
                        owned.append(pid)
                        rss += sum(int(line.split()[1]) * 1024 for line in status.read_text().splitlines() if line.startswith("VmRSS:"))
                except (OSError, ValueError):
                    pass
            elapsed = time.monotonic_ns() - start
            samples.append({"elapsed_ns": elapsed, "aggregate_rss_bytes": rss, "active_forks": len(running)})
            if elapsed >= plan["deadline_ns"]:
                stop = "shared_elapsed_deadline"
            if rss > plan["aggregate_host_bytes"]:
                stop = "aggregate_memory_limit"
            if sum(path.stat().st_size for path in output.glob("child-*.log")) > 64 * 1024**2:
                stop = "aggregate_log_limit"
            if sum(path.stat().st_size for path in output.rglob("*") if path.is_file()) > 512 * 1024**2:
                stop = "output_disk_limit"
            if any(record.get("owned_cleanup_remaining") for record in results.values()):
                stop = "owned_cleanup_incomplete"
            if stop:
                break
            time.sleep(0.1)
    except Exception as error:
        stop = f"controller_refusal:{type(error).__name__}:{error}"
    finally:
        for pid in list(running):
            try:
                os.killpg(pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            finish(pid, stop or "owned_cleanup")
        for index in range(next_arm, len(plan["arms"])):
            record = {"index": index, "id": plan["arms"][index]["id"], "terminal": True,
                      "complete": False, "stop": stop or "not_started"}
            durable(output / f"attempt-{index:02}.json", record)
            results[index] = record
    final_integrity = integrity()
    if not final_integrity:
        stop = stop or "integrity_final"
    cpu = os.times()
    manifest = {"plan_sha256": plan_sha, "cells": plan["cells"], "workers": plan["workers"],
                "canonical_order": identities, "results": [results[index] for index in range(len(identities))],
                "all_terminal": True, "all_complete": successful(stop, list(results.values()), final_integrity),
                "final_integrity_all_pins": final_integrity,
                "elapsed_ns": time.monotonic_ns() - start, "stop": stop,
                "original_checkpoint_immutable": sha(plan["checkpoint"]["path"]) == plan["checkpoint"]["sha256"],
                "aggregate_cpu_affinity": cpus, "rayon_workers_per_child": 1,
                "controller_and_child_CPU_seconds_OS_reading": {
                    "controller_user": cpu.user, "controller_system": cpu.system,
                    "children_user": cpu.children_user, "children_system": cpu.children_system},
                "peak_aggregate_rss_bytes": max((sample["aggregate_rss_bytes"] for sample in samples), default=0),
                "samples": samples, "targets_or_scorer_opened": False}
    durable(output / "ALL_ARMS_TERMINAL.json", manifest)
    print(json.dumps({key: value for key, value in manifest.items() if key not in ("samples", "results")}), flush=True)
    return manifest


if __name__ == "__main__":
    result = execute(*sys.argv[1:])
    sys.exit(0 if result["all_complete"] and result["final_integrity_all_pins"] else 1)
