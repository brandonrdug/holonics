"""Exclusive device0 training phase, using the existing host executor context.

The caller owns the fixed absolute phase deadline and aggregate process controller.
Graphics activity is permitted; a foreign compute process refuses/stops only this
owned training process group. The project lock is released before host evaluation.
"""
import fcntl
import json
import os
from pathlib import Path
import signal
import subprocess
import time


def compute_apps():
    result = subprocess.run(["nvidia-smi", "--id=0", "--query-compute-apps=pid,used_memory",
        "--format=csv,noheader,nounits"], capture_output=True, text=True, timeout=2)
    if result.returncode:
        raise RuntimeError("host device0 compute visibility failed: " + result.stdout + result.stderr)
    rows = []
    for line in result.stdout.splitlines():
        if line.strip():
            pid, memory = line.split(",")
            if not memory.strip().isdigit():
                raise RuntimeError("device0 compute memory is unresolved")
            rows.append({"pid": int(pid.strip()), "memory_MiB": int(memory.strip())})
    return rows


def classify(rows, group, get_group=os.getpgid):
    own, foreign = [], []
    for row in rows:
        try:
            (own if get_group(row["pid"]) == group else foreign).append(row)
        except ProcessLookupError:
            pass  # A process that has actually exited no longer owns a live context.
    return own, foreign


def verify_card_receipt(receipt):
    if (receipt.get("backend") != "cuda-observed-epoch-device0" or
        receipt.get("device_ordinal") != 0 or receipt.get("host_fallback") is not False or
        receipt.get("completed") is not True or
        any(type(receipt.get(key)) is not int or receipt[key] <= 0 for key in
            ("successful_card_forwards", "successful_retained_card_returns", "successful_card_aggregates"))):
        raise ValueError("missing actual successful card dispatch/retained return/statistics receipt")


def run_gpu_training(argv, log, deadline_ns, guard, rayon_threads=4):
    if guard.get("device_ordinal") != 0 or guard.get("own_sampled_memory_limit_MiB") not in (2048, 8192):
        raise ValueError("fixed device0 and declared sampled GPU ceiling required; CODE2GiB or proposed model8GiB")
    if guard.get("graphics_allowed") is not True or guard.get("foreign_compute_allowed") is not False:
        raise ValueError("display/compute access-context declaration mismatch")
    record = {"device_ordinal": 0, "graphics_allowed": True, "host_fallback": False,
              "samples": [], "cleanup_owner": "outer fixed native controller"}
    process = None
    failure = None
    lock_path = Path(guard["project_lock"])
    with lock_path.open("a+") as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        try:
            if time.monotonic_ns() >= deadline_ns:
                raise TimeoutError("fixed training deadline before GPU visibility check")
            record["pre_compute"] = compute_apps()
            if record["pre_compute"]:
                raise RuntimeError("foreign CUDA compute workload; no training child started")
            with Path(log).open("xb") as stream:
                env = dict(os.environ, RAYON_NUM_THREADS=str(rayon_threads),
                           CUDA_PATH="/opt/cuda", NVCC="/opt/cuda/bin/nvcc")
                process = subprocess.Popen(argv, stdout=stream, stderr=subprocess.STDOUT,
                                           start_new_session=True, env=env)
                while process.poll() is None:
                    if time.monotonic_ns() >= deadline_ns:
                        raise TimeoutError("fixed GPU-assisted training phase deadline; no extension")
                    own, foreign = classify(compute_apps(), process.pid)
                    memory = sum(row["memory_MiB"] for row in own)
                    record["samples"].append({"monotonic_ns": time.monotonic_ns(),
                        "own_compute": own, "foreign_compute": foreign, "own_memory_MiB": memory})
                    if foreign or memory > guard["own_sampled_memory_limit_MiB"]:
                        raise RuntimeError("foreign compute or owned sampled GPU-memory ceiling")
                    time.sleep(.5)
                record["exit"] = process.returncode
                if process.returncode:
                    raise RuntimeError(f"selected CUDA training exited {process.returncode}; no host fallback")
                record["post_compute"] = compute_apps()
                if classify(record["post_compute"], process.pid)[0]:
                    raise RuntimeError("owned CUDA context still present after training child exit")
        except BaseException as error:
            failure = error
            record["failure"] = type(error).__name__ + ": " + str(error)
        finally:
            if process is not None and process.poll() is None:
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
            path = Path(log).with_suffix(".gpu-guard.json")
            with path.open("x") as receipt:
                json.dump(record, receipt, indent=2)
                receipt.write("\n")
                receipt.flush()
                os.fsync(receipt.fileno())
        if failure is not None:
            raise failure
