#!/usr/bin/env python3
"""Run the pinned listener diagnostic once and write create-only run receipts.

The JSON configuration supplies an argv vector, never a shell command. Its SHA-256 is pinned
out-of-band on the command line so it cannot self-assert its own expected digest. One monotonic
start defines the cooperative native +290s, TERM +295s, cleanup +299s, and total +300s work/log
boundary. The terminal receipt write/fsync occurs after the recorded finish measurement. Memory
uses an 8 GiB per-process address-space limit plus sampled aggregate process-group RSS; it has no
hard cgroup aggregate-memory guarantee.
"""
from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time
from collections.abc import Callable, Sequence
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

import listener_diagnostic_stage as stage

DISK_FLOOR_BYTES = 512 * 1024 * 1024
HASH_CHUNK_BYTES = 1024 * 1024
RECEIPT_SCHEMA = "req063-listener-diagnostic-receipt-v2"
EVIDENCE_RESERVE_NS = 1_000_000_000
MAX_PROCESS_SAMPLES = 6_001
REQUIRED_PIN_ROLES = frozenset({"wrapper", "supervisor", "binary", "input", "cargo_lock"})
INPUT_ROLE = "input"


class ReceiptError(RuntimeError):
    """A preflight, monitoring, or receipt contract failure."""


class MonitorStop(RuntimeError):
    def __init__(self, reason: str, status: str):
        super().__init__(reason)
        self.reason = reason
        self.status = status


@dataclasses.dataclass(frozen=True)
class RepoState:
    head: str
    tree: str
    clean: bool


def _sha256(path: Path, *, deadline_ns: int, clock: Callable[[], int]) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        while True:
            if clock() >= deadline_ns:
                raise TimeoutError("fixed total deadline reached during pinned-file hashing")
            block = stream.read(HASH_CHUNK_BYTES)
            if not block:
                if clock() >= deadline_ns:
                    raise TimeoutError("fixed total deadline reached during pinned-file hashing")
                return digest.hexdigest()
            digest.update(block)


def _remaining_seconds(deadline_ns: int, clock: Callable[[], int]) -> float:
    remaining = deadline_ns - clock()
    if remaining <= 0:
        raise TimeoutError("fixed total deadline reached during preflight")
    return remaining / 1_000_000_000


def _git(root: Path, args: Sequence[str], *, deadline_ns: int, clock: Callable[[], int]) -> str:
    result = subprocess.run(
        ["git", "-C", str(root), *args],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        text=True,
        timeout=_remaining_seconds(deadline_ns, clock),
    )
    if result.returncode != 0:
        raise ReceiptError(f"git {args[0]} preflight failed with exit {result.returncode}")
    if clock() >= deadline_ns:
        raise TimeoutError(f"fixed total deadline reached after git {args[0]}")
    return result.stdout.strip()


def repo_state(root: Path, *, deadline_ns: int, clock: Callable[[], int]) -> RepoState:
    head = _git(root, ["rev-parse", "HEAD"], deadline_ns=deadline_ns, clock=clock)
    tree = _git(root, ["rev-parse", "HEAD^{tree}"], deadline_ns=deadline_ns, clock=clock)
    status = _git(
        root,
        ["status", "--porcelain=v1", "--untracked-files=all"],
        deadline_ns=deadline_ns,
        clock=clock,
    )
    return RepoState(head, tree, clean=(status == ""))


def _resolve(root: Path, value: str) -> Path:
    path = Path(value)
    return path.resolve() if path.is_absolute() else (root / path).resolve()


def _read_config(path: Path, expected_sha256: str, *, deadline_ns: int, clock: Callable[[], int]) -> dict[str, Any]:
    if clock() >= deadline_ns:
        raise TimeoutError("fixed total deadline reached while reading configuration")
    with path.open("rb") as stream:
        raw = stream.read(4 * 1024 * 1024 + 1)
    if clock() >= deadline_ns:
        raise TimeoutError("fixed total deadline reached while reading configuration")
    if len(raw) > 4 * 1024 * 1024:
        raise ReceiptError("configuration exceeds the 4 MiB metadata limit")
    actual_sha256 = hashlib.sha256(raw).hexdigest()
    if actual_sha256.lower() != expected_sha256.lower():
        raise ReceiptError("externally pinned configuration SHA-256 does not match")
    try:
        value = json.loads(raw)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise ReceiptError(f"configuration is not valid UTF-8 JSON: {error}") from error
    if not isinstance(value, dict):
        raise ReceiptError("configuration root must be a JSON object")
    return value


def _pin_snapshot(
    config: dict[str, Any],
    root: Path,
    *,
    deadline_ns: int,
    clock: Callable[[], int],
    repo_reader: Callable[..., RepoState] = repo_state,
) -> tuple[dict[str, Any], list[str]]:
    failures: list[str] = []
    snapshot: dict[str, Any] = {"repo": None, "files": []}
    expected_repo = config.get("repo")
    if not isinstance(expected_repo, dict):
        failures.append("config repo pin is missing or malformed")
    else:
        try:
            current = repo_reader(root, deadline_ns=deadline_ns, clock=clock)
            snapshot["repo"] = dataclasses.asdict(current)
            if current.head != expected_repo.get("head"):
                failures.append("repository HEAD differs from pin")
            if current.tree != expected_repo.get("tree"):
                failures.append("repository tree differs from pin")
            if expected_repo.get("clean", True) and not current.clean:
                failures.append("repository working tree is not clean")
        except (OSError, ReceiptError, subprocess.SubprocessError, TimeoutError) as error:
            failures.append(f"repository state unavailable: {error}")

    pins = config.get("files")
    if not isinstance(pins, list):
        failures.append("config file pins are missing or malformed")
        pins = []
    roles: set[str] = set()
    for item in pins:
        if not isinstance(item, dict):
            failures.append("malformed file pin entry")
            continue
        role, name, expected = item.get("role"), item.get("path"), item.get("sha256")
        if not isinstance(role, str) or not isinstance(name, str) or not isinstance(expected, str):
            failures.append("file pin requires string role, path, and sha256")
            continue
        if len(expected) != 64 or any(character not in "0123456789abcdefABCDEF" for character in expected):
            failures.append(f"pinned {role} file has malformed SHA-256")
            continue
        roles.add(role)
        record: dict[str, Any] = {"role": role, "path": name, "expected_sha256": expected}
        try:
            actual = _sha256(_resolve(root, name), deadline_ns=deadline_ns, clock=clock)
            record["actual_sha256"] = actual
            record["matches"] = actual.lower() == expected.lower()
            if not record["matches"]:
                failures.append(f"pinned {role} file digest differs")
        except (OSError, TimeoutError) as error:
            record["error"] = str(error)
            record["matches"] = False
            failures.append(f"pinned {role} file unavailable: {error}")
        snapshot["files"].append(record)
    missing = REQUIRED_PIN_ROLES - roles
    if missing:
        failures.append(f"required pin roles missing: {','.join(sorted(missing))}")
    wrappers = [item for item in pins if isinstance(item, dict) and item.get("role") == "wrapper"]
    supervisors = [item for item in pins if isinstance(item, dict) and item.get("role") == "supervisor"]
    if len(wrappers) == 1 and isinstance(wrappers[0].get("path"), str):
        if _resolve(root, wrappers[0]["path"]) != Path(__file__).resolve():
            failures.append("wrapper pin does not identify the executing receipt wrapper")
    if len(supervisors) == 1 and isinstance(supervisors[0].get("path"), str):
        if _resolve(root, supervisors[0]["path"]) != Path(stage.__file__).resolve():
            failures.append("supervisor pin does not identify the imported process supervisor")

    argv = config.get("argv")
    binary_pins = [item for item in pins if isinstance(item, dict) and item.get("role") == "binary"]
    if not isinstance(argv, list) or not argv or not all(isinstance(arg, str) for arg in argv):
        failures.append("config argv must be a nonempty array of strings")
    elif len(binary_pins) == 1 and isinstance(binary_pins[0].get("path"), str):
        try:
            if Path(argv[0]).resolve() != _resolve(root, binary_pins[0]["path"]):
                failures.append("argv[0] does not identify the pinned binary")
        except OSError as error:
            failures.append(f"pinned executable path is unavailable: {error}")
    elif len(binary_pins) != 1:
        failures.append("config must pin exactly one binary")
    if not isinstance(config.get("cwd", str(root)), str):
        failures.append("config cwd must be a path string")
    return snapshot, failures


def _input_binding(
    config: dict[str, Any],
    repo_root: Path,
    pin_snapshot: dict[str, Any],
) -> tuple[dict[str, Any], list[str]]:
    """Bind the one pinned input to the one separate --learn value used by the child."""
    failures: list[str] = []
    pins = config.get("files")
    input_pins = (
        [item for item in pins if isinstance(item, dict) and item.get("role") == INPUT_ROLE]
        if isinstance(pins, list)
        else []
    )
    binding: dict[str, Any] = {
        "status": "invalid",
        "input_pin_count": len(input_pins),
    }
    if len(input_pins) != 1:
        failures.append("config must contain exactly one input pin")
        return binding, failures

    pin = input_pins[0]
    pin_name = pin.get("path")
    pin_sha = pin.get("sha256")
    if (
        not isinstance(pin_name, str)
        or not pin_name
        or not isinstance(pin_sha, str)
        or len(pin_sha) != 64
        or any(character not in "0123456789abcdefABCDEF" for character in pin_sha)
    ):
        failures.append("input pin must have a nonempty path and a valid SHA-256")
        return binding, failures

    argv = config.get("argv")
    if not isinstance(argv, list) or not argv or not all(isinstance(argument, str) for argument in argv):
        failures.append("config argv must be a nonempty array of strings")
        return binding, failures
    learn_equals = [argument for argument in argv if argument.startswith("--learn=")]
    learn_positions = [index for index, argument in enumerate(argv) if argument == "--learn"]
    binding.update({
        "learn_argument_count": len(learn_positions),
        "learn_equals_count": len(learn_equals),
    })
    if learn_equals:
        failures.append("--learn must be a separate option and value; --learn=VALUE is ambiguous")
    if len(learn_positions) != 1:
        failures.append("argv must contain exactly one separate --learn option")
        return binding, failures
    position = learn_positions[0]
    if position + 1 >= len(argv) or not argv[position + 1] or argv[position + 1].startswith("--"):
        failures.append("--learn must be followed by one nonempty path value")
        return binding, failures

    cwd_value = config.get("cwd", str(repo_root))
    if not isinstance(cwd_value, str) or not cwd_value:
        failures.append("config cwd must be a nonempty path string")
        return binding, failures
    child_cwd = Path(cwd_value)
    if not child_cwd.is_absolute():
        child_cwd = repo_root / child_cwd
    child_cwd = child_cwd.resolve()
    pin_path = _resolve(repo_root, pin_name)
    learn_value = argv[position + 1]
    invoked_path = Path(learn_value)
    if not invoked_path.is_absolute():
        invoked_path = child_cwd / invoked_path
    invoked_path = invoked_path.resolve()

    pin_records = [
        item for item in pin_snapshot.get("files", [])
        if isinstance(item, dict) and item.get("role") == INPUT_ROLE
    ]
    pin_verified = (
        len(pin_records) == 1
        and pin_records[0].get("matches") is True
        and pin_records[0].get("actual_sha256", "").lower() == pin_sha.lower()
    )
    same_file = pin_path == invoked_path
    binding.update({
        "input_pin_path": pin_name,
        "input_pin_resolved": str(pin_path),
        "input_pin_sha256": pin_sha.lower(),
        "input_pin_verified": pin_verified,
        "child_cwd": str(child_cwd),
        "learn_value": learn_value,
        "learn_resolved": str(invoked_path),
        "same_file": same_file,
    })
    if not pin_verified:
        failures.append("pinned input file is not verified by this digest snapshot")
    if not child_cwd.is_dir():
        failures.append("configured child cwd is not an existing directory")
    if not same_file:
        failures.append("--learn path does not resolve to the pinned input from child cwd")
    if same_file and not pin_path.is_file():
        failures.append("resolved --learn input is not a regular file")
    if not failures:
        binding["status"] = "verified"
    return binding, failures


def _disk_read(path: Path) -> dict[str, int]:
    usage = shutil.disk_usage(path)
    return {"total_bytes": usage.total, "free_bytes": usage.free}


def _create_only_file(path: Path):
    if not path.parent.is_dir():
        raise FileNotFoundError(f"parent directory must already exist: {path.parent}")
    return path.open("x", encoding="utf-8")


def _write_receipt(stream, value: dict[str, Any]) -> None:
    stream.seek(0)
    stream.truncate()
    json.dump(value, stream, sort_keys=True, separators=(",", ":"))
    stream.write("\n")
    stream.flush()
    os.fsync(stream.fileno())


def _write_landing_sidecar(
    path: Path,
    receipt_path: Path,
    *,
    observed_ns: int,
    deadline_ns: int,
    work_status: str,
) -> None:
    """Create one small landing receipt; its own persistence latency is not measured."""
    sidecar = {
        "schema": "req063-listener-diagnostic-landing-v1",
        "receipt_path": str(receipt_path),
        "observed_monotonic_ns": observed_ns,
        "total_deadline_monotonic_ns": deadline_ns,
        "within_total_deadline": observed_ns <= deadline_ns,
        "landing_status": "within_total_deadline" if observed_ns <= deadline_ns else "landed_late",
        "work_status": work_status,
        "sidecar_write_latency_measured": False,
        "observation": "clock sampled immediately after terminal receipt fsync; sidecar write/fsync follows and is not measured",
    }
    with path.open("x", encoding="utf-8") as stream:
        json.dump(sidecar, stream, sort_keys=True, separators=(",", ":"))
        stream.write("\n")
        stream.flush()
        os.fsync(stream.fileno())


def _paths_outside_repo(config: dict[str, Any], root: Path) -> list[str]:
    failures: list[str] = []
    for name in ("output_dir", "log_path", "receipt_path"):
        value = config.get(name)
        if not isinstance(value, str):
            failures.append(f"config {name} must be a path string")
            continue
        path = _resolve(root, value)
        try:
            path.relative_to(root)
        except ValueError:
            continue
        failures.append(f"{name} must be outside the pinned repository")
    return failures


def run_receipted_stage(
    config_path: Path,
    config_sha256: str,
    receipt_path: Path,
    *,
    clock: Callable[[], int] = time.monotonic_ns,
    disk_reader: Callable[[Path], dict[str, int]] = _disk_read,
    repo_reader: Callable[..., RepoState] = repo_state,
    supervise: Callable[..., stage.ProcessResult] = stage.supervise,
    install_limits: bool = True,
) -> dict[str, Any]:
    """Run one config-pinned process with one start time and create-only result paths."""
    start_ns = clock()
    plan = stage.DeadlinePlan.fixed(start_ns)
    receipt_path = receipt_path.resolve()
    receipt_stream = _create_only_file(receipt_path)
    log_stream = None
    receipt: dict[str, Any] = {
        "schema": RECEIPT_SCHEMA,
        "status": "incomplete",
        "start_monotonic_ns": start_ns,
        "started_utc": datetime.now(timezone.utc).isoformat(),
        "landing_sidecar_path": str(receipt_path.with_name(receipt_path.name + ".landing.json")),
        "landing_verdict_source": "read valid landing sidecar; absent or invalid means unknown",
        "deadlines": dataclasses.asdict(plan),
        "preflight": None,
        "postflight": None,
        "disk_samples": [],
        "process_samples": [],
        "process": None,
        "failures": [],
        "limits": {
            "total_wall_ns": stage.TOTAL_NS,
            "native_cutoff_ns": stage.TOTAL_NS - 10_000_000_000,
            "term_deadline_ns": stage.TERM_NS,
            "evidence_reserve_ns": EVIDENCE_RESERVE_NS,
            "disk_floor_bytes": DISK_FLOOR_BYTES,
            "group_rss_bytes": stage.RSS_CAP_BYTES,
            "logical_cpus": stage.CPU_COUNT,
            "rayon_threads": 1,
            "gpu_visibility": "hidden",
            "retry_count": 0,
            "cpu_ticks_per_second": os.sysconf("SC_CLK_TCK"),
            "process_sample_limit": MAX_PROCESS_SAMPLES,
            "sample_note": "instant process-group samples can miss exited descendants; waited-child CPU is a separate direct-child counter",
            "deadline_note": "native +290s, TERM +295s, cleanup cutoff +299s, total +300s from one start; cooperative work/log boundary; terminal receipt write/fsync follows the recorded finish",
            "memory_note": "8 GiB RLIMIT_AS per process plus sampled aggregate process-group RSS; no hard cgroup aggregate-memory guarantee",
            "aggregate_memory_hard_limit": False,
            "terminal_receipt_write_in_finish_measurement": False,
            "terminal_receipt_write_deadline_enforced": False,
        },
    }
    _write_receipt(receipt_stream, receipt)

    config: dict[str, Any] | None = None
    repo_root: Path | None = None
    try:
        config = _read_config(
            config_path,
            config_sha256,
            deadline_ns=plan.total_ns,
            clock=clock,
        )
        repo_root_value = config.get("repo_root")
        if not isinstance(repo_root_value, str):
            raise ReceiptError("config repo_root must be a path string")
        repo_root = Path(repo_root_value)
        if not repo_root.is_absolute():
            repo_root = (config_path.parent / repo_root).resolve()
        configured_receipt = config.get("receipt_path")
        if not isinstance(configured_receipt, str) or _resolve(repo_root, configured_receipt) != receipt_path:
            raise ReceiptError("CLI create-only receipt path differs from pinned config")
        receipt["config_sha256"] = config_sha256.lower()
        receipt["receipt_path"] = str(receipt_path)
        receipt["argv"] = config.get("argv")
        _write_receipt(receipt_stream, receipt)

        failures = _paths_outside_repo(config, repo_root)
        if config.get("evidence_reserve_ns") != EVIDENCE_RESERVE_NS:
            failures.append("config must reserve exactly 1,000,000,000 ns inside the total deadline for evidence")
        snapshot, pin_failures = _pin_snapshot(
            config,
            repo_root,
            deadline_ns=plan.total_ns,
            clock=clock,
            repo_reader=repo_reader,
        )
        failures.extend(pin_failures)
        input_binding, input_binding_failures = _input_binding(config, repo_root, snapshot)
        failures.extend(input_binding_failures)
        config_file_hash = _sha256(config_path, deadline_ns=plan.total_ns, clock=clock)
        if config_file_hash.lower() != config_sha256.lower():
            failures.append("configuration changed during preflight")
        receipt["preflight"] = {
            "pins": snapshot,
            "config_sha256": config_file_hash,
            "input_binding": input_binding,
        }

        disk_root_value = config.get("disk_root", str(repo_root))
        if not isinstance(disk_root_value, str):
            failures.append("config disk_root must be a path string")
            disk_root = repo_root
        else:
            disk_root = Path(disk_root_value)
            if not disk_root.is_absolute():
                disk_root = (config_path.parent / disk_root).resolve()
        try:
            initial_disk = disk_reader(disk_root)
            receipt["disk_samples"].append({"monotonic_ns": clock(), **initial_disk, "phase": "preflight"})
            if initial_disk["free_bytes"] < DISK_FLOOR_BYTES:
                failures.append("free disk is below the 512 MiB floor")
        except (OSError, KeyError, ValueError) as error:
            failures.append(f"disk capacity unavailable: {error}")

        if failures:
            receipt["failures"].extend(failures)
            receipt["status"] = "preflight_failed"
        else:
            output_dir = _resolve(repo_root, config["output_dir"])
            log_path = _resolve(repo_root, config["log_path"])
            receipt["output_dir"] = str(output_dir)
            receipt["log_path"] = str(log_path)
            log_stream = _create_only_file(log_path)
            output_dir.mkdir(exist_ok=False)
            argv = list(config["argv"])
            cwd_value = config.get("cwd", str(repo_root))
            cwd = Path(cwd_value)
            if not cwd.is_absolute():
                cwd = (repo_root / cwd).resolve()
            env = {"REQ063_OUTPUT_DIR": str(output_dir)}

            def sample(sample_value: stage.ProcessSample) -> None:
                if len(receipt["process_samples"]) >= MAX_PROCESS_SAMPLES:
                    raise MonitorStop("process_sample_limit_exceeded", "resource_cap")
                record = dataclasses.asdict(sample_value)
                receipt["process_samples"].append(record)
                disk = disk_reader(disk_root)
                receipt["disk_samples"].append(
                    {"monotonic_ns": sample_value.monotonic_ns, **disk, "phase": "running"}
                )
                if disk["free_bytes"] < DISK_FLOOR_BYTES:
                    raise MonitorStop("disk_floor_breached", "resource_cap")

            def logged_popen(*args, **kwargs):
                child_env = dict(kwargs.pop("env"))
                child_env.update(env)
                kwargs["cwd"] = cwd
                kwargs["stdout"] = log_stream
                kwargs["stderr"] = subprocess.STDOUT
                return subprocess.Popen(*args, env=child_env, **kwargs)

            result = supervise(
                argv,
                plan=plan,
                clock=clock,
                popen_factory=logged_popen,
                sample_hook=sample,
                kill_cutoff_ns=plan.total_ns - EVIDENCE_RESERVE_NS,
                install_limits=install_limits,
            )
            receipt["process"] = dataclasses.asdict(result)
            receipt["status"] = result.status
            try:
                log_stream.flush()
                os.fsync(log_stream.fileno())
                log_stream.close()
                log_stream = None
                if result.group_alive_at_return or result.cleanup_uncertain:
                    receipt["log"] = {
                        "status": "unavailable",
                        "reason": "process group cleanup is uncertain; log may still be changing",
                    }
                    if receipt["status"] == "complete":
                        receipt["status"] = "integrity_unverified"
                else:
                    before = log_path.stat()
                    log_digest = _sha256(log_path, deadline_ns=plan.total_ns, clock=clock)
                    after = log_path.stat()
                    if (before.st_size, before.st_mtime_ns, before.st_ino) != (
                        after.st_size,
                        after.st_mtime_ns,
                        after.st_ino,
                    ):
                        raise ReceiptError("log changed while its final digest was computed")
                    receipt["log"] = {
                        "status": "verified",
                        "path": str(log_path),
                        "bytes": after.st_size,
                        "sha256": log_digest,
                    }
            except (OSError, TimeoutError, ReceiptError) as error:
                receipt["log"] = {"status": "unavailable", "reason": str(error)}
                receipt["failures"].append(f"final log evidence unavailable: {error}")
                if receipt["status"] == "complete":
                    receipt["status"] = "integrity_unverified"

        post_snapshot, post_failures = _pin_snapshot(
            config,
            repo_root,
            deadline_ns=plan.total_ns,
            clock=clock,
            repo_reader=repo_reader,
        )
        post_input_binding, post_binding_failures = _input_binding(config, repo_root, post_snapshot)
        post_failures.extend(post_binding_failures)
        receipt["postflight"] = {"pins": post_snapshot, "input_binding": post_input_binding}
        receipt["failures"].extend(post_failures)
        try:
            config_after = _sha256(config_path, deadline_ns=plan.total_ns, clock=clock)
            receipt["postflight"]["config_sha256"] = config_after
            if config_after.lower() != config_sha256.lower():
                receipt["failures"].append("configuration digest changed after process")
        except (OSError, TimeoutError) as error:
            receipt["postflight"]["config_sha256"] = None
            receipt["failures"].append(f"configuration postflight unavailable: {error}")
        if post_failures and receipt["status"] != "preflight_failed":
            if any("deadline reached" in failure for failure in post_failures):
                receipt["status"] = "integrity_unverified"
            else:
                receipt["status"] = "integrity_failure"
        if (
            receipt["status"] != "preflight_failed"
            and any(failure.startswith("configuration postflight unavailable") for failure in receipt["failures"])
        ):
            receipt["status"] = "integrity_unverified"
        elif receipt["status"] != "preflight_failed" and "configuration digest changed after process" in receipt["failures"]:
            receipt["status"] = "integrity_failure"
    except Exception as error:
        receipt["status"] = "preflight_failed" if receipt["preflight"] is None else "wrapper_failure"
        receipt["failures"].append(f"{type(error).__name__}: {error}")
        if config is not None and repo_root is not None and receipt["postflight"] is None:
            try:
                post_snapshot, post_failures = _pin_snapshot(
                    config,
                    repo_root,
                    deadline_ns=plan.total_ns,
                    clock=clock,
                    repo_reader=repo_reader,
                )
                post_input_binding, post_binding_failures = _input_binding(config, repo_root, post_snapshot)
                post_failures.extend(post_binding_failures)
                receipt["postflight"] = {"pins": post_snapshot, "input_binding": post_input_binding}
                receipt["failures"].extend(post_failures)
                if post_failures:
                    receipt["status"] = (
                        "integrity_unverified"
                        if any("deadline reached" in failure for failure in post_failures)
                        else "integrity_failure"
                    )
            except Exception as post_error:
                receipt["postflight"] = {"unavailable": str(post_error)}
                receipt["status"] = "integrity_unverified"
    finally:
        if log_stream is not None:
            try:
                log_stream.flush()
                os.fsync(log_stream.fileno())
            except OSError as error:
                receipt["failures"].append(f"log flush/fsync failed: {error}")
                if receipt["status"] == "complete":
                    receipt["status"] = "integrity_unverified"
                receipt["log"] = {"status": "unavailable", "reason": str(error)}
            finally:
                try:
                    log_stream.close()
                except OSError as error:
                    receipt["failures"].append(f"log close failed: {error}")
                    if receipt["status"] == "complete":
                        receipt["status"] = "integrity_unverified"
                    receipt["log"] = {"status": "unavailable", "reason": str(error)}
        finished_ns = clock()
        receipt["finished_monotonic_ns"] = finished_ns
        receipt["work_finished_utc"] = datetime.now(timezone.utc).isoformat()
        receipt["finish_boundary"] = "after work and log finalization, before terminal receipt write/fsync"
        receipt["elapsed_wall_ns"] = max(0, finished_ns - start_ns)
        receipt["deadline_overrun"] = finished_ns > plan.total_ns
        if receipt["deadline_overrun"]:
            receipt["status"] = "deadline_overrun"
        process_receipt = receipt.get("process")
        if receipt["status"] == "complete" and isinstance(process_receipt, dict):
            if process_receipt.get("group_alive_at_return") or process_receipt.get("cleanup_uncertain"):
                receipt["status"] = "cleanup_uncertain"
        if receipt_stream is not None:
            try:
                _write_receipt(receipt_stream, receipt)
                landing_observed_ns = clock()
            finally:
                receipt_stream.close()
            landing_path = receipt_path.with_name(receipt_path.name + ".landing.json")
            try:
                _write_landing_sidecar(
                    landing_path,
                    receipt_path,
                    observed_ns=landing_observed_ns,
                    deadline_ns=plan.total_ns,
                    work_status=receipt["status"],
                )
            except OSError:
                # A missing sidecar leaves landing unknown; it does not rewrite the durable work receipt.
                pass
    return receipt


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--config", required=True, type=Path)
    parser.add_argument("--config-sha256", required=True)
    parser.add_argument("--receipt", required=True, type=Path)
    args = parser.parse_args(argv)
    receipt = run_receipted_stage(args.config, args.config_sha256, args.receipt)
    print(json.dumps(receipt, sort_keys=True, separators=(",", ":")), flush=True)
    return 0 if receipt["status"] == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
