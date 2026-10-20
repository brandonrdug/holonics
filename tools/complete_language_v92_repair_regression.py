#!/usr/bin/env python3
"""Prepare, supervise, and score the V92 full-fibre repair regression.

Preparation is metadata/codec work. Execution is a model job and requires the separate,
explicitly approved native allocation. This module never extracts targets for generation.
"""
from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

CAP_NS = 2_400_000_000_000  # New proposed ceiling only; requires separate approval.
PHASE_NS = {"training": 1_800_000_000_000, "evaluation": 500_000_000_000,
            "receipts": 90_000_000_000, "cleanup": 10_000_000_000}
POLICIES = ("native", "founding-R", "tree", "fresh-native")
TRAIN_RAYON_THREADS = 4
OUTPUT_POOL_SIZE = 4
OUTPUT_CHILD_RAYON_THREADS = 1
DATA_MANIFEST = "/home/b/Documents/Codex/2026-10-17/task/alpha-complete-language-v91/approved-data-v2/native-inputs.json"
RAW_SHA = "17f347dc51477c50d4efb83959dbb7c56297aba886e5544ee2aaed3024813465"


def utc():
    return dt.datetime.now(dt.timezone.utc).isoformat()


def digest(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as source:
        for block in iter(lambda: source.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def write_new(path, value):
    path = Path(path)
    with path.open("x", encoding="utf-8") as out:
        json.dump(value, out, indent=2, ensure_ascii=True)
        out.write("\n")
        out.flush()
        os.fsync(out.fileno())
    fd = os.open(path.parent, os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def load(path):
    return json.loads(Path(path).read_text())


def source_paths(data):
    # Machine locations belong to the pinned exterior manifest, never public source.
    raw = Path(data["post_output_scoring"]["source_jsonl"]).resolve()
    return raw, raw.with_name("partition.json")


def verify_manifest(path):
    path = Path(path).resolve()
    data = load(path)
    root = path.parent
    index = {}
    for item in data["files"]:
        p = (root / item["path"]).resolve()
        if not p.is_relative_to(root) or p.stat().st_size != item["bytes"] or digest(p) != item["sha256"]:
            raise ValueError("prepared artifact identity mismatch: " + str(p))
        index[item["path"]] = dict(item, absolute=str(p))
    if data["training"]["rows"] != [2348, 6469, 535, 5955]:
        raise ValueError("fixed training selection changed")
    one = (root / "train-one-pass.bin").read_bytes()
    five = (root / "train-five-pass.bin").read_bytes()
    if len(one) != 564 or five != one * 5 or len(five) * 4 != 11280:
        raise ValueError("complete framing or five-pass count changed")
    prompts = data["prompts"]
    if len(prompts) != 4 or [x["row"] for x in prompts[:2]] != [2348, 6469]:
        raise ValueError("fixed retention prompt roles changed")
    for item in prompts:
        p = root / item["path"]
        if p.read_bytes()[-1:] != b"\n" or p.stat().st_size > 128 or digest(p) != item["sha256"]:
            raise ValueError("full Q+LF prompt identity mismatch")
    expected_keys = b"".join(hashlib.sha256(
        b"holonics-gsm8k-complete-language-v91-public-keys" + i.to_bytes(8, "big")
    ).digest()[:8] for i in range(128))
    if (root / "public-keys.bin").read_bytes() != expected_keys:
        raise ValueError("predeclared public key schedule changed")
    return data, root, index


def prepare(manifest, binary, output, source, backend, output_workers=OUTPUT_POOL_SIZE, training_binary=None, project_gpu_lock=None):
    if backend not in ("host-reference", "cuda-assisted-training-host-evaluation"):
        raise ValueError("explicit host-reference or CUDA-assisted training/host evaluation required; no fallback")
    if backend != "host-reference" and (training_binary is None or project_gpu_lock is None):
        raise ValueError("CUDA-assisted scope requires its separately pinned wrapper executable and project GPU lock")
    data, root, index = verify_manifest(manifest)
    if output_workers != OUTPUT_POOL_SIZE:
        raise ValueError("SchedulerV3 repair regression fixes output pool size at4")
    prompts = [dict(item, role=("exposed scored development regression; not blind"
        if item["row"] in (1026,1077) else "seen-training retention regression"))
        for item in data["prompts"]]
    # The original exposed proposal is retained, but cannot pass this prospective launch gate.
    dev_rows = [x["row"] for x in prompts[2:]]
    eligible = dev_rows == [1026, 1077] and not any("not fully blind" in x["role"] for x in prompts)
    provenance = data.get("source", data.get("data_source", {}))
    membership = data.get("partition_eligibility", {})
    raw_train, partition_path = source_paths(data)
    # Preparation checks only already-pinned metadata here. It does not open the raw
    # JSONL/Parquet source; selected-row decoding remains behind the output barrier.
    source_match = (provenance.get("train_jsonl_sha256") == RAW_SHA and
                    provenance.get("partition_sha256") == "a355c4c7528a2c29d9bc34ebd543f23c92fe8a8e54eb11b28bd4dcc5ac2780c1")
    partition = load(partition_path)  # Indices only, never dataset answers.
    eligible = eligible and source_match and membership.get("all_selected_groups_outside_exposure", False)
    eligible = eligible and all(row in partition["dev_indices"] and row not in partition["train_indices"] and row // 1000 not in {0,2,5,6} for row in dev_rows)
    min_horizon = 11280 + max(x["bytes"] for x in prompts) * 4 + 128
    if min_horizon > 16384:
        raise ValueError("fixed branch exceeds declared fresh horizon")
    prompt_arrivals = sum(x["bytes"] for x in prompts) * 4 * 4
    binary_path = str(Path(binary).resolve()) if binary != "__PIN_V92_OPTIMIZED_BINARY__" else binary
    binary_sha = digest(binary_path) if binary_path != "__PIN_V92_OPTIMIZED_BINARY__" else None
    plan = {
        "schema": "holonics.complete-language.v92.repair-regression-plan", "utc": utc(),
        "status": "PREPARED_REQUIRES_READINESS_AND_NEW_AUTHORIZATION" if eligible else "PREPARED_DATA_READINESS_BLOCKED",
        "model_execution_authorized": False, "source": source, "backend": backend,
        "receiving_law": "retained-fibre-v1", "training_command": "train-retained-fibre-v1",
        "checkpoint_law": "retained-fibre-v1", "scope": "paired repair regression; rows 1026/1077 are exposed development, not blind",
        "binary": binary_path, "binary_sha256": binary_sha,
        "data_manifest": str(Path(manifest).resolve()), "data_manifest_sha256": digest(manifest),
        "data_root": str(root), "data_eligible": eligible, "prompts": prompts,
        "files": index, "population": 16384, "minimum_branch_horizon": min_horizon,
        "branch_semantics": "one continuous fitting life; each prompt/policy forks the immutable trained or fresh checkpoint; no per-class reset",
        "training_cells": 11280, "expected_actual_epochs": 1128, "closure_cells": 10,
        "training_framing": "four fixed Q+LF+A+LF records, five passes, 2820 bytes; no flush",
        "training_causal_cut_count": 14,
        "training_causal_cut_offsets": [0, 172, 712, 1316, 1904, 2256, 4512, 6768, 9024, 9196, 9736, 10340, 10928, 11280],
        "output_bytes_per_policy": 32, "output_policies": list(POLICIES), "output_attempts": 16,
        "output_native_cells": 2048, "additional_cold_replay_cells": 4,
        "prompt_native_arrivals": prompt_arrivals, "output_cuts": [0, 1, 4, 16, 64, 128],
        "targets_absent_from_generator_interface": True,
        "mode_search": "none; preserved V90 native_section attempts remain incomplete",
        "native_cap_ns": CAP_NS, "phase_ns": PHASE_NS,
        "cpus": 4, "training_rayon_threads": TRAIN_RAYON_THREADS,
        "output_workers": output_workers, "output_child_rayon_threads": OUTPUT_CHILD_RAYON_THREADS,
        "scheduler_identity": "output-fork-scheduler-v3; separate from V91/V92 native-law identity",
        "aggregate_memory_bytes": 8589934592,
        "timing_basis": {"V91_training_ns": 787058547469,
            "V91_whole_native_charge_ns": 1343726657521,
            "V91_other_overhead_upper_ns": 556399403934,
            "limits": "V92 full-fibre training cost is unmeasured; V91 timing is context only; hard caps are cutoffs, not ETA or speed guarantee; no pilot"},
        "backend_stages": {"selected_reference": {"training_forward_reverse": "host", "grouped_statistics": "host",
            "query_prefix_advance": "host", "scalar_roots_normalization": "host", "scoring_certification": "host"},
            "existing_CUDA_connection": {"forward_adjoint_grouped_statistics": "real hybrid ObservedEpochDevice route; stream injection prepared",
                "exact_source_return": "runtime-width exact rational CUDA stages exist",
                "face_enclosure_normalization_scoring_certification": "current host consumers",
                "retained_stream_CUDA_CODE_parity": "PASS2 synthetic full-fibre host/card and late rollback controls; no model or speed claim",
                "complete_language_CUDA_adapter": "UNJOINED; continuation scalar/normalization/certification consumers remain host; no fallback"}},
        "receipts_accounting": "checkpoints inside train/eval are charged to those phases; separate90s is source verification and primary receipt/scoring reserve, not phase extension",
        "development_score_source": {"path": str(raw_train), "sha256": RAW_SHA, "blind": False,
            "use": "exposed development repair regression only; no new selection or blind claim",
            "rows": [{"row": x["row"], "question_sha256": hashlib.sha256((root/x["path"]).read_bytes()[:-1]).hexdigest()} for x in prompts[2:]],
            "read_rule": "only after all16 outputs terminal and durably hashed; skip unselected raw lines BEFORE JSON decoding"},
    }
    if backend == "cuda-assisted-training-host-evaluation":
        training_path = str(Path(training_binary).resolve())
        plan.update(training_binary=training_path, training_binary_sha256=digest(training_path),
            training_backend="cuda-observed-epoch-device0", output_backend="host-reference",
            gpu_guard={"device_ordinal": 0, "own_sampled_memory_limit_MiB": 8192,
                "graphics_allowed": True, "foreign_compute_allowed": False,
                "project_lock": str(Path(project_gpu_lock).resolve())},
            backend_stages={"training_card": "ObservedEpochDevice0 forwards, retained Word returns, grouped statistics",
                "training_host": "source/clock/normal law; scalar faces/roots/normalization/scoring/certification; finite admission and causal cuts",
                "evaluation_host": "prefix diagnostics; exact decode; four independent output forks; scoring/certification",
                "fallback": False},
            CUDA_full_model_acceptance="UNRUN; targeted synthetic adapter parity only; no speed claim")
    write_new(output, plan)
    return plan


def checked_plan(path, approved_digest=None):
    if approved_digest is not None and digest(path) != approved_digest:
        raise ValueError("approved launch-plan digest mismatch")
    plan = load(path)
    if digest(plan["binary"]) != plan["binary_sha256"] or digest(plan["data_manifest"]) != plan["data_manifest_sha256"]:
        raise ValueError("launch source/binary/data identity changed")
    if "training_binary" in plan and digest(plan["training_binary"]) != plan["training_binary_sha256"]:
        raise ValueError("pinned training executor binary identity changed")
    data, _, _ = verify_manifest(plan["data_manifest"])
    _, partition_path = source_paths(data)
    provenance = data.get("source", data.get("data_source", {}))
    if (provenance.get("train_jsonl_sha256") != RAW_SHA or
            provenance.get("partition_sha256") != "a355c4c7528a2c29d9bc34ebd543f23c92fe8a8e54eb11b28bd4dcc5ac2780c1"):
        raise ValueError("pinned source/partition metadata identity changed since preparation")
    # Partition JSON is exterior index metadata. The raw JSONL is not opened before
    # the post-output scoring process, where the fixed row skip-before-decode rule applies.
    partition = load(partition_path)
    for row in (1026, 1077):
        if row not in partition["dev_indices"] or row in partition["train_indices"] or row // 1000 in {0, 2, 5, 6}:
            raise ValueError("exposed development regression row identity changed")
    return plan


def commands(plan, out):
    out = Path(out)
    base = [plan["binary"], "complete-language"]
    f = plan["files"]
    corpus, cuts, keys = (f[n] for n in ("train-five-pass.bin", "causal-cuts.tsv", "public-keys.bin"))
    training = [plan.get("training_binary", plan["binary"]), "complete-language"] + ["train-retained-fibre-v1", plan.get("training_backend", plan["backend"]), corpus["absolute"], corpus["sha256"], cuts["absolute"], cuts["sha256"],
        "16384", "11280", "1128", str(out/"training")]
    samples = []
    for prompt_index, prompt in enumerate(plan["prompts"]):
        for policy in POLICIES:
            # Both checkpoints are emitted by the selected-law training command. Never
            # splice in the historical coarse-law fresh checkpoint.
            checkpoint = out/"training"/("fresh.state" if policy == "fresh-native" else "trained.state")
            destination = out/"outputs"/f"row-{prompt['row']}-{policy}"
            argv = base + ["sample", plan.get("output_backend", plan["backend"]), str(checkpoint), str(Path(plan["data_root"])/prompt["path"]), prompt["sha256"],
                keys["absolute"], keys["sha256"], policy,
                "cold-replay" if prompt_index == 0 and policy == "native" else "no-replay", str(destination)]
            samples.append({"row": prompt["row"], "policy": policy, "argv": argv, "directory": str(destination)})
    return training, samples


def run_phase(argv, log, deadline_ns, rayon_threads=1):
    if time.monotonic_ns() >= deadline_ns:
        raise TimeoutError("fixed phase deadline before launch")
    with Path(log).open("xb") as stream:
        env = dict(os.environ, RAYON_NUM_THREADS=str(rayon_threads))
        process = subprocess.Popen(argv, stdout=stream, stderr=subprocess.STDOUT,
                                   start_new_session=True, env=env)
        try:
            while process.poll() is None:
                if time.monotonic_ns() >= deadline_ns:
                    raise TimeoutError("fixed phase deadline; no extension or fallback")
                time.sleep(.05)
            if process.returncode:
                raise RuntimeError(f"native command exited {process.returncode}")
        finally:
            if process.poll() is None:
                os.killpg(process.pid, signal.SIGKILL)
                # The outer controller owns the one cleanup deadline and all descendants.


def verify_training_receipts(out, backend="host-reference"):
    """Require the native training law and actual Rayon identity, never infer from env."""
    root = Path(out)
    clock = load(root / "CLOCK_CONTRACT.json")
    complete = load(root / "TRAINING_COMPLETE.json")
    for name, receipt in (("CLOCK_CONTRACT", clock), ("TRAINING_COMPLETE", complete)):
        if receipt.get("actual_rayon_workers") != TRAIN_RAYON_THREADS:
            raise ValueError(f"{name} actual_rayon_workers must be {TRAIN_RAYON_THREADS}; absent/other is refusal")
    if complete.get("receiving_law") != "retained-fibre-v1":
        raise ValueError("training completion receipt is not retained-fibre-v1")
    if complete.get("accepted_cells") != 11280 or complete.get("actual_epochs") != 1128:
        raise ValueError("selected-law training receipt does not close the declared 11,280-cell / 1,128-epoch stream")
    if backend == "cuda-observed-epoch-device0":
        from complete_language_cuda_guard import verify_card_receipt
        if complete.get("backend") != backend:
            raise ValueError("training completion backend differs from selected card executor")
        verify_card_receipt(load(root / "CUDA_EXECUTION.json"))


def verify_output_receipt(reading, policy):
    if reading.get("actual_rayon_workers") != OUTPUT_CHILD_RAYON_THREADS:
        raise ValueError("output receipt actual_rayon_workers must be 1; absent/other is refusal")
    if reading.get("receiving_law") != "retained-fibre-v1":
        raise ValueError("output receipt is not retained-fibre-v1")
    if policy == "fresh-native" and reading.get("opening_accepted_cells") != 0:
        raise ValueError("fresh-native checkpoint was not fresh at first opening")


def run_output_attempts(samples, out, deadline_ns, workers, cpu_envelope):
    """Coordinate bounded whole-attempt subprocesses without changing any attempt."""
    if (not isinstance(cpu_envelope, int) or isinstance(cpu_envelope, bool) or cpu_envelope < 1 or
            not isinstance(workers, int) or isinstance(workers, bool) or not 1 <= workers <= cpu_envelope):
        raise ValueError("output worker count must be a positive integer within the declared CPU envelope")
    active = []
    next_index = 0

    def close_record(record):
        if not record["log"].closed:
            record["log"].close()

    def cleanup_and_raise(original):
        # Signal every group and do one nonblocking reap pass. The outer controller
        # owns the sole cleanup deadline for any leaders or descendants still alive.
        for record in list(active):
            try:
                os.killpg(record["process"].pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
        unreaped = []
        for record in active:
            if record["process"].poll() is None:
                unreaped.append(record)
            close_record(record)
        active.clear()
        if unreaped and hasattr(original, "add_note"):
            pids = ",".join(str(record["process"].pid) for record in unreaped)
            original.add_note(
                "outer controller owns the existing cleanup deadline; child leaders still running after immediate poll: " + pids)
        raise original

    def launch(index):
        item = samples[index]
        stream = Path(out).joinpath(f"sample-{item['row']}-{item['policy']}.log").open("xb")
        try:
            env = dict(os.environ, RAYON_NUM_THREADS=str(OUTPUT_CHILD_RAYON_THREADS))
            process = subprocess.Popen(
                item["argv"], stdout=stream, stderr=subprocess.STDOUT,
                start_new_session=True, env=env)
        except BaseException:
            stream.close()
            raise
        active.append({"index": index, "item": item, "process": process, "log": stream})

    try:
        while next_index < len(samples) or active:
            if time.monotonic_ns() >= deadline_ns:
                raise TimeoutError("fixed evaluation deadline reached; no extension or fallback")

            # Poll the current set before admitting any replacement. The coordinator
            # observes nonzero exits in canonical order and never launches later work
            # after observing one.
            still_running = []
            for record in active:
                status = record["process"].poll()
                if status is None:
                    still_running.append(record)
                else:
                    close_record(record)
                    if status:
                        item = record["item"]
                        raise RuntimeError(
                            f"sample attempt index={record['index']} row={item['row']} "
                            f"policy={item['policy']} exited {status}")
            active[:] = still_running

            while next_index < len(samples) and len(active) < workers:
                if time.monotonic_ns() >= deadline_ns:
                    raise TimeoutError("fixed evaluation deadline reached before next attempt launch")
                launch(next_index)
                next_index += 1
            if active:
                time.sleep(.01)
    except BaseException as exc:
        cleanup_and_raise(exc)
    return list(samples)


def seal_outputs(plan, out, samples):
    records = []
    transcript = ["Complete native conditional-sampling transcript", "Targets are absent from this transcript.", ""]
    prompts = {x["row"]: x for x in plan["prompts"]}
    for item in samples:
        directory = Path(item["directory"])
        meta, raw = directory/"OUTPUT.json", directory/"OUTPUT.bin"
        reading = load(meta)
        blob = raw.read_bytes()
        verify_output_receipt(reading, item["policy"])
        if list(blob) != reading["raw_bytes"] or len(blob) > 32 or reading["output_cells_requested"] != 128:
            raise ValueError("output receipt/raw identity mismatch")
        # File content and nested directory entries precede the durable scoring barrier.
        for path in (meta, raw):
            with path.open("rb") as file: os.fsync(file.fileno())
        fd = os.open(directory, os.O_RDONLY)
        try: os.fsync(fd)
        finally: os.close(fd)
        records.append({"row": item["row"], "policy": item["policy"], "metadata": str(meta),
            "metadata_sha256": digest(meta), "raw": str(raw), "raw_sha256": digest(raw),
            "bytes": len(blob), "stop": reading["stop"]})
        prompt = (Path(plan["data_root"])/prompts[item["row"]]["path"]).read_bytes()
        transcript.extend([f"Row {item['row']} / {item['policy']} / stop={reading['stop']}",
            "Prompt Q+LF: " + json.dumps(prompt.decode("utf-8"), ensure_ascii=True),
            "Output bytes: " + blob.hex(),
            "Exact UTF-8 (null means invalid/incomplete): " + json.dumps(_strict_utf8(blob), ensure_ascii=True), ""])
    if len(records) != 16:
        raise ValueError("all16 declared attempts must be terminal before targets open")
    transcript_path = Path(out)/"TRANSCRIPT.txt"
    with transcript_path.open("x", encoding="utf-8") as file:
        file.write("\n".join(transcript)); file.flush(); os.fsync(file.fileno())
    seal = {"utc": utc(), "data_manifest_sha256": plan["data_manifest_sha256"], "records": records,
        "transcript": str(transcript_path), "transcript_sha256": digest(transcript_path),
        "all_declared_attempts_terminal": True, "all_full32bytes": all(x["bytes"] == 32 and x["stop"] == "DeclaredLength" for x in records)}
    write_new(Path(out)/"ALL_OUTPUTS_TERMINAL.json", seal)
    return seal


def verified_output_barrier(plan, out):
    path = Path(out)/"ALL_OUTPUTS_TERMINAL.json"
    seal = load(path)  # This happens before any target file is opened or decoded.
    expected_order = [(p["row"], policy) for p in plan["prompts"] for policy in POLICIES]
    actual_order = [(x["row"], x["policy"]) for x in seal["records"]]
    if not seal["all_declared_attempts_terminal"] or actual_order != expected_order or len(seal["records"]) != 16:
        raise ValueError("incomplete output barrier")
    if seal["data_manifest_sha256"] != plan["data_manifest_sha256"]:
        raise ValueError("output/data manifest mismatch")
    for item in seal["records"]:
        if digest(item["raw"]) != item["raw_sha256"] or digest(item["metadata"]) != item["metadata_sha256"]:
            raise ValueError("sealed output changed before scoring")
    if "transcript" in seal and digest(seal["transcript"]) != seal["transcript_sha256"]:
        raise ValueError("sealed transcript changed before scoring")
    return seal, digest(path)


def score(plan, out):
    out = Path(out)
    seal, seal_hash = verified_output_barrier(plan, out)
    write_new(out/"SCORING_OPEN_EVENT.json", {"utc": utc(), "output_manifest_sha256": seal_hash,
        "selected_development_rows": plan["development_score_source"]["rows"],
        "source": plan["development_score_source"], "targets_not_passed_to_generation": True})
    data = load(plan["data_manifest"])
    root = Path(plan["data_root"])
    targets = {x["row"]: (root/x["path"]).read_bytes() for x in data["retention_scoring"]["targets"]}
    spec = plan["development_score_source"]
    if digest(spec["path"]) != spec["sha256"]:
        raise ValueError("post-output raw source hash mismatch")
    selected = {x["row"]: x for x in spec["rows"]}
    with Path(spec["path"]).open("rb") as source:
        for row, raw in enumerate(source):
            if row not in selected:
                continue  # No JSON decode, no answer lookup on any other line.
            item = json.loads(raw)
            if hashlib.sha256(item["question"].encode()).hexdigest() != selected[row]["question_sha256"]:
                raise ValueError("precommitted development question identity mismatch")
            targets[row] = item["answer"].encode() + b"\n"
    if not selected.keys() <= targets.keys():
        raise ValueError("precommitted target row absent")
    readings = []
    for item in seal["records"]:
        raw, target = Path(item["raw"]).read_bytes(), targets[item["row"]]
        common = 0
        for a, b in zip(raw, target):
            if a != b: break
            common += 1
        readings.append({"row": item["row"], "policy": item["policy"], "raw_hex": raw.hex(),
            "raw_bytes": list(raw), "strict_utf8": _strict_utf8(raw), "literal_target_prefix_bytes_equal": common,
            "all_returned_bytes_match_target_prefix": raw == target[:len(raw)] if raw else False,
            "semantic_answer_or_coherence_verdict": "not inferred from literal byte matching; inspect actual output"})
    write_new(out/"POST_OUTPUT_SCORES.json", {"utc": utc(), "output_manifest_sha256": seal_hash,
        "literal_comparisons": readings, "teacher_led_objective": "separate actual training epochs.jsonl prequential readings; no heldout teacher-forcing model run"})


def _strict_utf8(raw):
    try: return raw.decode("utf-8", errors="strict")
    except UnicodeDecodeError: return None


def execute(plan_path, out, approved_ns, approved_plan_digest=None):
    if approved_ns != CAP_NS or approved_plan_digest is None:
        raise PermissionError("separately approved native cap and exact plan digest are required")
    plan = checked_plan(plan_path, approved_plan_digest)
    if (not plan["data_eligible"] or
            plan["status"] != "APPROVED_FOR_THIS_EXACT_REPAIR_PLAN" or
            plan["model_execution_authorized"] is not True):
        raise PermissionError("V92 repair regression requires a new explicit approval of this exact plan; V91 balance is not authority")
    workers = plan.get("output_workers")
    if workers != OUTPUT_POOL_SIZE or plan.get("output_child_rayon_threads") != OUTPUT_CHILD_RAYON_THREADS:
        raise ValueError("the pinned repair scheduler uses exactly four child processes with one Rayon worker each")
    out = Path(out)
    out.mkdir()  # Existing evidence is never overwritten or resumed implicitly.
    (out/"outputs").mkdir()
    started = time.monotonic_ns()
    write_new(out/"STARTED.json", {"utc": utc(), "plan_sha256": digest(plan_path), "backend": plan["backend"],
        "approved_native_cap_ns": approved_ns, "phase_ns": PHASE_NS, "output_workers": workers,
        "scope": "model job; requires trusted prior human budget authorization"})
    training, samples = commands(plan, out)
    training_backend = plan.get("training_backend", plan["backend"])
    if training_backend == "cuda-observed-epoch-device0":
        from complete_language_cuda_guard import run_gpu_training
        run_gpu_training(training, out/"training.log", started + PHASE_NS["training"],
                         plan["gpu_guard"], rayon_threads=TRAIN_RAYON_THREADS)
    elif training_backend == "host-reference":
        run_phase(training, out/"training.log", started + PHASE_NS["training"], rayon_threads=TRAIN_RAYON_THREADS)
    else:
        raise ValueError("unimplemented training executor; no fallback")
    verify_training_receipts(out/"training", training_backend)
    training_end = time.monotonic_ns()
    eval_deadline = min(started + PHASE_NS["training"] + PHASE_NS["evaluation"], training_end + PHASE_NS["evaluation"])
    samples = run_output_attempts(samples, out, eval_deadline, workers, plan["cpus"])
    receipts_started = time.monotonic_ns()
    seal_outputs(plan, out, samples)
    # Scorer is a separate process, created only after the durable output barrier exists.
    run_phase([sys.executable, str(Path(__file__).resolve()), "score", "--plan", str(Path(plan_path).resolve()),
               "--plan-sha256", approved_plan_digest, "--out", str(out.resolve())],
              out/"scoring.log", receipts_started + PHASE_NS["receipts"])
    if time.monotonic_ns() - receipts_started > PHASE_NS["receipts"]:
        raise TimeoutError("fixed receipt/scoring phase limit exceeded")
    write_new(out/"TERMINAL.json", {"utc": utc(), "status": "ALL_DECLARED_ATTEMPTS_TERMINAL",
        "backend": plan["backend"], "elapsed_ns": time.monotonic_ns()-started,
        "output_workers": workers,
        "native_controller_owns_final_charge_and_cleanup": True, "GPU_model_validation": "selected CUDA training completed; output evaluation host" if training_backend == "cuda-observed-epoch-device0" else "UNRUN; selected host-reference"})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare")
    for name in ("manifest", "binary", "out", "source", "backend"): p.add_argument("--"+name, required=True)
    p.add_argument("--output-workers", type=int, default=OUTPUT_POOL_SIZE)
    p.add_argument("--training-binary")
    p.add_argument("--project-gpu-lock")
    p = sub.add_parser("execute", help="MODEL JOB: requires separate trusted budget authorization and outer resource controller")
    p.add_argument("--plan", required=True); p.add_argument("--out", required=True)
    p.add_argument("--approved-native-cap-ns", required=True, type=int)
    p.add_argument("--plan-sha256", required=True, help="digest pinned in the reviewed launch declaration")
    p = sub.add_parser("score")
    p.add_argument("--plan", required=True); p.add_argument("--out", required=True)
    p.add_argument("--plan-sha256", required=True)
    args = parser.parse_args()
    if args.command == "prepare": prepare(args.manifest,args.binary,args.out,args.source,args.backend,args.output_workers,args.training_binary,args.project_gpu_lock)
    elif args.command == "execute": execute(args.plan,args.out,args.approved_native_cap_ns,args.plan_sha256)
    else: score(checked_plan(args.plan,args.plan_sha256),args.out)


if __name__ == "__main__":
    main()
