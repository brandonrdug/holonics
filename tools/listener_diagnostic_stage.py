#!/usr/bin/env python3
"""Run one generic diagnostic command under the fixed REQ-063 outer envelope.

This supervisor is source code only; it knows no dataset, private paths, or listener workload.
The child receives CLOCK_MONOTONIC absolute cutoffs before it starts. No retry is performed.
"""
from __future__ import annotations

import argparse
import dataclasses
import errno
import json
import os
import resource
import signal
import subprocess
import sys
import time
from collections.abc import Callable, Sequence

TOTAL_NS = 300_000_000_000
TERM_NS = 295_000_000_000
NATIVE_GRACE_NS = 5_000_000_000
RSS_CAP_BYTES = 8 * 1024**3
CPU_COUNT = 3
POLL_NS = 50_000_000


@dataclasses.dataclass(frozen=True)
class DeadlinePlan:
    start_ns: int
    term_ns: int
    total_ns: int
    native_ns: int

    @classmethod
    def fixed(cls, start_ns: int) -> "DeadlinePlan":
        term = start_ns + TERM_NS
        return cls(start_ns, term, start_ns + TOTAL_NS, term - NATIVE_GRACE_NS)

    def valid_fixed_contract(self) -> bool:
        return (
            self.term_ns - self.start_ns == TERM_NS
            and self.total_ns - self.start_ns == TOTAL_NS
            and self.term_ns - self.native_ns == NATIVE_GRACE_NS
        )

    def child_environment(self, base: dict[str, str]) -> dict[str, str]:
        env = dict(base)
        env.update(
            {
                "REQ063_SUPERVISOR_START_MONOTONIC_NS": str(self.start_ns),
                "REQ063_TERM_DEADLINE_MONOTONIC_NS": str(self.term_ns),
                "REQ063_TOTAL_DEADLINE_MONOTONIC_NS": str(self.total_ns),
                "REQ063_NATIVE_DEADLINE_MONOTONIC_NS": str(self.native_ns),
                "RAYON_NUM_THREADS": "1",
                "REQ063_CLK_TCK": str(os.sysconf("SC_CLK_TCK")),
            }
        )
        return env


@dataclasses.dataclass(frozen=True)
class ProcessResult:
    status: str
    reason: str
    returncode: int | None
    deadline_evidence: bool
    term_sent: bool
    kill_sent: bool
    peak_group_rss_bytes: int | None
    start_ns: int
    term_ns: int
    native_ns: int
    total_ns: int
    finished_ns: int
    group_alive_at_return: bool
    cleanup_uncertain: bool

    def as_json(self) -> str:
        return json.dumps(dataclasses.asdict(self), sort_keys=True, separators=(",", ":"))


def classify_returncode(returncode: int | None, *, deadline_evidence: bool) -> str:
    """Never infer deadline from SIGKILL status alone."""
    if returncode is None:
        return "killed_unknown"
    if returncode in (-signal.SIGKILL, 128 + signal.SIGKILL):
        return "deadline" if deadline_evidence else "killed_unknown"
    if returncode < 0 and -returncode == signal.SIGTERM and deadline_evidence:
        return "deadline"
    return "complete" if returncode == 0 else "exited_nonzero"


def group_rss_bytes(pgid: int) -> int | None:
    """Sum resident pages for visible processes in a process group; unavailable stays unknown."""
    if not sys.platform.startswith("linux"):
        return None
    page_size = os.sysconf("SC_PAGE_SIZE")
    total = 0
    found = False
    try:
        entries = os.scandir("/proc")
    except OSError:
        return None
    with entries:
        for entry in entries:
            if not entry.name.isdigit():
                continue
            proc = f"/proc/{entry.name}"
            try:
                with open(f"{proc}/stat", encoding="ascii") as stream:
                    stat = stream.read()
                close = stat.rfind(")")
                fields = stat[close + 1 :].split()
                if int(fields[2]) != pgid:
                    continue
                with open(f"{proc}/statm", encoding="ascii") as stream:
                    statm = stream.read().split()
                resident_pages = int(statm[1])
            except FileNotFoundError:
                # A process can exit between reading /proc/<pid>/stat and statm.
                continue
            except PermissionError:
                return None
            except (OSError, ValueError, IndexError):
                return None
            found = True
            total += resident_pages * page_size
    return total if found else 0


def process_group_alive(pgid: int) -> bool:
    try:
        os.killpg(pgid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True
    return True


def select_cpu_affinity(available: Sequence[int]) -> tuple[int, ...]:
    """Choose exactly three visible logical CPUs or fail closed."""
    cpus = tuple(sorted(set(available))[:CPU_COUNT])
    if len(cpus) != CPU_COUNT:
        raise RuntimeError("fewer than three CPUs are available for the declared envelope")
    return cpus


def _child_limits() -> None:
    """Install fixed address-space/affinity limits in the new child before exec."""
    resource.setrlimit(resource.RLIMIT_AS, (RSS_CAP_BYTES, RSS_CAP_BYTES))
    if not hasattr(os, "sched_getaffinity") or not hasattr(os, "sched_setaffinity"):
        raise RuntimeError("three-CPU affinity requires Linux sched affinity support")
    os.sched_setaffinity(0, set(select_cpu_affinity(os.sched_getaffinity(0))))


def _send_group_signal(pgid: int, sig: int) -> None:
    try:
        os.killpg(pgid, sig)
    except ProcessLookupError:
        pass


def supervise(
    command: Sequence[str],
    *,
    plan: DeadlinePlan | None = None,
    clock: Callable[[], int] = time.monotonic_ns,
    popen_factory: Callable[..., subprocess.Popen[bytes]] = subprocess.Popen,
    group_alive: Callable[[int], bool] = process_group_alive,
    rss_reader: Callable[[int], int | None] = group_rss_bytes,
    signal_group: Callable[[int, int], None] = _send_group_signal,
    sleep_ns: Callable[[int], None] = lambda delay: time.sleep(delay / 1_000_000_000),
    install_limits: bool = True,
) -> ProcessResult:
    """Run exactly one process group; dependencies are injectable for clock/process controls."""
    if not command:
        raise ValueError("a command after -- is required")
    start_ns = clock() if plan is None else plan.start_ns
    plan = DeadlinePlan.fixed(start_ns) if plan is None else plan
    if not plan.valid_fixed_contract():
        raise ValueError("only the fixed 295s TERM / 300s total / 5s native grace contract is valid")
    env = plan.child_environment(dict(os.environ))
    try:
        process = popen_factory(
            list(command),
            env=env,
            start_new_session=True,
            preexec_fn=_child_limits if install_limits else None,
        )
    except (OSError, subprocess.SubprocessError):
        finished = clock()
        return ProcessResult(
            "launch_failed", "child_launch_or_limit_setup_failed", None, False, False, False,
            None, plan.start_ns, plan.term_ns, plan.native_ns, plan.total_ns, finished,
            False, False
        )
    pgid = process.pid
    term_sent = False
    kill_sent = False
    deadline_evidence = False
    reason = "child_exit"
    peak_rss: int | None = None
    rss_stop = False
    cleanup_deadline_ns: int | None = None
    while True:
        now = clock()
        try:
            measured_rss = rss_reader(pgid)
        except OSError:
            measured_rss = None
        if measured_rss is not None:
            peak_rss = measured_rss if peak_rss is None else max(peak_rss, measured_rss)
        if not term_sent and measured_rss is None and group_alive(pgid):
            reason = "process_group_rss_unavailable"
            rss_stop = True
            term_sent = True
            cleanup_deadline_ns = min(now + NATIVE_GRACE_NS, plan.total_ns)
            signal_group(pgid, signal.SIGTERM)
        if not term_sent and measured_rss is not None and measured_rss >= RSS_CAP_BYTES:
            reason = "process_group_rss_cap"
            rss_stop = True
            term_sent = True
            cleanup_deadline_ns = min(now + NATIVE_GRACE_NS, plan.total_ns)
            signal_group(pgid, signal.SIGTERM)
        if not term_sent and now >= plan.term_ns:
            reason = "outer_term_deadline"
            deadline_evidence = True
            term_sent = True
            cleanup_deadline_ns = plan.total_ns
            signal_group(pgid, signal.SIGTERM)
        returncode = process.poll()
        if returncode is not None and not term_sent and group_alive(pgid):
            reason = "leader_exited_group_cleanup"
            term_sent = True
            cleanup_deadline_ns = min(now + NATIVE_GRACE_NS, plan.total_ns)
            signal_group(pgid, signal.SIGTERM)
        alive = group_alive(pgid)
        if returncode is not None and not alive:
            status = classify_returncode(returncode, deadline_evidence=deadline_evidence)
            if deadline_evidence:
                status = "deadline"
            elif rss_stop and returncode in (-signal.SIGKILL, 128 + signal.SIGKILL):
                status = "killed_unknown"
            elif rss_stop and reason == "process_group_rss_cap":
                status = "resource_cap"
            elif rss_stop:
                status = "resource_measurement_unavailable"
            elif reason == "leader_exited_group_cleanup":
                status = "incomplete_group_cleanup"
            return ProcessResult(
                status, reason, returncode, deadline_evidence, term_sent, kill_sent, peak_rss,
                plan.start_ns, plan.term_ns, plan.native_ns, plan.total_ns, clock(),
                group_alive(pgid), False
            )
        cleanup_due = cleanup_deadline_ns is not None and now >= cleanup_deadline_ns
        if cleanup_due and not kill_sent:
            if deadline_evidence:
                reason = "fixed_total_deadline"
            kill_sent = True
            signal_group(pgid, signal.SIGKILL)
        if now >= plan.total_ns:
            reason = "fixed_total_deadline"
            deadline_evidence = True
            if not kill_sent:
                signal_group(pgid, signal.SIGKILL)
                kill_sent = True
            # Do not wait past the hard envelope. The result records a missing status honestly.
            returncode = process.poll()
            status = classify_returncode(returncode, deadline_evidence=deadline_evidence)
            if deadline_evidence:
                status = "deadline"
            alive_at_return = group_alive(pgid)
            return ProcessResult(
                status, reason, returncode, True, term_sent, kill_sent, peak_rss,
                plan.start_ns, plan.term_ns, plan.native_ns, plan.total_ns, clock(),
                alive_at_return, alive_at_return
            )
        delay = min(POLL_NS, plan.total_ns - now)
        if term_sent:
            # The cleanup period is strictly bounded by the fixed total deadline.
            sleep_ns(delay)
        else:
            sleep_ns(min(delay, max(1, plan.term_ns - now)))


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", nargs=argparse.REMAINDER, help="command to run after --")
    args = parser.parse_args(argv)
    command = list(args.command)
    if command and command[0] == "--":
        command.pop(0)
    if not command:
        parser.error("provide one command after --")
    result = supervise(command)
    print(result.as_json(), flush=True)
    return 0 if result.status == "complete" else 1


if __name__ == "__main__":
    raise SystemExit(main())
