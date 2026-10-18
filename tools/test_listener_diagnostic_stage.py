"""Pure deadline/process controls for listener_diagnostic_stage; never launches a listener."""
from __future__ import annotations

import signal
import subprocess
import sys
import time
import unittest

from listener_diagnostic_stage import (
    DeadlinePlan,
    RSS_CAP_BYTES,
    classify_returncode,
    select_cpu_affinity,
    supervise,
)


class FakeClock:
    def __init__(self, start_ns: int):
        self.now_ns = start_ns

    def __call__(self) -> int:
        return self.now_ns

    def sleep(self, delay_ns: int) -> None:
        self.now_ns += delay_ns


class FakeProcess:
    pid = 12345

    def __init__(self):
        self.returncode: int | None = None

    def poll(self) -> int | None:
        return self.returncode


class StageControls(unittest.TestCase):
    def test_fixed_deadline_contract_and_child_environment(self):
        plan = DeadlinePlan.fixed(1_000)
        self.assertTrue(plan.valid_fixed_contract())
        env = plan.child_environment({"KEPT": "yes", "RAYON_NUM_THREADS": "9"})
        self.assertEqual(env["REQ063_SUPERVISOR_START_MONOTONIC_NS"], "1000")
        self.assertEqual(env["REQ063_TERM_DEADLINE_MONOTONIC_NS"], str(1_000 + 295_000_000_000))
        self.assertEqual(env["REQ063_NATIVE_DEADLINE_MONOTONIC_NS"], str(1_000 + 290_000_000_000))
        self.assertEqual(env["REQ063_TOTAL_DEADLINE_MONOTONIC_NS"], str(1_000 + 300_000_000_000))
        self.assertEqual(env["RAYON_NUM_THREADS"], "1")
        self.assertEqual(env["KEPT"], "yes")

    def test_fixed_three_cpu_selection_and_unavailable_refusal(self):
        self.assertEqual(select_cpu_affinity([7, 2, 4, 1]), (1, 2, 4))
        with self.assertRaises(RuntimeError):
            select_cpu_affinity([0, 1])

    def test_sigkill_requires_deadline_evidence(self):
        self.assertEqual(classify_returncode(-signal.SIGKILL, deadline_evidence=False), "killed_unknown")
        self.assertEqual(classify_returncode(128 + signal.SIGKILL, deadline_evidence=False), "killed_unknown")
        self.assertEqual(classify_returncode(-signal.SIGKILL, deadline_evidence=True), "deadline")
        self.assertEqual(classify_returncode(0, deadline_evidence=False), "complete")

    def test_rc137_fixture_without_deadline_is_killed_unknown(self):
        plan = DeadlinePlan.fixed(10_000)
        proc = FakeProcess()
        proc.returncode = 137
        result = supervise(
            ["mock-command"],
            plan=plan,
            clock=FakeClock(plan.start_ns),
            popen_factory=lambda *a, **k: proc,
            group_alive=lambda _pgid: False,
            rss_reader=lambda _pgid: 1,
            install_limits=False,
        )
        self.assertEqual(result.returncode, 137)
        self.assertEqual(result.status, "killed_unknown")
        self.assertFalse(result.deadline_evidence)

    def test_mock_process_is_term_then_kill_inside_fixed_cleanup_window(self):
        plan = DeadlinePlan.fixed(10_000)
        clock = FakeClock(plan.term_ns)
        proc = FakeProcess()
        signals: list[int] = []

        def signal_group(_pgid: int, sig: int) -> None:
            signals.append(sig)
            if sig == signal.SIGKILL:
                proc.returncode = -signal.SIGKILL

        result = supervise(
            ["mock-command"],
            plan=plan,
            clock=clock,
            popen_factory=lambda *a, **k: proc,
            group_alive=lambda _pgid: proc.returncode is None,
            rss_reader=lambda _pgid: 1,
            signal_group=signal_group,
            sleep_ns=clock.sleep,
            install_limits=False,
        )
        self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
        self.assertEqual(result.status, "deadline")
        self.assertTrue(result.deadline_evidence)
        self.assertLessEqual(result.finished_ns, plan.total_ns)
        self.assertFalse(result.cleanup_uncertain)

    def test_deadline_kill_reports_actual_finish_and_uncertain_group_cleanup(self):
        plan = DeadlinePlan.fixed(10_000)
        clock = FakeClock(plan.total_ns + 17)
        proc = FakeProcess()
        signals: list[int] = []

        def signal_group(_pgid: int, sig: int) -> None:
            signals.append(sig)

        result = supervise(
            ["mock-command"],
            plan=plan,
            clock=clock,
            popen_factory=lambda *a, **k: proc,
            group_alive=lambda _pgid: True,
            rss_reader=lambda _pgid: 1,
            signal_group=signal_group,
            install_limits=False,
        )
        self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
        self.assertEqual(result.status, "deadline")
        self.assertTrue(result.cleanup_uncertain)
        self.assertTrue(result.group_alive_at_return)
        self.assertEqual(result.finished_ns, plan.total_ns + 17)

    def test_memory_cap_cleanup_kill_without_deadline_is_unknown_not_deadline(self):
        plan = DeadlinePlan.fixed(10_000)
        clock = FakeClock(plan.start_ns)
        proc = FakeProcess()
        signals: list[int] = []

        def signal_group(_pgid: int, sig: int) -> None:
            signals.append(sig)
            if sig == signal.SIGKILL:
                proc.returncode = -signal.SIGKILL

        result = supervise(
            ["mock-command"],
            plan=plan,
            clock=clock,
            popen_factory=lambda *a, **k: proc,
            group_alive=lambda _pgid: proc.returncode is None,
            rss_reader=lambda _pgid: RSS_CAP_BYTES,
            signal_group=signal_group,
            sleep_ns=clock.sleep,
            install_limits=False,
        )
        self.assertEqual(signals, [signal.SIGTERM, signal.SIGKILL])
        self.assertEqual(result.reason, "process_group_rss_cap")
        self.assertEqual(result.status, "killed_unknown")
        self.assertFalse(result.deadline_evidence)

    def test_missing_group_rss_measurement_fails_closed(self):
        plan = DeadlinePlan.fixed(10_000)
        clock = FakeClock(plan.start_ns)
        proc = FakeProcess()
        signals: list[int] = []

        def signal_group(_pgid: int, sig: int) -> None:
            signals.append(sig)
            if sig == signal.SIGTERM:
                proc.returncode = -signal.SIGTERM

        result = supervise(
            ["mock-command"],
            plan=plan,
            clock=clock,
            popen_factory=lambda *a, **k: proc,
            group_alive=lambda _pgid: proc.returncode is None,
            rss_reader=lambda _pgid: None,
            signal_group=signal_group,
            sleep_ns=clock.sleep,
            install_limits=False,
        )
        self.assertEqual(signals, [signal.SIGTERM])
        self.assertEqual(result.status, "resource_measurement_unavailable")
        self.assertEqual(result.reason, "process_group_rss_unavailable")

    def test_harmless_real_process_exits_under_bounded_supervisor(self):
        start = time.monotonic_ns()
        result = supervise(
            [sys.executable, "-c", "pass"],
            plan=DeadlinePlan.fixed(start),
            install_limits=False,
        )
        self.assertEqual(result.status, "complete")
        self.assertEqual(result.returncode, 0)
        self.assertFalse(result.term_sent)
        self.assertFalse(result.kill_sent)

    def test_bad_fixed_contract_is_rejected(self):
        plan = DeadlinePlan.fixed(0)
        broken = DeadlinePlan(plan.start_ns, plan.term_ns, plan.total_ns + 1, plan.native_ns)
        self.assertFalse(broken.valid_fixed_contract())


if __name__ == "__main__":
    unittest.main()
