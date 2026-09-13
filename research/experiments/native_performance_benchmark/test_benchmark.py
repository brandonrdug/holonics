import unittest
import sys

import benchmark

class MeasurementHelpersTest(unittest.TestCase):
    def test_process_resource_receiver_preserves_output_and_child_cost(self):
        completed, outer_wall, resources = benchmark.measured_process(
            [sys.executable, "-c", "print('measured')"])
        self.assertEqual(completed.returncode, 0)
        self.assertEqual(completed.stdout.strip(), "measured")
        self.assertGreater(resources["max_rss_kib"], 0)
        self.assertGreaterEqual(outer_wall, resources["child_wall_ns"])

    def test_rate_aggregates_count_over_total_elapsed_time(self):
        self.assertEqual(
            benchmark.rate(2, 3_000_000_000, "events/second"),
            {"numerator": "2", "denominator": "3", "unit": "events/second"},
        )

    def test_rate_rejects_nonpositive_elapsed_time(self):
        with self.assertRaises(ValueError):
            benchmark.rate(1, 0, "events/second")
        with self.assertRaises(ValueError):
            benchmark.rate(1, -1, "events/second")

    def test_label_selection_excludes_setup_and_readout(self):
        self.assertEqual(
            benchmark.selected_samples([9, 10, 11, 12], ["setup", "apply", "apply", "readout"], "apply"),
            [10, 11],
        )

    def test_percentiles_retain_sample_count_and_explicit_stall_deadline(self):
        summary = benchmark.latency_summary([4, 1, 8, 2], stall_deadline_ns=7)
        self.assertEqual(summary["count"], 4)
        self.assertEqual(summary["percentiles"], {"p50": 2, "p95": 8, "p99": 8, "max": 8})
        self.assertEqual(summary["stall_count"], 1)
        self.assertIsNone(benchmark.latency_summary([1, 2])["stall_count"])

    def test_c5_power_reference_is_integer_and_independent(self):
        result = benchmark.vector_apply(benchmark.matrix_power(benchmark.c5_laplacian(), 16), [2, -1, 3, 5, -4])
        self.assertEqual(result, [2937109375, -1633203125, -294531250, 2109765625, -3119140625])

    def test_math_validation_rejects_missing_measured_event(self):
        _, labels = benchmark.math_requests(1)
        events = [{"event": "mathematical-return", "value": {"status": "constructed"}}] * len(labels)
        with self.assertRaises(AssertionError):
            benchmark.validate_math_events(events, labels, 1)

    def test_wave_validation_requires_every_committed_update(self):
        _, labels = benchmark.wave_requests(2)
        event = {"event": "next-symbol-received", "value": {"observation_committed": True, "epoch": 1}}
        with self.assertRaises(AssertionError):
            benchmark.validate_wave_events([event], labels, 2)

    def test_math_validation_rejects_fraction_hidden_by_integer_truncation(self):
        _, labels = benchmark.math_requests(1)
        expected = benchmark.vector_apply(benchmark.matrix_power(benchmark.c5_laplacian(), 16), benchmark.math_input(0))
        values = [{"status": "constructed"}, {"status": "constructed"},
                  {"status": "applied", "output": [benchmark.rat(0)] * 5},
                  {"status": "applied", "output": [benchmark.rat(x) for x in expected]},
                  {"status": "read", "output": [benchmark.rat(x) for x in expected]}]
        events = [{"event": "mathematical-return", "value": value} for value in values]
        benchmark.validate_math_events(events, labels, 1)
        values[3]["output"][0] = {"numerator": str(2 * expected[0] + 1), "denominator": "2"}
        with self.assertRaises(AssertionError):
            benchmark.validate_math_events(events, labels, 1)


if __name__ == "__main__":
    unittest.main()
