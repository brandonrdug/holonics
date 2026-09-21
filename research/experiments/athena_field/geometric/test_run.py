import importlib.util
import tempfile
import unittest
from pathlib import Path


RUN_PATH = Path(__file__).with_name('run.py')
SPEC = importlib.util.spec_from_file_location('geometric_run', RUN_PATH)
run = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(run)


def report(*, declared, peeked, acknowledged, pending, retained=0, refused=0,
           paired=0, updates=0):
    return {
        'frames_declared': declared,
        'frames_peeked': peeked,
        'frames_acknowledged': acknowledged,
        'retained_pending_at_open': retained,
        'outcomes': {
            'native-request-refused': refused,
            'native-observation-refused': 0,
            'paired-and-applied': paired,
        },
        'generation_us': {'count': int(bool(pending))},
        'update_us': {'count': updates},
        'anatomy': {'pending': 0, 'pending_comparisons': [], 'retained_shared': pending},
        'held_request_symbols': 0,
        'context_source_lookup': {},
        'wall_us': 0,
    }


class PhaseReportTests(unittest.TestCase):
    def test_split_requires_every_frame_and_a_pending_comparison(self):
        split = report(declared=3, peeked=3, acknowledged=2, pending=[])
        errors = run.phase_errors(split, 'split', 3, require_pending=True)
        self.assertTrue(any('frames_acknowledged' in error for error in errors))
        self.assertTrue(any('retained comparison' in error for error in errors))

    def test_complete_split_resume_and_whole_reports_pass(self):
        split = report(declared=3, peeked=3, acknowledged=3, pending=[7])
        resumed = report(declared=1, peeked=1, acknowledged=1, pending=[], retained=1,
                         paired=1, updates=1)
        whole = report(declared=4, peeked=4, acknowledged=4, pending=[], paired=1, updates=1)
        self.assertEqual(run.phase_errors(split, 'split', 3, require_pending=True), [])
        self.assertEqual(run.phase_errors(resumed, 'resume', 1), [])
        self.assertEqual(run.phase_errors(whole, 'whole', 4), [])

    def test_incident_split_retains_the_same_native_and_exposure_comparison(self):
        split = report(declared=3, peeked=3, acknowledged=3, pending=[7])
        split['anatomy'].update(spec={'source_chart':'incident-field'}, pending=1, pending_comparisons=[7])
        self.assertEqual(run.phase_errors(split, 'split', 3, require_pending=True), [])
        split['anatomy']['pending_comparisons'] = [8]
        self.assertTrue(run.phase_errors(split, 'split', 3, require_pending=True))

    def test_phase_failure_writes_private_diagnostic(self):
        with tempfile.TemporaryDirectory() as directory:
            output = Path(directory)
            bad = report(declared=3, peeked=3, acknowledged=2, pending=[])
            with self.assertRaises(RuntimeError):
                run.fail_phase(output, 'split', bad, ['acknowledgment mismatch'], 3)
            self.assertTrue((output / 'split-phase-error.json').exists())

    def test_public_field_request_requires_the_emitted_event_schema(self):
        event = {'schema': run.STREAM_EVENT_SCHEMA, 'event': 'field-request', 'value': {'epoch': 1}}
        self.assertEqual(run.public_field_request([event]), {'epoch': 1})
        with self.assertRaises(ValueError):
            run.public_field_request([{'event': 'field-request', 'value': {}}])
        with self.assertRaises(ValueError):
            run.public_field_request([event, event])

    def test_receiver_mode_comes_from_declared_metadata(self):
        self.assertEqual(run.resolve_codec(None, {
            'codec': 'unicode-scalars', 'source_chart': 'incident-field'}), 'unicode-scalars')
        self.assertEqual(run.resolve_codec(None, {
            'codec': 'unicode-scalars', 'source_chart': 'incident-field',
            'response_aperture': 8, 'solve_steps': 32}), 'unicode-scalars')
        self.assertEqual(run.resolve_codec('utf8-nibbles', {
            'codec': 'utf8-nibbles', 'source_chart': 'geometric-regions'}), 'utf8-nibbles')
        with self.assertRaises(ValueError):
            run.resolve_codec(None, {'source_chart': 'unknown'})
        with self.assertRaises(ValueError):
            run.resolve_codec('unicode-scalars', {'source_chart': 'geometric-regions'})


if __name__ == '__main__':
    unittest.main()
