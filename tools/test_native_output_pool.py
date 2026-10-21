"""Controller closure adversaries only; actual native fork tests are separate."""
import json
from pathlib import Path
import tempfile
import unittest
from native_output_pool import sha, pins_valid, successful, sample_command

class Closure(unittest.TestCase):
    def test_full_question_command_is_explicit_and_not_a_training_alias(self):
        self.assertEqual(sample_command({'cells':512}),'sample-prepared-retained-512-v1')
        self.assertEqual(sample_command({'cells':512,'sample_command':'sample-prepared-retained-full-question-v1'}),'sample-prepared-retained-full-question-v1')
        for command in ['train','sample','sample-prepared-retained-fibre-v1']:
            with self.assertRaises(AssertionError):sample_command({'cells':512,'sample_command':command})
        with self.assertRaises(AssertionError):sample_command({'cells':128,'sample_command':'sample-prepared-retained-full-question-v1'})

    def test_changed_noncheckpoint_pin_refuses_even_when_every_output_completed(self):
        with tempfile.TemporaryDirectory() as directory:
            root=Path(directory);pins=[]
            for name in ['binary','checkpoint','prompt','keys']:
                p=root/name;p.write_bytes(name.encode());pins.append({'path':str(p),'sha256':sha(p)})
            plan=root/'plan.json';plan.write_text(json.dumps(pins));digest=sha(plan)
            self.assertTrue(successful(None,[{'complete':True}],pins_valid(plan,digest,pins)))
            (root/'prompt').write_bytes(b'changed after last child')
            self.assertFalse(successful(None,[{'complete':True}],pins_valid(plan,digest,pins)))
    def test_late_controller_stop_is_not_success_or_missing_terminal_coverage(self):
        completed=[{'complete':True,'terminal':True} for _ in range(5)]
        for stop in ['integrity_after_child','shared_elapsed_deadline','output_disk_limit']:
            self.assertFalse(successful(stop,completed,True))
            self.assertTrue(all(r['terminal'] for r in completed))
        self.assertFalse(successful(None,[{'complete':False}],True))
        self.assertFalse(successful(None,[],True))

if __name__=='__main__':unittest.main()
