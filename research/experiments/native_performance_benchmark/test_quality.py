import copy
from fractions import Fraction as Q
import unittest

import quality


class ConsequenceReceiversTest(unittest.TestCase):
    def test_existing_evidence_reports_missing_values_separately_from_given(self):
        events=[r for r in quality.load_lines(quality.FIELD/'run/evaluation-events.jsonl') if r['event']=='field-request']
        result=quality.check_field(events)
        rows=[r for family in result['families'].values() for r in family]
        self.assertEqual((len(rows),sum(r['inferred_correct'] for r in rows),sum(r['supplied_preserved'] for r in rows)),(39,45,63))
        changed=copy.deepcopy(events)
        changed[0]['value']['symbols']=[]
        rows=[r for group in quality.check_field(changed)['families'].values() for r in group]
        self.assertFalse(rows[0]['complete_correct'])
        self.assertEqual(rows[0]['inferred_correct'],0)
        self.assertGreater(rows[0]['inferred_count'],0)
        changed=copy.deepcopy(events)
        changed[0]['value']['text']='wrong visible rendering'
        rows=[r for group in quality.check_field(changed)['families'].values() for r in group]
        self.assertFalse(rows[0]['complete_correct'])
        self.assertFalse(rows[0]['presentation_agrees_with_symbols'])

    def test_missing_or_refused_responses_cannot_silently_zip_to_success(self):
        with self.assertRaises(ValueError):quality.check_events([],1,'field-request')
        with self.assertRaises(ValueError):quality.check_events([{'sequence':1,'event':'refused'}],1,'field-request')
        with self.assertRaises(ValueError):quality.check_events([{'sequence':1,'event':'x'},{'sequence':3,'event':'x'}],2,'x')

    def test_exact_enclosure_and_task_error_are_distinct(self):
        output={'center':[{'real':{'numerator':'1','denominator':'3'},'imaginary':{'numerator':'0','denominator':'1'}}],
                'radius':{'numerator':'0','denominator':'1'}}
        self.assertTrue(quality.enclosure_difference(output,[(Q(1,3),Q(0))])['contains_reference'])
        self.assertFalse(quality.enclosure_difference(output,[(Q(0),Q(0))])['contains_reference'])
        with self.assertRaises(ValueError):quality.enclosure_difference(output,[])

    def test_algebra_uses_returned_factors_not_claimed_tensor_image(self):
        rows=quality.load_lines(quality.MATH/'responses.jsonl')
        factors=copy.deepcopy(rows[46]['value']['factors'])
        original=quality.factor_tensor(factors)
        factors['left_forms'][0][0]={'numerator':'999','denominator':'1'}
        self.assertNotEqual(quality.factor_tensor(factors),original)

    def test_old_math_run_has_four_distinct_preparations_and_nonzero_task_error(self):
        result=quality.check_math(quality.load_lines(quality.MATH/'responses.jsonl'))
        self.assertEqual(result['normal_query_count'],35)
        self.assertEqual(result['distinct_normal_preparations'],4)
        self.assertTrue(all(r['contains_reference'] for r in result['normal']))
        exchange=[r['unregularized_exchange'] for r in result['normal'] if 'unregularized_exchange' in r]
        self.assertTrue(all(not r['contains_reference'] for r in exchange))
        self.assertTrue(result['algebra'][0]['all_coefficients_equal'])
        self.assertFalse(result['algebra'][2]['source_products_recomputed'])


if __name__=='__main__':unittest.main()
