"""Tests of tools/gsm8k_variants.py, the exterior terrain that generates variants of problems.

    python3 -m unittest tools/test_gsm8k_variants.py

Every problem here is synthetic and written for the test; no dataset text is read.
"""

import contextlib
import io
import json
import os
import re
import sys
import tempfile
import unittest
from fractions import Fraction

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import gsm8k_variants as g  # noqa: E402

CARRY = """Tom buys 12 pens at 5 dollars each and then pays 3 dollars for a bag. How much did he spend?
He pays 12*5=<<12*5=60>>60 dollars for the pens.
In total he spends 60+3=<<60+3=63>>63 dollars.
#### 63"""

HALF = """A box holds 24 pencils. Sam takes 3 boxes and gives half of all the pencils to a friend. How many does he keep?
He has 3*24=<<3*24=72>>72 pencils.
He keeps 72/2=<<72/2=36>>36 pencils.
#### 36"""

PERCENT = """Maya earns 80 dollars and saves 50% of it. How much does she save?
She saves 80*50/100=<<80*50/100=40>>40 dollars.
#### 40"""

DECIMAL = """A book costs 12.5 dollars and Ana buys 4 books. How much does she pay?
She pays 12.5*4=<<12.5*4=50>>50 dollars.
#### 50"""

SPLIT = """A rope is 91 meters long and is cut into 7 equal pieces. How long is a piece?
Each piece is 91/7=<<91/7=13>>13 meters.
#### 13"""

AMBIGUOUS = """Ben has 12 apples, 3 pears and 4 plums. How many pieces of fruit are there?
The pears and plums make 3*4=<<3*4=12>>12 pieces.
With the apples there are 12+12=<<12+12=24>>24 pieces.
#### 24"""

COMMAS = """A town of 1,000 people holds its 3rd fair at 10:30 and sells 25 tickets. How many tickets are left?
The town has 1,000-25=<<1000-25=975>>975 people without a ticket.
#### 975"""

FIXED = """Lena works 6 days a week. How many minutes does she work if she works one full day each time?
A day has 24*60=<<24*60=1440>>1440 minutes.
She works 6*1440=<<6*1440=8640>>8640 minutes.
#### 8640"""

# One question number, and every other digit a constant: no replacement can be found.
EXHAUSTED = """Kim has 5 coins. How many are there with the others?
Together 5+1+2+3+4+6+7+8+9=<<5+1+2+3+4+6+7+8+9=45>>45 coins.
#### 45"""


def parse(text):
    return g.parse_problems(text)[0]


def first_variant(problem, seeds=range(200), index=0, **kw):
    """The first variant over the seeds, with the seed that gave it."""
    for seed in seeds:
        variant, receipt = g.variant_of(problem, index, 0, seed, **kw)
        if variant is not None:
            return variant, seed
    raise AssertionError("no seed gave a variant")


def calculations(passage):
    """(expression, stated result, exact value of the expression) of each calculation."""
    out = []
    for m in g.CALCULATION.finditer(passage):
        leaves, ast = g.parse_expression(m.group(1))
        out.append((m.group(1), g.to_value(m.group(2)), g.evaluate(ast, [x[3] for x in leaves])))
    return out


def values(text):
    return [g.to_value(t[2]) for t in g.number_tokens(text)]


class Parse(unittest.TestCase):
    def test_passages_split_on_one_blank_line(self):
        problems = g.parse_problems(CARRY + "\n\n" + HALF + "\n")
        self.assertEqual(len(problems), 2)
        self.assertEqual(problems[0].answer, "63")
        self.assertEqual(len(problems[0].solution), 2)
        self.assertEqual(problems[0].passage(), CARRY)

    def test_a_problem_without_its_answer_line_is_refused(self):
        with self.assertRaises(ValueError):
            g.parse_problems("a question\na line")

    def test_the_identity_render_is_the_original(self):
        for text in (CARRY, HALF, DECIMAL, COMMAS, FIXED, AMBIGUOUS):
            problem = parse(text)
            a = g.analyse(problem)
            new_q = [t.value for t in a.q_roles]
            new_c = [c.result for c in a.calcs]
            question, solution, answer = g.render(a, new_q, new_c, [t.text for t in a.q_roles])
            self.assertEqual(g.Variant(0, 0, question, solution, answer, (), {}).passage(), text)


class Carry(unittest.TestCase):
    def test_the_second_calculation_consumes_the_first_result(self):
        problem = parse(CARRY)
        a = g.analyse(problem)
        self.assertEqual([c.roles for c in a.calcs],
                         [[("q", 0), ("q", 1)], [("c", 0), ("q", 2)]])
        variant, _ = first_variant(problem)
        first, second = calculations(variant.passage())
        self.assertEqual(first[1], first[2])
        self.assertEqual(second[1], second[2])
        q = values(variant.question)[:3]
        self.assertEqual(first[1], q[0] * q[1])
        self.assertEqual(second[1], first[1] + q[2])
        # the carried operand is written as the first calculation's new result
        self.assertTrue(variant.solution[1].startswith(f"In total he spends {first[1]}+{q[2]}="))
        self.assertEqual(g.to_value(variant.answer), second[1])
        self.assertEqual(variant.solution[0].split("=")[0], f"He pays {q[0]}*{q[1]}")

    def test_the_prose_carries_no_original_number_but_its_constants(self):
        variant, _ = first_variant(parse(CARRY))
        prose = g.CALCULATION.sub("", "\n".join(variant.solution))
        self.assertFalse({12, 5, 3, 60, 63} & {int(v) for v in values(prose)})

    def test_a_fixed_calculation_is_a_constant_and_does_not_block_a_variant(self):
        problem = parse(FIXED)
        a = g.analyse(problem)
        self.assertEqual(a.fixed, frozenset({0}))
        variant, _ = first_variant(problem)
        self.assertTrue(variant.solution[0].startswith("A day has 24*60=<<24*60=1440>>1440"))
        q = values(variant.question)[0]
        self.assertEqual(g.to_value(variant.answer), q * 1440)


class Constants(unittest.TestCase):
    def test_a_constant_operand_is_left_alone(self):
        variant, _ = first_variant(parse(PERCENT))
        expr = g.CALCULATION.search(variant.solution[0]).group(1)
        self.assertTrue(expr.endswith("/100"))
        a, b = values(variant.question)[:2]
        self.assertEqual(expr, f"{a}*{b}/100")
        self.assertEqual(calculations(variant.passage())[0][1], Fraction(a * b, 100))

    def test_a_halving_constant_stays(self):
        variant, _ = first_variant(parse(HALF))
        _, second = calculations(variant.passage())
        self.assertEqual(g.CALCULATION.findall(variant.solution[1])[0][0].split("/")[1], "2")
        self.assertEqual(second[1] * 2, calculations(variant.passage())[0][1])
        roles = variant.record["calcs"][1]["operands"]
        self.assertEqual([x["role"] for x in roles], ["c:0", "const"])
        self.assertEqual(roles[1]["orig"], roles[1]["new"])


class Decimals(unittest.TestCase):
    def test_a_decimal_number_keeps_its_places(self):
        variant, _ = first_variant(parse(DECIMAL))
        token = g.number_tokens(variant.question)[0][2]
        self.assertRegex(token, r"^[1-9]\d\.[1-9]$")
        (_, result, exact), = calculations(variant.passage())
        self.assertEqual(result, exact)
        self.assertEqual(result.denominator, 1)
        self.assertIn(f"<<{token}*", variant.solution[0])

    def test_a_comma_number_keeps_its_grouping_and_the_skipped_tokens_stay(self):
        variant, _ = first_variant(parse(COMMAS))
        self.assertIn("3rd", variant.question)
        self.assertIn("10:30", variant.question)
        number = re.search(r"A town of (\S+) people", variant.question).group(1)
        self.assertRegex(number, r"^[1-9],\d{3}$")
        self.assertIn(f"{number}-", variant.solution[0])


class Refusals(unittest.TestCase):
    def test_a_fractional_result_is_refused_and_every_written_result_is_whole(self):
        problem = parse(SPLIT)
        fractional = 0
        written = 0
        for seed in range(40):
            variant, receipt = g.variant_of(problem, 0, 0, seed)
            fractional += receipt["reasons"]["fractional"]
            if variant is not None:
                written += 1
                (_, result, exact), = calculations(variant.passage())
                self.assertEqual(result, exact)
                self.assertEqual(result.denominator, 1)
        self.assertGreater(fractional, 0)
        self.assertGreater(written, 0)

    def test_a_negative_result_is_refused(self):
        problem = parse("Ed has 40 stickers and gives away 15. How many are left?\n"
                        "He has 40-15=<<40-15=25>>25 left.\n#### 25")
        negative = 0
        for seed in range(40):
            variant, receipt = g.variant_of(problem, 0, 0, seed)
            negative += receipt["reasons"]["negative"]
            if variant is not None:
                self.assertGreaterEqual(g.to_value(variant.answer), 0)
        self.assertGreater(negative, 0)

    def test_a_replacement_that_collides_with_a_constant_leaves_no_variant(self):
        variant, receipt = g.variant_of(parse(EXHAUSTED), 0, 0, 1, tries=8)
        self.assertIsNone(variant)
        self.assertEqual(receipt["refused"], 8)
        self.assertEqual(receipt["reasons"]["q_const"] + receipt["reasons"]["q_same"]
                         + receipt["reasons"]["q_original"], 8)

    def test_a_decimal_result_longer_than_the_original_is_refused(self):
        problem = parse("A pack costs 2.5 dollars and Joy buys 4 packs. What does she pay?\n"
                        "She pays 2.5*4=<<2.5*4=10>>10 dollars.\n#### 10")
        for seed in range(30):
            variant, receipt = g.variant_of(problem, 0, 0, seed)
            if variant is not None:
                (_, result, _), = calculations(variant.passage())
                self.assertEqual(result.denominator, 1)

    def test_a_problem_whose_answer_is_no_source_has_no_variant(self):
        problem = parse("Al has 7 cards.\nHe has <<7+0=7>>7 cards and keeps 5 of them.\n#### 5")
        variant, receipt = g.variant_of(problem, 0, 0, 1)
        self.assertIsNone(variant)
        self.assertEqual(receipt["unusable"], "answer")

    def test_a_problem_without_a_calculation_has_no_variant(self):
        variant, receipt = g.variant_of(parse("Al has 7 cards.\nHe has 7.\n#### 7"), 0, 0, 1)
        self.assertIsNone(variant)
        self.assertEqual(receipt["unusable"], "no_calcs")

    def test_variants_of_one_problem_differ(self):
        problem = parse(CARRY)
        first, _ = g.variant_of(problem, 0, 0, 5)
        second, _ = g.variant_of(problem, 0, 1, 5, avoid={first.key})
        self.assertNotEqual(first.key, second.key)


class Roles(unittest.TestCase):
    def test_no_question_number_of_the_original_survives_in_a_variant(self):
        for text in (CARRY, HALF, DECIMAL, COMMAS, AMBIGUOUS):
            problem = parse(text)
            original = set(values(problem.question))
            for seed in range(25):
                variant, _ = g.variant_of(problem, 3, 0, seed)
                if variant is None:
                    continue
                self.assertFalse(original & set(values(variant.question)), text)
                self.assertEqual(len(values(variant.question)), len(values(problem.question)))

    def test_a_variant_keeps_the_digit_counts_of_the_numbers(self):
        problem = parse(CARRY)
        variant, _ = first_variant(problem)
        old = [len(t[2]) for t in g.number_tokens(problem.question)]
        new = [len(t[2]) for t in g.number_tokens(variant.question)]
        self.assertEqual(old, new)
        # the question outside its numbers is the original's
        self.assertEqual(re.sub(g.NUMBER, "#", problem.question),
                         re.sub(g.NUMBER, "#", variant.question))

    def test_the_roles_record_of_a_variant(self):
        variant, seed = first_variant(parse(CARRY))
        record = variant.record
        self.assertEqual((record["problem"], record["variant"], record["seed"]), (0, 0, seed))
        q = values(variant.question)
        self.assertEqual([r["orig"] for r in record["roles"]], ["12", "5", "3"])
        self.assertEqual([g.to_value(r["new"]) for r in record["roles"]], q[:3])
        self.assertEqual([[o["role"] for o in c["operands"]] for c in record["calcs"]],
                         [["q:0", "q:1"], ["c:0", "q:2"]])
        self.assertEqual(record["calcs"][1]["operands"][0]["orig"], "60")
        self.assertEqual(record["calcs"][1]["operands"][0]["new"], record["calcs"][0]["new_result"])
        self.assertEqual(record["calcs"][0]["orig_result"], "60")
        self.assertTrue(record["calcs"][0]["orig_exact"])
        self.assertEqual(record["answer"]["role"], "c:1")
        self.assertEqual(record["answer"]["orig"], "63")
        self.assertEqual(record["answer"]["new"], variant.answer)
        self.assertEqual(record["ambiguous_operands"], 0)

    def test_an_operand_that_matches_two_sources_is_counted_and_takes_the_calculation(self):
        a = g.analyse(parse(AMBIGUOUS))
        self.assertEqual(a.ambiguous, 2)  # both operands of 12+12 are a question number and a result
        self.assertEqual(a.calcs[1].roles, [("c", 0), ("c", 0)])
        self.assertEqual(a.calcs[0].roles, [("q", 1), ("q", 2)])


class Stream(unittest.TestCase):
    def test_the_stream_is_deterministic_and_keyed(self):
        a = [g.Stream(7, 3, 1).below(1000) for _ in range(3)]
        self.assertEqual(a, [g.Stream(7, 3, 1).below(1000) for _ in range(3)])

        def draws(*key):
            stream = g.Stream(*key)
            return [stream.below(10**6) for _ in range(5)]

        self.assertNotEqual(draws(7, 3, 1), draws(7, 3, 0))
        self.assertNotEqual(draws(7, 3, 1), draws(7, 2, 1))
        # an xor of the keys would give these two the same stream
        self.assertNotEqual(draws(7, 2, 1), draws(7, 3, 0))

    def test_the_same_seed_gives_the_same_variant_and_another_seed_another(self):
        problem = parse(CARRY)
        one, _ = g.variant_of(problem, 4, 0, 11)
        two, _ = g.variant_of(problem, 4, 0, 11)
        other, _ = g.variant_of(problem, 4, 0, 12)
        self.assertEqual(one.passage(), two.passage())
        self.assertEqual(one.record, two.record)
        self.assertNotEqual(one.passage(), other.passage())


class Cli(unittest.TestCase):
    def run_cli(self, source, *extra):
        directory = tempfile.TemporaryDirectory()
        self.addCleanup(directory.cleanup)
        path = os.path.join(directory.name, "in.txt")
        out = os.path.join(directory.name, "out.txt")
        with open(path, "w", encoding="utf-8") as f:
            f.write(source)
        stdout, stderr = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stderr):
            code = g.main([path, out, *extra])
        self.assertEqual(code, 0)
        with open(out, encoding="utf-8") as f:
            text = f.read()
        with open(out + ".roles", encoding="utf-8") as f:
            roles = [json.loads(line) for line in f]
        return stdout.getvalue(), stderr.getvalue(), text, roles

    def test_the_summary_line_the_passages_and_the_sidecar(self):
        source = "\n\n".join([CARRY, HALF, EXHAUSTED]) + "\n"
        stdout, stderr, text, roles = self.run_cli(source, "--variants", "2", "--seed", "20261101")
        lines = stdout.strip().split("\n")
        self.assertEqual(len(lines), 1)
        self.assertRegex(lines[0], r"^VARIANTS problems=3 written=\d+ refused_draws=\d+ "
                                   r"no_variant=\d+ ambiguous_operands=\d+ elapsed_ms=\d+$")
        fields = dict(f.split("=") for f in lines[0].split()[1:])
        passages = g.parse_problems(text)
        self.assertEqual(len(passages), int(fields["written"]))
        self.assertEqual(len(roles), int(fields["written"]))
        self.assertEqual(int(fields["written"]) + int(fields["no_variant"]), 6)
        self.assertGreaterEqual(int(fields["no_variant"]), 2)  # the exhausted problem
        self.assertTrue(stderr.startswith("DETAIL "))
        # the originals are not written, and each variant stands under its record
        self.assertNotIn("Tom buys 12 pens", text)
        for passage, record in zip(passages, roles):
            self.assertEqual(passage.answer, record["answer"]["new"])
        self.assertEqual([r["variant"] for r in roles if r["problem"] == 0], [0, 1])

    def test_the_output_is_reproducible(self):
        source = CARRY + "\n\n" + DECIMAL + "\n"
        one = self.run_cli(source, "--seed", "9")
        two = self.run_cli(source, "--seed", "9")
        self.assertEqual(one[2:], two[2:])
        self.assertEqual(re.sub(r"elapsed_ms=\d+", "", one[0]), re.sub(r"elapsed_ms=\d+", "", two[0]))

    def test_tries_bound_the_draws(self):
        _, _, text, _ = self.run_cli(EXHAUSTED + "\n", "--seed", "1", "--tries", "3")
        self.assertEqual(text, "")


def add(a, b, name="Ann"):
    return (f"{name} has {a} stickers and Bo has {b} stickers. How many do they have together?\n"
            f"Together they have {a}+{b}=<<{a}+{b}={a + b}>>{a + b} stickers.\n#### {a + b}")


def escaped(release):
    """A release as the FREE.tsv of tools/gsm8k writes a field."""
    return "".join("\\x7c" if b == 0x7C else chr(b).encode("unicode_escape").decode()
                   if 32 <= b < 127 or b in (9, 10, 13) else f"\\x{b:02x}" for b in release)


class ClaimFixture(unittest.TestCase):
    """Two or more held problems, their variants through the tool, and releases written by the
    test: the originals' releases and the variants' releases as two directories of FREE.tsv."""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.root = self.dir.name

    def path(self, *parts):
        return os.path.join(self.root, *parts)

    def make(self, problems, seed="5"):
        with open(self.path("held.txt"), "w", encoding="utf-8") as f:
            f.write("\n\n".join(problems) + "\n")
        with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            g.main([self.path("held.txt"), self.path("variants.txt"), "--variants", "2", "--seed", seed])
        with open(self.path("variants.txt.roles"), encoding="utf-8") as f:
            self.records = [json.loads(line) for line in f]
        self.assertEqual(len(self.records), 2 * len(problems))
        return self.records

    def new(self, n, k):
        """The variant n's number for role k, as text."""
        return self.records[n]["roles"][k]["new"]

    def release_dir(self, name, releases):
        os.makedirs(self.path(name))
        with open(self.path(name, "FREE.tsv"), "w", encoding="latin-1") as f:
            f.write("".join(f"{i}\t{escaped(r)}\n" for i, r in enumerate(releases)))
        return self.path(name)

    def claim(self, orig_releases, var_releases):
        dirs = (self.release_dir("orig", orig_releases), self.release_dir("var", var_releases))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            g.main(["claim", self.path("held.txt"), self.path("variants.txt"),
                    self.path("variants.txt.roles"), *dirs])
        return out.getvalue().strip().split("\n")


class ReleaseReading(unittest.TestCase):
    def test_calculations_are_the_well_formed_markups_before_the_first_blank_line(self):
        release = b"a <<1+2=3>>3 <<x=5>> <<4*5.5=22>>22 <<7-2=\n\n<<9+9=18>>"
        self.assertEqual(g.release_calculations(release),
                         [[Fraction(1), Fraction(2)], [Fraction(4), Fraction("5.5")]])
        self.assertEqual(g.release_calculations(b"<<8*(2+1)=24>>24\n\n<<9+9=18>>"),
                         [[Fraction(8), Fraction(2), Fraction(1)]])
        self.assertEqual(g.release_calculations(b"no markup here"), [])

    def test_claim_of_counts_a_role_taken_under_any_operation_and_not_a_shifted_one(self):
        record = {"roles": [{"role": 0, "orig": "14", "new": "52"}, {"role": 1, "orig": "23", "new": "71"}]}
        two = [[Fraction(14), Fraction(23)], [Fraction(14), Fraction(9)]]
        # calculation 0 takes both new numbers by a product; calculation 1 is missing
        self.assertEqual(g.claim_of(two, [[Fraction(52), Fraction(71)]], record), (3 - 1, 3))
        # the new numbers one calculation late are not taken
        self.assertEqual(g.claim_of(two, [[Fraction(2)], [Fraction(52), Fraction(71)]], record), (1, 3))
        # the original's numbers copied are not taken
        self.assertEqual(g.claim_of(two, [[Fraction(14), Fraction(23)], [Fraction(14)]], record), (0, 3))
        # an operand that is no question number is not counted
        self.assertEqual(g.claim_of([[Fraction(5), Fraction(6)]], [[Fraction(5)]], record), (0, 0))


class Claim(ClaimFixture):
    def build(self):
        self.make([add(14, 23), add(31, 46, "Cy")])
        n = self.new
        # problem 0 (variants 0, 1): the original writes `14+23` and a calculation from no question number
        original0 = b"Together <<14+23=37>>37 and <<37*2=74>>74."
        # problem 1 (variants 2, 3): two calculations that take both numbers
        original1 = b"<<31*46=1426>>1426 then <<46+31=77>>77"
        variants = [
            # a different operation from the original's, both numbers taken
            f"<<{n(0, 0)}*{n(0, 1)}={int(n(0, 0)) * int(n(0, 1))}>>x".encode(),
            # a malformed markup first (not a calculation), then the first number taken only
            f"<<x=5>> <<{n(1, 0)}+5={int(n(1, 0)) + 5}>>".encode(),
            # only calculation 0 is written: calculation 1 is missing
            f"<<{n(2, 0)}*{n(2, 1)}={int(n(2, 0)) * int(n(2, 1))}>>".encode(),
            # calculation 0 takes no question number, calculation 1 takes both
            f"<<2*3=6>>6 <<{n(3, 1)}+{n(3, 0)}={int(n(3, 0)) + int(n(3, 1))}>>".encode(),
        ]
        return [original0, original1], variants

    def test_the_summary_and_the_lines_a_variant(self):
        originals, variants = self.build()
        lines = self.claim(originals, variants)
        self.assertEqual(
            lines[0], "VARIANTS_CLAIM taken=7 of=12 share_millionths=583333 problems=2 "
                      "calculations_original=4 calculations_variant=5")
        self.assertEqual(lines[1], "VARIANTS_COMPUTED variant_right=4 variant_of=4 original_right=3 original_of=3")
        self.assertEqual(lines[2:], [
            "VARIANTS_CLAIM_PROBLEM index=0 variant=0 taken=2 of=2",
            "VARIANTS_CLAIM_PROBLEM index=0 variant=1 taken=1 of=2",
            "VARIANTS_CLAIM_PROBLEM index=1 variant=0 taken=2 of=4",
            "VARIANTS_CLAIM_PROBLEM index=1 variant=1 taken=2 of=4",
        ])

    def test_no_operand_from_the_question_is_a_share_of_zero(self):
        self.make([add(14, 23)])
        lines = self.claim([b"<<2+2=4>>4"], [b"<<2+2=4>>4", b""])
        self.assertEqual(lines[0], "VARIANTS_CLAIM taken=0 of=0 share_millionths=0 problems=1 "
                                   "calculations_original=1 calculations_variant=1")

    def test_the_sidecar_must_describe_the_files(self):
        originals, variants = self.build()
        with open(self.path("variants.txt.roles"), encoding="utf-8") as f:
            records = [json.loads(line) for line in f]
        records[1]["roles"][0]["new"] = "99"
        with open(self.path("variants.txt.roles"), "w", encoding="utf-8") as f:
            f.write("".join(json.dumps(r) + "\n" for r in records))
        with self.assertRaises(SystemExit):
            self.claim(originals, variants)

    def test_a_release_directory_must_hold_one_row_a_passage(self):
        originals, variants = self.build()
        with self.assertRaises(SystemExit):
            self.claim(originals, variants[:3])


class Show(ClaimFixture):
    def build(self):
        self.make([add(14, 23), add(31, 46, "Cy"), add(52, 17, "Di"), add(28, 65, "Ed"),
                   add(41, 12, "Flo")])
        originals = [
            b"<<2+2=4>>4",  # problem 0 takes no question number
            b"<<31+46=77>>77\n\nafter a blank line",
            b"<<17+52=69>>69\tand a tab",
            b"<<28*65=1820>>1820",
            b"<<41+12=53>>53",  # a fourth qualifying problem, not shown
        ]
        variants = [f"variant release {n}\n\nsecond paragraph \\ {n}".encode() for n in range(10)]
        return originals, variants

    def run_show(self, out_file):
        originals, variants = self.build()
        dirs = (self.release_dir("orig", originals), self.release_dir("var", variants))
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            g.main(["show", self.path("held.txt"), self.path("variants.txt"),
                    self.path("variants.txt.roles"), *dirs, out_file])
        return out.getvalue().strip(), originals, variants

    def test_three_problems_with_their_two_variants_verbatim(self):
        out_file = self.path(".local", "report.txt")
        os.makedirs(os.path.dirname(out_file))
        line, originals, variants = self.run_show(out_file)
        self.assertEqual(line, "VARIANTS_SHOW shown=3 indices=1,2,3")
        with open(self.path("held.txt"), encoding="utf-8") as f:
            held = g.parse_problems(f.read())
        with open(self.path("variants.txt"), encoding="utf-8") as f:
            made = g.parse_problems(f.read())
        with open(out_file, "rb") as f:
            data = f.read()
        expected = b""
        for p in (1, 2, 3):
            expected += (f"=== problem {p} ===\n--- original question\n".encode()
                         + held[p].question.encode() + b"\n--- original release\n"
                         + originals[p] + b"\n")
            for v in (0, 1):
                n = 2 * p + v
                expected += (f"--- variant {v} question\n".encode() + made[n].question.encode()
                             + f"\n--- variant {v} release\n".encode() + variants[n] + b"\n")
        self.assertEqual(data, expected)
        self.assertNotIn(b"=== problem 0 ===", data)
        self.assertNotIn(b"=== problem 4 ===", data)

    def test_the_report_is_refused_outside_a_local_directory(self):
        with self.assertRaises(SystemExit):
            self.run_show(self.path("report.txt"))


class ComputedReading(unittest.TestCase):
    def test_computed_counts_right_calculations_with_the_question_numbers(self):
        release = b"a <<3+4=7>>7 then <<7*2=15>>15 then <<5*5=25>>25\n\nrest"
        self.assertEqual(g.computed_of(release, {Fraction(3), Fraction(7)}), (1, 2))
        self.assertEqual(g.computed_of(release, {Fraction(5)}), (1, 1))
        self.assertEqual(g.computed_of(release, set()), (0, 0))


if __name__ == "__main__":
    unittest.main()
