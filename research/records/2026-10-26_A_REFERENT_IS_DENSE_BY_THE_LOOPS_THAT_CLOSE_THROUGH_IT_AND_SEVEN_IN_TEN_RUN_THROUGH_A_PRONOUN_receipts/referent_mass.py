"""The referent's mass and laps: the training text and the John samples, read exactly.

Usage: python3 -I referent_mass.py TRAIN_JSONL PARTITION_JSON RECORDS_DIR

TRAIN_JSONL is GSM8K's training split, PARTITION_JSON the output of tools/gsm8k/partition.py,
RECORDS_DIR the repository's research/records. The training text is render "b" of the audit
(question, newline, answer, blank line, over the training rows). Every count is an integer and
every share an exact fraction; the decimal beside a fraction is a printed reading.

Rules (written before the read):
- A named problem is design's: the question's first word is capitalized and occurs capitalized more
  often than lowercase in the training text (tools/listener/bank_trace.py, `named`).
- A person name is an opening name whose capital is not explained by a sentence start: after a
  lowercase word its lowercase form never occurs, or occurs less often than the capital.
- The sheets are the English third-person pronouns: m = he, him, his, himself; f = she, her, hers,
  herself. A name's sheet is the sheet of most of the problems it opens whose pronouns are of one
  sheet only; a tie leaves it unsheeted.
- A mention is a person name or a sheeted pronoun. A name resolves to itself. A pronoun resolves to
  the most recently mentioned referent of its sheet, or, when there is none, founds an unnamed
  referent of that sheet.
- A sample's answer is its text up to the first blank line (the blank line's clock resets there).
  The prompt is the held-out question about John, so a sample starts with John (sheet m) as the only
  referent.
"""

import collections
import glob
import hashlib
import json
import os
import re
import sys
import time
from fractions import Fraction

LETTERS = re.compile(r"[A-Za-z]+")
M = {"he", "him", "his", "himself"}
F = {"she", "her", "hers", "herself"}
CHECKS = []


def check(cond, what):
    CHECKS.append(what)
    if not cond:
        raise SystemExit("check failed: " + what)


def show(fr):
    fr = Fraction(fr)
    if fr.denominator == 1:
        return str(fr.numerator)
    whole, rest = divmod(fr.numerator * 1000, fr.denominator)
    if 2 * rest >= fr.denominator:
        whole += 1
    return "%d/%d (%d.%03d)" % (fr.numerator, fr.denominator, whole // 1000, whole % 1000)


def words(text):
    return LETTERS.findall(text)


class Referents:
    """Recency with sheet agreement: the observer's coreference rule."""

    def __init__(self, sheet_of, start=()):
        self.sheet_of = sheet_of
        self.order = list(start)  # most recent last
        self.founded = 0

    def sheet(self, r):
        if r.startswith("?"):
            return r[1]
        return self.sheet_of.get(r)

    def mention(self, w, names):
        lw = w.lower()
        if w in names:
            r = w
        elif lw in M or lw in F:
            s = "m" if lw in M else "f"
            r = next((x for x in reversed(self.order) if self.sheet(x) == s), None)
            if r is None:
                self.founded += 1
                r = "?%s%d" % (s, self.founded)
        else:
            return None
        if r in self.order:
            self.order.remove(r)
        self.order.append(r)
        return r


def read_mentions(text, names, refs):
    out = []
    for w in words(text):
        r = refs.mention(w, names)
        if r is not None:
            out.append((w, r))
    return out


def main():
    train_path, part_path, records = sys.argv[1:4]
    t0 = time.monotonic_ns()
    rows = [json.loads(l) for l in open(train_path, encoding="utf-8")]
    part = json.load(open(part_path))
    train = part["train_indices"]
    text = "".join(rows[i]["question"] + "\n" + rows[i]["answer"] + "\n\n" for i in train)
    digest = hashlib.sha256(text.encode()).hexdigest()
    check(digest.startswith("050b94f367625ad2"), "the training text is the audit's render b")

    counts = collections.Counter(words(text))
    mid_cap = collections.Counter(m.group(1) for m in re.finditer(r"[a-z]+ ([A-Za-z]+)\b", text))
    named = []
    for i in train:
        q, a = rows[i]["question"], rows[i]["answer"]
        m = LETTERS.match(q)
        if not m:
            continue
        w = m.group()
        if w[:1].isupper() and counts[w] > counts[w.lower()]:
            named.append((i, w))
    chunks = 0
    for m in re.finditer(r"(?s).+?(?:\n\n|\Z)", text):
        q, nl, a = m.group().partition("\n")
        mm = LETTERS.match(q)
        if nl and a and mm and mm.group()[:1].isupper() and counts[mm.group()] > counts[mm.group().lower()]:
            chunks += 1
    check(chunks == 4524, "design's rule over blank-line chunks counts 4,524")
    check(len(named) == 4523, "per training row the same rule counts 4,523 (a blank line inside one answer "
                              "makes design's extra chunk)")
    openers = collections.Counter(w for _, w in named)
    names = {w for w in openers if mid_cap[w] > mid_cap[w.lower()] or mid_cap[w.lower()] == 0}
    dropped = sorted((w for w in openers if w not in names), key=lambda w: -openers[w])

    def sheet_counts(s):
        ws = [x.lower() for x in words(s)]
        return sum(x in M for x in ws), sum(x in F for x in ws)

    by_name = collections.defaultdict(collections.Counter)
    for i, w in named:
        mm, ff = sheet_counts(rows[i]["question"] + "\n" + rows[i]["answer"])
        by_name[w]["m" if mm and not ff else "f" if ff and not mm else "both" if mm else "none"] += 1
    sheet_of = {}
    for w, c in by_name.items():
        if c["m"] > c["f"]:
            sheet_of[w] = "m"
        elif c["f"] > c["m"]:
            sheet_of[w] = "f"

    print("== A. The terrain: %d training problems, %d named, %d opening words, %d person names" % (
        len(train), len(named), len(openers), len(names)))
    print("opening words dropped as not names (capital explained by the sentence start):",
          ", ".join("%s %d" % (w, openers[w]) for w in dropped))
    print("person names by problems opened: " + ", ".join("%s %d" % (w, c) for w, c in openers.most_common(14) if w in names))
    jc = by_name["John"]
    print("John opens %d training problems; their pronouns: only he/him/his %d, only she/her %d, both %d, none %d" % (
        openers["John"], jc["m"], jc["f"], jc["both"], jc["none"]))
    check(openers.most_common(1)[0][0] == "John", "John is the most frequent opening name")
    check(sheet_of.get("John") == "m", "John's sheet is m")
    sheeted = [w for w in names if w in sheet_of]
    agree = sum(by_name[w][sheet_of[w]] for w in sheeted)
    against = sum(by_name[w]["f" if sheet_of[w] == "m" else "m"] for w in sheeted)
    print("sheeted names %d of %d; their problems with one sheet: agreeing %d, against %d" % (
        len(sheeted), len(names), agree, against))
    john_mentions_any = sum(1 for i in train if re.search(r"\bJohn\b", rows[i]["question"] + rows[i]["answer"]))
    print("training problems mentioning John anywhere: %d" % john_mentions_any)

    # Mass and laps of the opening referent, per named problem with a person opener.
    k_hist = collections.Counter()
    laps_id = laps_str = 0
    ans_by = collections.Counter()
    ans_c1 = collections.Counter()
    first_ok = first_n = 0
    n_people = 0
    for i, w in named:
        if w not in names or w not in sheet_of:
            continue
        n_people += 1
        q, a = rows[i]["question"], rows[i]["answer"]
        refs = Referents(sheet_of)
        mq = read_mentions(q, names, refs)
        ma = read_mentions(a, names, refs)
        k = sum(r == w for _, r in mq + ma)
        lit = sum(x == w for x, _ in mq + ma)
        k_hist[k] += 1
        laps_id += max(k - 1, 0)
        laps_str += max(lit - 1, 0)
        a_lit = sum(x == w for x, _ in ma)
        a_pro = sum(x != w and r == w for x, r in ma)
        ans_by["name" if a_lit else "pronoun only" if a_pro else "neither"] += 1
        if ma:
            ans_c1["all to opener" if all(r == w for _, r in ma) else "some elsewhere"] += 1
            first_n += 1
            first_ok += ma[0][1] == w
        else:
            ans_c1["no mention"] += 1
    print("problems opened by a sheeted person name: %d" % n_people)
    print("mentions resolved to the opener per problem (k: problems): " +
          ", ".join("%d: %d" % kv for kv in sorted(k_hist.items())))
    total_k = sum(k * c for k, c in k_hist.items())
    print("mass, summed: %d mentions; laps (k-1) identified with pronouns %d, by the name's letters alone %d" % (
        total_k, laps_id, laps_str))
    print("share of the laps that pass through a pronoun: %s" % show(Fraction(laps_id - laps_str, laps_id)))
    print("mean mass per problem: %s" % show(Fraction(total_k, n_people)))
    print("the answer re-mentions the opener: by name %d, by pronoun only %d, neither %d" % (
        ans_by["name"], ans_by["pronoun only"], ans_by["neither"]))
    print("answers whose every mention resolves to the opener %d, some elsewhere %d, no mention %d" % (
        ans_c1["all to opener"], ans_c1["some elsewhere"], ans_c1["no mention"]))
    print("answers whose first mention resolves to the opener: %s" % show(Fraction(first_ok, first_n)))
    check(laps_id > laps_str, "pronouns carry laps the letters do not")

    # Type against token: what follows the name at its mentions.
    nxt = collections.Counter()
    john_next = collections.Counter()
    for i, w in named:
        if w not in names:
            continue
        s = rows[i]["question"] + " " + rows[i]["answer"]
        for m in re.finditer(r"\b%s\b\W+([A-Za-z]+)" % re.escape(w), s):
            nxt[(w, m.group(1).lower())] += 1
            if w == "John":
                john_next[m.group(1).lower()] += 1
    pairs_once = sum(1 for c in nxt.values() if c == 1)
    print("(name, next word) pairs: %d distinct over %d mentions; %d occur once" % (
        len(nxt), sum(nxt.values()), pairs_once))
    print("after John in his %d problems: %d distinct next words over %d mentions; most: %s" % (
        openers["John"], len(john_next), sum(john_next.values()),
        ", ".join("%s %d" % kv for kv in john_next.most_common(8))))
    volunt = [i for i in train if re.search(r"volunt", rows[i]["question"] + rows[i]["answer"], re.I)]
    volunt_named = [w for i, w in named if i in set(volunt)]
    print("training problems with volunt-: %d; opened by a name: %d (%s)" % (
        len(volunt), len(volunt_named), ", ".join(sorted(volunt_named))))
    t1 = time.monotonic_ns()
    print("elapsed_ms %d" % ((t1 - t0) // 1000000))

    # B. The held-out problem and its reference answer, the foil.
    john = rows[207]
    check(207 in part["dev_indices"], "the John problem is held out")
    check(john["question"].startswith("John volunteers at a shelter"), "row 207 is the John problem")
    refs = Referents(sheet_of)
    mq = read_mentions(john["question"], names, refs)
    prompt_state = list(refs.order)
    ref_answer = john["answer"]
    ma = read_mentions(ref_answer, names, refs)
    print()
    print("== B. The held-out question and its reference answer")
    print("question mentions: %s" % " ".join("%s->%s" % m for m in mq))
    print("reference answer mentions: %s" % " ".join("%s->%s" % m for m in ma))
    k = sum(r == "John" for _, r in mq + ma)
    lit = sum(x == "John" for x, _ in mq + ma)
    print("mass of John over the problem %d; laps %d identified, %d by the letters J-o-h-n alone" % (
        k, k - 1, max(lit - 1, 0)))
    check(prompt_state == ["John"], "the prompt leaves John as the only referent")
    check(all(r == "John" for _, r in ma) and len(ma) == 2, "the reference answer keeps John twice, as he")

    # C. The committed samples.
    files = sorted(glob.glob(os.path.join(records, "2026-10-26_*_receipts", "SAMPLES*.md")))
    samples = []
    for f in files:
        tag = "_".join(os.path.basename(os.path.dirname(f)).split("_")[1:5]) + "/" + os.path.basename(f)
        section = header = ""
        inside = False
        buf = []
        for line in open(f, encoding="utf-8"):
            if inside:
                if line.startswith("```"):
                    inside = False
                    sub = section
                    if "PC_PASSES" in f:
                        first = header.split()[0].rstrip(",") if header else ""
                        sub = "%s, %s" % (first, "framed" if "framed" in header else "as written")
                    samples.append((tag, sub, "".join(buf)))
                    buf = []
                else:
                    buf.append(line)
                continue
            if line.startswith("```text"):
                inside = True
            elif line.startswith("## "):
                section = line[3:].strip()
            elif line.startswith("### "):
                header = line[4:].strip()
        check(not inside, "every text block in %s is closed" % os.path.basename(f))
    check(len(samples) == 400, "400 committed samples after the John question")

    def read_sample(s):
        answer = s.split("\n\n", 1)[0]
        refs = Referents(sheet_of, start=["John"])
        ms = read_mentions(answer, names, refs)
        j = sum(r == "John" for _, r in ms)
        nm = sum(x.lower() in M for x, _ in ms)
        nf = sum(x.lower() in F for x, _ in ms)
        others = {r for _, r in ms if r != "John"}
        sw = 0
        prev = "John"
        for _, r in ms:
            sw += r != prev
            prev = r
        whole = {x.lower() for x in words(s)}
        part = {x.lower() for x in words(answer)}
        return dict(n=len(ms), j=j, m=nm, f=nf, founded=len(others), switches=sw,
                    first=(ms[0][1] == "John") if ms else None,
                    named_others=sorted({r for r in others if not r.startswith("?")}),
                    whole=whole, part=part, volunt=("volunt" in s.lower(), "volunt" in answer.lower()))

    ref = read_sample(ref_answer)
    check(ref["n"] == 2 and ref["j"] == 2 and ref["founded"] == 0 and ref["switches"] == 0,
          "the reference answer: two mentions, both John, nothing founded, no switch")

    groups = collections.OrderedDict()
    for f, sec, s in samples:
        groups.setdefault((f, sec), []).append(read_sample(s))
    groups[("all", "")] = [r for g in list(groups.values()) for r in g]

    print()
    print("== C. The samples (answer = text before the first blank line), against the reference answer")
    print("columns: samples | with a person mention | first mention resolves to John | every mention resolves "
          "to John | founds another referent | any she-sheet pronoun | names John | mentions on John (pooled)")
    print("reference answer | 1 | 1 | 1 | 1 | 0 | 0 | 0 | 2 of 2")
    others_all = collections.Counter()
    for (f, sec), rs in groups.items():
        n = sum(r["n"] for r in rs)
        j = sum(r["j"] for r in rs)
        with_m = [r for r in rs if r["n"]]
        label = "ALL" if f == "all" else "%s | %s" % (f, sec[:80])
        print("%s | %d | %d | %d | %d | %d | %d | %d | %d of %d" % (
            label, len(rs), len(with_m), sum(1 for r in with_m if r["first"]),
            sum(1 for r in with_m if r["j"] == r["n"]), sum(1 for r in rs if r["founded"]),
            sum(1 for r in rs if r["f"]), sum(1 for r in rs if "john" in r["part"]), j, n))
    rs = groups[("all", "")]
    n = sum(r["n"] for r in rs)
    nm = sum(r["m"] for r in rs)
    nf = sum(r["f"] for r in rs)
    sw = sum(r["switches"] for r in rs)
    founded = sum(r["founded"] for r in rs)
    for r in rs:
        others_all.update(r["named_others"])
    with_m = [r for r in rs if r["n"]]
    print("he-sheet share of pronouns: %s; referent changes per mention: %s; referents founded: %d over %d samples" % (
        show(Fraction(nm, nm + nf)), show(Fraction(sw, n)), founded, len(rs)))
    print("per sample with a mention: first mention on John %s; every mention on John %s" % (
        show(Fraction(sum(1 for r in with_m if r["first"]), len(with_m))),
        show(Fraction(sum(1 for r in with_m if r["j"] == r["n"]), len(with_m)))))
    print("distinct named persons founded across all samples: %d; most: %s" % (
        len(others_all), ", ".join("%s %d" % kv for kv in others_all.most_common(15))))
    print("samples naming John anywhere in the 400 bytes: %d" % sum(1 for r in rs if "john" in r["whole"]))

    # Content carry: each word of the question.
    print()
    print("== D. Carry of the question's words: training problems containing the word | samples whose answer "
          "contains it | samples containing it anywhere (of 400) | in the reference answer")
    allrs = groups[("all", "")]
    tr_words = [{x.lower() for x in words(rows[i]["question"] + " " + rows[i]["answer"])} for i in train]
    df = collections.Counter(x for ws in tr_words for x in ws)
    qwords = []
    for x in words(john["question"]):
        if x.lower() not in qwords:
            qwords.append(x.lower())
    ref_words = {x.lower() for x in words(ref_answer)}
    for x in sorted(qwords, key=lambda x: (df[x], x)):
        print("%s | %d | %d | %d | %s" % (x, df[x], sum(x in r["part"] for r in allrs),
                                           sum(x in r["whole"] for r in allrs), "yes" if x in ref_words else "no"))
    v_tr = sum(1 for i in train if "volunt" in (rows[i]["question"] + rows[i]["answer"]).lower())
    print("volunt- (stem) | %d | %d | %d | yes" % (v_tr, sum(r["volunt"][1] for r in allrs),
                                                   sum(r["volunt"][0] for r in allrs)))

    t2 = time.monotonic_ns()
    print("elapsed_ms %d" % ((t2 - t1) // 1000000))
    print()
    print("all %d checks hold" % len(CHECKS))


main()
