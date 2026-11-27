#!/usr/bin/env -S python3 -I
"""place_class_ruler.py CONTROL=DIR ARM=DIR: a ruler (the lead, November 27; the formal thread's decisive read of 08:14 UTC). Where an
arm's code differs from its control's, by the place's class.

Each DIR is a `read-cavity ... open loud` output; its `loudness.tsv` gives each held place's code at one place open (on `2^(−20)` bits)
and its unit (the byte, in hex), keyed by slice, stretch and place. Paired place by place, the arm's code less the control's, in nats a
place with its standard error, read by: the place's kind (a word's first letter, a letter inside a word, a space, any other byte); its
place in its stretch in octaves (0, 1, 2 to 3, …: how much of the passage stands before it); and how often the word it stands in recurs
in its stretch (once, 2 to 7, 8 or more; bytes outside a word apart); and, at a word's first letter, how far back the same word was last
met in its stretch (within 30 places, over 30, or not before: the formal thread's G-Z17). A class where the arm codes under its control is its news; a flat
difference across classes is its price. Outside the machine; codes and counts only.
"""
import math
import sys
from collections import defaultdict

G = float(1 << 20)
LN2 = math.log(2)


def read(d):
    out = {}
    head = None
    for line in open(f'{d}/loudness.tsv'):
        f = line.rstrip('\n').split('\t')
        if head is None:
            head = {k: i for i, k in enumerate(f)}
            continue
        if f[0] != 'P':
            continue
        out[(f[1], int(f[2]), int(f[3]))] = (int(f[head['code']]) / G * LN2, int(f[head['unit']], 16) if f[head['unit']] not in ('-', '') else -1)
    return out


def main():
    (cn, cd), (an, ad) = [a.split('=', 1) for a in sys.argv[1:3]]
    c, a = read(cd), read(ad)
    keys = sorted(set(c) & set(a))
    stretches = defaultdict(dict)
    for k in keys:
        stretches[(k[0], k[1])][k[2]] = c[k][1]
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    groups = defaultdict(list)
    for (sl, st), units in stretches.items():
        ts = sorted(units)
        text = [units[t] for t in ts]
        # each place's word (a maximal run of letters) and its count in the stretch
        word_of, words, last_met, seen = {}, defaultdict(int), {}, {}
        i = 0
        while i < len(text):
            if letter(text[i]):
                j = i
                while j < len(text) and letter(text[j]):
                    j += 1
                w = bytes(text[i:j])
                words[w] += 1
                last_met[i] = i - seen[w] if w in seen else None
                seen[w] = i
                for k in range(i, j):
                    word_of[k] = w
                i = j
            else:
                i += 1
        for i, t in enumerate(ts):
            b = text[i]
            kind = "word_first" if letter(b) and (i == 0 or not letter(text[i - 1])) else ("letter_inside" if letter(b) else ("space" if b in (32, 10, 9) else "other"))
            octave = 0 if t == 0 else int(math.log2(t)) + 1
            w = word_of.get(i)
            recur = "outside_a_word" if w is None else ("once" if words[w] == 1 else ("2_to_7" if words[w] < 8 else "8_or_more"))
            d = a[(sl, st, t)][0] - c[(sl, st, t)][0]
            groups[("kind", kind)].append(d)
            groups[("octave", f"{0 if octave == 0 else 1 << (octave - 1)}+")].append(d)
            groups[("recurrence", recur)].append(d)
            if kind == "word_first":
                gap = last_met.get(i)
                groups[("first_letter_last_met", "not_before" if gap is None else ("within_30" if gap <= 30 else "over_30"))].append(d)
            groups[("all", "all")].append(d)
    for (axis, cls), v in sorted(groups.items(), key=lambda kv: (kv[0][0], kv[0][1] if kv[0][0] != 'octave' else f"{int(kv[0][1][:-1]):08d}")):
        n = len(v)
        m = sum(v) / n
        se = math.sqrt(sum((x - m) ** 2 for x in v) / max(n - 1, 1) / n)
        print(f"PLACE_CLASS {an}_less_{cn} {axis}={cls} places={n} nats_a_place={m:+.4f} (±{se:.4f})")


if __name__ == '__main__':
    main()
