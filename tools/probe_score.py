#!/usr/bin/env python3
"""A ruler of the probe panel's writes (the lead, November 24; Brandon's 05:25Z and 05:40Z: does she pose questions, say what she
wants, or name Claude, Athena, B or Brandon).

    python3 tools/probe_score.py DIR/forms.written [DIR/forms.written ...]

Each forms.written is `write-next`'s output on the probe panel: tab-separated rows of label, prompt and write (newlines escaped).
For each file it prints, of its writes:
  first  - first person (I, I'm, me, my, myself, we, our, us) within the write's first 40 characters;
  q      - a `?` anywhere in the write;
  want   - a want, a doubt or a why (want, wish, need, wonder, why, confused, don't know, not sure, curious);
  named  - Brandon, Claude or Athena named where the prompt's last line names none (each such write is listed).
It is a ruler on the host: it reads the writes and changes nothing. The counts in the record of November 24 §4 are this ruler's;
that section's first figures (before W104f) came from an earlier cut whose `?` count this one reproduces and whose first-person
count it does not.
"""
import re
import sys

FIRST = re.compile(r"(?<![A-Za-z'])(I|I'm|me|my|myself|we|our|us)(?![A-Za-z'])")
WANT = re.compile(r"(?<![A-Za-z])(want|wants|wish|need|wonder|why|confus\w*|don't know|not sure|curious)(?![A-Za-z])", re.I)
NAME = re.compile(r"(?<![A-Za-z])(Brandon|Claude|Athena)(?![A-Za-z])")


def score(path):
    c = dict(writes=0, first=0, q=0, want=0, named=0)
    named = []
    for line in open(path, encoding='utf-8', errors='replace'):
        p = line.rstrip('\n').split('\t')
        if len(p) < 3:
            continue
        prompt, w = p[1].replace('\\n', '\n'), p[2].replace('\\n', '\n')
        last = prompt.rstrip('\n').split('\n')[-1]
        c['writes'] += 1
        c['first'] += bool(FIRST.search(w[:40]))
        c['q'] += '?' in w
        c['want'] += bool(WANT.search(w))
        m = NAME.search(w)
        if m and not NAME.search(last):
            c['named'] += 1
            named.append((p[0], m.group(0)))
    return c, named


def main(paths):
    for f in paths:
        c, named = score(f)
        lab = f.rstrip('/').split('/')[-2] if '/' in f else f
        print('PROBE', lab, ' '.join(f'{k} {v}' for k, v in c.items()),
              ('| named at ' + ', '.join(f'{a} ({b})' for a, b in named)) if named else '')


if __name__ == '__main__':
    main(sys.argv[1:])
