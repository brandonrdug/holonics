#!/usr/bin/env -S python3 -I
"""strand_cut_ruler.py DUMP ROWS: a ruler (the lead, November 23, the level's receipt record §5). Which epoch a strand's open place is
handed by the level, and how large the handed row stands beside the state it joins.

`read-strand-cut ... past` writes, for passages read by two streams, the known stream's anchors and the epoch each open place reads
(`cut.tsv`), and at each of the `2n` sites the squared length of the row the level added and of the state it joined (`powers.tsv`). This
reads, over the rows of `ROWS` (`word_rows.py`'s table, the passage's text):
  - where the anchors fall: at a word's first letter (a letter after a space or a line feed), inside a word, or at a space or a mark;
  - the epochs' lengths in places;
  - at each word start three or more words into its passage, which epoch the open place reads: its anchor and end, and whether it
    holds the first letter of the word before, of the word two before, or neither (an epoch that starts inside a word holds its letter);
  - the handed row's power over the state's at the open places, and at the open places at word starts.
Outside the machine; counts and ratios only, floats at the exterior.
"""
import sys
from collections import Counter


def main():
    d, rows_f = sys.argv[1], sys.argv[2]
    texts = []
    for line in open(rows_f, encoding='utf-8'):
        f = line.rstrip('\n').split('\t')
        texts.append((f[1] + f[2]).replace('\\n', '\n').encode())
    letter = lambda b: 65 <= b <= 90 or 97 <= b <= 122
    powers = {}
    for line in open(f'{d}/powers.tsv'):
        r, site, row, state = line.split('\t')
        powers[(int(r), int(site))] = (int(row), int(state))
    kinds, lengths, held, ratio_all, ratio_ws = Counter(), Counter(), Counter(), [0, 0], [0, 0]
    starts = 0
    for line in open(f'{d}/cut.tsv'):
        r, n, anchors, source = line.rstrip('\n').split('\t')
        r, n = int(r), int(n)
        text = texts[r][:n]
        anchors = [int(a) for a in anchors.split(',') if a]
        source = [None if s == '-' else int(s) for s in source.split(',')]
        ends = anchors[1:] + [n]
        for a, e in zip(anchors, ends):
            lengths[min(e - a, 16)] += 1
            if a == 0:
                continue
            kinds['first letter' if letter(text[a]) and not letter(text[a - 1]) else 'inside a word' if letter(text[a]) else 'space or mark'] += 1
        # the first letters of the words, in order
        firsts = [t for t in range(n) if letter(text[t]) and (t == 0 or not letter(text[t - 1]))]
        for t in range(n):
            row, state = powers[(r, n + t)]
            ratio_all[0] += row
            ratio_all[1] += state
        for i, t in enumerate(firsts):
            if i < 2 or text[t - 1] not in (32, 10):
                continue
            starts += 1
            row, state = powers[(r, n + t)]
            ratio_ws[0] += row
            ratio_ws[1] += state
            j = source[t]
            if j is None:
                held['no epoch'] += 1
                continue
            a, e = anchors[j], ends[j]
            prev, prev2 = firsts[i - 1], firsts[i - 2]
            tag = 'the word before' if a <= prev < e else 'the word two before' if a <= prev2 < e else 'inside the word before' if prev < a < t else 'before the word two before' if e <= prev2 else 'other'
            held[tag] += 1
            held[f'ends {min(t - e, 12)} places before'] += 1
    total = sum(kinds.values())
    print(f"STRAND_CUT {d.rstrip('/').split('/')[-1]} anchors={total} " + ' '.join(f"{k.replace(' ', '_')}={v / total:.3f}" for k, v in sorted(kinds.items())))
    nl = sum(lengths.values())
    print("STRAND_CUT_LENGTHS " + ' '.join(f"{k}{'+' if k == 16 else ''}={v / nl:.3f}" for k, v in sorted(lengths.items())))
    print(f"STRAND_CUT_HANDED word_starts={starts} " + ' '.join(f"{k.replace(' ', '_')}={v / starts:.3f}" for k, v in sorted(held.items()) if not k.startswith('ends')))
    print("STRAND_CUT_ENDS " + ' '.join(f"{k.split()[1]}={v / starts:.3f}" for k, v in sorted(held.items(), key=lambda kv: int(kv[0].split()[1]) if kv[0].startswith('ends') else 99) if k.startswith('ends')))
    print(f"STRAND_CUT_POWER row_over_state open_places={ratio_all[0] / max(ratio_all[1], 1):.4f} at_word_starts={ratio_ws[0] / max(ratio_ws[1], 1):.4f}")


if __name__ == '__main__':
    main()
