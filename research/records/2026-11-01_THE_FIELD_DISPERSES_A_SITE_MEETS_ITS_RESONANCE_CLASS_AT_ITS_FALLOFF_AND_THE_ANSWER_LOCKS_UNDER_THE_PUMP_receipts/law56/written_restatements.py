"""§16.43: the written answers' restated results, `=C>>D` with C and D runs of digits, `.`, `,` and `$` (a sentence's closing
`.` or `,` after D is not part of it), counted by how D differs from C: equal, or by the fewest dropped and added characters
(`|C| + |D| − 2 LCS`), or by substituted characters at equal length. Reads written SAMPLE.tsv files (private) and prints
counts only.
"""
import re, sys

def slips(a, b):
    m = [[0] * (len(b) + 1) for _ in range(len(a) + 1)]
    for i in range(len(a)):
        for j in range(len(b)):
            m[i + 1][j + 1] = m[i][j] + 1 if a[i] == b[j] else max(m[i][j + 1], m[i + 1][j])
    return len(a) + len(b) - 2 * m[len(a)][len(b)]

for path in sys.argv[1:]:
    counts = {}
    for line in open(path, encoding='utf-8'):
        text = line.split('\t', 1)[1].replace('\\n', '\n')
        for m in re.finditer(r'=([0-9.,$]+)>>([0-9.,$]*)', text):
            c, d = m.group(1).rstrip('.,'), m.group(2).rstrip('.,')
            if c == d:
                k = 'equal'
            elif len(c) == len(d) and slips(c, d) == 2 * sum(x != y for x, y in zip(c, d)):
                k = f'{sum(x != y for x, y in zip(c, d))} substituted'
            else:
                k = f'{slips(c, d)} dropped or added'
            counts[k] = counts.get(k, 0) + 1
    total = sum(counts.values())
    print(path.split('/')[-2] + '/' + path.split('/')[-1], 'restatements', total, ' '.join(f'{k}={v}' for k, v in sorted(counts.items())))
