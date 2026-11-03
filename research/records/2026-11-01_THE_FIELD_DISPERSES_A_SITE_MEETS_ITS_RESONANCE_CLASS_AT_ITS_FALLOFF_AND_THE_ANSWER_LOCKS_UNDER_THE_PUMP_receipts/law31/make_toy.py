# A synthetic terrain for §16.31: the answer is triples (a, b, c), a and b drawn fresh and c = T[a][b] for one 8 × 8 table T
# drawn once, so c is coded exactly by a reader of its two left neighbours and not by a reader of one. GSM8K's layout: a
# question line, the answer's lines, problems apart by a blank line.
import random
rng = random.Random(31)
letters = 'abcdefgh'
table = [[rng.choice(letters) for _ in letters] for _ in letters]
def problem():
    q = 'Q ' + ''.join(rng.choice(letters) for _ in range(8)) + '?'
    xs = []
    for _ in range(21):
        a, b = rng.choice(letters), rng.choice(letters)
        xs += [a, b, table[letters.index(a)][letters.index(b)]]
    return q + '\n' + ''.join(xs) + '\n#### ' + xs[-1]
for name, n in [('TRAIN.txt', 2000), ('HELD.txt', 128)]:
    with open(name, 'w') as f:
        f.write('\n\n'.join(problem() for _ in range(n)) + '\n')
