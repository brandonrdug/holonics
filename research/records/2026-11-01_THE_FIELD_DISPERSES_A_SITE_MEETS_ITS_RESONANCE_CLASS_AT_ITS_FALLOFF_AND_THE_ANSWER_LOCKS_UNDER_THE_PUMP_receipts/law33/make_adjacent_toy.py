# A synthetic terrain for §16.32: the answer is triples (a, c, b), a and b drawn fresh and c = T[a][b] between them, so c is
# coded exactly by a reader of its one neighbour on each side (the strand contacts E₋, E₊). GSM8K's layout: a
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
        xs += [a, table[letters.index(a)][letters.index(b)], b]
    return q + '\n' + ''.join(xs) + '\n#### ' + xs[-1]
for name, n in [('TRAIN.txt', 2000), ('HELD.txt', 128)]:
    with open(name, 'w') as f:
        f.write('\n\n'.join(problem() for _ in range(n)) + '\n')
