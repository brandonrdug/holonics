# A synthetic terrain for §16.35: the answer copies its question's eight letters in order, drawn without repeats from
# sixteen, so after its first letter each answer letter is fixed by the question site that follows its left neighbour's
# match (an induction read), and none is fixed without the question (4 bits a letter at most, 3 bits a letter for the
# last of eight). `near`: the eight letters end the question line; `far`: 288 dots stand between them and the line's end,
# so the answer reads its question about 300 places back, as GSM8K's answers do (median 306). GSM8K's layout: a question
# line, the answer's lines, problems apart by a blank line.
import random, sys
gap = {'near': 0, 'far': 288}[sys.argv[1]]
rng = random.Random(35)
letters = 'abcdefghijklmnop'
def problem():
    xs = rng.sample(letters, 8)
    q = 'Q ' + ''.join(xs) + '.' * gap + '?'
    return q + '\n' + ''.join(xs) + '\n#### ' + xs[-1]
for name, n in [('TRAIN.txt', 2000), ('HELD.txt', 128)]:
    with open(name, 'w') as f:
        f.write('\n\n'.join(problem() for _ in range(n)) + '\n')
