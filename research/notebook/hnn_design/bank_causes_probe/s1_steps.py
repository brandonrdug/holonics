import os
import sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from dumpio import parse_learn
from fractions import Fraction
import math

Es, train = parse_learn(os.environ.get('BANK_CAUSES_DIR', os.path.dirname(os.path.abspath(__file__))) + '/learn.dump')
print('E snapshots', len(Es), 'train pairs', len(train))
E0x = Es[0][1]
for k in range(1, len(Es)):
    Ek, Ep = Es[k][1], Es[k - 1][1]
    step = [abs(Ek[i][j] - Ep[i][j]) for i in range(120) for j in range(5)]
    cum = [abs(Ek[i][j] - E0x[i][j]) for i in range(120) for j in range(5)]
    fro2 = sum(x * x for x in step)
    moved = sum(1 for x in step if x != 0)
    ms = max(step)
    mc = max(cum)
    print(k, 'step: entries moved', moved, 'max |dE|', ms, '(2^%d..2^%d)' % (math.floor(math.log2(ms)), math.floor(math.log2(ms)) + 1),
          'frobenius^2', fro2.limit_denominator(2**40), '| cumulative max', mc)
