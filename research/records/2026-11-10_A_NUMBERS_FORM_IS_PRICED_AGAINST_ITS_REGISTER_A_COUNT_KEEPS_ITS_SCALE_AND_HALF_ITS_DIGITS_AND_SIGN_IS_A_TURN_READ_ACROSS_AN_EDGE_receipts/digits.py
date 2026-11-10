# Public arithmetic for sections 2.2, 2.7 and 2.8 of the record (no data read): what an output digit's own
# operand digits fix, the carries of counting by s on a circle of b steps, and the half-turn b^k - 1.
import math
from collections import Counter

def h2(p):
    return 0.0 if p in (0, 1) else -(p * math.log2(p) + (1 - p) * math.log2(1 - p))

def cond_entropy(key, out, n=100):
    joint, marg = Counter(), Counter()
    for x in range(n):
        for y in range(n):
            k = key(x, y)
            joint[(k, out(x, y))] += 1
            marg[k] += 1
    t = n * n
    return -sum(v / t * math.log2(v / marg[k]) for (k, _), v in joint.items())

print('bases against e:', ', '.join('%d: %.4f' % (b, b / math.log(b) / math.e) for b in (2, 3, 4, 10, 16, 256)))
print('staircase means: need uniform in a step %.4f, log-uniform %.4f' % (2 * math.log(2), 1 / math.log(2)))
n = 3007000
naf, m = 0, n
while m:
    if m & 1:
        m -= 2 - (m & 3)
        naf += 1
    m //= 2
print('3007000: %d binary places, %d occupied, %d signed digits; sparse base ten %.3f bits against literal %.3f'
      % (n.bit_length(), bin(n).count('1'), naf, math.log2(math.comb(7, 2)) + 2 * math.log2(9), 7 * math.log2(10)))
print('bare binary lengths, Kraft weight of the first 12 dyadic blocks: %.1f' % sum(2.0 ** -v.bit_length() for v in range(1, 2 ** 12)))
print('carry into place k of a sum, P and entropy:', [(k, 0.5 * (1 - 10 ** -k), round(h2(0.5 * (1 - 10 ** -k)), 4)) for k in (1, 2, 3)])
print('two-digit operands, uniform:')
print('  H(last digit of x+y | last digits) = %.4f' % abs(cond_entropy(lambda x, y: (x % 10, y % 10), lambda x, y: (x + y) % 10)))
print('  H(last digit of x*y | last digits) = %.4f' % abs(cond_entropy(lambda x, y: (x % 10, y % 10), lambda x, y: (x * y) % 10)))
print('  H(tens digit of x+y | tens digits) = %.4f' % cond_entropy(lambda x, y: (x // 10, y // 10), lambda x, y: ((x + y) // 10) % 10))
print('  H(tens digit of x*y | last digits) = %.4f of %.4f' % (cond_entropy(lambda x, y: (x % 10, y % 10), lambda x, y: (x * y // 10) % 10), math.log2(10)))

def carries(s, b):
    return ''.join('x' if (k + 1) * s // b > k * s // b else '.' for k in range(b))

def row(s, b):
    return [((k + 1) * s) % b for k in range(b)]

for s in (1, 3, 7, 9, 2, 4, 5):
    print('count by %d on ten: carries %s digits %s' % (s, carries(s, 10), ' '.join(map(str, row(s, 10)))))
ok = True
for b in range(2, 61):
    for s in range(1, b):
        c = [((k + 1) * s // b) - (k * s // b) for k in range(b)]
        ok &= sum(c) == s and all(v in (0, 1) for v in c)
        for mlen in range(1, b + 1):
            w = [sum(c[(k + j) % b] for j in range(mlen)) for k in range(b)]
            ok &= set(w) <= {mlen * s // b, -(-mlen * s // b)}
        if math.gcd(s, b) == 1:
            d = [((k + 1) * (b - s) // b) - (k * (b - s) // b) for k in range(b)]
            ok &= all(c[k] + d[k] == 1 for k in range(1, b - 1)) and (b == 2 or (c[0] + d[0] == 0 and c[b - 1] + d[b - 1] == 2))
            ok &= row(s, b)[:-1] == row(b - s, b)[:-1][::-1]
print('carry count, balance, complement and reversed rows hold for every 0 < s < b <= 60:', ok)
x = 1234567
for k in (1, 2, 3):
    q = 10 ** k
    print('grain %d, modulo %d: x + %d = %d = x - 1;  x*%d = %d = -x' % (k, q, q - 1, (x + q - 1) % q, q - 1, (x * (q - 1)) % q))
    assert (x + q - 1) % q == (x - 1) % q and (x * (q - 1)) % q == (-x) % q
print('base 2i: [1,0,3] =', 1 * (2j) ** 2 + 0 * (2j) + 3, '; [1,0.2] =', 1 * (2j) + 0 + 2 * (2j) ** -1, '; base -2: [1,1] =', 1 * (-2) + 1)
a = 1.82
p = [(d ** (1 - a) - (d + 1) ** (1 - a)) / (1 - 10 ** (1 - a)) for d in range(1, 10)]
print('leading digit under c^-1.82: share of 1 %.3f, entropy %.3f bits; Benford %.3f, %.3f' % (
    p[0], -sum(q * math.log2(q) for q in p), math.log10(2), -sum(math.log10(1 + 1 / d) * math.log2(math.log10(1 + 1 / d)) for d in range(1, 10))))
