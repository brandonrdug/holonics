"""Which faces Athena's held-back draws keep and break, and the per-place
cost a reader would pay on uniform operands 0..99 if it had located only
some faces (teacher-forced, leading digit first). Exact integer work; the
entropies are exterior float readings."""
import math, collections, json, sys

draws = ["85-42=43","71+41=102","73+31=104","23+51=84","56+3=56","8+82=90",
         "47-20=27","99-56=5","74-72=1","92*65=6090","83*27=2309","46*15=850","12*35=405"]

def ev(a, op, b): return a+b if op=='+' else a-b if op=='-' else a*b
def lead_fibre(a, op, b):
    # one leading digit of each operand and the lengths: exact enclosure
    def iv(x):
        s = len(str(x)) - 1; A = x // 10**s
        return A*10**s, (A+1)*10**s - 1
    (al, ah), (bl, bh) = iv(a), iv(b)
    if op == '+': return al+bl, ah+bh
    if op == '*': return al*bl, ah*bh
    return max(al-bh, 0), ah-bl

rows = []
for d in draws:
    lhs, r = d.split('='); r = int(r)
    op = next(c for c in "+-*" if c in lhs); a, b = map(int, lhs.split(op))
    t = ev(a, op, b)
    lo, hi = lead_fibre(a, op, b)
    rows.append(dict(draw=d, true=t, ok=(r == t),
        len_ok=len(str(r)) == len(str(t)), last_ok=r % 10 == t % 10,
        mod2_ok=r % 2 == t % 2, mod5_ok=r % 5 == t % 5,
        mod9_ok=r % 9 == t % 9, mod11_ok=r % 11 == t % 11,
        in_lead_fibre=lo <= r <= hi, lead_fibre=[lo, hi],
        ratio=round(r / t, 3) if t else None,
        ones_of_sum=(a % 10 + b % 10) % 10 if op == '-' else None))
for x in rows: print(x)

# per-place teacher-forced cost under located-face hypotheses
def digits(n): return [int(c) for c in str(n)]
def cost(pairs, face):
    groups = collections.defaultdict(collections.Counter)
    items = []
    for a, b, r in pairs:
        f = face(a, b); ds = digits(r)
        for k, d in enumerate(ds):
            key = (f, tuple(ds[:k])); groups[key][d] += 1
            items.append((key, d, len(ds) - 1 - k))
    by = collections.defaultdict(lambda: [0.0, 0])
    for key, d, place in items:
        c = groups[key]; p = c[d] / sum(c.values())
        by[place][0] += -math.log2(p); by[place][1] += 1
    return {pl: round(s / n, 3) for pl, (s, n) in sorted(by.items())}

R = range(100)
prod = [(a, b, a*b) for a in R for b in R]
summ = [(a, b, a+b) for a in R for b in R]
diff = [(a, b, a-b) for a in R for b in R if a >= b]
def L(x): return len(str(x))
def lead(x): return int(str(x)[0])
def size(a, b): return (L(a), L(b), lead(a), lead(b))
def cls(x): return (x % 2 == 0, x % 5 == 0)
def units(x): return x % 10
def ten(x): return (x // 10) % 10
out = {}
out['prod: nothing'] = cost(prod, lambda a, b: 0)
out['prod: size (lengths, one leading digit each)'] = cost(prod, size)
out['prod: size + last-digit crossing class'] = cost(prod, lambda a, b: size(a, b) + cls(a % 10) + cls(b % 10))
out['prod: size + last digits'] = cost(prod, lambda a, b: size(a, b) + (units(a), units(b)))
out['prod: size + last digits + their product\'s carry known'] = cost(prod, lambda a, b: size(a, b) + (units(a), units(b), units(a)*units(b)//10))
out['sum: nothing'] = cost(summ, lambda a, b: 0)
out['sum: place pairs mod 10, carries unread'] = cost(summ, lambda a, b: (L(a), L(b), (units(a)+units(b)) % 10, (ten(a)+ten(b)) % 10, (ten(a)+ten(b)) >= 10))
out['sum: size only'] = cost(summ, size)
out['diff: nothing'] = cost(diff, lambda a, b: 0)
out['diff: place pairs mod 10, borrows unread'] = cost(diff, lambda a, b: (L(a), L(b), (units(a)-units(b)) % 10, (ten(a)-ten(b)) % 10))
out['diff: size only'] = cost(diff, size)
out['diff: places right, half-turn missed (sum of last digits)'] = cost(diff, lambda a, b: (L(a), L(b), (units(a)+units(b)) % 10, (ten(a)-ten(b)) % 10))
for k, v in out.items(): print(f"{k:62s} {v}")
json.dump(dict(draws=rows, budgets={k: {str(p): c for p, c in v.items()} for k, v in out.items()}), open('faces.json', 'w'), indent=1)
