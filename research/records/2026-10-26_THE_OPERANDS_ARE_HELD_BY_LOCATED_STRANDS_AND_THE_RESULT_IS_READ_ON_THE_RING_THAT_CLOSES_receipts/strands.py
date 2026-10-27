# The strands: A held, G stepped, H turned with the carrier's orientation o.
# Keys: u(+): A<-H, H<-0, o<- -1 ; u(-): A<-H, H<-0, o<- +1 ; v(=): G<-H, H<- -A, o<- +1 ; w: H<-0, o<- +1.
# Check on every x, y < 1000 and both hands: at each step k of writing z on ring L = len(z),
# the tenth of conj(H - G)'s face is z's next digit, and at k = L the ring closes.
import itertools
W = 4
def run(x, y, op):
    z = x + y if op == '+' else x - y
    if z <= 0: return None
    s = str(z); L = len(s)
    if L > W: return None
    q = 10**L - 1
    if z == q: return 'nines'
    A = G = H = 0; o = 1
    for d in str(x): H = (10*H + o*int(d)) % q; G = 10*G % q
    A, H, o = H, 0, (1 if op == '+' else -1)
    for d in str(y): H = (10*H + o*int(d)) % q; G = 10*G % q
    G, H, o = H, (-A) % q, 1
    for k, ch in enumerate(s):
        c = (H - G) % q                       # comparison exponent
        conj = (-c) % q
        if (10*conj) // q != int(ch): return 'bad_digit'
        H = (10*H + o*int(ch)) % q; G = 10*G % q
    return 'ok' if (H - G) % q == 0 else 'bad_close'
from collections import Counter
c = Counter(run(x, y, op) for x in range(1000) for y in range(1000) for op in '+-')
print(dict(c))
