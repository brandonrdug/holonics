"""Exact checks of the arithmetic contract's finite claims (standard library only).

The record: research/records/2026-09-29_THE_ARITHMETIC_CONTRACT_A_NUMERAL_IS_A_FACE_OF_A_COUNTING_NAVIGATOR_AND_ITS_PRODUCER_IS_A_KEY.md.
Every value is an integer, a Fraction, or log2 of a positive rational read at the grain 1/16
(`a + j/16 + e` means the exact value lies in [a + j/16, a + (j + 1)/16)); nothing is floated.
- §1 the consumer square: digit vectors joined by addition, convolution or repeated convolution,
  then one carry cascade, decode to the integer consequence in bases 2, 10 and 16, and rebasing
  commutes; the carry at a place is the section flux of that place's wheel;
- §2 code lengths: 13122 = 2·3^8, its neighbour the prime 13121, 729 = 3^6, 8191 and 65537 under
  declared prefix codes (digits, factorization, anchor ± offset);
- §3 the multiplication table as the map of digit-pair carries in bases 2, 3, 7, 10 and 16;
- §4 provenance: the producers of one face, their jets along the operand clock, and the ties;
- §5 the holds sheet's code over N computed results, 2N − log2 C(2N, N);
- §6 the digit counts of powers of two: locked in bases 2 and 16, unlocked in base 10.
Run: python3 contract_checks.py. Each line prints a claim and its exact value; a failed claim
stops the script.
"""
import math
import random
from fractions import Fraction


def check(name, ok):
    assert ok, name
    print(f"{name}: {bool(ok)}")


# -------------------------------------------------------------------------------------------
# exact readings


def log2_grain(x):
    """The 1/16 grain cell of log2 x for a positive rational x: K with 2^(K/16) <= x < 2^((K+1)/16)."""
    x = Fraction(x)
    assert x > 0
    p, q = x.numerator ** 16, x.denominator ** 16
    # K = floor(log2(p/q)); start from bit lengths and correct exactly
    k = p.bit_length() - q.bit_length()
    while (q << k if k >= 0 else q) > (p if k >= 0 else p << -k):
        k -= 1
    while (q << (k + 1) if k + 1 >= 0 else q) <= (p if k + 1 >= 0 else p << -(k + 1)):
        k += 1
    return k


def reading(x):
    k = log2_grain(x)
    return f"{k // 16} + {k % 16}/16 + e"


def gamma(n):
    """Elias gamma length of n >= 1: 2 floor(log2 n) + 1 bits."""
    assert n >= 1
    return 2 * (n.bit_length() - 1) + 1


def digits(n, b):
    """Least significant first; [] for zero."""
    out = []
    while n:
        n, d = divmod(n, b)
        out.append(d)
    return out


def value(word, b):
    v = 0
    for d in reversed(word):
        v = v * b + d
    return v


# -------------------------------------------------------------------------------------------
# §1 the consumer square: one carry cascade after the pair's carry-free combination


def zip_add(u, v):
    n = max(len(u), len(v))
    return [(u[i] if i < len(u) else 0) + (v[i] if i < len(v) else 0) for i in range(n)]


def convolve(u, v):
    if not u or not v:
        return []
    out = [0] * (len(u) + len(v) - 1)
    for i, x in enumerate(u):
        for j, y in enumerate(v):
            out[i + j] += x * y
    return out


def carry_word(b, word, c=0):
    """The carry cascade: each place's total t = w + c is read on the circle of b steps, its phase
    the digit and its winding the carry passed up; the carries are returned beside the digits."""
    out, carries = [], []
    for w in word:
        t = w + c
        out.append(t % b)
        c = t // b
        carries.append(c)
    out.extend(digits(c, b))
    return out, carries


def section_crossings(b, total):
    """The walk 0 -> total of one wheel crosses the section b | x at these many steps."""
    return sum(1 for x in range(1, total + 1) if x % b == 0)


def consumer_square():
    rng = random.Random(20260929)
    checked = 0
    for b in (2, 10, 16):
        for length in range(1, 9):
            for _ in range(8):
                a = rng.randrange(b ** (length - 1), b ** length)
                c = rng.randrange(b ** (length - 1), b ** length)
                e = rng.randrange(0, 5)
                ea, ec = digits(a, b), digits(c, b)
                s, _ = carry_word(b, zip_add(ea, ec))
                p, carries = carry_word(b, convolve(ea, ec))
                w = [1]
                for _ in range(e):
                    w = convolve(carry_word(b, w)[0], ea)
                pw, _ = carry_word(b, w)
                assert all(d < b for d in s + p + pw)
                assert value(s, b) == a + c and value(p, b) == a * c and value(pw, b) == a ** e
                # the carried word is the product's digit word once its top zeros are dropped
                while p and p[-1] == 0:
                    p.pop()
                assert p == digits(a * c, b)
                # the carry at each place is the section flux of that place's wheel
                conv, carry_in = convolve(ea, ec), 0
                for j, w_j in enumerate(conv):
                    assert carries[j] == section_crossings(b, w_j + carry_in)
                    carry_in = carries[j]
                # rebasing commutes: the consequence is read alike through every radix receiver
                for b2 in (2, 10, 16):
                    q2, _ = carry_word(b2, convolve(digits(a, b2), digits(c, b2)))
                    assert value(q2, b2) == value(p, b)
                checked += 1
    check(f"1 consumer square (sum, product, power, carry = section flux, rebase) on {checked} seeded unseen pairs in bases 2, 10, 16", True)
    conv = convolve(digits(7, 2), digits(3, 2))
    word, carries = carry_word(2, conv)
    check("1 7·3: [1,1,1] * [1,1] = [1,2,2,1], carries [0,1,1,1], 10101 (least first) = 21",
          conv == [1, 2, 2, 1] and carries == [0, 1, 1, 1] and word == [1, 0, 1, 0, 1] and value(word, 2) == 21)
    conv = convolve(digits(255, 16), digits(255, 16))
    word, carries = carry_word(16, conv)
    check("1 255·255 in base 16: [225,450,225], carries [14,29,15], FE01 = 65025 = 3^2·5^2·17^2",
          conv == [225, 450, 225] and carries == [14, 29, 15] and word == [1, 0, 14, 15] and 65025 == 3**2 * 5**2 * 17**2)
    check("1 2+2, 2·2 and 2^2 leave one carry cascade with one face: 100 in base 2, 4 in base 10",
          carry_word(2, zip_add([0, 1], [0, 1]))[0] == [0, 0, 1]
          and carry_word(2, convolve([0, 1], [0, 1]))[0] == [0, 0, 1]
          and value(carry_word(10, zip_add([2], [2]))[0], 10) == 4)


# -------------------------------------------------------------------------------------------
# §2 code lengths under declared prefix codes


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(n) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytearray(len(sieve[p * p :: p]))
    return [p for p in range(n + 1) if sieve[p]]


PRIMES = primes_upto(70000)
INDEX = {p: i + 1 for i, p in enumerate(PRIMES)}


def factorization(n):
    out, rest = [], n
    for p in PRIMES:
        if p * p > rest:
            break
        e = 0
        while rest % p == 0:
            rest //= p
            e += 1
        if e:
            out.append((p, e))
    if rest > 1:
        out.append((rest, 1))
    return out


def literal_code(n, b):
    """|gamma(k)| + log2((b - 1) b^(k - 1)): the digit count, then the digits (leading nonzero).
    Returned as the positive rational whose log2 is the code."""
    k = len(digits(n, b))
    return Fraction(2 ** gamma(k) * (b - 1) * b ** (k - 1))


def factor_code(n):
    """|gamma(s)| + sum_i (|gamma(g_i)| + |gamma(e_i)|): the support size, then each prime by its
    index gap and its exponent. Integer bits."""
    f = factorization(n)
    bits, last = gamma(len(f)), 0
    for p, e in f:
        bits += gamma(INDEX[p] - last) + gamma(e)
        last = INDEX[p]
    return bits


def anchor_code(anchor, offset):
    """The anchor's factorization code, a sign bit and |gamma(|offset| + 1)|: counting from a
    landmark. Integer bits."""
    return factor_code(anchor) + 1 + gamma(abs(offset) + 1)


def code_lengths():
    check("2 13122 = 2·3^8, 13121 prime, 729 = 3^6, 8191 = 2^13 − 1 and 65537 = 2^16 + 1 prime",
          13122 == 2 * 3**8 and factorization(13121) == [(13121, 1)] and 729 == 3**6
          and factorization(8191) == [(8191, 1)] and factorization(65537) == [(65537, 1)])
    rows = [
        (13122, None), (13121, (13122, -1)), (729, None), (8191, (2**13, -1)), (65537, (2**16, 1)),
    ]
    for n, anchor in rows:
        size = n.bit_length()
        lit = {b: reading(literal_code(n, b)) for b in (2, 10, 16)}
        fac = factor_code(n)
        anc = anchor_code(*anchor) if anchor else None
        print(f"2 n = {n} = {' · '.join(f'{p}^{e}' for p, e in factorization(n))}: bit length {size};"
              f" literal base 2 {lit[2]}, base 10 {lit[10]}, base 16 {lit[16]};"
              f" factorization {fac} bits" + (f"; anchor {anchor[0]} {anchor[1]:+d}: {anc} bits" if anc else ""))
    check("2 13122: factorization 13 bits < bit length 14 < base-10 literal 5 + log2 90000 in [21, 22)",
          factor_code(13122) == 13 and 13122 .bit_length() == 14
          and 2**16 < 90000 < 2**17 and log2_grain(literal_code(13122, 10)) // 16 == 21)
    check("2 729: factorization 9 bits < base-10 literal 3 + log2 900 in [12, 13)",
          factor_code(729) == 9 and log2_grain(literal_code(729, 10)) // 16 == 12)
    check("2 13121 (prime, index 1561): factorization 23 bits > base-10 literal in [21, 22) > anchor 2·3^8 − 1 at 17 bits",
          INDEX[13121] == 1561 and factor_code(13121) == 23
          and log2_grain(literal_code(13121, 10)) // 16 == 21 and anchor_code(13122, -1) == 17)
    check("2 65537 (prime, index 6543): factorization 27 bits; anchor 2^16 + 1 at 15 bits < bit length 17",
          INDEX[65537] == 6543 and factor_code(65537) == 27 and anchor_code(2**16, 1) == 15)
    check("2 in base 3 the numerals are the factorizations: 729 = 1000000_3, 13122 = 200000000_3",
          digits(729, 3) == [0] * 6 + [1] and digits(13122, 3) == [0] * 8 + [2])


# -------------------------------------------------------------------------------------------
# §3 the multiplication table: (x, y) -> (floor(xy/b), xy mod b), a ratio with remainder


def table(b):
    return {(x, y): divmod(x * y, b) for x in range(b) for y in range(b)}


def multiplication_tables():
    for b in (2, 3, 7, 10, 16):
        t = table(b)
        digit_count = [sum(1 for (c, d) in t.values() if d == k) for k in range(b)]
        carry_count = {}
        for c, _ in t.values():
            carry_count[c] = carry_count.get(c, 0) + 1
        units = [x for x in range(1, b) if math.gcd(x, b) == 1]
        unit_rows_permute = all(sorted(t[(x, y)][1] for y in range(b)) == list(range(b)) for x in units)
        periods = [b // math.gcd(x, b) for x in range(1, b)]
        rows_repeat = all(
            t[(x, y)][1] == (x * (y + b // math.gcd(x, b))) % b for x in range(1, b) for y in range(b)
        )
        # a row's carries advance by the phase carry of the rate-x clock: floor(x(y+1)/b) - floor(xy/b)
        row_carry = all(
            (x * (y + 1)) // b - (x * y) // b == ((x * y) % b + x % b) // b for x in range(b) for y in range(b)
        )
        row_total = all(sum((x * (y + 1)) // b - (x * y) // b for y in range(b - 1)) == (x * (b - 1)) // b for x in range(b))
        print(f"3 base {b}: trailing digits {digit_count}; carries {dict(sorted(carry_count.items()))};"
              f" unit rows {units}; row periods b/gcd(x,b) {periods}")
        check(f"3 base {b}: unit rows permute the digits, rows repeat at b/gcd(x,b), row carries are the phase carry",
              unit_rows_permute and rows_repeat and row_carry and row_total)
    check("3 base 2: the table carries nothing (x·y is x AND y); every binary carry is a column sum's",
          all(c == 0 for c, _ in table(2).values()))
    check("3 a prime base's table has no zero divisors: digit 0 has 2b − 1 pairs, every other b − 1",
          all([sum(1 for (c, d) in table(p).values() if d == k) for k in range(p)] == [2 * p - 1] + [p - 1] * (p - 1)
              for p in (2, 3, 7)))
    check("3 base 10: digit 0 has 27 pairs (19 on a zero digit, 8 on the zero divisors 2·5), base 16: 0 has 48",
          sum(1 for (c, d) in table(10).values() if d == 0) == 27 and sum(1 for (c, d) in table(16).values() if d == 0) == 48)
    check("3 an odd base reads parity by the digit sum: n ≡ sum of digits mod 2 for b = 3, 7 on [0, 2^12)",
          all(n % 2 == sum(digits(n, b)) % 2 for b in (3, 7) for n in range(2**12)))


# -------------------------------------------------------------------------------------------
# §4 provenance: producers of one face, their jets along the operand clock


OPS = {"+": lambda a, k: a + k, "·": lambda a, k: a * k, "^": lambda a, k: a**k}


def jet(op, a, k):
    f = [OPS[op](a, k + i) for i in range(3)]
    return (f[0], f[1] - f[0], f[2] - 2 * f[1] + f[0])


def provenance():
    check("4 2 + 2 = 2 · 2 = 2 ^ 2 = 4: one face, three producers", all(OPS[o](2, 2) == 4 for o in OPS))
    check("4 their jets along the right operand's clock at (2, 2): (4, 1, 0), (4, 2, 0), (4, 4, 4)",
          [jet(o, 2, 2) for o in "+·^"] == [(4, 1, 0), (4, 2, 0), (4, 4, 4)])
    pairs = (("+", "·"), ("+", "^"), ("·", "^"))
    grid = [(a, k) for a in range(2, 40) for k in range(0, 40)]
    full = [(a, k, o1, o2) for a, k in grid for o1, o2 in pairs if jet(o1, a, k) == jet(o2, a, k)]
    first = {(a, k, o1, o2) for a, k in grid for o1, o2 in pairs if jet(o1, a, k)[:2] == jet(o2, a, k)[:2]}
    check("4 for 2 ≤ a < 40, 0 ≤ k < 40 the jet to second order separates every pair; face and first jet tie only · and ^ at (2, 1)",
          full == [] and first == {(2, 1, "·", "^")})
    check("4 at a = 0, · and ^ are one species along the right operand's clock (0·k = 0^k for k ≥ 1)",
          all(OPS["·"](0, k) == OPS["^"](0, k) for k in range(1, 64)))
    check("4 the left operand's clock separates them: 1·k = k, 1^k = 1", OPS["·"](1, 5) != OPS["^"](1, 5))
    fibre = sorted((a, o, c) for o in OPS for a in range(5) for c in range(5) if OPS[o](a, c) == 4)
    check(f"4 the face 4 alone over operands in [0, 5) has a fibre of {len(fibre)} producers: {fibre}", len(fibre) == 10)
    check("4 the add and mul sequences share the minimal recurrence (t − 1)^2; the power a^k's is t − a",
          all(OPS[o](a, k + 2) - 2 * OPS[o](a, k + 1) + OPS[o](a, k) == 0 for o in "+·" for a in range(9) for k in range(9))
          and all(OPS["^"](a, k + 1) == a * OPS["^"](a, k) for a in range(9) for k in range(9))
          and all((a + 1) * (a + 1) != a * (a + 2) for a in range(9)))


# -------------------------------------------------------------------------------------------
# §5 the holds sheet: a KT face over {holds, free} across the stream's computed results


def holds_sheet():
    for n in (1, 2, 4, 64, 4096):
        product = Fraction(1)
        for i in range(n):
            product *= Fraction(2 * i + 1, 2 * i + 2)
        assert product == Fraction(math.comb(2 * n, n), 4**n)
        print(f"5 N = {n}: the sheet's code over N holding results is 2N − log2 C(2N, N) = {reading(1 / product)}")
    check("5 the KT product over N holds telescopes to C(2N, N)/4^N (N ≤ 4096)", True)


# -------------------------------------------------------------------------------------------
# §6 digit counts of powers of two: a rate-log_b 2 clock read at the unit clock's sections


def power_digit_counts():
    lens = {b: [len(digits(2**k, b)) for k in range(0, 257)] for b in (2, 10, 16)}
    check("6 base 2: len(2^k) = k + 1 (rate 1: a carry every tick)", all(lens[2][k] == k + 1 for k in range(257)))
    check("6 base 16: len(2^k) = floor(k/4) + 1 (rate 1/4: locks with period 4)",
          all(lens[16][k] == k // 4 + 1 for k in range(257)))
    check("6 base 10 counts: 10^(len − 1) ≤ 2^k < 10^len, so len(2^k) − 1 = floor(k log_10 2)",
          all(10 ** (lens[10][k] - 1) <= 2**k < 10 ** lens[10][k] for k in range(257)))
    # the base-10 digit counts of 2^k for k ≤ 2^15, read by exact comparison with powers of ten
    n, count, ten, two, dec = 1 << 15, 1, 10, 1, []
    for k in range(n + 1):
        while two >= ten:
            count, ten = count + 1, ten * 10
        dec.append(count)
        two *= 2
    word = [dec[k + 1] - dec[k] for k in range(n)]
    print(f"6 base 10: carry word of len(2^k), k < 64: {''.join(map(str, word[:64]))}")
    near = [t for t in range(1, 1 << 14) if all(word[i] == word[i + t] for i in range(0, n - t))]
    breaks = {t: next(i for i in range(n - t) if word[i] != word[i + t]) for t in (10, 93, 196, 485, 2136, 13301)}
    print(f"6 base 10: each convergent denominator T of log_10 2 first fails as a period at k = {breaks}")
    check("6 base 10: no period T < 2^14 on k < 2^15, and 2^T ≠ 10^S for T ≥ 1 (the rate log_10 2 never locks)",
          near == [] and all(2**t != 10**s for t in range(1, 200) for s in range(0, 61)))


if __name__ == "__main__":
    consumer_square()
    code_lengths()
    multiplication_tables()
    provenance()
    holds_sheet()
    power_digit_counts()
