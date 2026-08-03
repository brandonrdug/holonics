# THE NUMERAL FACE TURNS; THE FACTOR BODY REMAINS

**2026-07-17 · DERIVED / BUILT / CUDA-FORWARD MEASURED / SOMA INTERIOR UNCHANGED**

## 1. A prime is not a digit pattern

Fix a radix `b >= 2` and write the positive integer

```text
n = sum_(i=0..k-1) d_i b^i,       0 <= d_i < b.
```

Its ordered numeral, digit sum, and reversal are receiver faces

```text
D_b(n) = (d_(k-1), ..., d_0),
S_b(n) = sum_i d_i,
R_b(n) = sum_(i=0..k-1) d_i b^(k-1-i).
```

Primality belongs to the positive-integer multiplication world: every possible divisor through
`sqrt(n)` has been excluded. Palindrome and reversal belong to `D_b`. A change of radix changes
those faces without changing the integer's factor body. Consequently:

- `13 <-> 31` and `17 <-> 71` are decimal reversal-prime pairs;
- `131` and `313` are each decimal palindromic primes;
- `313` is also binary-palindromic (`100111001`), but not hexadecimal-palindromic (`139`);
- `131` is decimal-palindromic, while binary reversal carries `10000011` to
  `11000001 = 193`, another prime; and
- none of these incidences defines primality.

Every one-digit numeral is trivially palindromic. That face must stay separate from a nontrivial
multi-digit closure.

## 2. Digit sum is an exact quotient, not a prime generator

Because `b = 1 (mod b-1)`,

```text
n = S_b(n)                         (mod b-1),
R_b(n) = S_b(n) = n                (mod b-1).
```

Reversal preserves the digit multiset and therefore preserves the digit sum, but need not preserve
factor disposition. This gives the familiar divisibility instruments without turning them into
prime law:

- decimal digit sum is the integer modulo `9`;
- binary digit sum is population count, while the `b-1=1` quotient is trivial; and
- hexadecimal digit sum is the integer modulo `15`, exposing the factors `3` and `5`.

The decimal observations `S_10(13)=4=2^2` and `S_10(17)=8=2^3` do not continue. In the local decade
`10 <= n <= 19`, `S_10(n)=n-9`; the two powers of two are incidences of that affine chart.
`S_10(19)=10`, `S_10(23)=5`, and `S_10(29)=11` immediately foil a power-of-two rule.

Twin-prime addition and digit sum meet only through the carry boundary. For any gap `g`,

```text
S_b(n+g) - S_b(n) = g              (mod b-1).
```

Thus a twin pair has digit-sum difference congruent to `2`, but the visible difference changes by
multiples of `b-1` when a carry crosses the local numeral boundary. Decimal `17 -> 19` gives
`8 -> 10`, while `29 -> 31` gives `11 -> 4`, namely `-7 = 2-9`. The twin-prime relation is the
additive gap; the digit face records how that gap crossed the chosen chart.

## 3. The `b+1` quotient explains the palindrome exceptions

Since `b = -1 (mod b+1)`, a `k`-digit reversal obeys

```text
R_b(n) = (-1)^(k-1) n              (mod b+1).
```

Every even-length palindrome is therefore divisible by `b+1`. It can be prime only when it is the
two-digit numeral `11_b = b+1` and `b+1` is itself prime. This one law produces the conspicuous
exceptions in the three declared charts:

```text
11_2  = 3,
11_10 = 11,
11_16 = 17.
```

All other palindromic primes in those charts have odd digit length. This is a lawful restriction on
one glyph family, not an implication that all odd-length palindromes are prime.

## 4. Reversal supplies an exact real Smith diameter

The declared numeral chart supplies the homogeneous pair

```text
q_b(n) = [n : R_b(n)]
```

and, whenever `n + R_b(n) != 0`, its real Cayley face

```text
chi_b(n) = (n - R_b(n)) / (n + R_b(n)).
```

Digit reversal swaps the homogeneous coordinates and sends `chi -> -chi`. A palindrome occupies
the self-dual locus `chi=0`. A non-palindromic reversal pair occupies opposite hands of the same
real diameter. For example,

```text
q_10(13) = [13:31],  chi_10(13) = -18/44,
q_10(31) = [31:13],  chi_10(31) =  18/44.
```

This is a valid one-dimensional Smith instrument. It is not a complete complex impedance chart,
and it does not identify reversal with physical time reversal. The lived current still retains the
ordered event which presented one face and then the other. Reversal is a chart involution only when
the represented word retains its extent; a trailing-zero face can collapse a leading zero on the
return.

Changing radix changes `q_b` and `chi_b` while preserving the integer and its factor disposition.
That is the exact sense in which the numeral face turns while the factor body remains.

## 5. Exact finite chart through 128

The complete `H_128` factor body contains 31 founded prime axes. Its chart incidences are:

| radix | palindromic primes | non-palindromic reversal-prime pairs |
|---:|---|---|
| 2 | `3,5,7,17,31,73,107,127` | `11<->13, 23<->29, 37<->41, 43<->53, 47<->61, 67<->97, 71<->113, 83<->101` |
| 10 | `2,3,5,7,11,101` | `13<->31, 17<->71, 37<->73, 79<->97` |
| 16 | `2,3,5,7,11,13,17` | `23<->113, 53<->83` |

The one-digit palindrome populations are retained rather than silently equated with the
multi-digit cases. A reversal outside `H_128` remains explicitly outside; the receiver does not
guess its factor disposition.

The exact `H_313` host gate additionally verifies the user-supplied faces:

```text
131 = (131)_10 = (10000011)_2 = (83)_16,
313 = (313)_10 = (100111001)_2 = (139)_16.
```

Both are prime and decimal-palindromic. `313` is also binary-palindromic. Their digit sums are
respectively `(5,3,11)` and `(7,5,13)` in `(base 10, base 2, base 16)`, which further foils a
power-of-two digit-sum law.

## 6. The plural rendering passage

The built world adds three radix charts to every candidate and returns every factor event through
compact typed values, algebraic inscription, and explanatory language. The exact typed population
reconstructs the complete `HorizonRead`; shared event ancestry remains listener provenance and
never enters Soma.

Two identical CUDA-forward passages each carried 6,150 currents / 374,653 active-light octets. The
2,024 exact mathematical events comprise the prior factor body plus 384 numeral charts. Edge one
produced 377,636 completion rows at maximum grain 20; the genuinely later edge produced 374,271 at
maximum grain 19. Both transitions invert exactly.

Every nonempty numeral path changed through the later body. The only exact numeral repeat was the
zero-row typed face of `1_2`. Across all renderings, 5,436 of 6,072 later paths reused at least one
prior node identity while 252,149 later node identities were first seen. This is simultaneous
recurrence and transformation, not a frozen lookup.

Different renderings of the same numeral event shared internal node identities for 347 of 384
events on the first passage and 338 on the second. At the exact inscription face, the requested
reversal pairs also exceeded selected same-radix controls:

| relation | shared nodes, first | shared nodes, later |
|---|---:|---:|
| decimal `13 <-> 31` | 2 | 7 |
| decimal `13` / `37` control | 0 | 2 |
| decimal `13` / `19` control | 0 | 2 |
| decimal `17 <-> 71` | 7 | 5 |
| decimal `17` / `37` control | 0 | 1 |
| decimal `17` / `19` control | 1 | 1 |

This is a bounded read of those exact current surfaces, not a universal reversal score. Conversely,
the most recurrent coarse typed completion word crossed primes, composites, palindromes, and
out-of-horizon reversals. Completion-word recurrence is therefore a non-faithful quotient and may
not be promoted into an authored taxonomy.

## 7. Engine consequence

The next natural construction grows the same factor body through `313` and returns the old and new
chart populations through one continued body. It asks which exact factor, gap, reversal, palindrome,
and digit-sum paths RIDE into the larger horizon and which FOUND. Base is carried as a receiver chart;
it never enters primality. The world may later present these same relations beside language, proof,
or code, but no palindrome class, prime label, score, route chooser, or decoder enters Soma.

Exact observation: `observations/factor-derivation-ecology-01/RESULTS.md`.

