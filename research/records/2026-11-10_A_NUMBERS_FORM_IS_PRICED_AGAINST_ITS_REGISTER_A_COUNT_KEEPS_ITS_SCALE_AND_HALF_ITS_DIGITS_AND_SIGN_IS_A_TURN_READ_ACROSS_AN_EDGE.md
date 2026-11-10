# A number's form is priced against its register, a count keeps its scale and half its digits, and sign is a turn read across an edge

[historical] A lens from Brandon (21:25 UTC, November 10) followed the price of a width in cells
given in [the grip record](2026-11-10_A_HELD_LETTER_IS_A_LEAKY_GRIP_THE_LAW_ACROSS_A_PLACE_IS_THREE_BODY_WIDTHS_ADD_ALONG_A_BRANCH_AND_PLASTICITY_IS_ANISOTROPY.md)
(its 2.6, `b·log_b N` cells for `N` configurations). It is paraphrased; his words stay in the
conversation logs.

- How does that cost compare with the standard? He takes ordinary registers to occupy space as a
  staircase in set multiples, because of a register for the sign and because registers
  conventionally double.
- Storing a coefficient at a magnitude, as scientific notation does, costs the storage of the
  scale as well. Three million is a 3 and a scale; 3,007,000 is two such terms, with no bits for
  the places between them.
- Because the cost is logarithmic he expects this to be cheaper only in particular contexts, and
  no technique for ordinary software. It suits a graph that keeps its own counts and frequencies
  at its own coarse-grained scales, where a quantity's magnitude is implied by where it sits.
- A 3 can sit on an edge of a local region whose magnitude is implicit. One region can be three
  orders of magnitude below its neighbour, and quantities read differently in that comparison;
  taken out of its region, a quantity is still typed to it.
- Negative regions likewise. Negativity is a relative turn, a quarter turn from another value; he
  recognizes no global signing. It is mutual, as loss is, and varies with the locale.

A second lens (21:40 UTC) answered the reply to the first, at the point that a form shortening
some numbers lengthens others and that a count's low digits are noise:

- that point is compression, and he had made it of the transcendentals and their possible
  normality, and of the mantissa and the distributions of digits;
- the classes of digits have set output patterns relative to each other. Anything plus 9 ends in
  the other number's last digit less one, anything minus 9 in that digit plus one, and anything
  times 9 in ten less that digit. The order of evaluation is consistent and self-similar, and
  depends on the pair of widths and on how they are navigated;
- such algebraic relations are properties of the families and pairs, and they bound what has to
  be predicted about one digit meeting another;
- the same holds for modalities, and for inference and perception; and it is the basis of
  rhythm, which is attained only by coupling harmonies.

This record recovers what the repository held, prices a real table of counts in each form on the
host, and states eight joins. The charts are the rows "Number, radix, places" and "Music,
acoustics" of [the atlas](../../docs/atlas/CHARTS.md). Refs #73, #406, #638.

## 1. Recovered: what the repository already held

| Part of the lens | Held as | Where |
|---|---|---|
| the cost `b·log_b N` | `E(b) = b/ln b`, least at `e`, among integers at 3 | `radix.economy` |
| a value as terms at scales | a value is a word or a graph whose branches sum into it (`1097 = 137·2³ + 1`); a width follows its information and is never doubled by default | the guide's precision law (November 3 and 5) |
| a number's cost depends on its form | literal, factor and landmark codes with Elias gamma scales: `13122 = 2·3⁸` costs 13 bits as factors against 14 as bits | `arith.presentation-codes` |
| a standard register | a native type is the place graph with its choices fixed; signed and unsigned are two sections of one ring; the sign is the top place with a negative weight | `radix.register-presets`, `radix.place-complex`, `radix.closing-edge` |
| a signed digit at a place | digits `{−1, 0, 1}`; the non-adjacent form has nonzero density 1/3 against binary's 1/2 | `radix.redundant-fibre` |
| a scale held by a locus | each locus's entries live on its own dyadic lattice `2^(−L)`, with a clock precision `k_m = 2⌊log₂ m⌋ + 1` and the remainder carried | `hnn.lattice-deposit`, `hnn.gamma-kraft` |
| a scale and a phase | `log_b n = k + θ`: the length is the winding, the mantissa the phase | `radix.leading-face-gas`, `radix.level-laws` |
| a count's grain | `L(N) = ⌈√(N ln 2/2)⌉` cells distinguish a rate after `N` readings | `receiver.refining-grain` |
| a turn in the radix | a mode reads the passage as a numeral in its own complex radix `2^(−D) e^(iΘ)` | `hnn.mode-radix-register` |
| the log of a ratio | a lift fibre whose winding is the branch; projective (`logFibre(u·r) = logFibre(r)`) and additive along composed comparisons | `ratio.log-branch`, `ratio.log-fibre-projective-additive` |
| turns on edges | the connection-valued incidence `(d_A φ)_e = g_e φ(t e) − φ(s e)`; an odd ring of alternating preferences is frustrated | `complex.connection-incidence`, `contact.odd-alternation`, `key.connection-cheeger` |
| negation | the Swing is harmonic conjugation, the point reflection about its anchor | `swing.harmonic-conjugation`, `contact.negation-tie` |
| plus, minus and times 9 | `m ≡ −1 (mod b) ⇒ m x ≡ −x`; on ten's two cycles 9 is the identity on ℤ/2 and the half-turn on ℤ/5; `−d/9` is the repdigit `…ddd` | `radix.multiplier-face-action`, `radix.digit-move-place-kind`, `radix.base-neighbour-rings` |
| digit classes with set patterns | the last digit, the digit sum and the alternating sum are faces modulo divisors of `b`, `b − 1`, `b + 1`; a conserved face is a congruence, one law for every operation | `radix.cheap-faces`, `face.conserved-is-congruence`, `arith.association-is-evaluation` |
| what is left to predict | the carry is a chain whose uncertainty falls by `b` for each place read below; the middle place of a product is fed by the most paths and flattens first | `radix.carry-chain-eulerian`, `radix.digit-path-heat` |
| a row of the table as a clock | each row is the rate-`x` clock on the circle of `b` steps, with period `b/gcd(x, b)`; a carry is a section crossing | `radix.multiplication-table`, `radix.carry-section-flux` |
| digit distributions | the leading face is a rotation read through the base's log partition (Benford) | `radix.leading-rotation-benford`, `rotation.three-distance` |

Not held before this record: the price of a form against a staircase of containers, Kraft's
inequality stated for sparse forms, how a code moves when a count loses its low digits, the share
of a value's scale its region fixes, the base turned so that no sign register exists, signs on
regions as a gauge, the bits of an output digit split into conserved and carried, the carries of
a rate as a rhythm, and the leading digit's law under a scale law other than Benford's.

## 2. The joins added

### 2.1 The base is not the waste: the container, the turned place and the unneeded digits are

[proved-standard] `b·log_b N = (b/ln b)·ln N`, so bases compare by `b/ln b` (`radix.economy`).
Against the best base `e`: base 2 costs 6.2% more, base 3 0.5%, base 4 the same as base 2, base
10 60%, base 16 2.1 times, and a byte used as one digit 17 times. Binary places are close to the
floor.

[proved-standard] A standard register adds three choices to the places
(`radix.register-presets`).

```text
containers w₀·rʲ (8, 16, 32, 64: w₀ = 8, r = 2):   W(n) = the least container ≥ n,
past the first step:   1 ≤ W(n)/n < r,
need uniform within a step:       mean W/n = r ln r/(r − 1)   (2 ln 2 at r = 2),
need log-uniform within a step:   mean W/n = (r − 1)/ln r     (1/ln 2 at r = 2),
below the first step:   W(n)/n = w₀/n, unbounded   (a count of 1 in a byte: 8).
```

- **The container.** Past its first step a doubling staircase costs between one and two times
  the need, 39% to 44% over on the means above. Below its first step the factor has no bound, and
  a table of small counts lives there.
- **The turned place.** In two's complement the sign is the top place given the weight
  `−2^(W−1)`. That weight belongs to the container: widening copies the top bit across every new
  place, and `−1` is a word of all ones at any width, the densest word for the smallest
  magnitude.
- **The digits.** A register holds every digit down to the units whether the value's information
  reaches them or not (2.3).

Atlas `radix.container-staircase`.

### 2.2 A form that shortens some numbers lengthens others

[proved-standard] Bare binary digits cannot stand alone: the lengths `⌊log₂ n⌋ + 1` give each
dyadic block the weight 1/2, so `Σ_n 2^(−len n)` diverges and Kraft's inequality
`Σ 2^(−ℓ(n)) ≤ 1` fails. A length has to be carried, and a carried length is a scale. Elias gamma
carries it in unary, `|γ(n)| = 2⌊log₂ n⌋ + 1`, and fills Kraft's sum (`hnn.gamma-kraft`); it is
the ideal code of a law falling as the inverse square of `n`. Whatever form is chosen, its mean
length over a law `p` is the entropy of `p` plus `D(p‖2^(−ℓ))` (`code.kraft-shannon`): a form is
cheap only on the numbers whose law it matches. That is the theorem behind the lens's
expectation that the saving is particular to a context.

[proved-standard] Terms at scales, the scientific notation of the lens. Among the numbers below
`b^L`, those with `k` occupied places number `C(L, k)(b − 1)^k`, so:

```text
sparse(L, k) ≥ log₂ C(L, k) + k log₂(b − 1)   against   literal = L log₂ b,
3007000 = 3·10⁶ + 7·10³:   log₂ 21 + 2 log₂ 9   (under 11 bits)   against   7 log₂ 10   (over 23),
3007000 in binary:   22 places, 10 of them occupied;   with signed digits, 7.
```

A sparse form wins when few places are occupied, and occupation is relative to the base:
3,007,000 is sparse in base ten and not in base two. A signed digit at a place makes more numbers
sparse (`2¹³ − 1` is thirteen ones or two signed digits; `radix.redundant-fibre`), which is the
first sense in which a local sign is cheaper than a global one. The repository's presentation
codes are the same statement for factors and landmarks (`arith.presentation-codes`). Atlas
`code.form-kraft-sparse`.

### 2.3 A code at rest in its counts moves at second order in their digits

[proved-standard] Let a context hold counts `c_x` with shares `p_x = c_x/N`, and let every count
be changed by a relative error `δ_x`, `|δ_x| ≤ ε`. The code of the context's own law under the
changed table moves by

```text
D(p‖q) = ln(1 + δ̄) − Σ_x p_x ln(1 + δ_x) = ½ Var_p(δ) + O(ε³) ≤ ½ ε² + O(ε³),   δ̄ = Σ_x p_x δ_x,
rounding to s leading binary digits:   ε ≤ 2^(−s),   move ≤ ½·4^(−s),
a lone cell (p = 1):   Var_p(δ) = 0, no move at any rounding,
on another law p′ (held text):   first-order term Σ_x (p_x − p′_x) δ_x.
```

Each leading bit kept buys a factor of four. A count `n` of independent arrivals has a sampling
error of relative size `n^(−1/2)`, so its digits below the top `½ log₂ n` lie inside its own
noise: the grain of `receiver.refining-grain` is the same square root. A count needs its scale
and about half its digits. Atlas `code.count-digits-second-order`.

### 2.4 The code of a place is a difference of scales, and a region's scale is paid once

[proved-standard] A count table codes a place at `−ln(c/N) = ln N − ln c`: the count is never read
alone, only against its region's total, and the reading is a difference of two scales. That is
the lens's edge of a region with an implied magnitude, and it is the real part of the log of a
ratio (`ratio.log-fibre-projective-additive`: a common factor on a region's counts changes no
reading inside it).

[proved-standard] For values with scales `e` in regions with scales `e_R`:

```text
H(e) = I(e; e_R) + H(e | e_R),
m values of one region:   H(e_R) + m·H(e | e_R)   against   m·H(e),   saving m·I(e; e_R) − H(e_R).
```

A scale the region holds is paid once and takes from each member what the region's scale says
about it. Section 3 measures how much that is: all of it for a lone member, little in a large
region. Atlas `code.region-scale-chain`.

### 2.5 Sign is a turn: carried by the places, or read across an edge

[proved-standard] For real values `u`, `v` about a pivot `a`:

```text
log((v − a)/(u − a)) = ln|v − a| − ln|u − a| + iπ·[a lies between u and v]   (mod 2πi).
```

The real part is the difference of scales of 2.4 and the imaginary part is the relative turn. A
value has a side of a pivot and a turn relative to another value. Negation is the half-turn about
the pivot (`swing.harmonic-conjugation`), and the pivot is the region's own.

[proved-standard] Signs on regions are a gauge. Flip every value of a region `R` about its pivot
(`s_R = −1`): every ratio inside `R` is unchanged, and the turn on each edge leaving `R` changes
by `g_e ↦ s_(t e) g_e s_(s e)` (`complex.connection-incidence` with transports `±1`). The product
of the turns round a loop is unchanged by every such flip. A loop with product `−1` cannot be
flipped flat; it is the frustration of `contact.odd-alternation`. So the turns on edges are what
is read, the loop products are what is invariant, and a sign attached to a value alone is a
choice of gauge. Atlas `ratio.sign-edge-turn`.

[proved-standard] The turn can also be carried by the places. Let the base be `β = ρ e^(iθ)`.

```text
θ = 0:     β = 2, digits {0, 1}: the sign is a state apart, or a turned top place (two's complement);
θ = π:     β = −2, digits {0, 1}: every integer once, no sign place   (−1 = [1,1]);
θ = π/2:   β = 2i, digits {0, 1, 2, 3}: every Gaussian integer with one place below the point,
           no sign place   (−1 = [1,0,3],   i = [1,0.2]),   |β|² = 4 = the count of digits.
```

In the quarter-turned base neighbouring places stand a quarter turn apart and a negative weight
is the place two steps on. This is the lens's quarter turn: negation is two of them, and a real
register is the special case that keeps only every second place. A quarter turn between two
values is also the relation with no mutual gain or loss: the in-phase part of a pairing does work
and the quadrature part turns without work (the parametron's row of the objects). The machine's
modes already carry their own turned radix (`hnn.mode-radix-register`), so a contribution's sign
there is the turn its place has accumulated, read relative to the receiver. Atlas
`radix.turned-base`.

### 2.6 Nine is the half-turn of the ring of ten, at every grain

[proved-standard] The three rules of the second lens are one fact, `9 ≡ −1 (mod 10)`:

```text
x + 9 ≡ x − 1,   x − 9 ≡ x + 1,   9x ≡ −x   (mod 10);
b^k − 1 ≡ −1 (mod b^k):   x + 99 ≡ x − 1 and 99x ≡ −x on two digits, and so at every grain k.
```

The repository held it (`radix.multiplier-face-action`, October 23). The join is to 2.1 and 2.5:
a two's-complement register is this fact at the container's width, where `−1` is the word of all
ones, `2^W − 1`. Its arithmetic is the ring's and reads no sign (`radix.register-presets`: the
wrapping sum, difference and product of signed and unsigned words are the same bits). What is
called the sign is a section of the ring, the choice of which half is read as negative. So the
standard's sign is the ring's half-turn with a section chosen once for every value: the same
local fact, made global by the choice.

### 2.7 What has to be predicted is what the operands' faces do not conserve

[proved-derived] A face `q` is conserved by an operation `T` when `q(T(x, y))` is a function of
`q x` and `q y` (`face.conserved-is-congruence`); it then costs nothing to predict. For uniform
independent digits in base `b`, with `h₂` the entropy of a coin:

```text
H((x + y)_0 | x_0, y_0) = 0,      H((x y)_0 | x_0, y_0) = 0,
H((x + y)_k | x_k, y_k) = h₂(½(1 − b^(−k))):   h₂(9/20) at k = 1 in base ten, tending to one bit,
base ten, two-digit operands:   H((x y)_1 | x_0, y_0) > 2 + 15/16 bits of log₂ 10.
```

A digit of a sum takes `log₂ 10 − 1` of its bits from its own pair and one bit from the carry,
which is navigation: it is a function of the places below, and each lower place read cuts its
uncertainty by `b` (`radix.carry-chain-eulerian`). The tens digit of a product takes under 3/8 of
a bit from the units pair and the rest from navigation. The two ends of a product are cold (the
trailing face is a ring's, the leading face a rotation's) and its middle is hot
(`radix.digit-path-heat`). Atlas `code.digit-conserved-carried`.

[reading] Counts and arithmetic sit at opposite ends of one account. For a count the trailing
digits are sampling noise and are released (2.3); for arithmetic the trailing digits are the most
lawful face. Which digits a receiver may release is decided by the family the number came from,
which is the lens's statement. The transcendentals are the limit case: in the digit face of any
base they look flat (their normality is open, and nothing here rests on it), and their whole law
is in the constraint identity the guide keeps them as.

### 2.8 A rhythm is the carries of one rate read on another's circle

[proved-standard] Count by `s` on a circle of `b` steps, `0 < s < b`. The carry at step `k` is

```text
c_s(k) = ⌊(k + 1)s/b⌋ − ⌊k s/b⌋ ∈ {0, 1},      Σ_(k<b) c_s(k) = s,
any m consecutive steps hold ⌊m s/b⌋ or ⌈m s/b⌉ carries,
gcd(s, b) = 1:   c_s(k) + c_(b−s)(k) = 1 for 0 < k < b − 1   (0 at the first step, 2 at the last),
digit rows:   (b − s)k ≡ −s k, the row of b − s is the row of s read backwards.
```

Counting by 3 on ten gives digits 3 6 9 2 5 8 1 4 7 0 and carries `...x..x..x`: three onsets
spread as evenly as they can be among ten steps, which music theory calls a Euclidean rhythm
(Toussaint, 2005) and the theory of rotations a balanced word. The carry is a section crossing
(`radix.carry-section-flux`), and a section crossing is a clock tick, so:

- a rhythm needs two periods, a rate and a circle. One period gives a pulse and no pattern;
- the half-turn `s ↦ b − s` of 2.6 takes a rhythm to its complement and its digit row to its
  reverse: counting by 9 carries at every step but the first, and its digits run backwards;
- the periods a circle offers are its divisors (`b/gcd(s, b)`): on ten they are 1, 2, 5 and 10,
  and the last digit is two against five (`ℤ/10 ≅ ℤ/2 × ℤ/5`).

Atlas `radix.carry-rhythm`.

## 3. The reads

All reads are host rulers on the text's count tables (never machinery): the table of two letters
each side of TRAIN (543,071 cells in 356,758 contexts; largest count 191,853), read on HELD128
through the chain of one letter each side then two (code 0.5758 nats a place). Guesses were fixed
before each read and are in the receipts with their times.

[measured] **The cost of a count in each form** (`cap_i.py`), bits a cell:

| Form | Bits a cell | Against the floor |
|---|---|---|
| a 64-bit register | 64 | 19 times |
| a 32-bit register | 32 | 9.5 times |
| one width for the whole table | 18 | 5.4 times |
| the staircase 8/16/32/64 (unsigned; signed 8.14) | 8.07 | 2.4 times |
| scale, then every digit (Elias gamma) | 3.43 | 1.02 times |
| the floor: the entropy of the counts' own law | 3.36 | 1 |
| scale, then the leading half of the digits | 2.87 | below: digits released |
| scale alone | 2.44 | below: digits released |

Elias gamma's 3.434 bits are 2.217 of scale in unary and 1.217 of digits below the leading one. A
sign bit on each value would add 29% to it. In whole digits a cell holds 4.43 states of hardware
in base 2, 4.89 in base 3, 5.75 in base 4, 11.67 in base 10 and 258 as one byte (the floors
`e ln(c + 1)`: 3.79; base 2: 4.03; base 3: 3.81). Score G19a: the share of ones was guessed 55%
and read 47%; the entropy guessed 2.4 and read 3.36 (missed); bare digits 2.2 (2.22), gamma 3.4
(3.43), the staircase 8.3 (8.07) and the least width 18 (18) held.

[measured] **The counts of counts** (`cap_k.py`). The share of cells with `⌊log₂ count⌋ = j`
falls as `2^(−0.82 j)` over `j` = 0 to 9 (0.470, 0.234, 0.124, 0.072, 0.043, 0.025, …), so the
share of a count `c` falls as `c^(−1.82)`. Gamma is the ideal code of `c^(−2)`, which is why it
sits 2% over the floor.

[measured] **Rounding every count** (`cap_i.py`), both tables, context totals summed again:

| Counts rounded to | Held code | Move | Cells changed |
|---|---|---|---|
| unrounded | 0.5758 | | |
| two decimal digits | 0.5757 | −0.0001 | 1.9% |
| the leading half of their bits | 0.5764 | +0.0006 | 25.7% |
| one decimal digit | 0.5770 | +0.0012 | 12.6% |
| the nearest power of two (scale alone) | 0.5795 | +0.0037 | 30.0% |

Score G19b: the guesses were +0.0005, +0.004, +0.012 and +0.035, each about ten times the read.
The rule read: the low half of a count's digits is baggage for this ruler, and all but its scale
costs 0.6% of the code. The misses have one cause, the second-order law of 2.3, which was derived
after the read. Held places hit cells of count 16 or more 82% of the time (5.0% hit no cell).

[measured] **The region's share of a cell's scale** (`cap_j.py`, `cap_k.py`), entropy of a cell's
bit length in bits:

| Cells | Share | Alone | Given its context total's scale | Given that and the context's count of cells |
|---|---|---|---|---|
| all | 1.000 | 2.198 | 1.353 | 0.950 |
| in contexts of two cells or more | 0.500 | 2.415 | 2.016 | 1.901 |
| in contexts of eight cells or more | 0.080 | 2.663 | 2.523 | 2.476 |

Score G20: guessed 2.2, 1.6 and 1.45 over all cells; the fall is larger than guessed, 38% then
57%. Score G22, fixed after G20 to test it: half the cells sit alone in their context (76% of
contexts hold one cell; a context holds 1.52 cells on average), where the cell is the total and
its scale is free. Among the cells that share a context the total's scale takes 16.5% off (the
guess was under 15%: missed, narrowly), and 5% in contexts of eight cells or more. The guess of
3.0 bits for the scale alone there read 2.415 (missed), and a figure of 2.71 entered as needing
no guess was a wrong derivation (the pooled conditional does not know a cell is alone); it read
2.016. Reading: a region's total fixes a member's scale when the region is small, and says little
of each member in a large region, whose members spread over every scale. The member's rank in its
region says more (2.415 to 1.289 with the total's scale). The relative scale, total's minus
cell's, costs 2.135 bits alone against 2.198 for the cell's own: reading relative to the region
does not by itself shorten the scale on this table.

[proved-standard] **The digits of a scale law.** If the share of a value `c` falls as `c^(−α)`
over whole decades of base `b`, the leading digit has the law

```text
P(leading digit = d) = (d^(1−α) − (d + 1)^(1−α)) / (1 − b^(1−α)),   α → 1:   log_b(1 + 1/d)   (Benford),
```

and the shares of the `b` values sharing every digit but the last differ by at most the factor
`(1 + (b − 1)/c)^α`, so the trailing digit flattens as the value grows. Atlas
`radix.leading-digit-power-law`.

[measured] **The leading and the trailing digit of the counts** (`cap_l.py`):

| Digit | Cells | Entropy, bits | Reading |
|---|---|---|---|
| leading, counts of 10 or more | 78,296 | 2.261 (Benford 2.876; flat 3.170) | 1 leads 50.2%; the law `c^(−1.82)` gives 51.1% and 2.23 |
| last, counts 10 to 99 | 66,715 | 3.280 (flat 3.322) | shares fall from 0.149 to 0.069 inside the decade |
| last, counts of 100 or more | 11,581 | 3.3213 (flat 3.3219) | flat to the sample's bias (0.0006) |
| leading, context totals of 100 or more | 12,387 | 2.154 | 1 leads 52.5% |
| last, context totals of 100 or more | 12,387 | 3.3204 | flat |

Score G23: the leading digit was guessed at 49% and 2.3 bits; the last digit at 3.31 bits or more
for counts of 100 or more and 3.25 for 10 to 99. All four held, and the rule read: the leading
digits carry the law and the trailing digits are flat.

## 4. What follows for the machine

1. **The standard's waste is named and none of it is in the base.** [ruling] A register preset
   fixes three things the precision law leaves to the value: the container, the turned place, and
   the digits kept. The law for each is in section 2: a width is a scale plus the digits its
   consumer's code needs (2.3); a scale is held by the region where its members share one (2.4);
   a turn is carried by a place or read on an edge (2.5). Nothing in the machine is changed by
   this record.
2. **A release tolerance for counts.** [derived] The precision law releases a term only by
   partition at a declared tolerance with its remainder accounted. For a count read as a share,
   2.3 gives that tolerance its price: keeping `s` leading binary digits moves the code of a
   context at rest by at most `½·4^(−s)` nats. The deposit law already carries a remainder at each
   locus's own lattice (`hnn.lattice-deposit`); this gives the count's side of the same account.
3. **One read on the field's own numbers, ordered from design at 21:34 UTC.** The plain
   64-contact state at its last lap is copied and every stored number rounded to its leading `s`
   significant binary digits at its own scale, `s` = 8, 4, 2, 1; the held joint is read for each.
   - G21 (fixed 21:31 UTC): moves of +0.0005, +0.006, +0.06 and +0.5 nats a place. Rule: under
     0.01 at `s` = 4 means the digits past the fourth are baggage at this state; 0.03 or more
     means they carry law. Guess: baggage.
   - G21b (fixed 21:38 UTC, after 2.3 was derived; G21 is scored as guessed): at second order the
     move at `s` = 8 is under 0.0001. Rule: a ratio near 16 between the moves at `s` = 2 and
     `s` = 4 means the state rests in its numbers; near 4, it sits on a slope in them.
   - With it, no run: the width each number of the state occupies on the card and in the saved
     file, by part, and whether a part shares one scale or each number carries its own.
4. **Sign in the machine is already local.** [reading] A mode's contribution carries the turn of
   its complex radix, and a pair contact reads a relative turn. The lens asks that no receiver
   read a turn against a global pivot. That is a property to check in the source when the number
   system of #638 is next touched, and no part of it is ruled here.
5. **The account of a prediction has two columns.** [reading] What a receiver owes for an output
   is what its operands' faces do not conserve (2.7). The read of item 3 is that account for the
   field's stored numbers: the trailing digits are released and the held joint says whether they
   were noise, as a count's are, or law, as arithmetic's are. No further read is ordered.
6. **Rhythm is a pair's reading.** [reading] 2.8 places rhythm on objects the machine has: a rate,
   a ring and its section. It adds no part. The chord record of November 10 holds the same pair as
   circles closing at their least common multiple; 2.8 adds the pattern inside one closing.

## 5. What does not transfer

- Elias gamma, or any prefix code, as the machine's storage. The codes price a ruler's table.
- The count table. It is a ruler; a table addressed by a context is the cache the lessons refuse.
- A float. It has a scale, and it is refused for what it fixes: one width of scale, one width of
  digits and a sign bit for every value, whatever the value's information.
- Base ten. The scales of the lens are whatever base the places have.
- "Rounding is free." It was measured on a ruler at rest in its counts, read as shares. The
  field's numbers enter products across ticks, and G21 tests them.
- The quarter-turned base as machinery. It is named because it shows that a sign needs no
  register. No digit set is authored into the machine.
- Base ten's table. The rules of nine are the half-turn of whatever ring is read; no table of
  digit rules and no calculator enters the machine.
- Music theory's catalogue of rhythms, and any authored meter.
- The normality of π or of any constant. It is open, and 2.7 uses only that its digit face holds
  no law a receiver has found.

## 6. Owed

- The scores of G21 and G21b, and design's report of widths and scales by part.
- Still owed from 21:03 UTC: G12 with the rest of the answer open and its splits, G18 by octave,
  and whether `f` = 68 and 72 run as built.
- Lean, for #410: the staircase means (2.1), the block weight of bare digits and the count of
  sparse numerals (2.2), the second-order identity (2.3), that base −2 writes every integer once
  (2.5), the carry entropy of a sum (2.7), and the carry identities of 2.8 (the balance, and the
  complement under `s ↦ b − s`).

## Receipts

Device: the host reads used no card. They ran in a VM of two threads on the PC's host, each in
under 3 s after the tables were fitted. The figures of 2.7 and 2.8 are public arithmetic,
enumerated by `digits.py` in the cloud session. Scripts and logs are in
[the receipts](2026-11-10_A_NUMBERS_FORM_IS_PRICED_AGAINST_ITS_REGISTER_A_COUNT_KEEPS_ITS_SCALE_AND_HALF_ITS_DIGITS_AND_SIGN_IS_A_TURN_READ_ACROSS_AN_EDGE_receipts/).
They read the passages under `.local/`, which stay private, and write only aggregate figures.
