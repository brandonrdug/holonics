# Code length is a field: its floor is the dark-energy term, its binding shows only through contacts, and the primes' hand sits on the floor

**Date:** 2026-10-23. **Occasion:** Brandon asked whether bits a cell is the only reading worth
caring about. He wanted the expansion and contraction of code lengths per partition, read through
dark energy and dark matter so that the information theory makes sense, with the network of entropy
lenses kept local in space and time. He asked for the reading to be paired with RH and the null cone,
for units and implicit casts, for algebraic and motion classes, and for spectral signatures of the kind
cryptanalysis reads.

**Joins:**
- The lens is the released passage tree with the node lock: the located equality of the
  [contacts record §8](2026-10-23_THE_CONTACTS_ARE_A_SHEAF_WEIGHT_TYING_REPRESENTS_THE_WORDS_AND_THE_SQUARE_LAW_IS_THE_SCATTERING_READ.md).
- The density code keeps its dilation (atlas `code.density-dilation-rate`), and a comoving receiver
  reads pressure work (`gr.comoving-deformation`).
- The cosmological constant's quantity lines are in the
  [August 25 record](2026-08-25_THE_COSMOLOGICAL_CONSTANT_IS_INFERRED_THROUGH_PLURAL_RECEIVER_FIBRES_AND_A_PRINTED_DECIMAL_IS_NOT_THE_MEASUREMENT.md).
- The null cone is the constitution's lock in the
  [September 24 record](2026-09-24_THE_NULL_CONE_IS_THE_CONSTITUTIONS_LOCK_AND_CLOSURE_IS_A_RECEIVER_READING.md).
- The hand's square-root law is the proposition `Zeta/Hand.TheHandCancelsToSquareRoot`.
  `Zeta/Seam.ThePlacementAndTheHandAreOneStatement` names its classical equivalence with the seam,
  which is not formalized.

**Truth discipline:**
- `[proved-standard]` marks a classical result, `[proved-derived]` a short derivation given here,
  and `[measured]` an exterior float reading with its receipts.
- `[interpretation]` marks a correspondence into the objects or into cosmology. The cosmological words
  are a dictionary for the information theory, not a claim about the universe.
- `[open]` marks what is owed.

## 1. The reading: a code length per region, per stretch of passage, per clock

The passage is the whole training partition (6,726 problems, 3,528,168 bytes, 14,112,672 cells),
coded online by the lens. Every byte belongs to one region:
- **Q**, the question (with its newline);
- **P**, the answer's text outside the calculations, digits excluded;
- **N**, the answer's digits outside the calculations;
- **M**, the calculation markup `<<…>>`.

Each region also has its own clock: `V_R` counts the bytes of `R` seen so far. The passage is also
cut into 20 blocks of about 336 problems, and the eleven fine roles of the earlier receipts are kept.

**Readings** `[proved-derived]`, all on a declared clock:
- `L_R(V)` is the region's cumulative code in bits; `ℓ̄ = L/V` is its mean rate and `ℓ = dL/dV` its
  marginal rate.
- **Equation of state.** `w = −d ln L / d ln V = −ℓ/ℓ̄`, read per octave as
  `w = −log₂(L(2V)/L(V))`.
- **Density ratio across an octave.** `1 + z := ρ(2V)/ρ(V) = 2^(−(1+w))`, with `ρ = L/V` the code
  density.

This is the cosmological continuity law read on code. With `E = L` the energy in a comoving volume
and `ρ = L/V`, an equation of state `p = wρ` gives `dE = −p dV`. For code this says the
**pressure is minus the marginal rate**, `p = −ℓ`, and `dL = ℓ dV` is the first law.

Three cases:
- **The floor** (`w = −1`, `ℓ = ℓ̄`). The density holds as the volume grows, like a cosmological
  constant.
- **Contraction** (`w > −1`). The density dilutes, as matter's does: a fixed cost paid once has
  `w = 0`.
- **Expansion** (`w < −1`, phantom). The density rises: the region grows harder as the passage goes on.

**A learning region cannot expand** `[proved-derived]`. If `L = hV + C(V)` with the excess `C`
concave and `C(0) = 0`, then `C′ ≤ C/V`, so `ℓ ≤ ℓ̄` and `w ≥ −1`. Expansion therefore needs an excess
that is not concave: the material itself must change.

Every reading here except the rates is dimensionless: `w`, `1 + z`, the binding fraction, the
coincidence ratio and the spectral slope survive the bits↔nats cast (`× ln 2`) and the cell↔byte
cast (`× 4`). The rates do not (§6).

## 2. Expansion and contraction per partition `[measured]`

**Regions** (node arm; bits a byte on the region's own clock):

| region | share | in context | alone | `w` at the last octaves | last block / first |
|---|---|---|---|---|---|
| question | 0.448 | 1.817 | 1.799 | −0.904, −0.923, −0.929 | 0.713 |
| answer prose | 0.424 | 1.345 | 1.545 | −0.959, −0.961, −0.970 | 0.856 |
| answer numbers | 0.052 | 2.592 | 2.795 | −0.967, −0.966, −0.979 | 0.878 |
| calculation markup | 0.076 | 1.844 | 1.871 | −0.933, −0.930, −0.903 | 0.730 |
| whole passage | 1 | 1.659 | — | −0.923, −0.939, −0.948 | — |

Every region contracts on its own clock. In context, every octave's `w` lies between −0.75 and
−0.98. The only readings below −1 are the whole passage's first octave (256 to 512 bytes, −1.018) and
one early octave of the numbers read alone (−1.006).

**Fine roles**, the last block's rate over the first:

| fine role | first → last block | ratio |
|---|---|---|
| separators | 2.087 → 0.739 | 0.35 |
| a result repeated after `>>` | 1.556 → 0.588 | 0.38 |
| calculation markup | 1.888 → 1.117 | 0.59 |
| calculation result digits | 3.330 → 2.042 | 0.61 |
| question prose | 2.332 → 1.649 | 0.71 |
| question digits | 4.834 → 3.972 | 0.82 |
| answer prose | 1.556 → 1.348 | 0.87 |
| final answer digits | 3.257 → 3.059 | 0.94 |
| answer digits in prose | 3.416 → 3.306 | 0.97 |
| calculation operand digits | 2.482 → 2.464 | 0.99 |

- The calculation's result digits contract from about `log₂ 10` to 2.04 bits a byte. The result's
  first digit is read inside the lens's six-byte reach (`48/2=` before `24`), so the lens is learning
  a table of small calculations it has met. That is a table at the lens's grain, not arithmetic.
- Answer prose stops contracting after the first quarter of the passage: its late slope is
  +0.0009 bits a byte per block.
- The operand digits hold at their floor and edge up by +0.010 bits a byte per doubling of the
  passage. They are the one weakly expanding role: new numbers the lens cannot locate.

## 3. The floor and the learning part, and their motion classes

**Fit.** On each region's own clock, octaves from `2^13` bytes, the marginal rate is fitted by
`ℓ(V) = h + c V^(−α)` (power law) and by `ℓ(V) = h + k/(2V ln 2)` (the parametric law).
- `h` is the fitted floor, the dark-energy term.
- `C(V) = L − hV` is the learning part, the matter term.
- The floor's share of the code is `Ω_floor = hV/L`.

**Measured** `[measured]`:
- **Whole passage.** `h = 1.220` bits a byte, `α = 0.21` (rms 0.022 against 0.139 for the parametric
  law). The floor's share rises from 0.29 at 256 bytes to 0.74 at the end, crossing ½ near `2^15` bytes,
  about 62 problems. Early passage is matter-dominated (most code is learning); late passage is
  floor-dominated.
- **Question.** `h = 1.187`, `α = 0.22`; floor share at the end 0.65, still learning.
- **Answer prose.** `h = 1.209`, `α = 0.30`; floor share at the end 0.90, near its floor.
- **Numbers and markup** have no resolved floor. The best power is at the grid's edge (`α = 0.02`)
  with a negative `h`: their rate still falls about linearly in `log V`.
- The fitted floor is a reading of a fit over about nine octaves, not a bound.

**Motion classes** `[interpretation]`, on the octave clock in the excess chart `C`:
- **Identity.** `C ↦ C`: a fixed cost paid once (`w_C = 0`).
- **Shear** (parabolic). `C ↦ C + k/2` per octave: a parametric model, half a bit per parameter per
  octave. This is the Krichevsky–Trofimov and Jeffreys `½ log₂ V`.
- **Boost** (hyperbolic). `C ↦ 2^(1−α) C` per octave: a nonparametric model that grows with the
  passage (Heaps-like).
- **Turn.** The floor itself: its density multiplier across an octave has modulus 1, so it sits on
  the circle.

This places the 10-17 keystone (knowledge is boost, secrecy is turn) on a code-length flow:
- Every text region's learning part is a boost: `α` is between 0.14 and 0.30 where it is resolved.
  The parametric shear needs thousands of parameters (`k` from 2,200 to 12,200) and still fits 1.8 to
  13 times worse in rms.
- The primes' signs are turn-class (§5).

## 4. Binding, the dark-matter term `[measured]`

**Binding** is what a region's code loses by being read in the passage rather than alone:
`B_R = L_R^alone − L_R^context`. The region's own lens cannot see it; it is information shared with
other regions. Its sum over the four regions is the multi-information the lens reads:
`Σ L_R^alone − L^whole = 316,506` bits on the node arm, 5.4% of the whole code.

| region | binding (bits a byte) | share of its alone code | binding `w` |
|---|---|---|---|
| answer prose | 0.200 | 13.0% | −0.51 … −0.93 |
| answer numbers | 0.203 | 7.2% | −0.95 … −1.27 at the end |
| calculation markup | 0.027 | 1.4% | noisy |
| question | −0.017 | −1.0% | noisy |

- **Answer prose.** Its binding to its question (names, objects) dilutes as its own lens learns.
- **Answer numbers.** Their binding does not dilute: copies of numbers are a constant-rate binding.
- **Question binding is negative.** The lens is not told which region a byte is in, so the regions
  share one alphabet of contexts. The answers dilute the question's statistics, and the question pays
  1% for the implicit cast (§6).

**The binding is dark in the raw spectrum.** The coincidence ratio of the passage bytes (the
Friedman index at each lag over the independent-draw floor `Σ p_b² = 0.0574`) falls back to the floor
beyond about 4 KB:
- lags 9–64: 1.078 on average;
- lags 65–512: 1.030;
- lags 513–4,096: 1.003;
- lags beyond 4,096 bytes: 1.000 (at most 1.010).

Yet located contacts save 66,553 bits at offsets of `2^15` to `2^23` cells (8 KB to 2 MB). The
long-range binding shows only through its effect on a located contact, as lensing shows a mass that
emits nothing.

**The offset profile.** These are the node lock's saved bits by octave of its offset `δ` (in cells),
the "rotation curve":

| part | octaves of `δ` | saved bits |
|---|---|---|
| inner core | `2^5`–`2^10` (8 to 256 bytes: the same problem) | 135,445 |
| dip | `2^11`–`2^14` (the neighbouring problems) | −22,794 |
| halo | `2^15`–`2^23` (across the passage) | 66,553 |

- The halo is roughly flat at 10,000 to 12,500 bits per octave from `2^18` to `2^21`, then falls at
  the passage's edge.
- The dip straddles the passage horizon `2^13`. Inside the horizon the passage term already holds the
  recent past, so the lock's wrong contacts cost. The halo lies outside it, where the passage term has
  forgotten.
- By region:
  - answer prose is mostly core (103,085 of its 115,633 bits): copies from its own question;
  - calculation markup is almost all halo (16,918): calculation forms recur across the passage, not
    within a problem;
  - question is split between core (26,730) and halo (30,943): templates recur.

## 5. RH: the primes' hand sits on the floor

**The count lens** reads the hand `λ(n) = (−1)^Ω(n)` through one learned bias. Write
`L(N) = Σ_(n≤N) λ(n)`.

**The deficit sandwich** `[proved-derived]`. The count lens's maximum-likelihood saving over the
floor is `D(N) = N(1 − h₂((N + L)/(2N)))` bits. With `y = L/N`, `1 − h₂((1 + y)/2)` is
`(1/ln 2) Σ_(k≥1) y^(2k)/(2k(2k − 1))`, so:

`L²/(2N ln 2) ≤ D(N) ≤ L²/N`

The lower side is Pinsker's inequality; the upper side holds because the series over `y²` increases
in `|y|` and equals `ln 2` at `|y| = 1`.

**RH as a growth law on the saving** `[proved-derived]`. RH holds exactly when `L(N) = O(N^(½+ε))`
for every `ε > 0` (`[proved-standard]`, from `Σ λ(n) n^(−s) = ζ(2s)/ζ(s)`). In Lean that growth law
is `TheHandCancelsToSquareRoot`; its equivalence with RH is named by the seam and not formalized.
By the sandwich, the growth law is equivalent, with no hypothesis, to a growth law on the saving:

**RH ⇔ for every ε > 0, `D(N) = O(N^ε)`:** the count lens's saving on the primes' hand grows slower
than every power.

The prime number theorem is the weaker statement `L = o(N)`, that is `D(N)/N → 0`: the hand's code
density converges to the floor.

**The excess is a shear with no boost.** The count lens's code is
`KT(N) = N + ½ log₂ N + ½ log₂(π/2) − D(N) + o(1)` (`[proved-standard]`, Stirling). Its excess is
therefore a shear of ½ a bit per octave (its one parameter) less `D`. RH says no boost component ever
enters that excess.

The shear's ½ and the critical line's ½ are one square-root scale `[interpretation]`. A learned bias
pays back its ½ log₂ N only where `|L| ≳ √(N ln N)`.

**Beyond RH** `[open]`. Gonek and Ng conjecture that `M(x) ≪ √x (log log log x)^(5/4)`. Under the
hand's analogue, `D(N)` grows slower than `log N`, so the count lens's parameter never pays back: the
primes' key stays dormant (the 10-17 keystone).

**Measured** `[measured]`, `N` up to `2^22 = 4,194,304`:
- **Count lens.**
  - The largest deficit is `D = 1.276` bits at `N = 96,862` (`L = −414`, `|L|/√N = 1.33`), where the
    parameter costs 8.6 bits.
  - `D` never exceeds the parameter's cost for `64 ≤ N ≤ 2^22`.
  - At `2^22`, `KT − N = 11.27` bits, that is `11 + 0.33 − 0.06`.
  - For the Möbius signs on the 2,549,834 squarefree `n`, `|M|/√N` is at most 0.567 (at `N = 199`),
    and the saving is at most 0.254 bits for every `N` from 4,096 on (at `N = 59,577`).
- **The tree lens** (the same lens as the text, without a clock):
  - **λ.** 1.00001 bits a cell; `w = −1.000` on every octave from `2^14`.
  - **μ.** 1.0371 bits a cell, split exactly into three parts:
    - its zeros: 0.4161 a cell, contracting from 1.209 to 0.392 a cell across the octaves with
      `w` between −0.87 and −0.94: a boost, the learnable structure of square divisors;
    - its signs: 0.6165 a cell, 1.014 a sign, with `w = −1.00 ± 0.01`: the floor, the 1.4% being
      the tree's regret;
    - the alphabet cast: 0.0045 a cell.

  So μ is a floor (its signs) plus matter (its zeros), and λ is a pure floor.
- **Coincidence spectra.**
  - The hand's lag correlation stays within noise: at most 0.0014 over 351 lags up to 961,548,
    against `1/√N = 0.0005`. Chowla's two-point conjecture says it tends to 0, and Tao proved the
    logarithmically averaged form.
  - The Möbius signs: at most 0.0027.
  - The Möbius zeros: +0.744 excess at multiples of 4 and −0.305 elsewhere, the square divisors'
    pattern.

  So the hand has the ciphertext signature (flat), and the zeros have the plaintext signature
  (structured).
- **Sarnak's conjecture** `[open]`: μ is orthogonal to every zero-entropy sequence. In this record's
  words, the hand is turn-class for every deterministic lens. The count lens and the tree lens are two
  such readings, measured.

## 6. Units, casts and the cone

**Quantity lines.**
- A rate is bits (or nats) per byte (or cell) of a declared region on a declared clock.
- The bits↔nats cast multiplies rates by `ln 2`, and the byte↔cell cast divides by 4.
- `w`, `1 + z`, the binding fraction, the coincidence ratio and the spectral slope carry no unit.

**Region clocks.**
- The cast between a region's own clock and the passage clock is the region's share. It holds across
  blocks to about 3%: Q 0.440–0.452, P 0.423–0.429, N 0.050–0.053, M 0.074–0.078.
- So `w` agrees on the two clocks to that grain.

**The alphabet cast.**
- μ coded in four-valued cells pays for the value it never uses: 0.0045 bits a cell overall, 0.215 in
  the first octave and 0.003 late.
- The hand pays 0.19 a cell in its first octave and nothing late.
- A cast's cost is paid early and dilutes: it is matter-like.

**The clock cast.** Giving the lens the residue `n mod 4` lowers μ from 1.0371 to 1.0258 bits a cell
(47,000 bits).
- The zero part costs 0.674 against 1.209 a cell in the first octave, but 0.388 against 0.392 in the
  last.
- The clock-free lens infers the residue from the content (an implicit cast), and the explicit clock's
  advantage dilutes.

**The region-type cast.** The question costs 1% more in the passage than alone (§4): the lens infers
which region it is in from context, and pays for sharing.

**The cone** `[interpretation]`. The lens reads three reaches:
- the window, 24 cells (6 bytes), read exactly;
- the passage horizon, `2^13` cells, the mixture's memory;
- the lock, which reaches the whole passage (`2^23` cells) through loop closure.

The lens advances one cell a tick. A contact's offset is therefore both a separation and an elapsed
time, and the cast between them is implicit at one cell a tick.

A holding lock is a null contact: its slip vanishes, `Q = ⟨Δ|Δ⟩ = 0`, which matches the 09-24 record's
null cone as the constitution's lock. The offset profile of §4 is the distribution of null contacts
over separation. The dip sits on the passage horizon, and the halo lies outside it.

**Spectral signature.** The node arm's code signal (bits a byte along the passage) has power
`∝ f^(−0.31)` between `10^(−4)` and 0.05 cycles a byte, between white and pink. The lock's saving
signal goes as `f^(−0.18)`.

## 7. Owed

- **Lean** (a box in #410):
  - the deficit sandwich `L²/(2N ln 2) ≤ D(N) ≤ L²/N` over `Real.binEntropy`;
  - `TheHandCancelsToSquareRoot ⇔ ∀ε > 0, D(N) = O(N^ε)`, unconditionally (the upper side needs only
    `log z ≤ z − 1`; the lower side needs `artanh y ≥ y`);
  - the concavity statement of §1 (a concave excess cannot expand).
- **Atlas rows:** `code.equation-of-state`, `code.region-binding`, `rh.hand-count-deficit`.

## Receipts

`2026-10-23_CODE_LENGTH_IS_A_FIELD_receipts/`. Every reading is an exterior float read: the programs
store floats, which the precision law allows only outside the machine.

**Programs:**
- `field.rs` extends the lock program with a phase modulus, cell input, per-cell outputs and the node
  lock's offset profile.
- `prep.py` writes the regions and the Möbius and Liouville sequences (sieve to `2^22`; it checks the
  rendering against the passage and the first twelve values).
- `run.sh` launches four lanes together.
- `analyze.py`, `blocks.py`, `classify.py`, `rh.py` and `spectra.py` read the outputs.

**Outputs:**
- the run summaries `run_*.txt`;
- `analyze.txt`, `blocks.txt`, `classify.txt`, `rh.txt`, `spectra.txt`;
- the curves `field.json`, `rh.json`, `spectra.json`, `classes.json`.

**Timing.** The projection took the largest measured rate, 4.72 µs a cell, with the upper end declared
at twice that for four lanes together. Each run's deadline was its upper end.

| run | cells | projection | deadline | wall | peak |
|---|---|---|---|---|---|
| whole passage | 14,112,672 | 67–133 s | 133 s | 63.1 s | 1,195 MiB |
| Q | 6,324,000 | 30–60 s | 60 s | 28.7 s | 605 MiB |
| P | 5,983,920 | 28–57 s | 57 s | 25.1 s | 546 MiB |
| N | 732,116 | 4–7 s | 7 s | 2.7 s | 145 MiB |
| M | 1,072,636 | 5–11 s | 11 s | 3.3 s | 135 MiB |
| μ, no clock | 4,194,304 | 20–40 s | 40 s | 36.1 s | 2,198 MiB |
| λ, no clock | 4,194,304 | 20–40 s | 40 s | 27.0 s | 1,226 MiB |
| μ, clock mod 4 | 4,194,304 | 20–40 s | 40 s | 31.5 s | 2,199 MiB |

- All exited 0. Measured over the projection's upper end ranged from 0.30 (M) to 0.90 (μ, no clock).
- The μ runs build about seven times the nodes per cell of the text (25 million against 12 million
  for three times fewer cells), since the primes' sequence repeats few long contexts.
- The whole run reproduces the October 23 located-equality reading exactly: base 0.4274, node lock
  0.4147.
