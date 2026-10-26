# The generator is the modulator: a turn is two reflections, and the base turns, collapses or reflects each ring

October 26. Refs #404, #406, #405, #386. Two reads on Brandon's PC locate where the plain unit
tower fails at the equals; the derivation below says why it fails, what replaces the retired stores,
and which tower is built and read next, its acceptance and decision fixed before it runs. Grades:
[measured] for reads, [standard] for textbook mathematics with its source, [derived] for what
follows from the objects, [agent-inferred] for each choice and reading. Receipts:
[`…_receipts/`](2026-10-26_THE_GENERATOR_IS_THE_MODULATOR_A_TURN_IS_TWO_REFLECTIONS_AND_THE_BASE_TURNS_COLLAPSES_OR_REFLECTS_EACH_RING_receipts/RUN.md).

Computational object: the helical pair interaction. The derivation touches the helix (a mode's
phase), the pair (the contact that takes two phases' product), faces and placement (a numeral read
on a ring) and cell holonomy (the curvature of a pair table on the class graph's cycles); the tube
and the tower thread stay as the plain tower has them.

## 1. Where the plain tower fails: it holds only what it heard often

[measured] The read fixed in
[the digit-pieces record](2026-10-26_THE_DIGIT_PIECES_ARE_NOT_THE_CAUSE_THE_PLAIN_TOWER_WRITES_BACK_176_OF_1572_HEARD_CALCULATIONS_SO_THE_EQUALS_IS_READ_WHERE_IT_WAS_HEARD.md)
§3 ran as fixed (12.0 s of a 40 s deadline). On every ninth training problem the plain tower `C`
writes 157 of 2,344 calculations right at the equals, against 176 of 1,572 met held-out ones:
`z` = −4.95, so decision 1 holds. The tower does not write back a calculation even in the problem
it heard it in; the failure is holding.

[measured] The rules then binned every calculation by how many times the training text holds its
`<<expression=c>>` whole (`written_rules.py … heard`, added for this read):

| hearings | 0 | 1 | 2–3 | 4–7 | 8–15 | 16+ |
|---|---|---|---|---|---|---|
| `C`, training slice | — | 15 / 920 | 11 / 345 | 11 / 290 | 13 / 327 | 107 / 462 |
| `C`, held out | 14 / 876 | 7 / 239 | 11 / 224 | 4 / 255 | 23 / 326 | 131 / 528 |
| `F` (digit foil), held out | 25 / 876 | 12 / 239 | 3 / 224 | 10 / 255 | 22 / 326 | 84 / 528 |
| 6-gram, held out | 30 / 876 | 111 / 239 | 154 / 224 | 223 / 255 | 307 / 326 | 523 / 528 |
| 8-gram, held out | 34 / 876 | 206 / 239 | 211 / 224 | 254 / 255 | 326 / 326 | 528 / 528 |

[agent-inferred] At equal hearings the training slice and the held-out text read the same (heard
once: 1.6% and 2.9%; 16 or more: 23% and 25%), and a calculation heard once is written no better
than one never heard (1.6%). The problem's own hearing adds nothing. What `C` writes after `=` is
the frequency of the expression, not the crossing of its operands. The n-grams write back what
they heard because they hold contexts; nothing in this lane may do that (the retired stores).

[measured] The never-heard held-out calculations are 876: 169 sums and 143 differences of two
whole numerals (312), 118 products, 72 quotients, 102 with a decimal and 272 with more than two
operands. On the 312, the 6-gram writes 4 right and the 8-gram 8.

## 2. The derivation: the generator is the modulator

Brandon's lens of October 26 asks whether "generator" and "modulator" are one thing. In three
standard forms, they are.

1. [standard] **A turn is two reflections.** The helical code's group
   `⟨S, U | U² = 1, USU = S⁻¹⟩` is the infinite dihedral group, which is the Coxeter group generated
   by the two reflections `U` and `US`: `S = U·(US)`. On the circle, two reflections compose to the
   turn by twice their relative angle (`R_ψ R_χ = Rot(2(ψ − χ))`; Lean `reflection_mul_reflection`,
   `lean/Holonics/HNN/Floquet.lean:408`). A generator is two modulators, and a modulator is a
   generator seen in a mirror.
2. [standard] **Shift and clock are one operator a quarter-turn apart.** On `ℤ/m`, the discrete
   Fourier transform `F` conjugates the shift `X` to the clock `Z` (`F X F⁻¹ = Z^{±1}`, the sign a
   convention), and `F²` is the reflection `x ↦ −x`. Over the reals, the metaplectic representation of `SL(2)` makes the
   turn a fractional Fourier transform, the boost a dilation and the shear a chirp, the Swing's
   three kinds. Which of shift or clock "generates" is fixed only by the receiver's frame, so no
   frame is privileged.
3. [standard] **A modulated law is a constant law in the pump's frame.** By Floquet–Lyapunov, a
   periodically modulated constitution `ẋ = A(t)x` is `x = P(t) e^{Bt}` with `P` periodic: the
   modulation is a constant generator `B` read in a moving frame. And for a closed ribbon,
   `Lk = Tw + Wr` (Călugăreanu–White–Fuller; the guide's helical code §5): the linking number is
   invariant while its split between the frame's twist and the strand's writhe depends on where
   one looks.

[agent-inferred] The last is the shape of mutual code length: `L(A) + L(B|A) = L(B) + L(A|B)`. The
sum is one invariant, and how it splits between the two conditional lengths is the frame. Two
Holons comparing through a contact repair this invariant together, as a duplex keeps its linking
number. No side is the teacher.

### The same identity in music and in the primes

1. [standard] **A scale's generator is its modulator.** Music theory calls the interval that stacks
   a scale its generator: the diatonic scale is seven fifths in a row, and on the twelve pitch
   classes `×7 (mod 12)` turns the chromatic order into the circle of fifths. Modulating to the
   neighbouring key slides the seven-fifth window one step along the same chain (one sharp more).
   The sizes of the well-formed scales the fifth generates (5, 7, 12, 41, 53) are the denominators
   of the convergents and semiconvergents of `log₂(3/2)`. A line of that slope wound on the torus is
   unicursal, and its crossings with the grid write the scale: a Sturmian word, with at most three
   gap sizes (the three-distance theorem). [agent-inferred] Read at its crossings, a unicursal
   generator is a modulator.
2. [standard] **How much coupling a prime ring needs is a question about the Riemann hypothesis's
   family.** The rotor (next section) couples the planes of a prime ring `p` along the cycles of
   `×10`, whose length is `ord_p(10)`, the period of `1/p`. The primes where it is one cycle through
   every nonzero residue are those with 10 a primitive root (7, 17, 19, 23, 29, 47, …). Assuming the
   generalized Riemann hypothesis, their density among the primes is Artin's constant, 0.3739558…
   (Hooley, 1967; 10 is not a power and `10 ≢ 1 (mod 4)`, so no correction factor).

### The base on coprime rings

[derived] A numeral `d_n … d_0` is read by Horner's step `v ← 10v + d`. On the ring `ℤ/m` the
base acts by its residue `b = 10 mod m`, and each ring is one of the Swing's kinds:

| ring | `10 mod m` | the step | kind | what it reads |
|---|---|---|---|---|
| 3, 9 | 1 | `v ← v + d` | turn | the digit sum (casting out nines) |
| 11 | −1 | `v ← −v + d` | reflection | the alternating sum (casting out elevens) |
| 2, 5, 10 | 0 | `v ← d` | collapse | the last digit |
| 7, 13, 37, 101, 100, … | other | `v ← 10v + d` | coupled planes | the period of `1/m`; the tens |

[derived, the mathematics thread; checked exactly over 411,365 integer cases, its
[record](2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md)] **What one plane carries.** On a ring coprime to 10, the digit maps generate the ring's
whole affine group, which is finite, so it fixes a point and acts linearly, and its translations
need every character in the orbit of `×10` and conjugation. One plane carries the residue only if
`10 ≡ ±1`: rings 3, 9 and 11. A prime `p` needs `ord_p(10)` real planes, half that when the order is
even, in every chart (7 and 13 three complex planes, 37 three, 101 two). The suffix, the last `k`
digits, is different: `x ↦ (x + d)/10` is a contraction, so one real coordinate with `λ = 1/10`
holds it down to its grain (the chaos-game address, geometric, with no store), and a real plane
holds units and tens as two coordinates under the nilpotent move `(s, t) ↦ (d, s)`. What fails is
the phase chart, where a sum is one crossing (a product of turns): there the last two digits take a
chain of two coupled planes, while in the coordinate chart a sum's tens is a staircase read through
many kinks. The step `x ↦ 10x + d` is one dilation by 10 about the pivot `−d/9` (the 10-adic
`…ddd`): it boosts at the real place, contracts at 2 and 5, translates at 3, is a half-turn at 11
and a turn of order `ord_p(10)` elsewhere. In a ring's Fourier chart the coupling it needs is a
rotor: the mode of frequency `k` takes the old mode of frequency `10k` and turns by `k·d`. Generator
and modulator are again one move.

On the tower's pumped mode `h ← αh + β·conj(h)`, the depth `κ` of the pump realizes the three
kinds: `κ = 0` turns, `|κ| = ½` collapses (determinant `ρ²(1 − 2|κ|) = 0`) and `|κ| = 1` reflects.
The base's action on a ring is the depth `κ = (1 − b)/2` for `b ∈ {1, 0, −1}`.

[standard] By the Chinese remainder theorem, `9·10·11 = 990` addresses a numeral below 990 from
its own digits on three coprime rings, with no table; a larger numeral adds rings (`7`, `13`, `101`)
or its size. Sums add phases on every ring. Products add them in each ring's index chart: on
`(ℤ/p)ˣ` a primitive root `g` turns `xy` into `ind x + ind y`, so a multiplication is a turn in
the generator's chart, and `0` (a zero divisor on a composite ring) is a collapse.

[measured, earlier] The machine already located one such key for itself: on arithmetic text the
newline closure's torsion is `b(b + 1)`, casting out elevens, with `−` reflecting and `=`
restarting, and split by result length the closure is the exact sum
([the newline closure record](2026-10-25_THE_NEWLINE_CLOSURE_HAS_TORSION_B_TIMES_B_PLUS_ONE_A_PAIR_KEY_CARRIES_THE_UNITS_AND_CASTS_OUT_ELEVENS_AND_SPLIT_BY_LENGTH_THE_CLOSURE_IS_THE_SUM.md)).

### What a register keyed by its class can and cannot add

[derived] Every per-class move (turn, collapse, reflection, keyed by the arriving class alone) is
real-affine in the state. After `a + b`, the register is `M(digits of b)·h_a + c(digits of b)`:
- **Ring 9 (content).** `M = 1`, so `a + b` comes out exactly. A turned mode keyed by its class
  carries it.
- **Ring 11 (order, the hand).** The register reads `(−1)^{len b}·a + b`: right on one parity of
  `b`'s length. This is the newline closure's split by length. Class keying gets half; the hand
  carries the rest.
- **Ring 10 (position, the seam).** `v ← d` forgets `a`. Keeping `a₀` while `b`'s digits collapse
  needs two states co-present, and the sum is the product of their phases,
  `e^{iθ(a₀ + b₀)} = e^{iθa₀} e^{iθb₀}`. One linear read and threshold cannot read a relative phase
  (Lean `no_linear_threshold_reads_relative_phase`, `Floquet.lean:446`). The pair contact's
  bilinear block can: `Re(c₁h₁)·Re(c₂h₂)` holds `½Re(c₁c₂·h₁h₂)`.

[derived] A pair table's turn is then an exact part plus curvature. Keyed linearly on (current,
previous) class, a turn is `f(c) + g(p)`, which gives the relative phase `a(c) − a(p)` of two
modulators. The pairs `(digit, +)` and `(+, digit)` need a turn not of that form. That residue is
the holonomy of the pair 1-cochain on the class graph's cycle digit → `+` → digit: its harmonic
part in the Hodge split ([faces on cycles](2026-10-24_FACES_ARE_READ_ON_CYCLES_A_FACE_IS_A_COHOMOLOGY_CLASS_THE_CARRY_IS_ITS_BOCKSTEIN_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART.md)).
The exact part is the modulators. The curvature is the generator proper.

### Why the plain tower cannot, and what replaces the stores

[derived] The plain tower's mode is gated: the arriving unit sets each mode's hold `ρ_t`, and its
turn `u` is fixed. A unit therefore never moves a phase; it only weights how long a superposition
of inputs lasts. Sums of phases (ring 9), the hand (ring 11) and the product of two phases
(ring 10) are all outside it, which is what §1 measured: it writes after `=` what it heard most.

[derived; agent-inferred] The replacement begins with the tower's own pumped mode and pair
contacts, both built on October 23 and 24 (`hnn::tower`, `TowerDeclaration::pumped`,
`ContactLaw::Pair`) and never trained on units, and is completed by the rotor, the coupling of a
ring's planes that the tens and the coprime rings need (built next). Every arriving unit turns and reflects each mode at its own angle (the generator
and the modulator are one move); relative phase and order are then carried by the motion; and the
pair contact takes two modes' phases' product at the seam. Between crossings a mode carries its
phase unchanged, as an ideal fluid carries its circulation (Kelvin), and only a crossing changes
it. Addressing is geometric: a numeral's place on the rings is its address, so nothing is filed or
looked up.

## 3. The first build loop, fixed before it runs

[measured] **The rings read the n-grams.** `written_rules.py … rings` (added in this commit) reads,
on the 312 never-met sums and differences, how many written values are right modulo 9, 10 and 11,
each beside a shifted foil (the next such calculation's written value against this one's exact
value):

| | ring 9 | foil | ring 10 | foil | ring 11 | foil | mod 990 | foil |
|---|---|---|---|---|---|---|---|---|
| 6-gram | 24 | 37 | 232 | 80 | 15 | 26 | 4 | 2 |
| 8-gram | 22 | 35 | 237 | 82 | 21 | 25 | 8 | 1 |

[agent-inferred] The n-grams carry position and nothing else: ring 10 three times its foil, ring 9
and ring 11 below theirs. A context of a few bytes holds `a₀` and `b₀` together (a pair, by
adjacency), so the last digit is right, while the content and the hand of the whole numeral are
missing. This is the decomposition the derivation predicts, read on a machine that has only one of
the three.

[definition] **The towers.** On `C`'s recipe and committed units (`64 64 256 2 8 128 3 7`, the
founding key stream of the cause test, three passes), two towers:
- `P`, `train-unit-pumped-tower`: pumped modes, rectifying contacts;
- `PP`, `train-unit-pair-pumped-tower`: pumped modes, pair contacts.

Each is read by `read-unit-tower-written` as `C` was (the `lapD8` key file, one draw, 400 free
bytes, the equals at 64, a cap of 8 units) on the held-out text, then by
`written_rules.py dev.txt train.txt rings C P PP` and `… heard C P PP`. `C`'s rings are read first,
from its existing read.

[agent-inferred] **Predictions.** `C` at its foil on rings 9 and 11 (a gated mode moves no phase);
ring 10 open for `C`, which may hold adjacent last digits through its fast modes as the n-grams do.
`P` above its foil on ring 9. `PP` above its foil on rings 9 and 10, and ring 11 partly. Neither is
expected to pass the acceptance: a pumped mode holds a sum's tens only in the coordinate chart, as a
staircase its readout reads through many kinks, not in the phase chart where the sum is one
crossing (§2). The loop's
reading is which rings rise, which tells whether the towers' own descent locates keyed turns on
mixed text at all; the rotor ring, the build the mathematics thread proposes (its record's §7–8, with its own
acceptance on the never-met calculations against the 8-gram), takes the same descent.

**The acceptance**, the product claim of this step: a tower writes at least 156 of the 312
never-heard sums and differences right at the equals, and its held-out code after three passes is
at most `C`'s 1.869 bits a byte. Until it passes, the step reports what it measured.

**The decision**, with each ring's count read against its foil by the pooled two-proportion `z`:
1. A tower passes the acceptance: the next loop is products, read in the index chart (rings 7, 11,
   13 and their primitive roots).
2. Ring 9 is not above its foil in `P` or `PP` (`z ≤ 1.96`): the keyed turn is not learned by
   descent; the next loop locates the turn angles by loop closure over the digit classes.
3. Ring 9 is above and ring 11 is not: the hand is missing; the next loop is the reflection at the
   operator and the restart at `=`.
4. Rings 9 and 11 are above and ring 10 is not in `PP`: the seam is missing; the next loop is the
   seam state at the operator, the pair contact's operands.
5. All three are above and the acceptance fails: what is missing is the tens and the carry, which
   one plane cannot hold as a phase; the next loop is the rotor ring on `PP` (the mathematics
   thread's law): a level's modes grouped in rings of four, each class permuting each ring by an
   integer key `σ ∈ ℤ/4` located by loop closure before the existing pumped move, so mode `j` holds
   the character `10^j`; at `σ = 0` it is `PP` itself, the permutation is unitary, and it indexes no
   position and stores no content.

Beside the decision, read and reported: the heard profile of `P` and `PP`, by operation, and the
held-out code by region.

**The level read** (agent-inferred from the mathematics thread's request, fixed before it runs).
`read-unit-tower-at` reads each of `C`, `P` and `PP` from rest on every problem, framed as the
written read frames it and followed by its true answer, and writes each level's carried modes after
the unit holding a place (`tools/gsm8k/numeral_rings.py places`). Two kinds of place are read:
`numerals`, the last digit of each whole numeral of three or more digits (10,792 places in the first
2,000 training problems, 3,810 in the held-out problems), labelled by the numeral; and `equals`, the
`=` of each calculation `<<a+b=` or `<<a-b=` (2,200 and 841), labelled by `a`, by `b` and by the
exact result, which reads the capture directly: whether the state at the equals still holds the
operand read before the operator, the one read after it, and their sum or difference.
`numeral_rings.py probe` fits a nearest class mean on the training cells labelled modulo 9, 10, 11,
7, 13 and 100, names the held-out cells, and prints
beside it the same probe on the modes' energies (blind to phase), the majority residue, the residue
the numeral's last two digits name (the suffix, what position alone carries) and a foil read
against another problem's cell. A level holds a ring as a phase where its modes name more than the
suffix (pooled two-proportion `z > 1.96`) and more than its energies do. The derivation predicts
that `C` holds none past the suffix, and that a pumped tower whose descent located keyed turns holds
ring 9, and ring 11 under `PP`, but not 7 or 13, which need coupled planes. It is a reading of the
state, not an acceptance; a ring left at its foil under `PP` names the capture at the operator as
the first missing part (the pair block reads `a + b` and `a − b` only from operands captured there),
and at the equals a ring-9 phase turned through the whole calculation holds a sum's result without
any capture (the concatenation `10^len(b)·a + b` equals `a + b` modulo 9), so there the capture is
named only by the result's other rings and by `a` held apart from `b`.

[definition] **The run.** On the PC, at the commit of this record, with the binary built from it,
under the `wait4` wrapper, `RAYON_NUM_THREADS=8` and an 8 GiB memory scope per run. `P` and `PP`
are independent and run together (16 of 24 cores, two scopes of 8 GiB).
- A development pass for each on the first 800 training problems, together, under a 180 s
  deadline (unmeasured, as `C`'s was: 14.4 s).
- The projection for three passes is the cause test's form `3·(S·1.12·w + h) + 1 s`, with `S` =
  1,311 sections, `w` the largest measured milliseconds a section in the development pass's
  windows, and `h` its held-out read. The deadline is that projection, held by `timeout`, and a run
  whose 32-section window passes `32 · 1.12 · w` is stopped and reported incomplete. No deadline is
  raised.
- The reads as `C`'s, under the cause test's 30 s deadline each.
- The level read: `read-unit-tower-at` unmeasured in release (80 problems took 18.8 s in a debug
  build in the container), planned at one to three minutes, deadline 180 s a read, four reads a
  state (two kinds, training and held-out); the probe 300 s a state and kind, the three states
  together.

## 4. The recorded failures this loop could repeat

- **An authored routine standing in for learning.** The rings, the foil and the bar are exterior
  reads; nothing enters the machine but the text. The towers find their angles by their own
  descent; no digit, operator or ring is named to them.
- **Store or copy machinery standing in for learning.** The pumped mode and the pair contact keep
  no context, slot or key; a numeral's address is its phase on the rings.
- **Seen material graded as unseen.** The acceptance counts only the never-heard calculations.
- **Text run on its codec's grain as the exception.** The pumped mode and the pair contact are
  modality-free (the tower reads classes of a declared alphabet). The rings are the arithmetic face
  of a law that reads any periodic structure: a beat in audio, a stride in motion, a period in an
  image row.
- **Bits read as progress.** The held-out code is a condition beside the acceptance, never the
  claim.
- **A refusal answered with a larger limit.** The deadlines are fixed above from measured rates.
