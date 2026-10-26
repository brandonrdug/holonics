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

## 4. What the first loop measured, and the rotor loop

[measured, October 26, on the PC] **`C` holds no ring past its last two digits.** At the last digit
of a held-out numeral (3,810 places), `C`'s first level names it, against the suffix (what the last
two digits alone name), the majority residue, the energy probe and the foil:

| ring | modes | energy | majority | suffix | foil |
|---|---|---|---|---|---|
| 9 | 1,017 | 621 | 637 | 1,530 | 418 |
| 10 | 2,964 | 1,841 | 3,079 | 3,800 | 2,206 |
| 11 | 991 | 583 | 599 | 1,518 | 362 |
| 7 | 1,064 | | | 1,574 | |
| 13 | 942 | | | 1,491 | |
| 100 | 1,744 | | | 3,800 | |

The second level names fewer on every ring. At the equals (841 held-out calculations) the second
operand `b` is named on ring 9 at 247 against its suffix's 676 and on ring 100 at 442 against 839;
`a` and the result sit near their majority. Nothing passes its suffix, as §3 predicted: the plain
tower's modes carry a numeral's ending and nothing a ring adds.

[measured; incomplete] **`P` and `PP` were stopped by the window guard.** Their development passes
coded the first 800 problems at 2.479 (`P`, 17.0 s) and 2.495 (`PP`, 19.4 s) bits a byte against
`C`'s 2.458 (14.4 s). In training, `P` stopped at pass 0, section 1,184 (a window of 3,157 ms against
its bound of 3,046.4 ms) and wrote no state; `PP` finished pass 0, coding the held-out text at 1.931
bits a byte against `C`'s 1.984 after the same pass, and stopped at pass 1, section 1,120 (4,095 ms
against 3,960.3 ms). Neither was relaunched. The bound came from one development window with the
cause test's margin; the training windows ran 1.5–7.9% above it in steady state, the stopping
windows coincided with load from other programs on the host, and the pumped towers halved more
steps than `C` (`P` 8 and `PP` 18 against `C`'s 1 by pass 0's section 1,184; `PP` 74 against 0 by
pass 1's section 1,120). A halving rereads the section, so a window's work is not 32 sections. The
decision of §3 is unread.

[agent-inferred] **The next loop changes the read, not the limit.**
- The unit of work is an evaluation: a section, and each halving it makes (a halving costs one
  forward read, less than a section, so the count bounds the work from above).
- `w` is the largest milliseconds an evaluation took in any 32-section window measured before
  launch: the development passes and the stopped runs' full-text windows, which ran side by side
  under the host's own load (the waiting standard's largest measured value). A tower whose
  full-text windows were never measured takes its twin's, scaled by the ratio of their development
  passes when that ratio exceeds one.
- The guard stops a window whose time passes `1.12·w·(32 + H)` with `H` the window's halvings; the
  deadline is `3·(S·1.12·w·(1 + η) + h) + 1 s`, with `η` the largest halvings a section measured in
  a pass before launch.

[agent-inferred with the mathematics thread] **The rotor loop.** The mathematics thread places the
rotor on `PP` (its record's §11), and at `σ = 0` the rotor tower is `PP` itself, so one paired run
reads both: `PP` retrained (its first pass should reproduce the stopped run's state bit for bit, a
check of the realization), and `PR`, the same tower with the rotor (`hnn::tower::Rotor`). `P` waits;
its question, whether ring 9 is learned without pair contacts, does not decide this loop.
- `found-unit-rotor-tower` (`tower_rotor.rs`) locates the step by loop closure over the training
  text's calculations of whole numerals and founds `PR` as `PP` is founded. Under a step `s` for every
  byte of a numeral, each loop and each final mode is an integer row over the unknown turns
  `θ_m[b]`; the step is the `s` whose rows' torsion (their rank modulo `p` below their rank over the
  rationals) carries the most. Its test reads `{3, 11, 101}` at `s = 1` and `s = 3`, `{3, 11}` at
  `s = 2` and `{3}` at `s = 0`: the rings of `9999`, `99` and `9` that §11 of the mathematics
  record derives, located from the rows, not supplied. A unit steps by `s` times its located bytes,
  modulo 4; the second level holds still.
- The acceptance is the mathematics thread's: never-met calculations right at the equals, `PR`
  against the 8-gram's 34 of 876 and `C`'s 14, by the paired line against `PP`; met calculations are
  reported as recitation. The level read of §3 is read for `PR` beside `PP`.

## 5. What the rotor loop measured

[measured, October 26, on the PC; receipts in `ROTOR_RUN.md`] **The locator found the tenfold
step on the real text.** Over the training text's 7,204 calculations of whole numerals (10 digit
bytes, 40 unknown turns), the rows carry torsion `3` at step 0, `{3, 11, 101}` at steps 1 and 3
(carried `3333`) and `{3, 11}` at step 2; `PR` was founded at step 1, with 120 of the 1,318 units
stepping. `PP`'s first-pass state reproduced the stopped run's bit for bit.

**The changed read held both runs.** Neither was stopped; their largest windows ran 105.7 and
106.0 ms an evaluation against bounds of 121.9 and 122.1. The window that stopped the first `PP`
took 4,095 ms over 32 sections and the 55 halvings the stopped log counts within it (74 at its
end): 47.1 ms an evaluation, inside the changed read's bound of 121.9.

| run | projection | deadline | wall | ratio | peak resident |
|---|---|---|---|---|---|
| train `PP`, three passes | 549.49 s | 550 s | 410.7 s | 0.747 | 293,148 KiB |
| train `PR`, three passes | 550.69 s | 551 s | 408.1 s | 0.741 | 291,368 KiB |

**The rotor tower codes best and recites most.** Held-out bits a byte after each pass, and the
regions after the third (question, answer prose, answer numbers, calculation markup):

| tower | pass 0 | pass 1 | pass 2 | Q | P | N | M |
|---|---|---|---|---|---|---|---|
| `C` | 1.984 | | 1.869 | 1.318 | 2.390 | 0.608 | 1.878 |
| `PP` | 1.931 | 1.823 | 1.880 | 1.496 | 2.485 | 0.720 | 1.885 |
| `PR` | 1.970 | 1.843 | 1.779 | 1.201 | 2.459 | 0.423 | 1.786 |

`PP` coded more in its third pass than its second; `PR` coded less each pass. At the equals:

| tower | right | met (of 1,572) | never met (of 876) | `+` | `−` | `×` | `÷` |
|---|---|---|---|---|---|---|---|
| `C` | 190 | 176 | 14 | 14 | 21 | 114 | 29 |
| `PP` | 109 | 104 | 5 | 14 | 11 | 63 | 16 |
| `PR` | 277 | 259 | 18 | 26 | 26 | 158 | 52 |
| 8-gram | | | 34 | | | | |

Paired: `PR` against `PP` writes 197 met calculations only it writes right against 42, and 16
never-met against 3 (sign test 0.004); against `C`, 140 against 57 met (`z` = 4.3 pooled) and 15
against 11 never-met (0.56). Its right writes sit on what it heard most: 179 of 528 calculations
heard 16 or more times, 39 of 326 heard 8–15, 9 of 239 heard once (`C` 131, 23, 7).

**The acceptance fails, and no ring rises.** 18 of 876 never-met calculations is below the
8-gram's 34 (and §3's 156 of 312). On the 312 never-met sums and differences:

| tower | ring 9 | foil | ring 10 | foil | ring 11 | foil | mod 990 | foil |
|---|---|---|---|---|---|---|---|---|
| `C` | 44 | 39 | 109 | 76 | 30 | 26 | 6 | 1 |
| `PP` | 39 | 32 | 113 | 84 | 23 | 23 | 3 | 1 |
| `PR` | 32 | 35 | 123 | 88 | 27 | 30 | 4 | 4 |

Ring 10 is above its foil (`PR` `z` = 3.0, `PP` 2.5); rings 9 and 11 are not (`PR` −0.4 and −0.4,
`PP` 0.9 and 0.0). At the last digit of a held-out numeral (3,810), the modes against the energies:

| level | tower | 9 | 10 | 11 | 7 | 13 | 100 |
|---|---|---|---|---|---|---|---|
| 0 | `PP` | 550 / 367 | 1,700 / 1,268 | 621 / 394 | 653 / 461 | 574 / 346 | 611 / 49 |
| 0 | `PR` | 788 / 700 | 1,040 / 1,825 | 771 / 816 | 887 / 922 | 798 / 715 | 482 / 1,218 |
| 1 | `PP` | 480 / 432 | 1,461 / 1,519 | 420 / 287 | 662 / 522 | 449 / 399 | 361 / 126 |
| 1 | `PR` | 817 / 636 | 2,490 / 1,677 | 832 / 486 | 930 / 737 | 788 / 478 | 1,135 / 293 |
| | suffix | 1,530 | 3,800 | 1,518 | 1,574 | 1,491 | 3,800 |

Every ring of every tower is below its suffix (`z` < −17 for `PR`). `PR`'s modes name ring 13 as
often as rings 9 and 11 at both levels, and 13 is a ring the tenfold step cannot hold in four
modes (10 has order 6 modulo 13): what the modes name is which numeral, the identities the
training text repeats, not a phase. By §3's decision 2 (ring 9 not above its foil in `PP`), the
keyed turn is not learned by descent.

[agent-inferred] **Why: the rotor as founded is the generator without the modulator.** A unit
steps by `s` times its located bytes, whatever the digits are, so each digit carries mode `j`'s
content to mode `j + 1` and nothing else: a clock of position modulo 4. A character obeys
`χ(10n + d) = χ_10(n) χ(d)`: the shift (`χ_c ↦ χ_10c`, the generator) and the turn by the
arriving digit (`χ_c(d)`, the modulator) are one move, and the founding kept only the first. The
turn was left to the pumped mode's descent (`W_φ`, `b_φ`), and descent did not find it. What `PR`
gained is what position buys, which is what the n-grams have: recitation, the answer numbers' code
(0.423 against `C`'s 0.608) and ring 10. The linear state cannot supply the missing product from
its drive either: it holds `Σ_s M_(>s) B x_s`, a sum of the arrivals' drives, where a character
is a product of their turns.

The locator already holds the modulator. At step 1 the rows' rank drops by one modulo each of 3,
11 and 101, so each has a one-dimensional kernel: a turn key `θ_m[b]` (mode `m` of the ring, digit
byte `b`) that closes every loop of the menu modulo `p`, located from the text's own calculations.
The founding kept `s` and dropped the kernel.

**The next loop, fixed before it is built** (agent-inferred with the mathematics thread): the
rotor carries keyed turns, `h' = T P^σ h` with `(T P^σ h)_(s_k + j) = e^(2πi r/q_k) h_(s_k + ((j + σ)
mod w_k))`, one monomial move (`Rotor`). At each torsion prime of the located step whose kernel is
one line, the line is the turn modulo `p` at the gauge `c = 1` (one character a prime suffices, its
orbit kept whole), lifted to `p^e` while the rows close with it (to 9 at 3; nothing lifts at 11 or
101), and the ring's width is the turn's period in the mode, the order of 10: ring 9 one mode, ring
11 two, ring 101 four. Seven of the 64 modes move and the rest hold still until a loop needs another
ring (7, 13 and 37 arrive with a period of 6). Each stepping unit's turn on a ring mode is a residue
composed over its bytes as the rows compose them, held as an integer and read through its resident
face `e^(2πi r/q)` (`found-unit-rotor-tower … PERIOD LAW`). The equation at the consumer is a test:
read from rest, the residue on mode `j` of a ring after the numeral `n` is `10^j·n` modulo the
ring's modulus, through units of one digit and of several with unlocated bytes between them
(`the_numeral_read_is_its_characters`), and the located kernels are the tenfold characters
(`the_turns_are_the_tenfold_characters`). There is no restart: the modulated strand over the
generator-only strand is `χ(n)` only where the step is monomial on the orbit, and the level's own
move after the rotor damps and reflects (`λ`, `β`), so whether the character survives that move is
what the run measures. The run is `PRT` (law `modulated`) beside `PRS` (law `free`: the same rings
stepping without a turn), so the paired line isolates the turn, with this loop's acceptance and
reads, beside `PR`, `PP` and `C`. If the rings rise and the acceptance fails, the drive within a
numeral and the capture at the operator are the next loop's subject.

## 6. The recorded failures this loop could repeat

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
