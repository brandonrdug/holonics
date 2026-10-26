# The generator and the modulator are one move and the place decides which, so a ring coprime to ten needs a rotor

October 26. Refs #404, #405, #410. **Grade.** Each claim carries one of these grades:
- [owned]: an existing owner states it.
- [proved-standard]: a classical result, with its source.
- [proved-derived]: proved here.
- [checked]: verified by this record's receipts, in integers and fractions only (1,000,350 and 1,749,434 checks).
- [agent-inferred]: a choice or join made here.
- [interpretation]: a reading across subjects.

The exact receipts are `generator_modulator.py` (parts A to G) and `rotor_and_staircase.py`
(parts H to N, for §11 and §12) in
[`…_receipts/`](2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR_receipts/RUN.md).

**Computational object.** The helical pair interaction, read here as a mode's move under an
arriving symbol: a move about its pivot, and modes coupled in a ring. Of the winding guide's six
objects it touches:
- the helix: the move's carry and winding;
- the pair: the pair contact as ring modulation;
- faces and placement: which place reads the move;
- cell holonomy: the rotor's ring.

The tube and the tower thread stay as the tower has them.

## 1. The lens, and the question it asks

Brandon, October 26, in the mathematics thread (paraphrased; his words stay outside the repository).
He asked whether design is only removing contamination, or whether the proper mechanism has been
derived. He is concerned that we do not see how recursive fluid dynamics run along parametric,
unicursal, fractal-like generators that cross: knots and strings, gauge theory, music, RH. He asked
that these ideas be carried forward:
- no privileged perspective;
- mutual code lengths repaired like invariants, as in DNA's helical and toroidal geometry and in
  proteins (modulators, the entropy lens, the fractal generator);
- primes and coprimality;
- fluid dynamics and simulation, for approaching the limits of analogy about interiors (the
  overture, the under-side of time, relativity).

He offered an intuition he had not weighted before: "generator" and "modulator" are likely
fundamentally the same thing.

Minutes later he gave the image for mutual modulation. It is a flock of computational organisms,
which he often calls "ant integration": many local interactions integrating into global fields of
communities and societies. That is what one mind is, and what every organism is (his siphonophore).
It is how reward, scoring and reinforcement are beaten in ontology. A parent who privileges itself is
outgrown by its spawn, and learning about the spawn as it diverges is gradient descent in the
abstract: physical evolution in information theory, which he has called localized P = NP and
growing.

[agent-inferred] **The answer to his first question.** On October 26 design removed the store
machinery: the bank, the reset clock, the passage tree and the letters copy
([the store audit](2026-10-26_THE_BINDING_BANK_IS_A_STRAND_CLOCKED_BY_ITS_ANTECEDENT_AND_A_RELEASE_IS_TRACED_BY_ITS_ADDRESS.md)).
It then ran cause tests on the plain tower. The replacement was not derived. This record derives the
part that the measured failure points to and that the intuition settles.

## 2. One move, one pivot

[owned] A move `x ↦ λx + b` with `λ ≠ 1` is the modulation `x ↦ λ(x − a) + a` about its pivot
`a = b/(1 − λ)`. Only `λ = 1`, the carry, has its pivot at infinity (`motion.affine-move-pivot`,
`motion.complex-move-pivot`). The multiplier is the move's invariant: a cross ratio of its pivots,
the body and its image (`motion.mobius-multiplier-cross-ratio`). Where the pivot sits is a choice of
frame. This is the generator–modulator identity in its smallest form: a push is a modulation about a
point the push itself places.

[checked] Reading a numeral is a word of such moves.
- `x ↦ 10x + d` is the dilation by ten about `−d/9`.
- In the ten-adic integers, `−d/9` is the repdigit `…ddd`: modulo `10^k` it is `d` written `k`
  times, for `k = 1, …, 12` (so `−1 = …999`).
- Every numeral below `10^5` is the word of these dilations about its digits' pivots.

[proved-derived] **The tower's mode is the same move.** `h_t = λ_t h_(t−1) + γ_t B x_t` turns and
boosts by `λ_t` about the symbol's pivot `a_t = γ_t B x_t/(1 − λ_t)`. With real `λ` in `(0, 1)` it is
the convex share `h_t = λh_(t−1) + (1 − λ)a_t`, the reading-mass law (`spectro.reading-mass`). The
state is pulled toward the symbol's pivot by the symbol's share.

So the state after a passage is the point a chaos game reaches. Its address is where it sits, and
the recent word is that address, read from the most recent symbol outward. [checked] One contracting
coordinate, `x ↦ (x + d)/10`, holds every digit of a numeral's suffix: the `j`-th digit from the end
is the `j`-th place of `x`, for every numeral below `10^5`.

Nothing is stored or indexed. Two contexts sit near each other when their recent words agree, or
when they substitute symbols whose pivots sit near each other.

[interpretation] Each symbol switches on a vortex sink at its pivot, and the state is a tracer in
that flow: Aref's blinking vortex, the founding model of chaotic advection (Aref, *J. Fluid Mech.*
143, 1984).

This is the address by geometry that the audit asked for, and the plain tower already has it.

## 3. The place decides the kind

[checked; the product formula is owned, `trace.place-ledger`] Read the one move `x ↦ 10x + d` at
each place of the rationals:

| Place | `\|10\|` there | The move is |
|---|---|---|
| real | 10 | a boost: the digits grow outward |
| 2 and 5 | 1/2 and 1/5 | a contraction toward the pivot `…ddd`: the units-first geometry, where a numeral's address is its last digits |
| 3 | 1, with `10 ≡ 1 (mod 9)` | a shear, free fall: `x ↦ x + d`, the digit sum |
| 11 | 1, with `10 ≡ −1` | a half-turn `x ↦ d − x`: the alternating sum |
| any other `p` | 1 | a turn of order `ord_p(10)`, which is the period of `1/p` |

For example, `ord_p(10)` is 6 at 7, 6 at 13, 3 at 37, 5 at 41 and 4 at 101; the receipt checks it
equals the period of `1/p` for every prime below 110. The product of the three nontrivial readings
is `10 · ½ · ⅕ = 1`, and the product formula holds for every integer from 2 to 2000.

[proved-derived] So whether the move generates (a carry, a translation, free fall) or modulates (a
turn, half-turn or contraction about a pivot) is not a property of the move. It is a property of the
place it is read at. The same digit is:
- a boost to the real receiver;
- a contraction to the 2-adic and 5-adic receivers;
- a carry to ring 9;
- a reflection to ring 11;
- a rotor step to ring 7.

No place is privileged: the product formula multiplies the readings to one.

This is Brandon's intuition, held exactly: the generator and the modulator are one move, and which
one it is belongs to the receiver. It extends the finding that whether a rule is one crossing
depends on the receiver's chart
([pocket of reducibility](2026-10-23_A_POCKET_OF_REDUCIBILITY_IS_A_FACE_THAT_COMMUTES_WITH_THE_STEP_AND_THE_RECEIVERS_CHART_DECIDES_WHICH.md),
§2) from charts to places.

## 4. One stroke or a link: coprimality makes a modulator a generator

[checked] Long division of `1/p` walks the remainders `r ↦ 10r (mod p)`. The walk is one unicursal
stroke through every nonzero remainder exactly when 10 generates `(ℤ/p)^×`. Otherwise it splits into
`(p − 1)/ord_p(10)` strokes.

Over the primes below `10^5`, with 2 and 5 left out:

| Strokes | Primes |
|---|---|
| 1 | 3,617 of 9,590 (share 0.377) |
| 2 | 2,684 |
| 3 | 635 |
| 4 | 711 |

The one-stroke share is 0.361 below 1000 and 0.381 below `10^4`. Artin's product over the primes
below 1000 is 0.374, as a reading.

[proved-standard] Hooley (*J. reine angew. Math.* 225, 1967) proved that this share tends to Artin's
constant, assuming the Riemann hypothesis for the Dedekind zeta functions of the Kummer fields.

A step on `ℤ/n` generates exactly when it is coprime to `n`. The generators form one orbit of the
multiplications, so which generator is "the" generator is a choice of frame.

[checked] On the torus, the `(p, q)` winding is `gcd(p, q)` strokes, checked for `p, q ≤ 40`:
coprime windings are one stroke (a knot), and the rest are a link. Equivalently, `(1, 1)` generates
`ℤ/p × ℤ/q` exactly when `gcd(p, q) = 1` (the Chinese remainder theorem).

So the unicursal stroke Brandon names is coprimality. How often the base is a generator, rather than
a modulator of several strokes, is a question of RH.

## 5. Fourier exchanges the generator and the modulator

[checked; proved-standard] On `ℤ/n`, the shift `X` (the generator of translation) and the clock `Z`
(multiplication by a character, the modulator) satisfy, for `n = 2, …, 40`:
- `F X = Z F` and `F Z = X⁻¹ F`: the Fourier chart exchanges them;
- `Z X = ω X Z`: they do not commute, and the defect is a pure phase.

This is the Heisenberg pair. On a torus with flux it is the pair of magnetic translations, whose
spectrum is the gap-labelled Cantor set (`gap.label-chern-edge`). [interpretation] In music it is
delay and transposition, exchanged by the same transform.

[checked] On a ring of four modes the Fourier chart is exact in Gaussian integers over 4, and
`F⁻¹ diag(i^(ks)) F` is the cyclic shift by `s`. Stepping a ring is a turn in its dual chart.

[interpretation] **The flock.** Take a ring of local organisms, each passing its state to its
neighbour. In the ring's Fourier chart, that passing is each collective mode turning by its own
phase: local passing is global modulation, the same exchange. This is how many local interactions
integrate into global fields with no member leading. The collective modes are the field, and nothing
outside the ring scores it. Brandon's flock is this exchange at every scale.

[checked; proved-standard, Gauss] The `±1` sheet is the quadratic character: the half-turn lock of
the parametron and of the referent record's he/she sheet. Read against the additive turn, its Gauss
sum satisfies `τ² = (−1/q) q` for every odd prime `q` below 60, so `|τ| = q^(1/2)`. The sheet and the
turn see each other spread at exactly the square root. That is the half that RH puts on the critical
line and Hasse–Weil puts on a curve's Frobenius (`bsd.split-chart-rotation` reads `g² = p` in one
chart).

## 6. The torus: two twists compose into every kind

[checked; proved-standard] Take the torus's two Dehn twists, `T = [[1,1],[0,1]]` and
`L = [[1,0],[−1,1]]`: the braid generators `σ₁, σ₂` through `SL(2,ℤ)`. Each is a pure carry, a
shear. They satisfy the braid relation `TLT = LTL`, and their words give every kind of move:
- `TL⁻¹ = [[2,1],[1,1]]` is a boost (trace 3): the cat map, Arnold's mixing of the torus. Its fixed
  points on the torus number `|det(Aᵏ − 1)| = L_(2k) − 2`, the Lucas numbers. This is checked for
  `k = 1, …, 20`, and point by point for `k ≤ 5`: 1, 5, 16, 45, 121.
- `TL` is a turn of order six.
- `TLT = [[0,1],[−1,0]]` is the quarter turn, which in the Weil representation is the Fourier chart
  of §5.

Conversely, the commutator of the two boosts `[[2,1],[1,1]]` and `[[1,1],[1,2]]` is
`[[−7,6],[−6,5]]`: trace −2, a shear. Two generators compose into a modulator, and two modulators
compose into a generator.

[proved-standard; interpretation] **Fluids.** The same algebra stirs fluids. Rods moved in the braid
`σ₁σ₂⁻¹` mix a fluid with topological entropy `log φ²`, the cat map's (Boyland, Aref and Stremler,
*J. Fluid Mech.* 403, 2000: the taffy puller).

**DNA.** It also keeps invariants the way DNA does. For a closed ribbon, `Lk = Tw + Wr` (Călugăreanu,
White, Fuller):
- a Dehn twist adds one unit of twist;
- twist (the modulation of the frame along the strand) and writhe (the generation of the strand's
  path) trade freely;
- only a strand passage, a crossing change, alters the sum, by whole units (topoisomerases do it one
  or two at a time).

**Vortices.** In reconnecting vortex knots in water, helicity survives the reconnection because
linking and writhe convert into twist (Scheeler, Kleckner, Proment, Kindlmann and Irvine,
*PNAS* 111, 2014).

That is "repairing mutual code lengths like invariants": the invariant is the sum, local repair
trades its parts, and only a crossing (a contact) changes it, in quanta.

## 7. What one plane of the tower can carry

**(a) Rings coprime to ten.** [proved-derived; checked where finite] Let `m ≥ 3` be coprime to 10.
The digit maps `x ↦ 10x + d` on `ℤ/m` generate the whole affine group `ℤ/m ⋊ ⟨10⟩`, every
translation included. [checked] It has `m · ord_m(10)` moves for every such `m < 120`.

Suppose one real plane carries the numeral's residue modulo `m` as `m` distinct points, and each
digit acts by an affine map of the plane.
- If the points are collinear, a cyclic group of order `m ≥ 3` would act faithfully by affine maps of
  a line, which is impossible.
- If they span the plane, each map permutes a spanning set, so it is invertible, and the maps form a
  finite group. That group fixes the points' barycentre and acts linearly about it.
- The translation by 1 is then a turn `R` of order `m`, with eigenvalues primitive `m`-th roots of
  unity.
- The digit move conjugates it into the translation by 10, which is `R^10`. Conjugation keeps
  eigenvalues, so `10 ≡ ±1 (mod m)`.

So one plane carries exactly the coprime rings 3, 9 and 11, in any chart (the receipt lists them
for every `m ≤ 300`). This is the
converse of `radix.cheap-faces`, which owns the "if".

**(b) A bank of uncoupled planes.** [proved-derived] Consider a diagonal level, each plane moving by
its own symbol-keyed maps, which permute that plane's reachable states. On the residues it realizes a
section of a product of dihedral groups (the finite subgroups of `O(2)`). Every such section has an
abelian normal subgroup with quotient an elementary abelian 2-group.

`ℤ/p ⋊ ⟨10⟩` with `ord_p(10) ≥ 3` has none: its only nontrivial abelian normal subgroup is `ℤ/p`,
whose quotient is cyclic of order `ord_p(10)`. So no number of uncoupled planes holds ring 7, 13, 37,
41 or 101 as faces that move with the digits. The cheap rings are all such a bank holds. This reads
on rings the counting law (`motion.lag-residue-factorization`) and the order law
(`motion.plane-reflections-commute`).

**(c) The rotor.** [proved-derived; checked] Any linear realization of ring `p` with distinct
residues needs real dimension at least `|⟨10, −1⟩|` in `(ℤ/p)^×`. The translations must show a
nontrivial character; the digit move carries it around the orbit of `×10`; and reality adds its
conjugate. That is:
- `ord_p(10)/2` planes when the order is even (then `−1` is a power of 10);
- `ord_p(10)` planes when it is odd.

The rotor attains it. The mode for character `a` takes the old mode for `10a` and turns by `a·d`.
[checked] Rings 3, 7, 9, 11, 13, 17, 37, 41, 73, 101 and 1001 read every numeral below 3000 exactly,
with plane counts 1, 3, 1, 1, 3, 8, 3, 5, 4, 2 and 3. For every prime below 200 the count is the
order or half of it.

The stepping (`a ↦ 10a`, a permutation of the modes) is the generator, and the turn (`a·d`) is the
modulator. By §5 they are one law in two charts. This is the Enigma reading of CLAUDE.md made exact:
a rotor's stepping is winding with carry.

**(d) The units-first part.** [proved-derived; checked]
- **Phase chart.** Here a residue is a turn and a sum is one crossing, a product of turns. One plane
  cannot hold the last two digits: the digit map would have to collapse every chord
  `ω^(n+10) − ω^n`, and those span the plane. A chain of `k` coupled planes holds the last `k`
  digits: the mode for 1 takes the old mode for 10, which takes the old mode for 100, down to the
  constant (checked for 4, 8, 20, 40, 100 and 1000). It is a cascade: information moves one decade
  finer per digit and is released as it reaches the constant.
- **Coordinate chart.** One contracting coordinate holds the whole suffix (§2). One real plane holds
  units and tens by the nilpotent move `(s, t) ↦ (d, s)` (checked for every numeral below `10^5`).
  There a sum is a step function of the coordinates, with its carries as kinks, not one crossing.

**(e) Across levels.** [agent-inferred] The tower's levels feed the next through contacts, so two
diagonal levels can compose a cascade (Krohn–Rhodes). The first level counts the digits modulo
`ord_p(10)`, and the second accumulates digits with weights read from the first through a pair
contact. That route needs the final read to raise a turn to a power. The rotor instead puts the ring
inside one level's recurrence.

[measured, design] **What design measured fits this.**
- The arithmetic-only tower writes a sum's units right where it crosses the operands' units (191 of
  240,
  [near-miss record](2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md)),
  and the units are a one-plane ring.
- The plain tower `C` writes 14 of 470 sums right at the equals
  ([digit cause test](2026-10-26_THE_DIGIT_PIECES_ARE_NOT_THE_CAUSE_THE_PLAIN_TOWER_WRITES_BACK_176_OF_1572_HEARD_CALCULATIONS_SO_THE_EQUALS_IS_READ_WHERE_IT_WAS_HEARD.md)).
  A sum's tens need a coupled chain in the chart where a sum is one crossing.

## 8. What it forces in the learner, and the build

[agent-inferred] Three consequences:
1. **Addressing is geometric and stays so.** The tower's state is the chaos-game point of its moves
   about their pivots (§2). No store, slot, key, clock or index of contexts enters, and none is
   needed for the address of the present context.
2. **Place value needs coupled modes.** A diagonal bank holds counts, the cheap rings and a suffix
   coordinate. It cannot hold a ring coprime to ten past the cheap ones, nor the last two digits
   where a sum is one crossing. The same holds outside text: a motor chart is serial screw words,
   which do not commute, and a diagonal bank sees only their counts. The minimal coupling is the
   rotor.
3. **Generator and modulator are one law in two charts,** so the coupling is built as one: a ring's
   stepping is a turn in its Fourier chart.

**The build, offered to design as its owner** (sent October 26): rotor rings in the plain tower.
- A level's modes are grouped into rings of four.
- At each cell, each ring is stepped by a located turn `s_t` in its four-point Fourier chart. `s_t`
  is keyed by the arriving face as the turned mode keys its turn (`hnn.tower-turned-mode`), and it
  opens at zero.
- Then the existing gated, turned or pumped move acts on each mode.

For one ring, with `F_jk = i^(jk)`:

```text
h'  = F⁻¹ diag(i^(k s_t)) F h_(t−1)     the stepping: adds and i-swaps, exact over 4
h_t = λ_t ⊙ h' + γ_t ⊙ B x_t            the existing move
```

Its properties:
- At `s_t = 0` it is the plain tower, so the rotor tower opens on `C`.
- The stepping is unitary on the ring, so passivity holds per ring, with the same bound in the
  ring's norm.
- An integer `s` is an exact rotor step. A fractional `s` is a band-limited fractional step, which
  keeps the stepping's covector continuous.
- Rings of four host every orbit of length one, two and four exactly. Whether rings of other sizes
  are needed is read from the build, never chosen for base ten.

**The consumer equation** is the near-miss record's: on every ring the learner holds,
`x_q(release) = T_q(x_q(a), x_q(b))`. Here `x_q` is held by a rotor instead of rebuilt by contacts.

[checked] **Correction, the same day (§11).** Read on past the operator, one rotor register holds
the concatenation `10^len(b)·a + b`, which is the sum only on ring 9. So `x_q(a)` must be captured
at the operator and the ring restarted, and `T_q` is read by the pair contact's bilinear block. The
rotor therefore stands on the pair-contact tower, not on `C`, and its step is an integer key located
by closure, with the Fourier form below kept as a foil. §11 gives the law at the consumer.

**The acceptance, fixed before any build runs.** The rotor tower `R` is trained with `C`'s recipe:
- width 64, 64 modes, 256 contacts, two levels, eight streams;
- sections of 128, three passes, rate `2^(−7)`;
- the same founding key stream.

It is read by `read-unit-tower-written` and the written rules exactly as `C` was. `R` passes when it
writes more never-met calculations right at the equals than:
- the 8-gram's 34 of 876;
- `C`'s 14, by design's paired line: the `R`-only count minus the `C`-only count exceeds 1.96 times
  the square root of their sum.

Reported beside it:
- the counts by operation, sums first;
- met calculations, read as recitation and never as the acceptance (the 6-gram and 8-gram lead
  there because they are stores).

**A cheap reading first, on `C`'s state.** At the end of each numeral of the held-out text, decode
`n mod 9`, `n mod 10` and `n mod 11`, against `n mod 7`, `n mod 13` and `n mod 100`, from `C`'s
level-1 face by a linear read in the phase chart. §7 predicts that the first three read and the last
three do not.

## 9. What is not yet derived

[open] **Binding at a distance**, for instance John's quantity carried to his question. In the rotor
picture, what was heard sits wherever the ring has stepped it, and its address is the winding since
(design's own phrasing of its decision 2). How a question unwinds to it without a store is the next
derivation, and it waits on design's train-slice read:
- if the failure is holding, the subject is what a pass deposits;
- if it is addressing, the winding address is derived on the rotor rings.

## 10. The recorded failures this could repeat

- **An index of contexts or a copier** (lessons failure 2, eight times). The rotor indexes no
  positions and copies nothing. Its stepping is a turn located per symbol, never a counter of cells
  or a pointer into the passage. The reset clock was such a pointer; this is not.
- **Catered machinery.** The rings are not chosen for base ten (four is the exact Fourier chart), and
  no step is set to `×10`. The theorem names which rings a learner could hold, and the learner
  locates its own steps.
- **A design thought in arrays.** The build is stated as rotors, turns and their Fourier exchange.
- **Seen material graded as unseen.** The acceptance reads never-met calculations only, and met
  calculations are reported as recitation.
- **Bits read as progress.** Code lengths are reported beside the acceptance, never as it.

## 11. Design's questions, and the rotor at the tower

Design asked four things on October 26:
- a check of its own derivation;
- how a class holding several digits acts on ring 11;
- whether its predictions for the pumped towers `P` and `PP` hold;
- the rotor's law as equations at `hnn::tower`.

The answers below are checked by part H of `rotor_and_staircase.py`.

[checked] **One register holds the concatenation.** Read on past an operator, one register holds
`10^len(b)·a + b`. That is `a + b` mod 9, `(−1)^len(b)·a + b` mod 11 and `b` mod 10. Ring 9 is the
one ring on which the concatenation is the sum.

So a sum on any other ring needs three pieces:
1. **Capture.** The operator opens the gate of a mode that captures the first operand's ring.
2. **Restart.** The ring restarts. Its founded `|λ|` is small, so the digits close its gate and it
   holds; the operator opens the gate, so the ring releases at `|λ|²` and takes the push.
3. **The bilinear read.** At the equals the pair contact's bilinear block reads both products:
   `2Re(c₁h₁)·Re(c₂h₂) = Re(c₁c₂·h₁h₂) + Re(c₁c̄₂·h₁h̄₂)` (part N). Here `h₁h₂` carries the phase of
   `a + b` and `h₁h̄₂` the phase of `a − b`, on every ring at once.

[owned] `contact.face-table-blocks` calls a sum's ring face additive. It is, in the ring's own
chart. Realized as two co-present phases in a plane, it is their product, which is the bilinear
block. The chart decides, as in §3.

Design's predictions follow from this:
- `C` stays at its foil;
- `P` rises on ring 9, about half on ring 11, and stays at its foil on ring 10;
- `PP` rises on all three only if descent finds the capture.

So under `PP`, a ring left at its foil names the capture before it names the hand or the seam.

[checked] **A class holding several digits, on ring 11.** A class of `k` digits with value `D` acts
as `x ↦ (−1)^k x + D`:
- for even `k`, a turn;
- for odd `k`, the mirror about `6D`.

That gives 22 actions, the dihedral group of 11. The closure's key on ring 11 splits into two parts:
- a sign character on the classes, located first as a parity system over GF(2) around the loops;
- translations, a linear system over `ℤ/11` twisted by the signs.

Both stages are linear.

[proved-derived] **The rotor's law at the consumer.**

```text
(P^σ h)_(4k+j) = h_(4k + ((j + σ) mod 4))          σ ∈ ℤ/4, keyed by the arriving class
h'_(t−1)       = P^(σ_t) h_(t−1)
h_t            = λ_t ⊙ h'_(t−1) + γ_t ⊙ B x_t       the turned move (the pumped move likewise on h')
G_h(t)         = (Cᵀδr)⁻ + P^(−σ_(t+1)) (conj(λ_(t+1)) ⊙ G_h(t+1))
```

- **Step, then the move.** The character law is `χ_a(10n + d) = ω^(ad)·χ_(10a)(n)`: the mode for
  `a` takes the old mode for `10a`, then turns by `a·d`.
- **What the keys hold.** Let mode `j` hold the character `10^j`. Then `σ = 1` for every digit, and
  mode `j` turns by `2·10^j·d/p` half turns. The turned mode's keyed turn already represents that
  turn.
- **Covectors.** Every covector that reads `h_(t−1)` reads `h'_(t−1)` instead. `σ` has no covector.
- **The opening.** At `σ = 0` the rotor tower opens on its turned twin.
- [agent-inferred] **σ is located by closure.** It is an integer key per class and per ring, opens
  at 0, and is located by closure, not by descent, for two reasons:
  - a step from 0 to 1 is a permutation, and any relaxed path between them passes through mixtures
    of modes;
  - `σ` is a winding, which changes only at a crossing, in whole units: helicity changes only at a
    reconnection (Moffatt), §6.

  The Fourier form of §8 stays as a foil.
- [checked] **Passivity.** A permutation hands each mode exactly one mode's state, so the tower's
  bound `|h| ≤ √((1 + ρ_max)/(1 − ρ_max))·max|Bx|` holds unchanged, because
  `ρK + √(1 − ρ²) ≤ K(ρ_max)` for every `ρ ≤ ρ_max`.
- [agent-inferred; corrected on review, the arithmetic checked in part K of the
  [Galois-gap receipt](2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE_receipts/RUN.md)]
  **The relaxed Fourier step.** It mixes modes, so a mode's input no longer meets its own `λ`, and
  only the ring's ℓ² norm is kept. The triangle inequality then certifies
  `‖h‖₂ ≤ ‖Bx‖₂/(1 − ρ_max) ≤ 2·2^12·max|Bx| = 2^13·max|Bx|` on a ring of four. That is about `2^6.5`
  times the per-mode bound `√(2^13 − 1)·max|Bx|` at `ρ_max = 1 − 2^−12`. It is a certified bound,
  not a shown need: no sharper bound for the Fourier step is derived.
- [checked] **What a ring holds.** A ring of `K` modes stepped once a digit holds `n` mod every
  divisor of `10^K − 1`:
  - four modes hold `9999 = 3²·11·101`;
  - six modes hold `999999 = 3³·7·11·13·37`.

[proved-standard; agent-inferred] **The fluid side.**
- **Kelvin.** Kelvin's carried circulation is the held mode: a closed gate, not `ρ = 1`.
- **Reconnection.** Through a reconnection, link and writhe convert into twist and the sum is kept
  (Scheeler et al.). So when a key is relocated, the reading is the joint two-sided code length
  `L(A) + L(B|A)`. One side's bits can move while the joint is kept.

[checked; proved-standard] **Design's derivation** holds, with three corrections:
- **The helix's group is infinite.** The helical code's screw has infinite order, so its dihedral
  group is the infinite one, `⟨a, b | a² = b² = 1⟩`. `(ab)ⁿ = 1` holds only on a ring of `n`.
- **A reflection is not a conjugated turn.** A reflection is never conjugate to a turn, because their
  determinants differ. Reflections are conjugate to each other by turns:
  `R_ψ = Rot(ψ/2)·R_0·Rot(−ψ/2)` for `R_ψ z = e^(iψ) z̄`.
- **Floquet's frame doubles past the bifurcation.** The real Floquet frame needs the doubled period
  once the monodromy has a negative eigenvalue, which is the pump's half-turn sheet.

Its reading of `Lk = Tw + Wr` as the symmetric joint code length is an interpretation that holds.
The shared quantity is the mutual information `I(A:B) = I(B:A)`. It is exact for entropies, and for
description lengths it holds to `O(log)`.

## 12. Why only these rings: the base's neighbours, the grain staircase and the Galois colours

Brandon, October 26 (paraphrased). He asked why only 2, 3, 5, 9, 10 and 11 are one-plane turns.
He read a Fermat-like and cryptanalytic flavour in the list, and noticed that:
- 2 cycles the even endings, and 5 the endings 0 and 5;
- 9 is `3²` while `4 = 2²` is missing;
- the list feels like a staircase.

He joined this to chart transitions, foveation, stereophony and colour: gauging information takes
two or more receptors, whose comparison has spectral gaps to work with.

[checked, part I] **The base's three neighbours.** One plane can turn, mirror or flatten. A digit
multiplies a ring's angle by the base, so ring `m` is one plane in one of three ways:
- a turn exactly when `b ≡ 1 (mod m)`;
- a mirror exactly when `b ≡ −1`;
- a flattening exactly when `b ≡ 0`.

These are the divisors of `b − 1`, `b + 1` and `b`, checked for every base from 2 to 60:
- base 10 gives 2, 3, 5, 9, 10 and 11;
- base 9 gives 2, 3, 4, 5, 8, 9 and 10, and there 2 is a turn.

This is `radix.cheap-face-table` read as motion.

[checked, part J] **The staircase is the grain.** Read `k` digits at once and the base is `10^k`, so
the one-plane rings are the divisors of `10^k − 1`, `10^k` and `10^k + 1`:
- 4, 25 and 101 arrive at two digits;
- 7, 13 and 37 arrive at three (`999 = 3³·37`, `1001 = 7·11·13`).

Three cases cover every ring:
- a ring coprime to ten arrives at `ord_m(10)/2` or `ord_m(10)` digits (Euler);
- a ring made of 2s and 5s arrives at `max(v₂, v₅)` digits;
- a ring that mixes both kinds never arrives. Rings 6, 12, 14, 15, 18, 22, … always need two
  planes, one for each kind.

Prime powers climb by lifting the exponent. Since `v₃(10^k − 1) = 2 + v₃(k)`, rings 3, 9, 27 and 81
arrive at grains 1, 1, 3 and 9. Rings 11, 121 and 1331 arrive at 1, 11 and 121.

[interpretation] Depth and width trade: a coarse fovea sees as one turn what a fine one holds in
coupled planes. The tower's levels are those depths (§7(e)).

[checked, part L] **The 2 and the 5 nest.** In base 10 the even endings 0, 2, 4, 6, 8 add as ring 5
and read every residue mod 5 once. The endings 0 and 5 are ring 2. In any base `b = rs` with `r` and
`s` coprime, the endings divisible by `r` are a copy of ring `s`, so each factor's cycle runs on the
other's zeros.

[proved-standard; checked, part K] **The colours are Galois conjugates.** On the `p`-th roots of
unity, multiplying the angle by 10 is the Galois automorphism `σ₁₀ = σ₂σ₅`, the product of the
Frobenius elements at the base's primes. One plane is one complex embedding and its mirror; the
mirror is complex conjugation, the Frobenius at the real place. So a ring is one plane only when
`σ₁₀` is the identity or the mirror.

Otherwise the orbit carries a root to its conjugates, other "colours" of the same number, and the
rotor needs one plane per conjugate pair:
- rings 7, 13 and 37 need three planes, as the eye has three kinds of cone;
- ring 101 needs two, as there are two ears;
- ring 41 needs five, 73 four, and 17 eight.

Whether the half-way grain `(p − 1)/2` is a turn or a mirror is the Legendre symbol `(10/p)`
(Euler's criterion). Quadratic reciprocity sets it by `p mod 40`: a mirror for
`p ≡ 7, 11, 17, 19, 21, 23, 29, 33`. That `±1` is the quadratic character of §5.

[interpretation] **Two receptors.** The pair contact compares two co-present receptors and reads
their sum and difference at once (part N). In audio these are mid and side; in vision, luminance
and the opponent channels. Coprime receptors meet once per residue pair, modulo their product (the
helical code's law), which is how two rings resolve more than either alone.

[interpretation] **Fermat and cryptanalysis.** Fermat's little theorem is why every coprime ring
arrives at some grain. The digit move is the cyclotomic Frobenius. Fermat's Last Theorem was proved
through Frobenius acting by `2×2` matrices on an elliptic curve's torsion (Wiles); that is the
two-plane case, and `trace.hasse-bound` holds its trace. In cryptanalysis the same order of the base
sets the cost of a discrete logarithm: Pohlig–Hellman splits it along the factors of `p − 1`. The
index chart of §7 is that discrete logarithm.

[interpretation; checked, part M] **Music.** A step on twelve notes makes `gcd(step, 12)` strokes:
- fifths make one stroke, the circle of fifths;
- minor thirds make three diminished sevenths;
- major thirds make four augmented triads.

This is the same split as long division (§4). Twelve fifths overshoot seven octaves by
`3¹²/2¹⁹ = 531441/524288`, the Pythagorean comma. A power of 3 never equals a power of 2, so the helix
of fifths never closes, and its carry is the comma.

## 13. Owed

To #410:
- (a) the one-plane theorem for rings coprime to the base, the converse of `cheap_faces`;
- (b) the dihedral-section bound for uncoupled banks;
- (c) the rotor's plane count as a lower bound, with the rotor attaining it;
- (d) `F X = Z F` and `Z X = ω X Z` on `ZMod n`;
- (e) the braid words in `SL(2,ℤ)` and the cat map's Lucas fixed points;
- (f) the base-action lemma: on `ℤ/m`, `x ↦ bx + d` is a translation if `b ≡ 1`, the mirror
  `x ↦ d − x` if `b ≡ −1`, the constant `d` if `b ≡ 0`, and otherwise permutes the characters
  `a ↦ ba`, turning each by `a·d`. Its corollary is the grain staircase: ring `m` is one plane at
  grain `k` iff `m` divides `b^k − 1`, `b^k` or `b^k + 1`, and a ring mixing the base's primes with
  others never is;
- (g) the residue address: by CRT, `n mod lcm(m_i)` from the rings' faces (`990` from 9, 10 and 11);
- (h) the dihedral group generated by two reflections, finite (`(ab)ⁿ = 1`) and infinite;
- (i) the rotor's step: a ring of `K` modes stepped once a digit holds `n` mod every divisor of
  `10^K − 1`, and a permutation keeps the passivity bound.

(f), (g) and (h) were formal-checked the same day in
[`Mathematics/BaseAction`](../../lean/HolonicsResearch/Mathematics/BaseAction.lean):
- (f) is `digitMove_translation`, `digitMove_mirror`, `digitMove_flattening`,
  `digitMove_on_characters`, `unit_permutes_characters`, `word_action`, `one_plane_iff` and
  `mixed_ring_never_one_plane`;
- (g) is `residue_address`, `address_nine_ten_eleven` and `address990`;
- (h) is `two_reflections` and `two_reflections_generate` inside `DihedralGroup n`, and the rest of
  the box is in [`Geometry/TwoReflections`](../../lean/HolonicsResearch/Geometry/TwoReflections.lean):
  in any group, two distinct involutions other than `1` generate a copy of
  `DihedralGroup (orderOf (ab))` (`dihedralHom`, `two_involutions_dihedral`), with `2·orderOf(ab)`
  elements (`card_two_involutions`, `0` by `Nat.card`'s convention when `ab` has infinite order); a
  plane mirror is never conjugate to a turn, since their determinants are `−1` and `1`
  (`mirror_not_conj_turn`); and the mirrors are conjugate to each other by turns
  (`mirror_conj_by_turn`, `mirror_conj_by_turn_complex`: `v·conj(conj v·z) = v²·conj z`).

Atlas rows:
- `radix.digit-move-place-kind`;
- `radix.long-division-strokes`;
- `radix.one-plane-coprime-rings`;
- `radix.uncoupled-bank-dihedral`;
- `radix.rotor-planes`;
- `motion.fourier-exchanges-shift-and-clock`;
- `motion.torus-twists-every-kind`;
- `motion.generator-is-modulator`;
- `radix.concatenation-not-sum`, `radix.base-neighbour-rings`, `radix.grain-staircase`,
  `radix.rotor-galois-orbit` and `contact.bilinear-sum-difference` (§11 and §12).
