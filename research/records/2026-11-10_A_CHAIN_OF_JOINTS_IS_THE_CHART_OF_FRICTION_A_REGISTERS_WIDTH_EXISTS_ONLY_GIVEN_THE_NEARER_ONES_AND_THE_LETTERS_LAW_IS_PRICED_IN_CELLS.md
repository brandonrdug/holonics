# A chain of joints is the chart of friction, a register's width exists only given the nearer ones, and the letters' law is priced in cells

[historical] On the evening of November 10 Brandon gave a lens, paraphrased here (his words stay in
the conversation logs):
- what he keeps describing as friction through geometry is kinematics and inverse kinematics, with
  induction and relativity, and a torque moment passed along a chain over something like Markov
  chains and blankets, which turns into Bayesian inference;
- an arm writing: hand, forearm and upper arm modulated from further in, signals arriving at their
  times and places by being pivoted away from the others that superpose with them (a filter, which
  is computation), and the fingers calibrated to telescope down to the scale of what receives the
  writing while they feed back;
- fingers are jointed emitters, the reverse of a cone or a rod; what he means by coarse graining
  is causing cycles of motion far away from the system that originates them; digits imply the
  widths of registers, as a channel's diameter sets its voltage and current;
- the voice and the ear repeat the picture; the signals wind about one another like an orbit;
- an impulse has a mass that a pressure gauge could read in information theory;
- permittivity and permeability tie to the overture (imaginary time), to thermodynamics and to
  strain for parts such as lenses;
- none of it is about the biological wiring: it is the geometry of diffusion and of induced action.

This record recovers what the repository already holds for each part, adds four joins, gives the
host measurements made that evening with their guesses and scores, and states what follows for the
machine. The chart is in [the atlas](../../docs/atlas/CHARTS.md), row "Kinematics, control, inference".
Refs #73, #406.

Two later lenses of the same evening corrected this record in two places (2.5 and item 4 of
section 4, each marked below). They are charted in
[the next record](2026-11-10_A_HELD_LETTER_IS_A_LEAKY_GRIP_THE_LAW_ACROSS_A_PLACE_IS_THREE_BODY_WIDTHS_ADD_ALONG_A_BRANCH_AND_PLASTICITY_IS_ANISOTROPY.md).

**Truth discipline.** `[proved-standard]` marks a classical result, `[measured]` an exterior float
reading of a ruler on the host with its receipts, `[source-inspected]` a claim read from the code,
`[interpretation; agent-inferred]` a reading that no record or message of Brandon's carries yet.
A count table here is a ruler: it measures the text and is never machinery
([stores and caches](../../CLAUDE.md#stores-and-caches)).

## 1. Recovered: what the repository already held

Most of the lens was already on the objects.

| Part of the lens | Held as | Where |
|---|---|---|
| a chain of joints | the ordered product of finite screw motions, rightmost joint first; every prefix kept | `chain.serial-configuration`, `chain.prefix-accumulation` |
| a joint's lever at the end | Jacobian column `i` is joint `i`'s screw recharted by the motion before it | `chain.jacobian-columns`, `screw.adjoint-rechart` |
| torque and force | a wrench is the coholon of a twist; power is their pairing | `screw.wrench-power` |
| friction of the whole chain | one matrix `J_chainᵀ D J_chain` over all joints, cross-joint terms included | `chain.link-contact-material` |
| opposed digits | a grasp holds when its contact wrenches positively span; the thumb closes it | `chain.force-closure-count` |
| a blanket, and inference across it | eliminating an interior leaves one boundary operator with memory; the eliminated interior's free energy and its conditional covariance | `resolvent.dynamic-schur`, `thermal.eliminated-fibre-free-energy`, `code.free-energy-two-part` |
| mass | a receiver's mass along a reading is the inverse of its leverage, each reading adds one unit, and the receiver moves by the barycentric share, which is the Kalman gain; the count is the rest mass | `spectro.reading-mass`, [October 24](2026-10-24_INFORMATION_SPECTROSCOPY_WEIGHS_A_LOAD_BY_ITS_LINE_THE_CLOCK_HIDES_A_UNIFORM_MASS_AND_A_BASIN_IS_A_BOOST_SEEN_FROM_INSIDE.md) §4, §6 |
| a pressure gauge | a code length on its own clock has an equation of state, `dL = −p dV`, `w = −1` at its floor; confined radiation has inertia | `code.equation-of-state`, `code.clock-cast`, `mass.confined-radiation`, [October 23](2026-10-23_CODE_LENGTH_IS_A_FIELD_ITS_FLOOR_IS_THE_DARK_ENERGY_TERM_ITS_BINDING_SHOWS_ONLY_THROUGH_CONTACTS_AND_THE_PRIMES_HAND_SITS_ON_THE_FLOOR.md) |
| digits as registers | a width is a partition into lanes; the cost of a base's digits | [November 3](2026-11-03_A_STORED_FACE_AND_ITS_NAVIGATOR_ARE_TWO_ENDS_OF_ONE_EXCHANGE_AND_A_WIDTH_IS_A_BRANCH_REGISTER.md), `radix.economy` |
| the order of reading | the chain rule holds in every reading order, and uniform masks already draw a random order's states | `radix.held-face-reading-order`, `code.order-agnostic-masked-bound` |
| feedback from the write | a write is read back through several coupled sections | [November 8](2026-11-08_REAFFERENCE_A_WRITE_IS_READ_BACK_THROUGH_SEVERAL_COUPLED_SECTIONS_AND_A_WORD_IS_AN_ARC_OF_THE_MOTOR_CHART.md) |
| permittivity, permeability | `εμ = 1/c²` and `μ/ε = Z₀²`; a junction reflects by its mismatch | `em.impedance-alpha`, `wave.junction-reflection` |
| imaginary time | real time is unitary, imaginary time a semigroup; they are different evolution kinds of one generator | `quantum.evolution-kinds` |

So the lens names no new object. What it adds is the instruction to read them as one chain, and
the places where that reading was not yet written are the four joins below.

## 2. The joins added

### 2.1 Torque along the chain is the end's wrench pulled back through each joint

[proved-standard] For a serial chain with joint rates `θ̇_i`, the end's twist is
`ẋ = Σ_i J_i θ̇_i` with `J_i = Ad_(g_1⋯g_(i−1)) ξ_i` (`chain.jacobian-columns`). A wrench `W` at the
end does power `⟨W|ẋ⟩ = Σ_i ⟨W|J_i⟩ θ̇_i`, so the effort at joint `i` is `τ_i = ⟨W|J_i⟩`, the
transposed Jacobian of the wrench (atlas `chain.wrench-pullback`). Power is the same number read at
the end or summed over the joints.

[interpretation; agent-inferred] On the objects this is the paired adjoint of the learning law: the
covector of a declared comparison is the wrench at the end, and each level receives it through the
operands that produced the forward carriers, which are its lever. Friction is then one matrix seen
from the end, `JᵀDJ`, and "friction through geometry" is that matrix: what each joint dissipates,
weighed by the lever through which the end feels it. Writing is the forward product. Locating keys
is the inverse problem, solved by loop closure, and it has a fibre of solutions
(`infer.intersection-fibre`): a reference answer is one of them.

### 2.2 Eliminating a joint is a filter's update

[proved-standard] Let `P ≻ 0` be the inertia seen past a joint whose free directions are the
columns of `S`. Eliminating the joint leaves

```text
P⁺ = P − P S (Sᵀ P S)⁻¹ Sᵀ P,        Sᵀ P⁺ = 0,
```

the Schur complement of `SᵀPS`. This is the covariance update of a Kalman filter,
`P⁺ = P − P Hᵀ(H P Hᵀ + R)⁻¹ H P`, at `H = Sᵀ` and `R = 0`. The recursion that solves a chain's
dynamics is a filter run toward the base and a smoother run back to the tip (Rodriguez, 1987;
Featherstone's articulated-body inertia is built from `P⁺` carried to the parent). Atlas
`chain.articulated-elimination-filter`; its rank-one case is `spectro.reading-mass`.

[interpretation] A blanket is a joint's ports: what lies beyond it reaches the rest only through
them, which is the block form that lets the elimination proceed one joint at a time. That the
torque picture turns into Bayesian inference is therefore a theorem about chains and trees. Where
the chain closes on itself the recursion no longer runs one joint at a time: the loop's constraint
has to be carried with it.

### 2.3 A register's content given the nearer registers

[proved-standard] For a stationary source let `H_k` be the entropy of `k` consecutive letters and
`h_k = H_(k+1) − H_k`, the code of a letter given the `k` before it. Then for the letter `d` places
back:

```text
H(X_(−d) | X_(−d+1) … X_(−1)) = h_(d−1),
I(X_0 ; X_(−d) | X_(−d+1) … X_(−1)) = h_(d−1) − h_d,        Σ_(d≥1) (h_(d−1) − h_d) = h_0 − h_∞.
```

The register at distance `d` holds, given the nearer ones, the code of depth `d − 1`. It gives the
place the fall of the code from depth `d − 1` to depth `d`. The contents telescope down to the
entropy rate and never to nothing; what they give sums to the whole reach
(atlas `code.register-content-by-distance`).

[measured] On the python-codes passage (TRAIN 8,096,768 places, read on the 43,470 places of
HELD128, Witten–Bell chains, nats a place; `cap_e.py`, `cap_e_right.py`):

| `d` | the register's own content given the nearer letters | in bits | what it adds to the place | share of its content that bears on the place |
|---|---|---|---|---|
| 1 | 3.418 | 4.93 | 0.708 | 0.21 |
| 2 | 2.700 | 3.90 | 0.728 | 0.27 |
| 3 | 1.972 | 2.85 | 0.514 | 0.26 |
| 4 | 1.460 | 2.11 | 0.228 | 0.16 |
| 5 | 1.234 | 1.78 | 0.082 | 0.07 |
| 6 | 1.151 | 1.66 | 0.024 | 0.02 |

The own content was read directly as right-only tables, and agrees with the left tables of the same
depth within 0.01 (the identity above). The floor is 1.105 at eight back, 1.6 bits.

[interpretation; agent-inferred] This is the telescope of the lens. Each further digit is narrower
given the nearer ones (about 30, 15, 7, 4.3, 3.4 and 3.2 letters), and a falling share of it bears
on the end.

### 2.4 Read alone, a register does not narrow

[measured] The same letter at `−d` was then read only as one of `K` classes, one class map for
every context, with the nearer letters kept letter for letter. Classes were located on TRAIN
(letters followed alike, then reassigned to lower TRAIN's code) and, as a control, drawn by a hash.
The share of what the whole letter adds that `K` classes hold (hash, located):

| `d` | `K` = 4 | 8 | 16 | 32 | 64 | least `K` holding 0.9 |
|---|---|---|---|---|---|---|
| 1 | 0.09, 0.41 | 0.21, 0.55 | 0.40, 0.72 | 0.64, 0.93 | 0.81, 0.99 | 32 |
| 2 | 0.31, 0.41 | 0.51, 0.57 | 0.70, 0.70 | 0.85, 0.92 | 0.92, 0.99 | 32 |
| 3 | 0.40, 0.42 | 0.62, 0.59 | 0.79, 0.80 | 0.90, 0.94 | 0.95, 0.99 | 32 |
| 4 | 0.42, 0.39 | 0.67, 0.60 | 0.81, 0.80 | 0.91, 0.94 | 0.97, 1.00 | 32 |
| 5 | 0.25, 0.15 | 0.61, 0.43 | 0.77, 0.70 | 0.89, 0.87 | 0.98, 0.99 | 64 |

The guess fixed before the read was that the width narrows with distance (64, 32, 16, 16, 8, 8).
It missed: the width is 32 at every distance to four, and from two back a hash holds as much as the
located classes.

[measured] The far pair (places −4 and −3), read as one of `K` classes beside the near pair kept
letter for letter (`cap_d.py`), gives the same answer one grain up:

| Reader of the far pair | Code | Cells |
|---|---|---|
| none (two back) | 1.982 | 67,760 |
| its near letter only (three back) | 1.467 | 244,378 |
| the pair itself (four back, one level) | 1.219 | 542,182 |
| located classes, `K` = 16, 64, 256, 1024 | 1.597, 1.431, 1.280, 1.226 | 175,615; 268,092; 383,033; 494,415 |
| hashed classes, `K` = 16, 64, 256, 1021 | 1.600, 1.405, 1.286, 1.237 | 259,018; 387,374; 479,097; 522,375 |

The rule fixed before the read: a located radix compresses the letters' law if some `K` sits 0.10
or more under the whole tables' line at equal cells, and does not if every `K` sits within 0.05.
Every located `K` sits within 0.05 (0.003, 0.008, 0.047 and 0.022 under). The guesses for the codes
themselves were 0.06 to 0.12 too high for the located classes and 0.26 to 0.40 too high for the
hash.

[interpretation; agent-inferred] Past two letters the law of the letters is a lexicon: what it
costs follows the count of cells held, whatever keys them. A far digit has no width of its own. It
acts only in the frame the nearer digits carry, which is what a serial chain says of a far joint,
and it is why joints compose by product. [measured] A reader that sums separate contributions of
the two letters each side codes 1.63 on held 0–31 where the joint table of the same letters codes
0.569 (`add1.py`).

### 2.5 Coarse graining is reach, and two grips close the chain

[measured] Reach, from the third column of 2.3: the letters move the place four joints deep on one
side (0.71, 0.73, 0.51, 0.23, then 0.08 and 0.02). With both sides written the rings give 1.778,
1.064, 0.175 and 0.023 (codes 1.640, 0.576, 0.401, 0.378 at one to four letters each side;
`both3.py`): two rings deep.

[measured] Grips, from a ruler on scattered written letters (a uniformly random order of writing,
each place coded from the written ones among its four neighbours each side, every subset its own
table; `cap_b.py`): 2.763 when neither neighbour is written, 1.310 and 1.304 when one is, 0.514
when both are. The order-averaged code is 1.525.

[interpretation; agent-inferred] Motion far from the origin needs longer links and never more
letters: beyond four joints the letters' chain passes nothing, so what reaches further (a name's
second use, a bracket's closure, a block's end) travels another chain. A place held from both sides
is a closed chain, and its code is less than half an open one's. That is the lens's feedback: the
write is read back, and the reading closes the loop.

[correction, 21:10 UTC] "Two grips" here names the two ends of a difference and never a count of
receivers, and "closed" means held at both ends, which is one case of a boundary response and no
loop. [The next record](2026-11-10_A_HELD_LETTER_IS_A_LEAKY_GRIP_THE_LAW_ACROSS_A_PLACE_IS_THREE_BODY_WIDTHS_ADD_ALONG_A_BRANCH_AND_PLASTICITY_IS_ANISOTROPY.md)
2.1 and 2.5 state both, with the split of four letters between the sides (both ends matter;
balance hardly does).

### 2.6 The price of a cell

[definition] `code.equation-of-state` reads a code length against the passage's own clock. The
evening's reads move the other wall, the reader's capacity `V` in cells:

```text
π(V) = −dC/d ln V        (nats a place per nat of cells),        a factor r of cells buys π ln r.
```

[measured] Whole tables, one side: `π` = 0.40 from two to three back, 0.29 from three to four, 0.15
from four to five, 0.06 from five to six. Two each side, cut to its `k` most frequent contexts
(`cap_a.py`): the code is 1.640, 1.409, 0.975, 0.629 and 0.576 at `k` = 0, 1,000, 10,000, 100,000
and all 356,758, so `π` = 0.19 then 0.15 per nat of contexts through the middle decades. Of the
contexts, 41% occur once, and 2.9% of the held places meet a context TRAIN never shows.

[measured] The field with 64 contacts (the held locked visit of November 10) lacks 0.053, 0.127,
0.216 and 0.233 against that table cut to 1,000, 10,000, 100,000 and all contexts (`cap_a3.py`).
Of the 0.233, 84% sits in contexts seen 10 to 999 times. At contexts TRAIN never shows, and at
those it shows once, the field codes better than the table (1.40 against 3.04, and 1.19 against
1.47).

[interpretation] The mass of a context is its count (`spectro.reading-mass`: one arrival moves a
context of mass `M` by `1/(M + 1)`), and the counts of counts are the mass spectrum. The field's
lack is at middle mass. Heavy contexts it holds, and at the lightest it does what a table cannot:
it carries a law to a context it has not met.

### 2.7 Permittivity, permeability and imaginary time

[proved-standard] A constitution's two stores give a speed `1/√(LC)` and an impedance `√(L/C)`
(`em.impedance-alpha`). At a face between two impedances the reflected share is
`((R − M)/(R + M))²` (`wave.junction-reflection`). Under `t = −iτ` the ringing pair `e^(±iωt)`
becomes the relaxing pair `e^(∓ωτ)` with the same `ω² = K/C`, and a state at temperature `θ` is
periodic in `τ` with period `1/θ` (`quantum.evolution-kinds` keeps the two kinds apart).

[interpretation; agent-inferred] A lens, or any founded part, is a region whose two stores differ
from its surroundings, and its faces are where strain and reflection sit. The release's lock is the
real-time, pumped side of one constitution. Its settling and its re-draws to neutrality are the
imaginary-time side of the same one, and the neutrality at which the re-draws stop is that side's
temperature. [conjecture] A part founded with its couplings at zero meets the field at the worst
mismatch and charges slowly for that reason; the new contacts' straight travel
([the contact test](2026-11-10_GROWTH_IN_CONTACTS_BINDS_WEAKLY_THE_LANE_FIELD_WITH_64_CONTACTS_GAINS_0.013_IN_FOUR_LAPS.md))
is consistent with it and does not test it.

## 3. The field's own reads beside the rulers

[measured; design's reads on the RTX 4080 SUPER, held 0–31, nats a place]

| State (numbers) | Masks, a random order | Place order, whole prefix written | Octaves, the end given |
|---|---|---|---|
| lap 26 (31,190) | | 1.953 | 1.784 |
| 64 contacts, lap 4 (63,606) | 1.704 | 1.858 | 1.697 |
| 64 contacts, lap 6 | 1.706 | 1.792 | 1.677 |

The lane was 1.84 times the plain field's numbers (57,398), and 32 to 64 contacts was 1.108 times
the lane's. The held joint of the 64-contact line reads 1.8043, 1.7971, 1.7917 and 1.7858 at laps
four to seven: a steady 0.006 a lap.

[source-inspected; the line's v14 tree] The laps train three kinds of state: one random mask a
member; the opening (everything void); and, under `FIELD_PATH_WRITER`, the release's own state
given its end, with the answer's places ordered by the octave of their distance to the end and the
first `k` written. Place order with prefix states exists under `FIELD_PATH_PREFIX` and was retired
on November 6.

## 4. What follows for the machine

1. **The release's order stays.** [ruling] The order the release uses (the end given, places
   locked by octaves, re-draws to neutrality) is a trained order, and it codes within 0.03 of the
   masks' order. Place order, which no state trains, is 0.09 to 0.15 above and falling. Reason: the
   chain rule gives every order the same total under one law (`radix.held-face-reading-order`), so
   orders differ only by what the learner holds in each, and here they do not differ. A place held
   from both sides is the closed chain of 2.5. Withdrawn before it was sent: a working reading of
   19:50 that the release should grow from its written boundary, which compared a read with the end
   free that the release does not use.
2. **No class channel for the letters' law.** [ruling] By 2.4 a coarser reading of the far letters
   buys what its cells buy and no more, located or hashed. A level that reads far letters through
   classes is not ordered. What a longer link has to carry is reach (2.5), which the letters' chain
   does not have.
3. **The field's transmission by joint.** [ordered November 10 20:35 UTC] One reading, state bytes
   unchanged: the code at a held place when exactly its `d` nearest letters are written and the
   rest of the answer is void for four places or more beyond, the question given as always; one
   side, `d` = 0 to 4, and both sides, `d` = 1 to 4. The text's rows on held 0–31 are 3.481, 2.710,
   1.898, 1.423, 1.224 and 1.564, 0.569, 0.419, 0.397. Guess fixed before the read (G12 in the
   receipts): one side 3.30, 2.75, 2.15, 1.97, 1.90; both sides 1.72, 0.66, 0.56, 0.53. Rule fixed
   with it: the field's chain is short if its gain at `d` = 1 and at `d` = 2 is each 0.70 or more
   of the text's and its gain at `d` = 3 is under half the text's; it has friction at every joint
   if the three ratios lie within 0.15 of one another. A short chain asks for depth, a register
   read in the frame of the nearer ones. Friction at every joint asks for numbers at the near
   contacts. The reading that the field is about two joints deep (its whole-prefix code of 1.79
   lies between the two-back and three-back tables, and its locked code stands at the height of two
   letters each side while lacking 0.233 of that law) is the guess this read tests.
   [correction, 21:03 UTC] The order as worded was my error: the field reads a void place as the
   answer's end, so design's first read (16.4 nats at no letters) measures another state and is
   not scored. It was ordered again with the rest of the answer left open and with the uneven
   splits added. The guess and the rule stand unchanged and unread.
4. **Withdrawn (21:10 UTC): "growth is sized in doublings".** As first ruled: a growth test's
   guess is sized from the ratio of numbers, which the 32-to-64 test (1.108 times) did not do, and
   design was asked for a lap's card time and memory at two and four times the numbers. The
   observation stands (that test added a tenth to the numbers and its guess ignored it). The rule
   does not: a width is a composition, registers add along a branch, and a step is the part that
   is lacking in any integer count
   ([the next record](2026-11-10_A_HELD_LETTER_IS_A_LEAKY_GRIP_THE_LAW_ACROSS_A_PLACE_IS_THREE_BODY_WIDTHS_ADD_ALONG_A_BRANCH_AND_PLASTICITY_IS_ANISOTROPY.md)
   2.6, with design's projection in its section 3).
5. **Laps go on.** [correction, 20:45 UTC] A ruling sent at 20:35, that laps stop being a lever
   once the two running arms end, is withdrawn: it carried the plain field's stationary point over
   to a grown line whose new parts are still travelling. [measured; from the section lines of laps
   25 and 26, no run] The plain field of November 6 stands at a stationary point of its 31,190
   numbers: a step's first-order change of its own section is −1,806 millionths of a bit a site,
   and the same step taken once more moves the next section by +33, so laps do not move it. The
   64-contact line is not at such a point: it falls 0.006 a lap at lap seven. With it goes
   the statement that the field's numbers buy what the text's cells buy (0.12 to 0.19 against 0.15
   to 0.19): the field's figures were gaps read while its grown parts were still charging, so they
   are floors.
6. **Retired: the one-tick contact-form ruler** owed by
   [the chord record](2026-11-10_A_CHORD_IS_CIRCLES_CLOSING_AT_THEIR_LEAST_COMMON_MULTIPLE_DEPTH_IS_THE_RADIX_AND_INDUCTION_RECURS_ACROSS_GRAINS.md)
   §3 item 2. Reason: the additive reader already reads what a sum of pair terms can hold at one
   tick (1.63, 1.40, 1.29 at two, four and eight letters each side) and the field stands 1.06 under
   it, so a one-tick form is not the field as coded; item 3 above reads the field itself.

## 5. What does not transfer

- The biological wiring. Nothing of arms, cords or hair cells enters the machine.
- A joint list, a grammar of parts or a solver for a target pose. The machine's joints are its own
  levels and contacts, and its keys are located, never authored.
- The filter's Gaussian form. The elimination of 2.2 is the theorem for a chain with quadratic
  energy; the field's faces are not Gaussian, and only the block form (ports, one joint at a time)
  is claimed.
- A temperature for the machine. 2.7 names the neutrality of the re-draws as one; no number is
  given and no thermometer is built by this record.
- The count tables. They are rulers. A table keyed by its context recites and has no law to carry
  to a context it has not met (2.6 shows the field doing what the table cannot).

## 6. Owed

- The score of the read of item 3 as ordered again, and of the rate-by-part arm (guess 0.03 on the
  held joint after four laps; its first lap ended 0.0028 under the plain lap).
- The held locked visits of both arms' last states, read as the product of the chord record §2.8.
- A ruler under a consistent renaming of identifiers (the chord record §3 item 3), which reads the
  longer link of 2.5.
- Lean: 2.3 is finite entropy arithmetic over a stationary block law, and 2.2 a Schur-complement
  identity; both can join #410.

## Receipts

Device: none of these reads used the card. They ran on the host of the PC, in a VM of two threads
and about 4 GB, each under 180 s; the longest (`cap_b.py`, `cap_d.py` at `K` = 1024) ran about 150 s.
Scripts and reads are in
[the receipts](2026-11-10_A_CHAIN_OF_JOINTS_IS_THE_CHART_OF_FRICTION_A_REGISTERS_WIDTH_EXISTS_ONLY_GIVEN_THE_NEARER_ONES_AND_THE_LETTERS_LAW_IS_PRICED_IN_CELLS_receipts/),
with the machine root replaced by `${HOLONICS_ROOT}`:
- `guess_capacity.txt`: guesses G1 to G12 with the UTC time each was fixed, before its read;
- `capacity_reads.txt`: every read above, with the scores;
- `yard.py` (the loader and the Witten–Bell tables), `cap_a.py`, `cap_a2.py`, `cap_a3.py` (the cut
  table and the field against it), `cap_b.py` (scattered letters), `cap_c.py` and `both3.py` (the
  tables), `cap_d.py` (the far pair through classes), `cap_e.py`, `cap_e_right.py` and `cap_e.log.txt`
  (registers by distance), `add1.py` (the additive reader).

They read the passages and the visit dumps under `.local/`, which stay private. Scores of the
guesses not stated above: G1 (held places with an unseen context) guessed 6%, read 2.9%; G3 (the
cut table) guessed 1.25, 0.90, 0.65, read 1.41, 0.975, 0.63; G6 and G7 (the field's lack by cut and
by mass) guessed 0.03, 0.12, 0.21 and 70%, read 0.053, 0.127, 0.216 and 84%; G8 (the scattered
ruler) guessed 1.85, read 1.525; G9 (cells of the left tables) guessed 35k, 180k, 500k, read 68k,
244k, 542k. G4 and G5 belong to the ruler retired in item 6 and were never read.
