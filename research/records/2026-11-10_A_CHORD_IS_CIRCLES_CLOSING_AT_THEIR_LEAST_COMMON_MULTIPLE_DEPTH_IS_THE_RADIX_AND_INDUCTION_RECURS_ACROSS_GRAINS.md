# A chord is circles closing at their least common multiple, depth is the radix, and induction recurs across grains

[historical] On November 10 Brandon asked that the theory work extrapolate and no longer only review:
the unified physics and the advanced mathematical routes (RH, Hodge, complex fluids, elliptic curves,
cryptanalysis, helical and toroidal geometry, lightning, sphere and fractal packing) and, with
emphasis, music. His lens, paraphrased (his words stay in the conversation logs):
- notes and chords integrate into characteristic configurations the way particles make atoms and
  molecules, and a compound is recognized by the pattern it radiates (a spectrogram, a Doppler shift);
  the relationships are implicit, potentials held by resonant code lengths on the helix;
- induction recurs across every kind of entropy transfer; a Holarchy is an unoriented table of
  potential geometries which an aeon orients, and causality needs induction between configurations;
- concentric annuli released from the innermost and falling look like a tube whose side is `a^x`:
  depth is what the radix is, the only way a number has places below one, and a ratio is "three per
  four" with its units attached; counts of counts carry the recursion;
- vortex rings are stabilized by their medium, energetic flux contorts into a helix, a whipped
  string pivots at a contact and winds around it;
- polarity is a labelled axis between configuration states, time parity is what governs symmetry
  and conservation, and a closed loop loses at its transitions to other conduits.

This record first recovers what the repository already holds for each part (most of it does, and a
false absence is the commonest defect here), then adds the joins that were missing, then states what
follows for the machine with each test. A chart of the disciplines is in
[the atlas](../../docs/atlas/CHARTS.md).

## 1. Recovered: what the repository already held

| Part of the lens | Owner (atlas id; record) |
|---|---|
| A beat is the slip of a pair contact, zero beat is a Farey lock, equal temperament leaves every fifth slipping | `pair.beat-is-slip`, `lock.farey-neighbour`, `lock.pair-lock-zero-power` |
| A helix of fifths never closes on its octaves; the comma and where a temperament places it | `ratio.comma-never-closes`, `ratio.comma-placement-gauge` |
| Scales of 5, 7, 12, 41 and 53 fifths are the two-gap counts of the rotation `log₂ 3` | `rotation.three-distance`, `rotation.fifth-gap-recursion` |
| A rate either locks (rational) or never repeats (a quasicrystal by cut and project) | `rotation.lock-or-quasicrystal`, `rotation.tube-window-projection` |
| A song is the family of its enactments: transposition, tempo and voicing are invisible | `holon.song-is-a-family` |
| A chord class and a performance are different receivers of one source (the cross terms) | `encoding.chord-cross-terms` |
| Hearing a string of holes multiplies its geometric face by ζ, and Möbius inversion listens back | `fractal.spectral-zeta-factor`, `fractal.full-spectrum-mobius-inversion`; [the music is in the holes](2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS.md) |
| A tone's period is located, never declared; a bank of rings sounds on a bounded lattice | [October 9](2026-10-09_A_TONES_PERIOD_IS_LOCATED_NOT_DECLARED.md), [October 10](2026-10-10_A_BANK_OF_RINGS_SOUNDS_ITS_EMISSION_ON_A_BOUNDED_LATTICE.md) |
| The height of a rational is a product over places and the product formula holds | `trace.place-ledger` |
| A digit move is a boost at the real place and a turn at the others; the leading face is a rotation whose invariant measure is Benford's | `radix.digit-move-place-kind`, `radix.leading-face-gas`, `radix.leading-rotation-benford` |
| The annulus carries scale and turn together, and the exponential folds the lift | [July 19](2026-07-19_THE_ANNULUS_CARRIES_THE_SCALE_TURN_LIFT_THE_EXPONENTIAL_FOLDS_THE_FACE.md) |
| Compatible circle covers with their carries (the solenoid's finite tower) | `solenoid.finite-compatible-chart`, `solenoid.restriction-action-square` |
| Coprime frames meet once per residue pair only modulo their product | `encoding.frame-explosion`, `lock.coprime-torus-diagonal` |
| A rate splits into a skew turn and a dissipative part; Faraday's successor | `ph.skew-dissipative-turn`, `em.faraday-successor`, `maxwell.stokes-dirac` |
| A navigator whose rate form vanishes sits on real part one half | `receipt.seam-g-skew` |
| A key is located by loop closure over a menu | `key.menu-loop-closure`, `key.enigma-reading` |

## 2. The joins added

### 2.1 The ear reads the real place and harmony reads the finite places

[proved-standard] A just interval is a positive rational `x = ∏_p p^(v_p)`. Its width as heard is
its real size, `log x = Σ_p v_p·log p`, and its harmonic content is the vector of valuations
`(v_2, v_3, v_5, …)`. The product formula (`trace.place-ledger`) ties them: what the real place
reads is the valuations summed with weights `log p`.

[interpretation] A **comma** is a rational that is small at the real place and far from the origin
in valuations: `81:80 = 2⁻⁴·3⁴·5⁻¹` is 0.0179 of an octave wide, and its height is
`81·80 = 6480 = 2⁴·3⁴·5`. Octave equivalence forgets `v_2`. A "p-limit" keeps finitely many
places. This is the exact sense of the p-adic analogy in the lens: a chord is one point read at
every place at once, and consonance and width are two readings of it that need not agree.

### 2.2 A temperament is a coholon on the valuation lattice, and its kernel is the commas

[definition; agent-inferred] A temperament is a linear map from the valuation lattice `ℤᵏ` to a
lattice of lower rank. Twelve equal steps on the 5-limit is the covector
`⟨12, 19, 28|`: `(v_2, v_3, v_5) ↦ 12v_2 + 19v_3 + 28v_5`.

[proved-derived] Its kernel is generated by `81:80` (`−48 + 76 − 28 = 0`) and `128:125`
(`84 − 84 = 0`). Its residual on the fifth is `7/12 − log₂(3/2)` (the fifth 0.00163 of an octave
flat) and on the major third `4/12 − log₂(5/4)` (0.0114 sharp).

[interpretation] This is Holonic Compression read on the lattice, term for term: the kernel is the
differences no admitted receiver distinguishes (a twelve-key instrument), the quotient is the
retention (twelve classes), and the residual is what is emanated, heard as the slip of
`pair.beat-is-slip`. Where the residual is placed is the gauge of `ratio.comma-placement-gauge`.
The kernel belongs to the receiver, never to the lattice: a receiver that distinguishes the comma
meets it as holonomy, the drift of a progression that returns a comma away
(`ratio.comma-never-closes`).

### 2.3 A chord is a set of circles closing at their least common multiple

[proved-standard] Tones at integer frequencies `a_i` (jointly coprime) repeat together once per
period of frequency `gcd = 1`, and the finest tick they share is `1/lcm(a_i)` of it. Rings with
integer periods `T_i` return together after `lcm(T_i)` ticks. Rings of periods 33, 7 and 11 close
at `231 = 3·7·11`, and as frequencies of that closing cycle they are the chord `7 : 33 : 21`.

[interpretation] A set of rings **is** a chord, its closing length is the chord's period, and its
frustration (what coprime periods cannot share before their product) is its roughness. The
fundamental a listener hears under partials that do not contain it is the located `gcd`: the
receiver infers the one navigator whose windings the partials are, by loop closure over the
partials, which is key location with the partials as the menu (`key.menu-loop-closure`; the
October 9 record). The inference is unavoidable in the lens's sense because a lock leaves no other
reading at the receiver's grain.

### 2.4 The code length of a ratio, and what a lock's width does not say

[definition] A ratio `p:q` in lowest terms costs `log p + log q` to state, the logarithm of its
height (`trace.place-ledger`). [proved-standard] Between Farey neighbours the mediant has the
smallest period, and every ratio between them costs at least it (`lock.farey-neighbour`).
[interpretation] So the potentials of the lens are ordered by code length, and consonance is that
order heard: the short codes are the locks a receiver meets first between any two it already holds.
The atlas keeps three quantities apart here and this record does too: the code length (a prior),
the width of the frequency interval over which a driven pair locks (which narrows with `q` in the
sine family and is not universal, `lock.tongue-exponent-not-universal`), and the measure of the
basin that reaches the lock (`lock.phase-viability`). A rigid rotation has no locks at all
(`lock.rigid-rotation-no-staircase`): a lock needs a driven family with a contact.

### 2.5 Major and minor hold the same pairs with opposite orientation

[proved-derived] `4:5:6` and `10:12:15` have the same three pairwise ratios (`5:4`, `6:5`, `3:2`),
and `10:12:15 = 1/6 : 1/5 : 1/4`. Inversion `x ↦ 1/x` reflects the valuation lattice through its
origin, takes one chord to the other, and exchanges the nearest shared fundamental with the nearest
shared overtone (`lcm = 60` is fifteen times the lowest tone of the first and six times the lowest
of the second).

[interpretation] No reading of pairs separates them. A third body does. This is the lens's
polarity: one configuration and its reflection, with orientation existing only in the pairing, and
which of the two a receiver is built on being a matter of its own history.

### 2.6 The zeta function on the half line scores equal divisions of the octave

[measured] At `t = 2πN/ln 2`, the sixteen largest local maxima of `|ζ(½ + it)|` for `2 ≤ N ≤ 60`
all lie within 0.1 of an integer, the largest at `N = 53.0` (8.24), `58.05` (7.64), `41.0` (7.50),
`46.0` (7.45) and `31.0` (6.81). At the integers it reads 5.08 at 12, 5.21 at 19, 5.86 at 22, 6.81
at 31, 7.50 at 41, 7.45 at 46 and 8.24 at 53, against a median of 1.18 over the grid
([receipt](2026-11-10_A_CHORD_IS_CIRCLES_CLOSING_AT_THEIR_LEAST_COMMON_MULTIPLE_DEPTH_IS_THE_RADIX_AND_INDUCTION_RECURS_ACROSS_GRAINS_receipts/zeta_equal_divisions.txt);
Borwein's series with integer coefficients on the cloud host, a float reading at step 0.05; the
observation is known to tuning theory).

[interpretation] Each prime contributes the phase `p^(−it)`, which is 1 when `N·log₂ p` is an
integer, so the function is large where one equal step approximates every small prime at once: the
divisions 12, 19, 22, 31, 41, 46 and 53 are the temperaments musicians found. On the half line the
weights are `n^(−1/2)`, the weights of 2.9 below. A zero is a division at which the whole harmonic
series cancels. This joins `fractal.spectral-zeta-factor` to the temperament of 2.2: hearing
multiplies by ζ, and a good temperament is a height on its half line where the multiplication is
loud.

### 2.7 Identity is a pattern of ratios modulo a common shift

[proved-standard] A Doppler shift multiplies every frequency of a source by one factor, a
translation in `log ν`. The ratios between lines do not move. Every line of a spectrum is a
difference of two term values (Ritz), so the lines are an exact cochain on the graph of levels and
sum to zero around every closed cycle of transitions.

[interpretation] The species is the pattern modulo the translation and the state of motion is the
translation: `holon.song-is-a-family` for sources. A compound is recognized by closure, three lines
closing a triangle, which is loop closure again with the term values as the keys. For a passage of
code the same quotient is consistent renaming: a coordinated substitution absorbed exactly when its
reached difference lies in the receiver's kernel (the helical code's own clause).

### 2.8 Source and filter are two knowledges in one product

[standard] A voice is a source (a pitch and its harmonics, relative, transposable) times a filter
(the tract's resonances, fixed in frequency, the same under every pitch). In logarithms the two add.

[measured] The held locked visits of November 10 read the field against a count of two letters each
side, a ruler on the host, as a product `face^a · table^b` (nats a place, HELD128, tables fit
outside the dumped sample, weights (0.6, 0.6) fit on half the held problems and read on the other):

| State | Field | Product | Field lacks | Field holds beyond the count |
|---|---|---|---|---|
| lap 26 | 0.646 | 0.361 | 0.285 | 0.225 |
| lap 37 (the lane) | 0.588 | 0.341 | 0.247 | 0.244 |
| four more laps, 32 contacts | 0.580 | 0.338 | 0.242 | 0.247 |
| four more laps, 64 contacts | 0.568 | 0.334 | 0.233 | 0.251 |

The guess fixed before the read was that 64 contacts lack 0.01 less than 32: measured 0.008,
missed by 0.002. About two thirds of every gain since lap 26 is the local law being filled
(0.038 of 0.058 from lap 26 to lap 37, 0.008 of 0.012 for the contacts). The ruler's scripts are in
the [receipts](2026-11-10_A_CHORD_IS_CIRCLES_CLOSING_AT_THEIR_LEAST_COMMON_MULTIPLE_DEPTH_IS_THE_RADIX_AND_INDUCTION_RECURS_ACROSS_GRAINS_receipts/ruler/):
`yard.py` builds the count tables, `xr_a.py` and `xr_b.py` fit them outside the dumped sample and
read their distributions at each dumped place, and `xr_e.py` forms the product and scores both
guesses. They read the passages and the visit dumps under `.local/`, which stay private.

[interpretation; agent-inferred] The two columns are two knowledges at one height: the local joint
law of the alphabet (which letters stand together, the same in every problem) and the relations of
the problem (which the count cannot hold). The lens's source and filter fit them as a first
reading: the local law is a filter, a constitution of fixed resonances, and the problem's relations
ride on it as the source. [measured] A second guess fixed before the read, that the contacts' gain
sits at the vowels more than at spaces, newlines and brackets, held only weakly: 0.0102 against
0.0089 nats at such a place. The contacts help brackets and newlines as much as the insides of
words, so this read does not show them to be the filter's organ in particular.

### 2.9 Depth is the radix: the falling annuli are the solenoid's tower

[proved-derived] Let ring `k` have radius `r₀bᵏ`, be released at time `kτ` and fall at speed `v`.
At time `t` it is at depth `z_k = v(t − kτ)`, so the rings lie on
`r(z) = r₀·b^((vt − z)/(vτ))`. The side of the tube is the graph of the exponential, depth is the
logarithm of radius, and the ring's index is the digit's place.

[interpretation] A positional numeral is read down this tube, one phase on each ring. The ring a
receiver stands on is the radix point, a position of the receiver and never of the number, which
is the floating point of `radix.leading-face-gas`: the winding `k` is the depth and the mantissa
`θ` is the phase. A ratio's expansion closes with the period of `radix.digit-move-place-kind`. The
rings outward without end are the `b`-adic direction, and the rings with their `b`-to-one covers
are the tower of `solenoid.finite-compatible-chart`. "Three per four" is two windings carried as an
undivided pair, the Ratio object, with the two rings as its units.

[proved-standard] A tube whose section grows by a constant ratio per unit depth,
`S(z) = S₀e^(mz)`, carries a wave `e^(−mz/2)·e^(i(ωt − kz))` with `k² = (ω/c)² − (m/2)²` (Webster's
horn). The amplitude falls as `S^(−1/2)`, which is what keeps the power through every
section equal, and it passes only above the cutoff `ω = mc/2`.

[interpretation] The weight `n^(−1/2)` of the half line is this conservation on the ring index:
dilation is unitary on `L²(dx)` with the factor `a^(1/2)`, the seam of `receipt.seam-g-skew`. A
tube that carries equal power at every depth is a signal with equal power per octave, which is
where music, speech and the field's own falloff sit, and an ear whose places run with the logarithm
of frequency reads it one digit per depth.

### 2.10 Induction recurs across grains

[proved-standard] A Holon's rate is `ẋ = (J − R)∇H` at its ports, `J` skew and `R ⪰ 0`
(`ph.skew-dissipative-turn`). The skew part exchanges between stores without loss: a change of flux
through a cell drives circulation on its boundary, Stokes with a time derivative
(`em.faraday-successor`). Eliminating an interior through `Λ_DN` returns at the boundary a skew
part and a dissipative part again, now with memory, and the interior's initial state survives in
it (`resolvent.dynamic-schur`).

[interpretation] What was induction among the interior's modes arrives at the next grain as inertia
and delay, and what was order arrives as heat whose fluctuation is tied to its loss. So the lens's
recursion holds grain after grain: every entropy transfer is the `R` of one grain feeding the `J`
of the grain beneath, and information dissolves and is never annihilated. A closed strand carries
its whole windings without loss along itself and loses where it meets another conduit. The pair
contact is that junction: locked it passes current with no slip (`lock.pair-lock-zero-power`), slipping it dissipates, and
in a driven family its locks sit at rational ratios.

### 2.11 A deposit is a winding gained at a contact, and it needs heat

[interpretation; agent-inferred] The whipped string is the Swing: a strand meets a contact, pivots
on it and carries its momentum through. If the contact is lossless the strand swings past and
nothing is retained, since a reversible meeting leaves no record. With friction at the contact the
free length shortens, the strand winds, a whole winding is gained and the momentum's energy leaves
as heat there. Deposition "from covectors that actually reached that locus" is this capture: the
retained quantity is a count of windings, it is gained only where there is dissipation, and it is
bounded by the action dissipated. This is the store's law stated as geometry and heat, as the
November 9 lens asked.

[source-inspected] The learner's deposit already has this form at one grain: a number's step is its
first moment over the root of its second, the coherent part of the arriving flux against that
flux's own fluctuation, at a held rate of `2⁻¹²` of its unit a section.

## 3. What follows for the machine

Each item names its test. Nothing here is ordered except where it says so.

1. **The step at each grain is the coherence at that grain.** [ordered November 10] The rate for
   each founded part is the same law one grain up: a part whose displacements over successive laps
   hold a cosine above one half is in straight travel and opens one octave, below one half it
   closes one octave, never under the founding's `2⁻¹²`. Guess fixed: four laps end 0.03 or more
   under the plain-rate laps on the held joint, and lack 0.03 less against the count; under 0.01
   travel does not bind.
   [conjecture] If travel binds, the general form is a ladder of moments at octave rates, the
   flux's spectrum in logarithmic time, with each band stepping at its own coherence, so that a
   part's rate follows it within a lap. If travel does not bind this is not built.
2. **What the contact form can hold of the local law.** [owed, next] The count of two letters each
   side codes 0.585 and the field lacks 0.233 of it. Before more laps are spent charging contacts,
   a host ruler in the contact's own form (pair products of projected neighbours, at 32 to 512
   contacts) reads how much of the 0.233 that form can hold at all. The November 3 toy read
   1.667, 1.431 and 1.352 at 32, 64 and 128 contacts against a neighbour table, a slow fall. If
   the form saturates far above the count, what is owed is depth (products of more than two
   letters), never a larger count of contacts.
   [retired and answered, November 10 evening] The ruler as designed was retired
   ([the chain record](2026-11-10_A_CHAIN_OF_JOINTS_IS_THE_CHART_OF_FRICTION_A_REGISTERS_WIDTH_EXISTS_ONLY_GIVEN_THE_NEARER_ONES_AND_THE_LETTERS_LAW_IS_PRICED_IN_CELLS.md), item 6). Its question was answered by a stronger ruler: the best
   product of a left and a right contact at unlimited rank codes 1.030 where the count of two
   letters each side codes 0.576 ([the grip record](2026-11-10_A_HELD_LETTER_IS_A_LEAKY_GRIP_THE_LAW_ACROSS_A_PLACE_IS_THREE_BODY_WIDTHS_ADD_ALONG_A_BRANCH_AND_PLASTICITY_IS_ANISOTROPY.md) 2.3). The form saturates 0.455 above the
   count, so by the rule of this item depth is owed: a word of contacts across ticks.
3. **A renaming ruler.** [candidate] Held problems under a consistent renaming of their identifiers,
   read by the same locked visit: a field that holds the relations codes the renamed passage as it
   coded the original after each name's first arrival; a recitation does not. It is the
   transposition test of 2.7 on code and costs two minutes of the card a visit.
4. **A local store is the contact family, charged.** [interpretation] The lawful store for the local
   law is the one the machine has: contacts that charge from the flux reaching them, leak, and are
   shared by every context that excites them. A table of contexts is its ruler and never its
   realization, since it has no law to carry to a context it has not met.

## 4. What does not transfer

- Consonance as a preference is a fact about listeners. What transfers is the order of locks by
  code length.
- The zeta reading of 2.6 scores equal divisions. It says nothing about the zeros' line, and no
  claim about RH is made from it.
- Source and filter is a reading of two measured columns, not a mechanism of the field. The second
  guess of 2.8 did not separate them by letter.
- The horn's half is conservation of power in a tapered tube. That it is the same weight as the
  half line is an identity of the two weights; no spectral claim follows.
- Josephson's relation, Shapiro's steps and the cochlea are named as instances of a lock at a
  contact and of a logarithmic reader. Nothing of their materials enters the machine.
- The normality of transcendental constants, which the lens conjectures, is open in mathematics and
  is not used.

## 5. Owed

- ~~The contact form's ruler of item 2~~ (retired and answered the same evening; see item 2).
- The rate-by-part laps' score, and the same product read on each arm's last state.
- Lean: 2.2's kernel and residuals and 2.5's reflection are finite arithmetic and can join
  `RelationLadder` and the comma lemmas; carried in #410.
