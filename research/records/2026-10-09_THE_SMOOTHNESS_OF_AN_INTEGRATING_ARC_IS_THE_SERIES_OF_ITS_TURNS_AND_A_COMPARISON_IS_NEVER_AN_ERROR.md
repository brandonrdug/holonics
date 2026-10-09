# The smoothness of an integrating arc is the series of its turns, and a comparison is never an error

**Date.** October 9. **Issues.** #73, #62, #63. **Grade.** Lens record. Each claim carries its own
grade. The move pair, the path jets, the comma and the loss law are existing owners; the discrete
jet identity, the bending identity and the comma's placement ratio are derived here and were checked
by exact rational computation; the readings of the circuit are agent-inferred definitions, and
whether its gauge tracks learning is open.

## 1. The lens

Brandon, October 7. The circuit could be read by how smooth its integrating arcs are. A smooth arc
is one carried by many small turns; a jagged or rough one is one that lacks them. He is explicit
that smoothness is not a virtue in itself. Taking in a stimulus, carrying the action it calls for,
and answering it physically are each transitions that can run smoothly or in jolts, and that is the
way he would have cross-entropy and loss read. He calls "error" a poor ontological word, since
nothing is simply right or wrong; what the operators can read is whether the music is coming into
line, where separate songs are told apart and where they compose together inside the network.
Reading smoothness, he adds, is the same work as reading phases, modes and their modular pieces: the
comma, and music.

Earlier that day: a margin the agents reported as a single summed decimal had thrown away the
sequence of winding and turning contributions that told how its parts behaved. And fitting exactly
to something already authored is not the aim; a machine that only echoes what others wrote would not
be thinking.

[definition; agent-inferred] **The lens in the objects.** The smoothness of an integrating arc is
how its turn and its boost are distributed over the ticks of its passage: the series of its moves,
whose continuous form is the path jets. A comparison along the arc is a ratio carried with its
residual, and its smoothness is that ratio's jet along the clock. "Error" names no object.

## 2. The arc's series, exactly

[proved-derived; formal-checked where named] **Per tick: the move pair.** A mover's velocity before
and after a tick is carried as the undivided pair `(v, v′) ∈ ℤ[i]²`, never as its ratio, with
`Δv = v′ − v` and

```text
v̄·Δv = ⟨v, Δv⟩ + i·det(v, Δv)  =  |v|²(k − 1)   for v ≠ 0, k = v′/v
```

the power (the effort along the motion, the boost) and the signed turn (the effort across it). Its
kind (rest, start, stop, free fall, turn, boost, or turn and boost) is decided on the integers
without division (`motion.move-pair`; Rust `geometry::motion::Move::{power, turn, kind}`; Lean
`Geometry/Motion.power_is_boost_rate`, `normal_effort_is_turn_rate`). Its consumer today is the
chase terrain, not the HNN.

[proved-standard; formal-checked] **In the continuum: the path jets.** With velocity `e^w`,
`ẇ = v⁻¹v̇` is the boost rate plus `i` times the turn rate (the Maurer–Cartan form), and every
higher derivative is `x^(n+1) = e^w · Y_n(ẇ, ẅ, …)` with `Y_n` the complete Bell polynomials
(`motion.path-jets-bell`;
`Geometry/Motion.{velocity_rate_is_log_derivative, acceleration_and_jerk, bellJet, bellJet_two, position_jets}`).
The jerk is `e^w(ẇ² + ẅ)`.

[proved-derived; computational-witness] **The discrete jets are polynomials in the successive
ratios.** For a passage `z_0, z_1, …` with nonzero terms and ratios `r_k = z_(k+1)/z_k`,

```text
Δⁿ z_k = z_k · Σ_(j=0..n) C(n, j) (−1)^(n−j) ∏_(i<j) r_(k+i)
```

since `Δⁿ = (S − 1)ⁿ` and `z_(k+j) = z_k ∏_(i<j) r_(k+i)`. Every `n`-th difference of the passage is
its current value times a polynomial in its move ratios: the tick counterpart of `position_jets`,
with the successive ratios in place of the jets of `w`. Checked on random Gaussian-rational passages
for `n ≤ 6`. The continuous jet of a quadratic log and its tick-lattice differences already agree in
Lean (`Objects/Ratio.jet_continuous_matches_lattice`), and the higher differences keep their
chronology (`jet.chronology-not-free`: `[flip, erase]` reads `−1` where `[erase, flip]` reads `0`).

[definition] **The winding and turning contributions are this series.** A margin or a reading that
is a sum of per-tick contributions is reported as the series of its terms (the move pairs, or the
ratios with their windings), with its sum and its carry: the total turn's whole windings follow the
carry cocycle (`winding.carry-cocycle`), and a closed loop's lifted increments sum to an integer
winding (`Geometry/PhaseCarry.closed_loop_has_integer_winding`). One summed decimal loses the parts,
and the loss is not only presentational: equal squared scalar losses `|(1, 0)|² = |(0, 1)|²` carry
different oriented returns (`learn.scalar-loss-not-cultivation`,
`Computation/SituatedMachineLearning.scalarLossDoesNotDetermineCultivation`; the prototypes' D4,
scalar readings that pointed the wrong way).

## 3. Smooth and jagged, exactly

[proved-derived; computational-witness] **The same turn, spread or concentrated.** Read each tick's
turn on a declared phase grain of `N` steps per whole turn, as an integer increment `a_k` of the
lifted phase (`Geometry/PhaseCarry`: lift and carry), `n` ticks in all, with total `A = Σ a_k`. The
total is additive, and its whole windings are its carry. Lagrange's identity on the integers gives

```text
n · Σ a_k² − A² = Σ_(i<j) (a_i − a_j)²  ≥  0
```

so the quadratic gauge `Σ a_k²` is at least `A²/n`, with equality exactly when every `a_k = A/n`.
Smooth is the same total turn carried by equal micro-turns; jagged is the turn concentrated in a few
ticks; a corner puts all of it in one tick, `Σ a_k² = A²`, `n` times the smooth value. The total
turn, with its windings, is unchanged; the gauge reads only where it sits. The identity holds over
any commutative ring and was checked on two hundred random rational series. [proved-standard] The
turn angle `θ_k` of a Gaussian-rational move is not itself exact: it is transcendental whenever it
is nonzero, since `e^(iθ_k)` is algebraic (Lindemann–Weierstrass). Its exact rational face, the
spread `Im(r_k)²/|r_k|² = sin²θ_k` (`3 + 4i` has spread `16/25`), is not additive. So the gauge is
stated on the lifted grain, where the turns add.

[proved-derived; computational-witness] **The comma placed smoothly or in a wolf.** Twelve fifths
overshoot seven octaves by `3¹² : 2¹⁹ = 531441 : 524288`, and no stack of fifths closes on octaves
(`HolonicsResearch/Mathematics/Comma.{pythagorean_comma, three_pow_ne_two_pow}`;
`ratio.comma-never-closes`). In the log chart, with `κ` the comma's logarithm in any base, closing
the circle by narrowing each of the twelve fifths by `κ/12` gives the gauge `12·(κ/12)² = κ²/12`,
and narrowing one wolf fifth by `κ` gives `κ²`: the ratio is exactly `12`, whatever `κ` is: an
identity in `κ`, whose value is transcendental and is never reported as a decimal. The ghost
record's J4 already reads a temperament as a quotient by commas, with the comma spread over its
steps as the cokernel's residual
([J4](2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md)). Smoothness is where that
residual is placed. That is the sense in which gauging smoothness is the comma and the music.

[definition; agent-inferred] **The gauge reads; it does not choose.** A temperament that
concentrates its comma keeps other intervals exact for its receiver, and a sharp transition in the
circuit can be a meaningful new distinction (a lock's commit, a release). The gauge describes the
motion. It is never a descent target, and smoothing a passage to lower it would erase exactly the
concentrated turns that carry decisions.

[definition; agent-inferred] **The three processes Brandon names.** Recognition is the reception's
passage, transport is the Word's ticks, and the physical response is the release's passage. Each has
its own move series and its own gauge, read at its own clock. [open] Whether the HNN's passages are
jagged where it fails to learn and smooth where it composes is not measured; join 1's receipts, read
beside the comparisons, are its test.

## 4. A comparison is never an error

[definition; source-inspected] Loss is the logarithm of a ratio of Holons, `ℓ = log Ĝ_(T←H)`, with
its winding branch, and its covector is `R⁻¹dR` (§9 of the
[objects](../../docs/ELEMENTARY_OBJECTS.md#9-ratio); `ratio.loss-is-log-ratio`). A scalar loss is
one receiver's face of a residual, never the residual itself, and nonclosing transport remains exact
transport
([THE_MACHINE, the operative equations](../../docs/THE_MACHINE.md#the-operative-equations)). A
failed cocycle across a receiver atlas is holonomy, not loss
(`Foundation/ReceiverAtlas.defect_is_holonomy_not_loss`, `receipt.atlas-cocycle-defect`). The
remainders that keep a helix from closing are not error (the ghost record, §1). For π and `e`, error
enters only in how a face is attained
([emanation and resonance](../../docs/ELEMENTARY_OBJECTS.md#emanation-and-resonance)).

[definition; agent-inferred] So a comparison along an arc has exact parts and no "error": the ratio
(the relative transport of the produced and the compared Holon), its residual (what the receiver's
grain leaves open), and its jets along the clock (the smoothness). Against an authored target, the
ratio names which comparand is the target: it is a reading against that declared target, not a
verdict on the machine.

[definition; formal-checked where named] **The loss's smoothness is its jet on the clock.** The
cross-entropy rate along a clock is exchange plus deposition, each dot with its clock-rate map
(`Physics/Information/CrossEntropyRate.hasDerivAt_crossEntropy_clocks`); the jet of the log ratio
continues it (`ratio.jet`, `Objects/Ratio.{logJet, logJet_two}`: `L′ = R′/R`,
`L″ = R″/R − (R′/R)²`), and the order names (velocity, acceleration, jerk, snap, crackle, pop) are
labels on orders, asserting no kinematic law (`jet.names`). Measuring loss "that way" is reporting
this jet along the passage's clock, beside the endpoint face, never instead of it.

## 5. The music lining up

[proved-derived; formal-checked] Two passages advancing at integer rates `q, p` through a pair
contact of positive weight and null-definite material read zero power exactly when `q v_a = p v_b`
(`Transport/HelicalPairInteraction.lock_iff_zero_power`; `pair.synchronized-is-zero-power`). Two
clocks lock at their Farey address, and every `q`-tick aeon is then a cycle; at an irrational ratio
they never lock, and their near-returns fall at the convergents (`aeon.two-clocks-lock`).

[definition; agent-inferred] **Lining up** is the vanishing of the relative turn between two
passages' series at a rational ratio: they compose alongside each other and close together once per
Farey period. **Being differentiated** is a relative phase that keeps winding, so a receiver that
reads relative phase keeps them apart; in the parametron that reading goes through the pump (§5 of
the [objects](../../docs/ELEMENTARY_OBJECTS.md#5-parametron)). The jets of two passages' relative
ratio are therefore the gauge of their lining up.

## 6. What the repository already owns

- The per-tick move and its kinds: `motion.move-pair`, `geometry::motion::Move`; the continuous path
  jets: `motion.path-jets-bell`, `Geometry/Motion`; the ratio's jets and their lattice form:
  `Objects/Ratio.{logJet, jet_continuous_matches_lattice}`, `Transport/JetStaircase`,
  `Foundation/HigherDifferenceTransport.chronology_free_collapse_fails`.
- The curvature of the comparison itself: the station score's curvature in its logits is `ln 2/2` on
  the magnitude part and `q/4` on the phase part (`receiver.station-score-curvature`;
  `HNN/Ratio/Resolution.{station_score_quadratic_upper, station_curvature_constant}`), which sets
  the certified step's curvature bound.
- Winding and carry: `winding.carry-cocycle`, `Geometry/PhaseCarry.closed_loop_has_integer_winding`.
- The comma and the temperament: `Mathematics/Comma`, `ratio.comma-never-closes`, the ghost record's
  J3 and J4.
- No error ontology: the loss law, THE_MACHINE's operative equations,
  `Foundation/ReceiverAtlas.defect_is_holonomy_not_loss`, `learn.scalar-loss-not-cultivation`.
- Lock and slip: `Transport/HelicalPairInteraction.lock_iff_zero_power`, `aeon.two-clocks-lock`.

## 7. The joins owed

1. **The Word's passage read through the move pair.** For each receiving-face amplitude (or ring
   state) along a Word's ticks, the series of move pairs `(z_k, z_(k+1))` with each move's power and
   signed turn, and the total turn's whole windings counted at a declared section (an epoch
   reading), carried in the Word's receipt beside its comparison. Equation at the consumer:
   `Σ_k (power_k, turn_k)` is reported as its series with its sum and carry, and the reading
   `Δⁿ z_k = z_k Σ_j C(n, j)(−1)^(n−j) ∏_(i<j) r_(k+i)` holds on the receipt's own values. Consumer:
   the Word's receipt (`hnn::word`); not built. A located cause stays open meanwhile: no HNN passage
   has yet been read this way, so no claim about where it is jagged is made.
2. **Lean, owed in #62:** the discrete jet identity beside `Transport/JetStaircase`; the bending
   identity on grain increments `n Σ a_k² − (Σ a_k)² = Σ_(i<j)(a_i − a_j)²`; the comma's placement
   ratio `κ² / (12·(κ/12)²) = 12` (trivial, kept beside the comma's owner for the reading).
3. **The reporting rule.** A margin, score or reading built from contributions is reported as its
   series with its sum and carry, never as one decimal. Proposed for the reporting clause of
   CLAUDE.md's exact-arithmetic law and THE_MACHINE's "Measurement"; no owner moves.
4. **Lining up as a receipt.** For two passages that a pair contact joins, the relative ratio's jet
   and the lock reading (`lock_iff_zero_power`) as one more reading of the contact's receipt; its
   consumer is the pair contact's slip reading on the duplex (`compression::keys::duplex`). Owed.

**Recorded failures checked.** Bits read as progress (failure 7 and lesson 7 of the
[September 29 lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
whose §1 numbers the failures and §3 the lessons) and a single scalar of progress (the retired
phrasing): the gauge is a reading reported beside the comparison, never a target to descend. Scalar
readings that pointed the wrong way
([D4](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md)): the series is kept because
one number lost the direction. A known-truth fixture becoming the goal (the October 7 exchange): the
gauge reads the machine's own passage and needs no authored target. A located cause carried into a
new consumer (lesson 3): §7 names that no HNN passage has been read yet, rather than asserting a
smoothness result. Text as the exception (failure 3; lesson 2): path jets and move pairs are
modality-free; the motor chart is serial screw words, a pitch is a phase on the helix of octaves,
and a contour is a path in an image.
