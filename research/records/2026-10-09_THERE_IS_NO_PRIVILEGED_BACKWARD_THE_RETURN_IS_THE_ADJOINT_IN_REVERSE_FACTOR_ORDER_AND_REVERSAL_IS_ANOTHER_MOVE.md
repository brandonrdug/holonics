# There is no privileged backward: the return is the adjoint in reverse factor order, and reversal is another move

**Date.** October 9. **Issues.** #73, #62, #63. **Grade.** Lens record. Each claim carries its own
grade. Most of the law is already owned and kernel-checked; this record joins the lens to those
owners. The new identities of §4 (the reversal less the adjoint is twice the boost; a stationary
diffusion's reversal is its adjoint) and the witnesses were checked here by exact rational
computation. §2, §5 and §6 are definitions and readings.

## 1. The lens

Brandon, October 6, asking why backpropagation does anything valuable at all. He accepts it as a
real operation, in which transport is run the other way and integrated across the same connections,
but holds that reducing it to "backwards" is the error. Action and information move in many
directions at once; cross-entropy has many axes; Holons stand in many-to-many continuing relations
with epochs, and Holarchies with aeons, and none of those relations has to be singled out, because
singling out is the selective work of navigation. An instruction to simply run things in reverse is
not a method in general, given how the framework treats relativity and direction, and "backwards"
does not even say whether it means space, time or both.

Brandon, October 7: the agents keep circling the notion of "sign". A sign is nothing more than a
direction read against other frames; talking as if it were a property the object owns is what makes
it confusing.

[definition; agent-inferred] **The lens in the objects.** "Backward" has named four different
operations here. None is privileged; each is fixed by its operand. The learning return is one of
them, the adjoint. In a deterministic passage it is neither the time reversal nor the inverse,
except for a pure turn, where all three agree; in a stochastic chart, against a stationary law, the
adjoint is the reversal (a Bayes inversion) and still not an inverse (§4). The repository already
said most of this before the reset and in its guides; the lens recurs because no record joins those
statements to the words "backward" and "sign" where agents still use them.

## 2. Four operations that "backward" has named

[definition] Each is already an owner. They are kept apart because they act on different things.

| Operation | What it acts on | Law | Owner |
|---|---|---|---|
| **The adjoint (the return)** | covectors, in the dual of each stage | `(D₂D₁)* = D₁*D₂*`: reverse factor order, no inverse | `Computation/HolonicAdjointNormalization.dualMap_comp_reverse_order` (`norm.adjoint-scale`); `Transport/AddressedLinearizedPassage.addressedTwoStep_adjoint_reverseOrder` (`navigator.adjoint-reverse-order`) |
| **The reversal of an aeon** | the passage, as an arrow of the aeon groupoid | `Rγ` is the inverse arrow; a clock reads `t(Rγ) = −t(γ)` | `Aeon/Clock/Reading.reading_reverse`; Rust `aeon::Aeon::reverse` (`aeon.a1-groupoid`) |
| **The inverse of a step** | states, when the step is invertible | `x_k = T⁻¹x_(k+1)`; it need not exist | `HNN/Propagation.tick_step_not_invertible` |
| **Reading backward** | positions of a word | the half-turn `k ↦ n−1−k` about `(n−1)/2`, an involution | the helical pairing `σ̄(w) = σ(w)ᴿ` (`helical.complement-reverse`; [guide](../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode), part 2) |

[historical; source-inspected] The pre-reset records already separated them. One states that the
adjoint for receiver metrics is `T† = G_X⁻¹TᵀG_Y`, that a bare transpose assumes orthonormal charts,
and that backpropagation is the covector return through this adjoint, not matrix inversion; it also
lists chronology, the hand of a chart, orientability and reversibility as four relations never to be
collapsed
([§6 and §9](2026-08-18_THE_HOLON_IS_THE_OPERATION_COMPLEX_THE_FOREIGN_MAP_IS_A_PORTED_WORD_AND_THE_CARD_CARRIES_ITS_FRONTS.md)).
Another returned the falsifiers: a scale-by-two transport has adjoint `[2]` and inverse `[1/2]`; a
rectangular map has a lawful metric adjoint while its inverse is refused; and the composite adjoint
of `A` then `B` is `A†B†`, while the same-order foil `B†A†` is unequal to it
([falsifiers](2026-08-26_THE_SITUATED_DIFFERENCE_CROSSES_A_PERSPECTIVE_CHART_AND_ITS_CAUSAL_ADJOINT_RETURNS_ALONG_THE_ADDRESSED_WORD.md)).
The guide states the conclusion: an adjoint is not a physical reversal of time, and a unit metric is
not a theorem of learning dynamics
([HNN formula §3](../../docs/HNN_FORMULA.md#3-learning-is-variation-of-these-operators)). The metric
adjoint has its exact owner, refused when undeclared (`linalg.metric-adjoint`,
`ExactRatMatrix::metric_adjoint`).

[proved-derived; formal-checked] **The return needs no inverse.** The executed tick can fail to be
invertible: at `K = −2` the element step is zero (`HNN/Propagation.tick_step_not_invertible`), so no
state can be recovered from its successor. Its adjoint still exists, because every linear map has a
dual. A "backward pass" read as inverting the passage is undefined there; the return is defined.

[definition] **Space or time.** `dualMap_comp_reverse_order` reverses the order of any composition.
The factors can be ticks of one passage (time) or Holons joined along a path of a Holarchy (space).
The Word's return does both: it pulls the covector through the receiving map and its phase
transport, then through the ticks in reverse (the module header of `hnn::port`, `Word::pull_back`).
The answer to "spatially or temporally" is: through whatever was composed, in the reverse of its
composition order, and never by running time backward.

## 3. Why the return carries value: the pairing

[proved-derived; formal-checked] The swept covector pairs exactly with the trajectory at every
intermediate tick, `⟨λ_n, x_k⟩ = ⟨g, x_(k+n)⟩` (`HNN/Propagation.trajectory_pairing`). A change of
the block operators changes a reading by exactly the reverse telescope over the word's own
trajectory,

```text
⟨g, x′_t⟩ − ⟨g, x_t⟩ = Σ_(k<t) ⟨λ′_(t−1−k), (T′ − T) x_k⟩
```

with no inverse and no replay (`HNN/Propagation.word_variation_exact`, `hnn.word-variation-exact`).
On the concrete tick the same pairing and variation hold (`HNN/TickBlocks.fieldTick_pairing`,
`fieldTick_variation_exact`, `hnn.concrete-tick-blocks`).

[agent-inferred] **What this answers.** The value of the return is the duality identity
`⟨Ĝ*Ȟ|H⟩ = ⟨Ȟ|ĜH⟩`, the same kind of identity as Stokes' `⟨dȞ, H⟩ = ⟨Ȟ, ∂H⟩` with `d = ∂ᵀ`. It
carries the reading's sensitivity onto every earlier state and every material locus exactly: the
covector returned to a locus is the change of the declared comparison per change of that locus.
Nothing travels back in time. What travels is the coholon side of a pairing, along the same
composition. Two limits keep the claim exact:
- A covector is not yet a direction. Raising it to a gradient needs a declared tangent–cotangent
  chart, and changing the chart changes the gradient while the covector stays fixed
  (`HolonicAdjointNormalization.MetricGradientChart`, `gradient_eq_iff_same_chart_preimage`).
- The descent a deposit makes along it is certified at its declared scope, the certified step's
  curvature bound (`holon.certified-step`, `holon.gauss-newton-curvature`), not a guaranteed finite
  decrease of the full comparison.

[proved-standard] **Many-to-many without choosing.** For a composition whose incidence is a directed
acyclic graph of linear maps, the covector returned to a node is the sum, over every path from that
node to the reading, of the composed adjoints along the path (the chain rule). The return does not
pick among Holons, epochs or paths. It reaches only loci within the reading's causal diamond: it
vanishes at every block that observes no receiver within the passage, and an edge outside the
diamond receives nothing (`HNN/Propagation.covector_causal_cone`, `reached_loci_diamond`); inside it
a covector can still cancel. An operator outside that diamond changes no admitted reading
(`release_past_diamond`). Selection is a separate act: the release law chooses which action to
admit, and the covector only informs it.

## 4. The adjoint keeps dissipation; the reversal produces it

[proved-derived; formal-checked] Against a receiver's metric `G`, a rate splits into its turn
`T = ½(A − A♯)` and its boost `B = ½(A + A♯)`, with `A♯ = G⁻¹AᵀG` (`Geometry/Motion.adjointIn`,
`turn`, `boost`, `turn_add_boost`; `motion.turn-boost-split`), and the adjoint is the boost less the
turn, `A♯ = B − T` (`HolonicsResearch/Geometry/TurnBoostNormality.adjointIn_eq_boost_sub_turn`).
Already proved on the chain: transposing `(Ω − M)G` gives `G(−Ω − M)`, which reverses the
conservative part and leaves the dissipation's sign, and no orientation of the chain undoes its
dissipation (`Transport/HolonicChain.adjoint_is_the_reversed_structure`,
`no_direction_undoes_the_dissipation`; `tube.chain-reversal`). In the Holon's chart the same is
`adjointIn Q ((J − R)Q) = (−J − R)Q` (`Geometry/Motion.adjointIn_portHamiltonian`).

[proved-derived] **The new term: reversing the motion is a different move.** Running the motion
backward in time takes the rate `A` to `−A = −T − B`. Subtracting the adjoint,

```text
(−A) − A♯ = −2B          so  −A = A♯  ⇔  B = 0
```

The return and the time reversal of the motion agree exactly when the rate does no work against the
receiver's metric: a pure turn, energy-conserving. Wherever there is a boost (a push, a pump,
friction), they differ by twice the boost. In the Holon's chart the reversal is `(−J + R)Q`: the
resistive part enters with the producing sign, so the reversed motion of a passive Holon is active,
while its adjoint stays passive. The chain owner's word "reversed" names the transposed chain, which
in this record's terms is the adjoint; the time reversal of the motion is the other operation.

[proved-derived; computational-witness] Witnesses, checked over `ℚ`:
- `G = I`, `A = [[−1, 1], [−1, −1]]`: `T = [[0, 1], [−1, 0]]`, `B = −I`,
  `A♯ = Aᵀ = [[−1, −1], [1, −1]] = B − T`, while `−A = [[1, −1], [1, 1]]`. The rate of the
  receiver's quadrance `xᵀGx` is `2xᵀGBx`, so its energy `½xᵀGx` changes at `xᵀGBx`
  (`Geometry/Motion.energy_rate_is_boost`): the quadrance changes at `−2|x|²` along `A` and along
  `A♯`, and at `+2|x|²` along `−A`.
- `J = [[0, 1], [−1, 0]]`, `R = diag(1, 0)`, `Q = diag(2, 1)`: `A♯ = [[−2, −1], [2, 0]] = (−J − R)Q`
  and `−A = [[2, −1], [2, 0]] = (−J + R)Q`.
- `A♯ = B − T` and `(−A) − A♯ = −2B` also held on fifty random integer rates against random positive
  definite rational `G` in dimension three.

[proved-standard; formal-checked where named] **In the stochastic chart the reversal is a Bayes
inversion, and it is the adjoint.** For a stationary chain with law `π > 0`, the adjoint of `P` in
`ℓ²(π)` is the chain read backward, `P̂(y, x) = π(x)P(x, y)/π(y)`: the posterior of the previous
state given the next. Here the dual transport and the reversal are one kernel, `P̂`, which exists
whenever `π` is given, while a step's inverse need not be a kernel at all (collapsing two states
onto one has none, `Computation/HolonicDiffusionCharts.collapseBool_has_no_stochastic_inverse`).
What production separates is the forward chain from its reversal: `P = P̂` exactly under detailed
balance (`Aeon/Production/PathReversal.selfAdjoint_iff_detailedBalance`;
`aeon.reversibility-real-spectrum`), which is exactly when an aeon's production
`σₙ = D(P_γ ‖ P_(Rγ))` vanishes (`production_eq_zero_iff`; A6, `aeon.a6-irreversibility-kl`). The
biased rotation of three states, forward `2/3` and back `1/3` under the uniform law, produces
`σ = (1/3) log 2` per epoch, one third of a bit (`Rotation.rotation_production_pos`;
`aeon.rotation-production-counterexample`): its reversed chain is the rotation the other way, and
the difference between the two is the arrow. Self-adjointness reads differently in the two charts:
`A♯ = A` is a pure boost against `G`, while `P = P̂` is zero production.

[proved-derived; computational-witness] **The two charts meet in a stationary linear diffusion.**
Let `dx = Ax dt + dW` with noise of covariance rate `D ≻ 0` and stationary covariance `Σ ≻ 0`,
`AΣ + ΣAᵀ + D = 0` (Lyapunov). The time-reversed stationary process has covariance
`Σe^(Aᵀs) = e^(ΣAᵀΣ⁻¹s)Σ`, so its drift is `ΣAᵀΣ⁻¹`, the adjoint `A♯` in the stationary metric
`G = Σ⁻¹`. Lyapunov's equation multiplied by `Σ⁻¹` gives `A + A♯ = −DΣ⁻¹`, so

```text
A♯ = −A − DΣ⁻¹,        2B = −DΣ⁻¹        (G = Σ⁻¹)
```

The stochastic reversal is the adjoint, and it differs from running the drift backward, `−A`, by
exactly the score term `−DΣ⁻¹ = 2B`: Anderson's reverse drift `−f + D∇log p` with `∇log p = −Σ⁻¹x`
[proved-standard]. It is the identity `(−A) − A♯ = −2B` of the deterministic chart, with the boost
now the dissipation that the noise balances. Checked over `ℚ` on forty random stable rates and noise
rates in dimensions two and three; the first witness above, with `D = 2I`, has `Σ = I` and
`A♯ = Aᵀ = −A − 2I`. So a "backward" that is not declared confuses different things in different
charts: in a deterministic passage, the adjoint and the time reversal, which differ by twice the
boost; in a stochastic one, the reversal and a step's inverse, and the forward law and its reversal,
whose asymmetry is production.

## 5. Many cross-entropy axes

[proved-derived; formal-checked] The cross-entropy rate depends on the declared common parameter `λ`
and on each participant's clock-rate map:

```text
dC/dλ = −r_p Σ_i P′_i log Q_i − r_q Σ_i P_i Q′_i / Q_i
```

with `r_p = dτ_p/dλ` for the source clock and `r_q = dτ_q/dλ` for the receiving clock
(`Physics/Information/CrossEntropyRate.hasDerivAt_crossEntropy_clocks`; `info.cross-entropy-rate`;
Rust `physics::information::rate::cross_entropy_rate_on_clocks`). Its two terms are the exchange and
the deposition of the first law of learning (A7, `Aeon/Production/FirstLaw`).

[definition; agent-inferred] **An axis is a declared clock.** Each admitted clock `λ` with its two
rate maps is one axis of cross-entropy. Entropy per epoch is entropy per unit time times the mean
epoch length (A4, `aeon.a4-entropy-clock-change`), so the rates on different axes are related by the
pairings of their clocks, not by one master time; several clocks join into one time exactly when
every cycle of their declared rate ratios closes (`clock.axes-join`,
`Physics/Information/ClockJoin.join_iff_silent`). Reversing a parameter flips the oriented rate
(both terms change sign with `r_p` and `r_q`) and reverses no dissipation, as the guide's
measurement conventions already say ([§10](../../docs/ELEMENTARY_OBJECTS.md#10-receipt)). There is
no single "backward" for cross-entropy either: a reversed parameter is one more chart of the same
flux.

## 6. A sign is a direction read in a frame

[definition; formal-checked where named] Orientation exists only in the pairing: reorienting both
sides changes no face, and reorienting one side negates the reversed cell
(`Objects/Pairing.face_unchanged_by_joint_reorientation`, `one_side_reorientation_negates_the_cell`;
`holon.face-joint-reorientation`). A sign is what remains of a phase once its winding is deleted:
`−1 = e^(iπ)` is a half-turn, and on locked sheets the binary sign is the phase `0` or `π`
(`holon.sign-is-a-turn`, `Physics/PhaseCarrier.phaseNetworkEnergy_binaryPhase`;
[Holonic notation](../../docs/HOLONIC_NOTATION.md#arrows-signs-and-turns)). Rebasing the
observation, receiver and navigators through a half-turn preserves every possible future face
([the Swing](../../docs/ELEMENTARY_OBJECTS.md#the-swing)).

[definition; agent-inferred] **The comparison's sign is one covector in two frames.** CLAUDE.md
names `p − q` the cross-entropy logit gradient and `q − p` its descent covector. The code carries
the same pair: the ratio returns the magnitude part `p̃ − q` (`hnn::ratio::HolonRatio::covector`),
and the contact composition negates the pulled-back gradient into its descent
(`hnn::reference::compose_contact`). Which one is "the" gradient is a declared orientation of the
comparison, not a property of the motion. A reported sign names its frame: which comparand is
subtracted from which, and in which chart.

## 7. What the repository already owns

- The reverse-order adjoint:
  `Computation/HolonicAdjointNormalization.{dualMap_comp_reverse_order, causalAdjoint_carries_declared_scale, MetricGradientChart}`;
  `Transport/AddressedLinearizedPassage.addressedTwoStep_adjoint_reverseOrder`; the metric adjoint
  `ExactRatMatrix::metric_adjoint`.
- The word's return and its exactness:
  `HNN/Propagation.{trajectory_pairing, word_variation_exact, covector_causal_cone, reached_loci_diamond, release_past_diamond, tick_step_not_invertible}`;
  `HNN/TickBlocks.{fieldTick_pairing, fieldTick_variation_exact}`;
  `HNN/LatticeWord.executed_adjoint_unique`; `HNN/Word.reaction_stage_adjoint`; Rust
  `hnn::port::Word::pull_back`, whose module header states that it claims no inverse of a step and
  composes the executed ticks' transposes in reverse.
- The turn, the boost and the dissipation under transposition:
  `Geometry/Motion.{adjointIn, turn, boost, turn_add_boost, energy_rate_is_boost, adjointIn_portHamiltonian}`;
  `HolonicsResearch/Geometry/TurnBoostNormality.adjointIn_eq_boost_sub_turn` (the ghost record's
  [J6](2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md));
  `Transport/HolonicChain.{adjoint_is_the_reversed_structure, no_direction_undoes_the_dissipation}`.
- The reversal and its production: `Aeon/Clock/Reading.reading_reverse`;
  `Aeon/Production/PathReversal.{selfAdjoint_iff_detailedBalance, production_eq_zero_iff, Rotation.rotation_production_pos}`;
  the [aeon record](2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md)'s A1,
  A4, A6 and A7; a step's missing inverse,
  `Computation/HolonicDiffusionCharts.collapseBool_has_no_stochastic_inverse`.
- The clocks of cross-entropy: `Physics/Information/CrossEntropyRate`,
  `Physics/Information/ClockJoin`.
- Orientation and sign: `Objects/Pairing`, `Physics/PhaseCarrier`, the notation guide.

## 8. The joins owed

1. **The reversal–adjoint split, stated where agents read it.** In `Geometry/Motion`:

   ```text
   −A = adjointIn G A  ↔  boost G A = 0          (G invertible, 2 invertible)
   ```

   from the definition `boost G A = ½(A + adjointIn G A)`, with
   `(−A) − adjointIn G A = −2 · boost G A` from `adjointIn_eq_boost_sub_turn` and `turn_add_boost`.
   Its consumer is every reading that calls itself "time-reversed" or "backward": it declares
   whether it is `Rγ`, the inverse of a step, or the adjoint, and this statement makes the
   declaration checkable. Lean, owed in #62.
2. **The metric form of reverse order.** For invertible `G`,

   ```text
   adjointIn G (A * B) = adjointIn G B * adjointIn G A
   ```

   one line from `adjointIn G A = G⁻¹AᵀG`, checked here on fifty random rational triples. Its
   consumer is a return that carries a declared material metric between stages (the helical record's
   paired return names the material metric as what fixes a physical adjoint). Lean, owed in #62.
3. **The stationary reversal.** In `Geometry/Motion`, beside `adjointIn_portHamiltonian`: for
   invertible `Σ` with `A * Σ + Σ * Aᵀ + D = 0`,

   ```text
   adjointIn Σ⁻¹ A = −A − D * Σ⁻¹,        boost Σ⁻¹ A = −½ · D * Σ⁻¹
   ```

   an algebraic identity; the reversed process's covariance argument is standard and is not stated
   in Lean here. Its consumer is any diffusion chart that calls its reverse process "backward": it
   declares it as this adjoint and carries the marginal, the score, that the reversal needs. Lean,
   owed in #62.
4. **The vocabulary.** Proposed for the shared-word table of the
   [morphodynamic circuit](../../docs/ELEMENTARY_OBJECTS.md#the-morphodynamic-circuit): **backward**
   is stated as the return (the adjoint, reverse factor order), the reversal of an aeon (`Rγ`), the
   inverse of a step, or reading backward (the index half-turn); **sign** is stated as the
   orientation of a pairing in a named frame. No owner moves.

No new machinery is proposed. The return already is the adjoint in reverse factor order; the lens's
work is to keep the four operations apart wherever a consumer reads them.

**Recorded failures checked.** A design thought in the programming language rather than the
mathematics (lesson 11 of the
[September 29 lessons](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md),
in its §3): "backward pass" and "sign" are programming habits standing in for the adjoint and for a
frame's orientation, which is the confusion the lens names. Building before reading prior work, and
claiming it absent (process failures that the same record lists): §2 cites the August records that
already separated these operations, and only §4's two identities are new. A tape kept as retention
([D3](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md), and the retention law): the
return composes the executed ticks' duals within the Word that produced them and keeps no tape
across words; this record proposes none. A located cause carried into a new consumer (lesson 3): the
certified step's scope is stated in §3, not claimed as a finite decrease. Nothing here is
modality-specific, so text is not the exception.
