# Neutral is a ratio of one against where the receiver stands, and the scope decides what a colour reads

October 26. Refs #404, #405, #410. **Grade.** Each claim carries one of these grades:
- [owned]: an existing owner states it.
- [proved-standard]: a classical result, with its source.
- [checked]: verified by this record's receipt, in integers only (300,536 checks).
- [agent-inferred]: a choice or join made here.
- [interpretation]: a reading across subjects.

The exact receipt is `neutral_scope.py` in
[`…_receipts/`](2026-10-26_NEUTRAL_IS_A_RATIO_OF_ONE_AGAINST_WHERE_THE_RECEIVER_STANDS_AND_THE_SCOPE_DECIDES_WHAT_A_COLOUR_READS_receipts/RUN.md).
The Lean owners are [`Mathematics/ColourScope`](../../lean/HolonicsResearch/Mathematics/ColourScope.lean)
and `timeBoundary_one` in [`Physics/TimeBoundary`](../../lean/HolonicsResearch/Physics/TimeBoundary.lean).
It continues
[a Galois gap is a mode's momentum](2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md)
(§12, the two compressions and the tower of colours).

**Computational object.** The helical pair interaction, read as a receiver comparing a colour with
the colours it already holds. Of the winding guide's six objects it touches:
- the pair: the reading is a ratio of two, never a value of one;
- faces and placement: the scope's reading is a face, the relative trace;
- the tower thread: the layers of a prime's tower and, across them, the scopes at one level.

The helix, cell holonomy and the tube stay as the Galois-gap record has them.

## 1. The lens

Brandon, October 26 (paraphrased). The last record's polarity answer had said that coarse graining
leaves `+1`, `−1` and `0`, and that the neutral case is where the hard questions live. He corrected
and widened it.
- **A geometric transition.** The split is another axis of recursion.
- **Neutral is usually the cheap case.** It is easier to leave something grey than to collapse it
  into a certain state. An intelligence that collapses one perception into a certainty about another
  thing's cycles, and lets that way of becoming certain cascade into how it perceives everything
  else, can mislead itself across its whole ecology, like a butterfly effect or a vortex. Things have
  to cancel and cycle through local equilibria, like a quantum foam.
- **Neutral is relative.** Pushing toward an extreme can also be easy. In a society already
  organized around a violent hierarchy, staying in that cycle is the neutral move, and changing it
  costs a great deal of energy even when those in power can see how, regardless of ethics: a matter of
  thermodynamics and diffusion. A change from there reads positive or negative by the individual's
  perspective.
- **The scope changes the spectrum.** Coarse graining from individuals to the economy and society
  over many years changes what the spectrum is about.
- **Hardness is not general.** Saying the neutral case is where the hard questions live is like
  saying solutions are hard to find, which is not generally true. Frustration and tension are also
  spectra and gaps; there are holographic distances between being able to solve problems (P versus
  NP); the problem itself has to be discovered, and the nature of a solution is a problem with its own
  cycles, cancelling over many epochs and aeons.
- **Colour theory.** Colours are relative to each other. How a colour appears depends on what is
  near it, as with lightning and its surround; matter is never simply labelled with an intrinsic
  colour. This is why it matters for consciousness and intelligence.

[agent-inferred] The reply's sentence "the neutral case is where the hard questions live" is
withdrawn as a general claim. §6 states what replaces it.

## 2. Neutral is a ratio of one against where the receiver stands

[owned; proved-standard] Every neutral already in the framework is a ratio of one against what is
held, never a value.
- **The time boundary** is neutral at `r = Z/Z′ = 1` (`timeBoundary_one`): the medium did not
  change, whatever `Z` is. Any `Z` is neutral to the receiver that stays in it.
- **The digit move** `x ↦ bx + d` is a translation, the neutral kind, on a ring where `b ≡ 1`
  ([`digitMove_translation`](../../lean/HolonicsResearch/Mathematics/BaseAction.lean)).
- **The swing** ([elementary objects](../../docs/ELEMENTARY_OBJECTS.md#motion)): a stationary grip turns
  without work, and a push, pump, moving grip or friction boosts. Against a receiver's metric a rate
  splits into a skew turn and a self-adjoint boost, so the same motion can be work-free for one
  receiver and a boost for another.
- **Colour vision** (von Kries, 1902): each cone's response is divided by its response to the
  surround the eye has adapted to, so grey is the ratio one against the adapted surround and its
  place moves when the surround moves.

[interpretation] Brandon's palace is an adapted grey: the cycle a society is organized around is
the reference its receivers read against, so maintaining it reads neutral. A change of cycle is a
time boundary with `r ≠ 1`: its action is conserved and its energy is not (the Galois-gap record's
§8, `action_conserved`), so the change does work, and whether that work reads as a gain or a loss
depends on which receiver's metric reads it.

## 3. Repeating a cycle you hold is neutral; a new cycle's sign depends on the cycles you hold

[proved-standard; checked F, M] Over `ℚ(ζ_n)`:
- **Fibres** (`fibre_primitive`, `fibre_cancels`). When `p² ∣ n`, multiplying a primitive colour
  `ζ` by the `p`-th roots of unity keeps it primitive, and each fibre `{ζ·ω : ω^p = 1}` sums to `0`.
  So the primitive colours of order `n` fall into fibres over a cycle already present, and each fibre
  cancels: that is why `μ(n) = 0`. When `p` divides `n` once, every such fibre holds exactly one
  colour of lower order, so it is not a fibre of primitive colours and nothing cancels. The receipt
  checks 16,224 fibres for `n ≤ 400`.
- **A new prime flips the sign** (`new_prime_flips_sign`): `μ(p n) = −μ(n)` when `p ∤ n`
  (115,996 pairs in the receipt). The `p = 2` case is
  [`moebius_two_mul`](../../lean/HolonicsResearch/Mathematics/PrimeSimplex.lean).
- [owned] **The tower** (the Galois-gap record's §12, [`colour.colour-tower`](../../docs/atlas/arithmetic.tsv)):
  the trace from a layer of a prime's tower to the layer below keeps the old colours, times `p`, and
  erases the new ones. Seen from the cycle already held, a genuinely new colour averages to nothing.

[interpretation] Repeating a cycle already held is neutral, and a genuinely new cycle reads `+` or
`−` according to the parity of the independent cycles already held. The sign of a change is
relative to the holder, as the lens says.

## 4. The scope decides what a colour reads

[owned] A scope is a subgroup `H` of `(ℤ/n)ˣ`, and by the Galois correspondence it is the subfield
that `H` fixes: the receiver that cannot tell apart the colours `H` permutes
([`theGaloisCorrespondenceIsTheReceiverDuality`](../../lean/HolonicsResearch/Foundation/Separation.lean),
[`coupling.galois-receiver-duality`](../../docs/atlas/targets.tsv)). The scope's reading of the colour
`ζ_n` is its relative trace `Tr_H(ζ_n) = Σ_(h∈H) ζ_n^h`.

[proved-standard; checked S] **One colour, three readings.** The twelfth-turn colour `ζ = e^(iπ/6)`
(`scope_quarter_turn`, `scope_real`, `scope_cube_root`, `scope_rational`):

| Scope | `H` | Reading | Kind |
|---|---|---|---|
| `ℚ(i)`, the quarter turns | `{1, 5}` | `ζ + ζ⁵ = i` | a turn |
| `ℚ(√3)`, the real line | `{1, 11}` | `ζ + ζ¹¹ = √3` | a size |
| `ℚ(ζ₃)`, the cube roots | `{1, 7}` | `ζ + ζ⁷ = 0` | neutral |
| `ℚ` | `{1, 5, 7, 11}` | `0 = μ(12)` | neutral |

[checked S] **The census.** For `n ≤ 200` the receipt reads every colour `ζ_n` in every scope: 3,866
pairs `(n, H)`. 1,128 readings are real, 1,766 have a turning part, and 972 are neutral. Every reading lies in its
scope (each `h ∈ H` fixes it), and compressing in stages composes: for `H ⊆ H′`, `Tr_(H′)` equals the
sum over the cosets of `H′/H` of the conjugates of `Tr_H`.
- **When a scope reads neutral.** In all 3,866 pairs the reading is `0` exactly when `H` contains a
  repeated prime's fibre, the kernel of `(ℤ/n)ˣ → (ℤ/(n/p))ˣ` for some `p` with `p² ∣ n`. One
  direction is proved: such an `H` is a union of fibres, and each fibre cancels (§3). The converse
  is checked, not proved.
- [agent-inferred] So neutral readings are a quarter of the scopes here, not most of them. The lens's
  claim that neutral is the cheap case is about cost (§6), not about how often a scope reads it.

[interpretation] **Another axis of recursion.** The tower of colours is one axis: depth, the layers
`p^k` of one prime. The lattice of scopes at one level is a second axis, across it: at a fixed `n`,
moving from one subgroup to another changes what the colour reads, and not by refining it. Brandon's
move from individuals to the economy over many years is a move along this second axis: the same
current read by a different receiver, whose spectrum is about a different thing.

## 5. No colour is intrinsic

[proved-standard] **The Galois group moves any colour to any other of its order**
(`no_intrinsic_colour`): for every unit `j` mod `n` an automorphism of `ℚ(ζ_n)` carries `ζ_n` to
`ζ_n^j`. Nothing algebraic says which primitive root is "the" `ζ_n`; what survives every
automorphism is the orbit and the relations between colours. In the framework's words, orientation
exists only in the pairing ([the Holon](../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)), and
a ratio is one per two, carried as an undivided pair.

[proved-standard; interpretation] **Colour theory says the same.**
- **Simultaneous contrast.** One grey looks lighter on black than on white.
- **Retinex** (Land and McCann, 1971). Lightness is computed from products of intensity ratios
  across edges along paths, with slow illumination gradients removed. A lightness is a log ratio
  integrated along a path from its surround: `ℓ = log R` read across each gap.
- **Lightning.** The channel's appearance is set by the field the channel itself grew (the Galois-gap
  record's §12).

## 6. Grey is cheaper than certainty, and hardness is not the general case

[owned; proved-standard] **Collapse is a merge, and a merge is where the cost is paid.**
- [Learning can be lost](2026-10-09_LEARNING_CAN_BE_LOST_A_MASKED_DIFFERENCE_IS_NULL_TO_THE_PRESENT_AND_AN_ERASED_ONE_TO_EVERY_ADMITTED_FUTURE.md):
  erasure is a merge that pays Landauer, while an isometric medium only masks.
- [Order is torsion](2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md)
  (§7): Landauer's `k_B T ln 2` per bit is paid only where the retention quotient identifies two states
  the admitted future would separate.
- Collapsing a perception to a certainty identifies readings that a later receiver could separate,
  so it is exactly a merge. Leaving the reading grey, a plural preimage fibre
  ([`info.preimage-fibre`](../../docs/atlas/information.tsv)), costs nothing.
- **Lee and Yang** (1952): a finite system of coupled locks has its partition-function zeros off the
  positive real axis, so its free energy is smooth and it never collapses sharply; a sharp transition
  appears only in the infinite limit. The parametron record's coupled locks
  ([2026-09-29](2026-09-29_THE_PARAMETRON_RE_DERIVED_THE_PUMP_READS_RELATIVE_PHASE_AND_THE_FLOQUET_CERTIFICATE_DECIDES_THE_LOCK.md))
  are this case. A finite receiver cycles through local equilibria, as the lens says.

[interpretation] **The cascade.** A certainty wrongly collapsed and then used to read other things is
one of the lessons' most repeated failures: a located cause carried unrepaired into a new
consumer.

[interpretation] **What replaces the withdrawn sentence.** The neutral point is easy to sit at; what
costs is collapsing a marginal state into a certainty and letting the certainty cascade. RH has that
shape: the de Bruijn–Newman constant is `Λ ≥ 0` (Rodgers and Tao) and RH is `Λ = 0`, so RH asks for
certainty that ζ sits exactly at the marginal point at every scale at once. Difficulty in general is a
distance in the receiver's current constitution: the problem is found first, as a landmark, and a
founding shortens the distance, which is learning as locating keys
([CLAUDE.md](../../CLAUDE.md), keys and navigation) and the information-diffusion record's reading of
P versus NP
([2026-10-26](2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md)):
the exponential cost lives only in slow modes, which landmarks pin and foundings turn fast.

## 7. For Athena: the seeds

[agent-inferred] These continue the Galois-gap record's seeds 1 to 8, for design to build and test
against its fixed acceptance (never-met sums right at the equals).

9. **The neutral is the constitution already held.** A receiver reads each arrival as a ratio
   against its own running constitution, never against a fixed zero; its grey moves when its
   surround moves. The surround is the receiver's own deposited state, never an authored average.
10. **Keep the reading grey until a contact forces the merge.** A merge of readings is a deposition
    and is certified like one, with its remainder carried (the carried release). A reading that is
    still plural is not a failure to report.
11. **A coarser scope is a relative trace of the same field.** A receiver at a coarser grain reads by
    the group of colours it cannot tell apart, so a new receiver does not need a new measurement; it
    needs its scope.

## 8. What is not derived

- The converse of §4's neutral criterion is checked for `n ≤ 200` and not proved.
- The readings of colour vision, a society and RH are interpretations that place known statements on
  one picture. No Galois group acting on perceptions or on a society's cycles is constructed.
- Whether seeds 9 to 11 help Athena is design's measurement.

## 9. The recorded failures this could repeat

- **A single scalar of progress.** Neutral as a fixed value would be one; §2 makes it a ratio.
- **An authored routine standing in for learning.** Seed 9's surround is the receiver's own
  constitution; a surround computed by a hand-written average is refused.
- **An uncertified deposition step.** Seed 10's merge is certified like any deposition.
- **Text run on its codec's grain.** Nothing here is text-specific: the scope and the ratio are
  medium-neutral.

## 10. Owed

To #410:
- (p) the converse of the neutral criterion: `Tr_H(ζ_n) = 0` only when `H` contains the kernel of
  `(ℤ/n)ˣ → (ℤ/(n/p))ˣ` for some `p` with `p² ∣ n` (checked `n ≤ 200`).

Formal-checked the same day: `no_intrinsic_colour`, `fibre_primitive`, `fibre_cancels`,
`new_prime_flips_sign`, `colour12_primitive`, `colour12_pow_six`, `scope_quarter_turn`,
`scope_real`, `scope_cube_root` and `scope_rational` in `Mathematics/ColourScope`, and
`timeBoundary_one` in `Physics/TimeBoundary`.

Atlas rows:
- `colour.scope-reading`;
- `colour.neutral-fibre`;
- `wave.time-boundary` (its neutral case).
