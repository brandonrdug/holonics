# The asked encounter teaches the material through its held carry

**Date.** October 9. **Issues.** #73, #62, #63. **Grade.** [definition; agent-inferred] for the
objective and its acceptance, fixed here before any code; [proved-derived] for the tangent law at
the executed transit, checked below against the owner's own solve; nothing native is claimed until
its fixture runs in the sole queue.

## 1. The objective

Brandon, October 9 (relayed by Epime): organize the remaining research around ambitious, substantial
advances, with no real deadlines. Epime and Claude agreed one end-to-end advance for the day: **one
continuing loop in which the World's actual return changes the constitution through its own adjoint,
and the changed constitution answers differently.** It joins four owners that already exist:

1. **Selection.** The World-family probe offers the admitted wave `u*` whose compared-station readings
   partition the live keys most (`PreparedPhysicalProbe::world_ask`; the receiving-phase record §7).
2. **Experience.** The asked encounter executes once. The World model absorbs every actual step and
   eliminates keys only by their exact annihilators (`WorldModel::absorb`).
3. **Material response.** The contemporary receiving comparison's covector returns through the actual
   held carry to the contact C/K/D material of the earlier Word (this record's law, §3), and the
   existing finite-decrease landing admits a lattice step only on an exact strict improvement of the
   same passage's re-read (`word::continuation::FiniteDecrease`).
4. **Production.** The next prepared action's compared-station reading, and the next Ask's partition,
   read the deposited material.

**Stretch.** Learning across different observations: two asked crossings at different waves, where the
first deposit changes the second Ask's offered wave or its partition, read against the no-deposit
control, and the two deposits compose without an uncertified step (lesson 6 of September 29: the second
step reads a bound over every re-entry).

## 2. The acceptance, fixed before code

On one declared World, key family, actuator and admitted lattice (the World-ask fixtures'):
- **(a) Selection.** The Ask offers `u*` by the recomputed selection law (the coverage fixture's check).
- **(b) Experience.** Every elimination carries its verified annihilator, `wᵀ P N = 0` and
  `wᵀ (b − P c − Q a) ≠ 0` at its own step.
- **(c) Material.** The landing commits at least one lattice unit of a contact factor, the energy
  closes exactly, and a cold restore reproduces the change.
- **(d) Production.** The next crossing's compared-station reading moves, read against two matched
  controls: the same history without the deposit, and the same deposit without the asked history.
- **(e) The tangent identity at its consumer.** The delayed credit equals `⟨μ_open2, χ_open2⟩` computed
  from the actual held carry, and the forward tangent agrees with the exact passage: on an exact unsplit
  word, `x(θ + εH)` is a rational function of `ε`, so the residual
  `r(ε) = x(θ + εH) − x(θ) − ε χ` satisfies `r(ε)/ε² → c` and the central residual
  `(x(θ + εH) − x(θ − εH))/2ε − χ` is `O(ε²)`. Both are checked as exact inequalities on a declared
  dyadic ladder `ε = 2⁻ʲ`, never as a decimal tolerance.

A pass means the World's actual return reached the constitution through its own adjoint, and the
changed constitution answered differently. A failure is reported by its mechanism, with the next
experiment; no acceptance is rewritten to fit a result (lesson 12 of October 9).

## 3. The tangent law at the executed transit

[proved-derived; source-inspected] The derivation is the two-Word material credit of the
[plasma and gas record](2026-10-07_PLASMA_AND_GAS_CURRENTS_CROSS_THE_SAME_MOVING_TUBE.md) (eqs. 23–25,
Epime, October 8). Here it is restated at the owner's actual chart, so that the consumer computes
exactly what the transit executes.

`propagation::transit_solve` solves `A ζ = right`, with the solved midpoint `ω = (G/2h) ζ`,
`right = h(α_g − α_h) + 2Cw − hKu` and `A = (G/2h) M`, `M = 2C + (2h/G)·1 + hD + (h²/2)K`.
`transit_update` then sets `w′ = 2ω − w`, `u′ = u + hω` and the channel's outgoing waves
`α_g − ζ/h`, `α_h + ζ/h`. Differentiating `A ζ = right` along one contact-factor direction, with
`δC`, `δK`, `δD` its form derivatives and the state held:

```text
A δζ = 2δC w − hδK u − (G/2h)(2δC + hδD + (h²/2)δK) ζ
     = 2δC (w − ω) − hδD ω − hδK (u + hω/2)                          (1)
η = δω = (G/2h) δζ;   b_w = 2η,  b_u = hη,
b_arrive_g = −δζ/h = −(2/G) η,   b_arrive_h = +(2/G) η   (channel coordinates only)
```

This is eq. (23) of the plasma record, term for term. So the material forcing is one extra solve per
tick on the contact's existing `solve` (no new operator): `δζ = A⁻¹ r_δ` with `r_δ` the right side of
(1). For factors, `δC = H cᵀ + c Hᵀ`; `D` is analogous; `δK = H Σ bᵀ + b Σ Hᵀ` with the declared
signature. The finite factor movement's `H Σ Hᵀ` is not a tangent term.

**Within one Word.** The full state map of one tick at fixed operands is the existing
`prediction::physical_signed_tick` (one signed full-state response through the same junctions, loaded
resonators and contacts). The tangent is

```text
χ_(k+1) = physical_signed_tick(χ_k, opened_at + k) + b_(a,k)(u_k, w_k, ω_k),   χ_0 = 0      (2)
```

with `(u_k, w_k)` the contact state at the start of tick `k` and `ω_k` its executed midpoint, both read
from the Word's own passage record (`Passage::states`, `Passage::midpoints`), which lives only in the
Word. `χ_0 = 0` is the held, parameter-independent opening. A canonical opening whose rate is defined
through a changing `C` supplies its own derivative instead.

**Across the passage boundary.** `χ` is carried at the `Word::reception_end` convention: before a
terminal junction when the Word ended there. The next opening applies to it exactly the linear part of
`ReceptionCarry::crossed`: arriving waves times `2G_old/(G_old + G_new)` (`B_ref`), and the held
contact rate. For the same `C` on both sides, the two `δC w` terms cancel, so `χ_w` crosses unchanged
even for a singular `C`. Treating the recorded momentum as parameter-constant would add a false storage
term. Then the source rings' storage is replaced (`Π_int`, `interior_of`); the source term is zero
because no contact factor enters `SourceMoment::open_storage`. So

```text
χ_open2 = Π_int B_ref χ_carry,     delayed credit[H] = ⟨μ_open2, χ_open2⟩                   (3)
```

with `μ_open2` the second Word's full returned `ChangeCovector` (`Word::pull_back_full` or
`pull_back_continuing`), not `WordReturn.opening`'s storage projection. If the same parameter acts
in the second Word too, its direct return (the existing `compose_contact` contraction) is added.

**Why forward, not reverse.** The reverse route already exists structurally: the first Word's
`pull_back_continuing` with `end = (Π_int B_ref)ᵀ μ_open2` returns its factor gradients. But it keeps
the first Word, and its passage, alive until the second Word's return arrives. The forward tangent
carries one state-shaped `χ` per declared direction, overwritten at each tick. It retains no Word,
event list or trajectory, as the retention law requires. Its cost is one tangent per direction; the
fixtures' contact factors have a handful of entries.

**Scope.** An exact, unsplit, linear Word: no resonator saturation, contact parting or discrete
event, no deposit or release between the two Words, `Absorption::Nothing`, and a nonsingular contact
solve. A nonlinear passage owes its actual differential, and a chart, split or rank change owes its
branch receipt. A deposited parameter changes the crossing to eq. (26) of the plasma record, which is
not this scope.

## 3a. Across the World port: the tangent is located with the World

[definition; agent-inferred, October 9] A Word that meets a participating World emits its source
ring's storage as the incident wave and receives the reflected wave in its place
(`Word::return_source_wave`). The World is foreign, so its own tangent is not available to the
machine. Its model is: the World model's live keys each carry charts `ξ⁺ = F ξ + G a`,
`b = P ξ + Q a`. When exactly one key is live, its charts stand for the World, and the tangent
crosses the port as

```text
δa = χ.storage[source],   δb = P ψ + Q δa,   ψ ← F ψ + G δa,   χ.storage[source] ← δb            (4)
```

with `ψ = 0` at a held opening of both participants. With more than one live key the World's
tangent is not located, and the teaching encounter is refused before any physical work. This joins
selection to material response: **the Ask's work of locating the World's key is what lets the World's
return teach the native material.** The loop is one piece, not two consumers placed side by side
(`PreparedPhysicalProbe::encounter_teaching`; `execute_word`'s read-only per-tick observer).

## 3b. Measured in development

[measured; developer feedback, not claim-bearing acceptance] On 0279's field, the sole queue ran the
two tests of `hnn::tests::material_tangent` on `dbeb851d` (exit 0; 136,875,964,732 ns wall; peak
child RSS 2,622,224 KiB; [receipt](receipts/2026-10-09-material-tangent/DEV_TESTS.v1.json)). On
`ε = 2⁻⁴ … 2⁻⁸` the exact central residual divides by at least 4 at each halving
(`4 r_(j+1) ≤ r_j`, and `r_j < 5 r_(j+1)`), and `4ʲ r_j` keeps one integer part across the ladder:
`5` within one Word, `4` across the crossing into the next opening. The tangent is the passage's
derivative at second order, including the same-`C` crossing that cancels both `δC w` terms. The
World-port tangent (4) passed its own test on `23ea9d78` (sources identical to `578225b7`; exit 0;
81,041,698,365 ns wall; peak child RSS 1,629,408 KiB;
[receipt](receipts/2026-10-09-material-tangent/WORLD_DEV_TESTS.v1.json)). The World's state tangent
`ψ`, carried through the actual Word and the World model's one live key, matches the actual World run
on `θ ± εH`: each halving of `ε` divides the central residual by a ratio in `(63/16, 4)` that rises
toward 4, and `4ʲ r_j` stays in `(1/2, 1)`. With two live keys the teaching encounter is refused and
the World's commit does not move.

## 3c. Selection on this field: two measured negatives, and what they mean

[measured] The World-family Ask's acceptance (`tests/world_ask.rs` at `c65cd8b8`) failed: one
declared encounter eliminates both alternatives, because the World's own initial motion sits in port
pair 0 and every declared alternative differs there. The dormant-mode successor (`cbd41c47`) measured
the deeper reason: the passive (`u = 0`) encounter alone excites all four World ports, so no
alternative law differing on any port pair survives passive experience. [definition; agent-inferred]
For linear port hypotheses whose returns are affine in the wave, an Ask can only split what the
history left dormant. On this field and source the history leaves nothing dormant, and the World key
is located by experience alone. That is the location the material tangent (§3a) needs: on this field
the loop is **experience → location → material response → production**, with selection reserved for
fields whose history is not persistently exciting (a narrowband source, a history shorter than the
key's state, or nonlinear keys). The Ask stays on its branch until such a field is declared.

## 3d. The encounter's own comparison is credited through the World

[definition; agent-inferred, October 9] The encounter compares its produced station reads with the
World's observed faces, and its covector `g_j` (`ReceivingFaceRatio::covector`) has real entries
`p̃ − q̃` and imaginary entries `−q̃ (φ_q − φ_p)/2`. The existing return (`NativeReceivingReturn`)
pulls `g` back with the World's returns held, so it is not a derivative through the World. The
tangent supplies that derivative forward, at the two places the comparison reads:

- **The produced read.** The station read is `ℓ_p = R P^τ v`. The lift `τ` is an integer winding, so
  no first variation moves it. The participation anchor `v = ŵ_s s + Σ_a ŵ_a a_a` is linear in the
  change at the junction's weights, which a contact-material direction does not move. Hence
  `δℓ_p = R P^τ δv` with `δv = ŵ_s χ.s + Σ_a ŵ_a χ.a_a` at the station's epoch.
- **The observed face.** The World reads its face on its state after the step (`JointStep::face`).
  The located key's declared face (`KeyFace`, affine, chart rate 0) reads on the same convention as
  the coupled prospect (`hnn.world-model-key-face`), so `δf = C_S ψ_S + C_R ψ_R` with `ψ` the World
  tangent of (4).

The first variation of the comparison's smooth score is reported as its series:

```text
dℓ/dε = Σ_j ⟨Re g_j, Re δℓ_p,j⟩ + Σ_j ⟨Im g_j, Im δℓ_p,j⟩ − Σ_j ⟨Im g_j, Im δf_j⟩            (5)
          magnitude                  produced phase            observed phase
```

The phase term reads only the gap `φ_q − φ_p`, so the observed covector is the produced covector's
negative. The observed masses `q̃` are the World face's reading at its grain. They are constant inside
their cell, so they contribute no first variation, and a finite step that moves a target across a
cell boundary is a jump that the landing must re-read. The credit refuses when the key declares no
face, because the World's face is then not located. Its hypotheses are exactly one live key, an exact
unsplit Word, and contact-material directions only. If the key's face differs from the World's, the
credit is the credit of the key's hypothesis: a true port law with a wrong face is a different key.
Owners: `MaterialTangent::{anchor, observe_station, read_stations, comparison_credit}`,
`StationTangent`, `ComparisonCredit`; `execute_prepared` holds the stations in its observer and
reads them through the actual read's own map and lift (`ReceivingPhases::read`).

[measured; local developer read, not claim-bearing] `the_encounters_comparison_is_credited_through_the_world`
(`tests/material_tangent_world.rs`) declares the fixture's key with the World's own face and runs one
teaching encounter, then ten encounters on `θ ± εH` read at the frozen covector. Exit 0, test body
3.16 s, whole command 3,260,215,635 ns, on the source committed with this section
([receipt](receipts/2026-10-09-material-tangent/CREDIT_DEV_TESTS.v1.json)); the claim-bearing
run is the sole queue's. On the fixture every part is negative, so moving along `+H` lowers the
comparison's smooth score:

| part | enclosure |
|---|---|
| magnitude | `−2⁻⁴ < · < −2⁻⁵` |
| produced phase | `−2⁻¹⁰ < · < −2⁻¹¹` |
| observed phase | `−2⁻⁹ < · < −2⁻¹⁰` |
| total | `−2⁻⁴ < · < −2⁻⁵` |

The observed phase exceeds the produced phase in magnitude (`|obs| > |prod|`, quotient floor 1), and
the magnitude part exceeds the observed phase by quotient floor 34. **The World's face moves with the
native material, and more than the native read's own phase does.** A credit that held the World
fixed would miss that whole part. On `ε = 2⁻⁴ … 2⁻⁸` each part's exact central residual divides by
these ratios at each halving:
- magnitude: a ratio in `(3, 63/16)` at `j = 4`, then in `(63/16, 4)`;
- produced phase: a ratio in `(63/16, 4)` throughout;
- observed phase: a ratio in `(4, 4 + 2⁻⁶)`, falling toward 4.

For every part, `4ʲ r_j` stays within a factor below 2 across the ladder.

## 3e. One tick law, recovered: the held contact variation already owned it

[source-inspected; a recovery failure, corrected] `Word::contact_first_variation`
(`word/variation.rs`) already carried exactly the tangent of eq. (2) per raw Gram-factor coordinate:
the full signed tick, then `propagation::transit_variation` at the coordinate's form derivative. The
held contact variation (`HeldContactVariation`) carries those columns across Words and assembles
their factor steps. `MaterialTangent::step` had restated the same law through its own right side and
`transit_update`. That is the recorded failure of implementing before recovering (CLAUDE.md, recover
before implementing; the lessons record's item on located owners). The law is now kept once.
`Word::contact_forms_variation` is the tick at declared form derivatives, and both consumers call it:
the coordinate columns through `contact_first_variation`, and `MaterialTangent`. Directions are built
from raw coordinates (`MaterialDirection::of_coordinate`), and `MaterialDirection::right` is
deleted. `MaterialTangent` remains only for what the held variation does not yet carry: the World
port (4) and the encounter's station tangents (5).

[proved-derived; a latent defect found by the recovery] The coordinate's form derivative was
`E fᵀ + f Eᵀ` for all three families. The executed stiffness is `K = b Σ bᵀ` with the contact's
declared signature `Σ = diag(σ)` (`contact::signed_stiffness`), so the stiffness coordinate's
derivative is `E Σ bᵀ + b Σ Eᵀ`. The shared `coordinate_forms` now reads the signature. Without a
declared boost, `Σ = 1` and nothing changes. With a boost, the held variation's stiffness columns
would have been the wrong tangent, but `HeldContactVariation::begin` refuses signatures, so the defect
was latent. Today the correction is reachable only through `MaterialDirection::of_coordinate`
(Epime's review).

## 4. The owners it consumes, and the implementation

- `propagation::{transit_solve, transit_update, ContactOperands::solve}` for (1).
- `prediction::physical_signed_tick` for the fixed-operand tick in (2).
- `word::{Word::recorded, Passage, Word::reception_end, ReceptionCarry::crossed}` and the private
  `interior_of` for the crossing in (3).
- `port::ChangeCovector::pairing` for the credit.
- `word::continuation::{ContactCut, FiniteDecrease}` and `Constitution::first_reach` for the landing.

- `ratio::ReceivingFaceRatio::covector`, `receiving::ReceivingPhases::read`,
  `propagation::participation` and `physical::action::KeyFace` for the comparison credit (5).

The new consumer is one carrier in `hnn::word::continuation`, `MaterialTangent`. It holds the
declared direction's identity (contact, its `δC`, `δK`, `δD`, and the producing commit) and the
state-shaped `χ`. Its operations are `held_opening`, `step` (eq. 2, called in lockstep with the
Word's full ticks, as `prediction` advances its completion columns), `carried`, `opened` (eq. 3) and
`credit`. Its fixture checks (e) first, on one contact and one direction. The loop's fixture (a)–(d)
then consumes it.

**Owed (#62).** The tangent identity (2) as a Lean statement at the executed transit (the `HNN/Propagation`
owner), the crossing (3) at `HNN/MoveDirection`'s held-momentum law, and the series (5) as the
derivative of the receiving ratio's smooth score at its grain representative with the target's
masses held in their cell.

**Recorded failures checked.** An uncertified deposition step: the tangent proposes, and only the
landing's exact strict improvement admits. A tape kept as retention: the forward route keeps none. An
authored routine standing in for learning: the direction comes from the World's actual return, and
nothing task-specific enters. A fixture becoming the goal: (a)–(e) are fixed here before code.

## 5. The landing: experience proposes, the located model admits

[definition; agent-inferred, October 9] The loop's material response (c) lands as follows.

1. **The proposal.** Every raw Gram-factor coordinate of the declared contacts rides the teaching
   encounter as a tangent. The descent at coordinate `i` is `−dℓ/dε_i`, the negative total of
   series (5) (`continuation::world_descent`). It is assembled into one factor step per
   (contact, family) and normalized as `HeldContactComparison` normalizes its reached covector, by
   the family's within-Word feature energy and covector scale from the encounter's own composed
   return (`NativeReceivingReturn::contacts`, whose gradients are the World-held reading of the
   same comparison). The tangents open at a held opening, so they add no opening-column power and
   no dual bound. The proposal is bound to its encounter (`PhysicalReceiver::world_proposal`,
   `WorldProposal`). Every tangent shares one producing commit. The receiver must stand where that
   encounter left it, with the World model at its tick and the carried current it published, so
   the only change since production is the encounter's own receiving publication. The ratio, the
   normalizing steps, the reach and the opening clock are read from the encounter itself.
   `land_world_descent` accepts only a bound proposal and stages it only where it was bound (Epime's
   review, October 9).
2. **The step.** The proposal is staged at the contemporary constitution, which already carries
   the encounter's receiving deposit, with the encounter's own reach. It passes through the native
   declared-step law: the first reach read from the owner's own split, then the declared-step
   producer, which commits at least one lattice unit or refuses typed
   (`Constitution::{first_reach, deposited_with_contact_spans_at}`). The descent was located at the
   comparison's producing commit. The receiving step that followed changes it only jointly with
   the contact step, at second order. That is why it is a proposal, and why the admission below,
   not the step law, decides.
3. **The admission reads the admitted future.** The candidate `θ′` and the contemporary `θ` each
   read the *next* encounter, with the same source, receiver, preparation, compared station and
   control, through the World model's one live key from its located point
   (`PhysicalReceiver::world_prospect_ratio`). The produced faces are the prospective native
   logits. The observed faces are the key's declared raw face, read at the receiver's grain
   exactly as the encounter reads the World's. `decide` (Lean
   `HNN/FiniteDecrease.admission_sound`) admits only on an exact strict classical improvement with
   no worse phase excess. The reading-identity witness is not read for receiving face ratios, so a
   phase-only improvement refuses. A plural key fibre, more than one live key, or a key without a
   face refuses: the World's future is then not located. This replaces a replay of the past
   encounter, which would need a frozen opening state of the World (a tape). Nothing is held for
   replay.
4. **Publication.** An admitted `θ′` is published with the carried current crossed at held
   momentum (`C′ w′ = π`, `ReceptionCarry::crossed`). The stored energy's exact change at that
   crossing is returned as the deposition work, so the energy account closes exactly
   (acceptance (c)).
5. **Production (d)** is the actual next encounter on `θ′`. Under the located key the prospect
   must equal it exactly (the same code enclosure and excess), which checks the model's re-read. It
   is then read against the matched control, the same history without the landing.

`PhysicalReceiver::land_world_descent` performs steps 2–4. The test
`the_world_landing_reads_the_next_encounter` (`tests/material_tangent_world.rs`) runs steps 1–5 on
the fixture and reports the decision as measured. It is never forced.

[measured; local developer read in the slot Epime admitted, not claim-bearing]
`the_world_landing_reads_the_next_encounter` on the fixture
([receipt](receipts/2026-10-09-material-tangent/LANDING_DEV_TESTS.v1.json)). One teaching encounter carried
every raw coordinate of contact 0's three factor families, and their World-sensitive descent was
staged through the native declared-step law and committed. **The landing was admitted, classically:**

| reading (code in bits, at the grain) | code − 1 | phase excess |
|---|---|---|
| next encounter on `θ`, the key's prospect | in `[2⁻⁷, 2⁻⁶)` | `X` |
| next encounter on `θ′`, the key's prospect | in `[2⁻⁸, 2⁻⁷)` | `X′`, with `X − X′` in `[2⁻¹⁵, 2⁻¹⁴)` |

The candidate's upper endpoint lies below the producing lower endpoint by a gap in `[2⁻⁸, 2⁻⁷)`.
The held-momentum crossing released stored energy: the deposition work is negative, with magnitude
in `[2⁻¹², 2⁻¹¹)`, exact in the receipt.

**Production (d), first control.** The actual next encounter on the published `θ′` reproduced the
key's prospect exactly (equal code enclosure and excess). The matched control, the same history
without the landing on a fresh twin, reproduced the producing prospect exactly. The landed
material's actual next comparison lies strictly below the control's (landed upper < control
lower). **On this fixture the World's actual return changed the contact material through its own
derivative, and the changed material answered the next encounter strictly better than the same
history without it.** Not yet measured: the second matched control (the same deposit without the
asked history), the cold restore of acceptance (c), the queue's claim-bearing run, and any second
fixture. One fixture and one step are a single instance.

[measured; second admitted developer slot, not claim-bearing] **The loop over four encounters,
against its twin without landings** (`the_world_loop_is_read_against_its_twin_over_encounters`;
[receipt](receipts/2026-10-09-material-tangent/LOOP_DEV_TESTS.v1.json)). Code is in bits at the
grain; the excess is the phase part.

| round | learner's code against the twin's | phase excess, learner − twin | landing read after the round |
|---|---|---|---|
| 0 | equal (the same encounter; no landing yet) | 0 | admitted, classical |
| 1 | **strictly below**, gap in `[2⁻⁸, 2⁻⁷)` | negative, magnitude in `[2⁻¹⁵, 2⁻¹⁴)` | refused: phase worse |
| 2 | equal enclosure | negative, magnitude in `[2⁻¹⁴, 2⁻¹³)` | refused: phase worse |
| 3 | equal enclosure | positive, in `[2⁻¹⁶, 2⁻¹⁵)` | refused: equal endpoints |

**The second matched control, the landing without its history**
(`the_landed_material_is_read_without_its_history`): on a fresh World the landed material and the
contemporary one read the same code enclosure, and the landed one's phase excess is lower by an
amount in `[2⁻¹⁷, 2⁻¹⁶)`.

What this measures:
- The one admitted landing helped the encounter it was admitted for, and its classical gain was
  specific to the located World state. It vanished without that history, and by round 2 the
  learner's and twin's codes shared a cell.
- Later steps along the same kind of descent were refused, each typed. In rounds 1 and 2 the
  candidate improved nothing classical without worsening the phase excess.
- The admission did what it is for: no uncertified step entered.
- The loop's next subject is the refused phase. The descent is the total of series (5), so it trades
  phase against magnitude, and the admission refuses a phase loss. A descent of the classical part
  alone, or of the phase part at fixed code, is the separated step to measure next.

**Owed (#62).** The admission's soundness for a receiving face ratio read through a located key:
`HNN/FiniteDecrease.admission_sound` holds for the exact enclosures; that the key's prospect equals
the actual encounter is the C1b prospect law under its located point.

## 5a. The descent serves the admission's order

[definition; agent-inferred, October 9; the loop's measured refusals above] The admission is
lexicographic: a strict classical improvement with no worse phase excess, or (§5b) an exactly equal
code with a smaller excess. Per coordinate, the series (5) gives the classical gradient `g_L` (its
magnitude part) and the phase gradient `g_X` (its two phase parts). The descent in the admission's
order is the steepest classical descent that does not raise the phase at first order:

```text
d = −g_L                                    if ⟨g_L, g_X⟩ ≥ 0
d = −g_L + (⟨g_L, g_X⟩ / |g_X|²) g_X          otherwise                                       (6)
```

taken per family, exact and rational. Then `⟨g_X, d⟩ = 0` or `< 0`, and
`⟨g_L, d⟩ = −|g_L|² + ⟨g_L, g_X⟩²/|g_X|² ≤ 0`. Both hold per family, so they hold for any positive
per-family step, and the native law's exponents need not be known when the direction is chosen. A
family with `d = 0` contributes no step, and the admission, not the descent, decides
(`continuation::world_descent`). Owed (#62): (6) and its two inequalities.

[measured; the third admitted developer slot, local, not claim-bearing] Three descent laws were
measured on the fixture's loop of four encounters against the twin, all with the same admission
([receipt](receipts/2026-10-09-material-tangent/DESCENT_LAWS_DEV_TESTS.v1.json)):

| descent | landings admitted (rounds 0–3) | learner's code against the twin's | learner's excess − twin's |
|---|---|---|---|
| summed series (§5's first law), no witness | classical, then refused (phase worse twice, then equal endpoints) | strictly below in round 1, gap in `[2⁻⁸, 2⁻⁷)`; then equal | rounds 1 and 2 below, round 3 above |
| minimum-norm hull point of `{g_L, g_X}`, with the witness | phase, phase, refused (phase worse), phase | equal throughout | rounds 1 and 2 below; round 3 above, in `[2⁻¹⁹, 2⁻¹⁸)` |
| **(6), with the witness** | **phase in all four** | equal throughout | **below in rounds 1–3**, by amounts in `[2⁻¹⁵, 2⁻¹³)` |

The hull point is pulled toward the smaller gradient (here the phase gradient, at least 34 times
smaller than the magnitude part), which breaks the admission's order, so it is retired. Law (6)
admits every landing and never leaves the learner worse than its twin in the admission's order.
The summed law's single code gain came from a step whose phase trade carried the produced logits
across a code cell at the grain. Law (6), at the first reach of the *material* lattice, never
crossed one. **The next subject is the first reach at the receiver's grain:** the least step along
`d` at which a compared class's code cell changes, declared as the native first reach is declared
and admitted by the same law. With (6), the landing test's measured decision is `Phase`. The actual
next encounter reproduced the prospect exactly and was better than the matched control in the
admission's order (an equal code and a smaller excess). On a fresh World without the history, the
landed excess is lower by an amount in `[2⁻¹⁸, 2⁻¹⁷)` at an equal code.

## 5b. The witness of a receiving face ratio

[definition; agent-inferred, October 9] `ReceivingFaceRatio::code_length` reads only the produced
faces' grain and gauge-normalized cells `(n_c − n_max, k_c)` and the observed faces' odometer masses,
which a common carry shift leaves unchanged. So equal produced and observed grains and gauge cells at
every compared station give equal exact code expressions (`continuation::receiving_reading_identity`).
The observed phases are not code inputs; they move with the material (§3d) and are compared through
the excess. Identical enclosure endpoints alone never count. With this witness, `decide` admits a
strictly smaller excess at an exactly equal code (`Admitted::Phase`), as it already did for the
contact route's ratios (Lean `HNN/FiniteDecrease.witness_code_eq` covers the class-target form; the
soft-target form is owed to #62).

## 5c. The first reach at the receiver's grain

[definition; agent-inferred, October 9] The material's first reach is the least exponent at which a
factor's lattice cell moves. A classical improvement, though, needs the *receiver's* reading at its
grain to move. The landing therefore scans, and declares exactly one candidate:
1. From the material's first reach, every declared exponent is raised one dyadic step at a time
   (`DeclaredExponents::raised`).
2. Each raise is produced by the native declared-step law and read through the located key's
   prospect of the next encounter.
3. The scan stops at the first raise whose code inputs at the grain differ from the contemporary
   prospect's (`receiving_reading_identity` fails).
4. The scan ends when the producer refuses. Every stepping family must carry a positive covector
   scale, and `2^k c ≤ 1` bounds each family's exponent, so the scan is finite.
5. When the reading never moves first, the material first reach's candidate is declared.

`decide` reads only the declared candidate, so nothing is searched for an improvement: the first
movement is declared whether it is better or worse. `WorldLandingReading::grain_raise` reports the
raise.

[measured; developer reads under the common lease, not claim-bearing] The loop over six encounters
against its twin, with (6), the witness and the grain reach
([receipt](receipts/2026-10-09-material-tangent/GRAIN_REACH_DEV_TESTS.v1.json)):

| round | learner's code against the twin's | learner's excess − twin's | landing read after the round |
|---|---|---|---|
| 0 | equal | 0 | phase (the reading never moved) |
| 1 | equal | below, in `[2⁻¹⁵, 2⁻¹⁴)` | phase (never moved) |
| 2 | equal | below, in `[2⁻¹⁴, 2⁻¹³)` | refused, phase worse (moved at raise 6) |
| 3 | equal | below, in `[2⁻¹⁵, 2⁻¹⁴)` | **classical** (moved at raise 4) |
| 4 | **strictly below, gap in `[2⁻⁹, 2⁻⁸)`** | below, in `[2⁻¹⁴, 2⁻¹³)` | phase (never moved) |
| 5 | overlapping enclosures | below, in `[2⁻¹⁰, 2⁻⁹)` | refused, phase worse |

**On this fixture the loop learns from the World over six encounters, and wherever the comparison is
resolved it is never worse than its twin in the admission's order.** In round 5 the two code
enclosures overlap without being equal, so the classical comparison there is unresolved; only its
phase excess is lower. Four of six landings were admitted, three for the phase and one classical. The classical one produced a strict code gain at the next encounter. Every refusal is
typed, and no uncertified step entered. This is one fixture, one declared bank of contact factors and
one World. The queue's claim-bearing run, the cold restore, the two-observation delayed credit and any
second fixture remain.

## 5d. A second fixture

[measured; developer read under the common lease, not claim-bearing]
`the_world_loop_is_read_on_a_second_fixture`. The World medium has a non-uniform storage
(`diag(1, 2, 1, 3, 2, 1, 3, 1)`) and the native contact has different factors (storage `(3 + i)/4`
with upper `1/8`, stiffness `1/(1 + i)` with upper `1/16`, dissipation `1/4`). Both were declared
before any reading; the laws and the reading are the same as the first fixture's
([receipt](receipts/2026-10-09-material-tangent/SECOND_FIXTURE_DEV_TESTS.v1.json)):

| round | learner's code against the twin's | learner's excess − twin's | landing read after the round |
|---|---|---|---|
| 0 | equal | 0 | refused: code worse (the reading moved at raise 3) |
| 1 | equal | 0 | unreached: no family reached its lattice |
| 2 | equal | 0 | refused: phase worse |
| 3 | equal | 0 | refused: phase worse |
| 4 | equal | 0 | **classical** (moved at raise 3) |
| 5 | **strictly below, gap in `[2⁻¹⁰, 2⁻⁹)`** | below, in `[2⁻¹¹, 2⁻¹⁰)` | refused: equal endpoints (moved at raise 4) |

The grain reach declared a worse move in round 0 and the admission refused it, so the scan does not
select improvements. Here every round is resolved: the learner's code equals the twin's or lies strictly below it, and
it is never worse in the admission's order. As on the first fixture, its one classical landing gives
a strict code gain at the next encounter. Two
fixtures with one World law and one contact each remain a small sample.

## 5e. The landed material survives a cold restore

[measured; developer read under the common lease, not claim-bearing]
`the_landed_material_survives_a_cold_restore` covers acceptance (c)'s cold restore. A continued
state mounts only material on its loci's lattices, so this fixture declares dyadic contact factors.
The first fixture's `2/3` is off every dyadic lattice, and its cold mount refused with
"the state's material off its loci's lattices", a property of that declaration, not of the landing.
On the dyadic fixture:
1. The first teaching round's landing was admitted (phase).
2. The receiver's constitution and carry were saved as exact text (20807 bytes, a prime) and mounted
   on the declared founding, the material before any learning.
3. The restored material and carry equal the live ones exactly.
4. The World, exterior to the machine, was rebound by its owner at its live state; the World model
   was carried by value (its own save is owed).
5. The restored receiver's next encounter read the live one's comparison exactly: equal code
   enclosure and excess.

Run 00:26:53–00:26:57, exit 0
([receipt](receipts/2026-10-09-material-tangent/COLD_RESTORE_DEV_TESTS.v1.json)).

## 6. The tangent continues into the next encounter

[definition; agent-inferred, October 9] The stretch of §1 needs a credit that crosses encounters.
`MaterialTangent::continued` crosses a tangent's carry into the next opening by eq. (3),
`χ_open = Π_int B_ref χ_carry`. It keeps the World's state tangent `ψ` as it is, because the World's
state persists between encounters and steps only during them. `rebind` then ties the continued
tangent to the next Word, refusing unless the opening tick, the contact's executed forms and the
change's shape are all the same. The receiving publication between the encounters moves the commit,
never the contact. The receiving map is a readout, held as an exterior control that the tangent does
not differentiate (the learner's own deposit is not differentiated, as in
`ContactVariationAction`). `PreparedPhysicalProbe::encounter_continued` carries the continued
tangents through the next encounter's World port. Each tangent is also bound to its encounter's
applied source wave, so co-clock twins taught at different controls cannot swap tangents
(`co_clock_twins_cannot_swap_tangents`). **Provenance limit:** the binding does not carry the located
key's identity, so arbitrary-encounter provenance across receivers with different keys is not
certified (written beside `PhysicalReceiver::world_proposal`).

[measured; developer read under the common lease, not claim-bearing]
`the_tangent_continues_into_the_next_encounter`: after two encounters on `θ ± εH`, the World's
configuration and the native carry both confirm `ψ` and `χ` to second order on `ε = 2⁻⁴ … 2⁻⁸`. Each
halving divides the World residual and the carry residual by a ratio in `(63/16, 4)`. All nine World
tests pass (00:11:46–00:13:02, exit 0, child peak 2,028,788 KiB;
[receipt](receipts/2026-10-09-material-tangent/CONTINUED_DEV_TESTS.v1.json)). This is the derivative
the two-observation delayed credit consumes. Pairing it with the second encounter's comparison
(`comparison_credit` on the continued tangent) and landing on it are the next build.

