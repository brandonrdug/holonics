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
4. The World model's learned part, its tick and each key's state, was saved as its own exact text
   (491 bytes, a prime; `WorldModel::{to_text, restored}`) and restored on its declared keys, which
   are declarations and are not written. It equals the live memory. The World, exterior to the
   machine, was rebound by its owner at its live state.
5. The restored receiver's next encounter read the live one's comparison exactly: equal code
   enclosure and excess.

Runs 00:26:53–00:26:57 and, with the World model's text, 00:33:56–00:34:09, both exit 0
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


## 7. The credit of two observations, and its landing over both waves

[definition; agent-inferred, October 10; acceptance fixed before code] The stretch of §1 asked that the
first deposit change the second Ask. On this field that half stays reserved (§3c: the second Ask has
nothing dormant to partition). Its other half is measurable here: **learning across two observations
at different waves, landed as one step**. Two encounters run at the admitted waves `u₁ = 1`, then
`u₂ = −1`, with nothing landed between them. The second encounter carries the first's tangents,
continued (§6).

**The credit.** For each declared coordinate, the credit is `credit(T₁; r₁) + credit(T₂; r₂)`. Here
`T₁` is the first encounter's tangent with its comparison `r₁`, and `T₂` is the continued tangent with
the second comparison `r₂`, each at its own frozen covector. It is the derivative of the two
comparisons with the receiving relation each encounter publishes held as an exterior control: the
learner's own deposit is not differentiated (§6, as in `ContactVariationAction`). The second
comparison's produced logits read `R · P^τ v` through the relation the first encounter published, so
the end-to-end derivative also has a path through that deposit, which the credit does not carry.
Law (6) is applied to the summed credit per family.

**Acceptance.** On the published fixture (World, key, actuator, admitted lattice):
- **(a) The credit identity.** On `θ ± εH`, `ε = 2⁻⁴ … 2⁻⁸`, the observed-phase part of both
  observations is confirmed end to end to second order (it reads the World's face, not the receiving
  relation). The produced parts are confirmed by their composition: `χ` and `ψ` across two encounters
  to second order (§6), read through the station read at the held relation (§3d). The end-to-end
  central difference of the produced parts, which includes the receiving deposit's path, is reported
  beside them as measured, never as the credit.
- **(b) The binding is a chain.** A two-observation proposal is admitted only when:
  - each observation's tangents rode its own encounter;
  - consecutive encounters are consecutive on the Word and World clocks (the later opens where the
    earlier ended);
  - every later tangent is the earlier one continued (same direction, the same origin opening);
  - the receiver stands where the last encounter left it.
  Refused: the swapped order; fresh tangents at the second encounter in place of continued ones; a
  gap between the encounters.
- **(c) The landing over both waves.** One declared step along law (6) on the summed credit, staged
  where the last encounter left the receiver. The located key's prospect of the next encounter is read
  at each wave from the present opening. The grain scan raises until either prospect's reading moves.
  The step is admitted only when, at each wave, the decision is admitted or exactly unchanged (the
  witness with an equal excess), and at least one wave is admitted. The decision is reported as
  measured. When admitted, the actual next encounter at each wave, read on identical replays, equals
  its prospect exactly, and is read against the no-deposit twin at that wave.
- **(d) Against the continued credit alone.** The same chain is landed on the second observation's
  continued credit alone, and reported as measured beside (c).

Not claimed: selection (the first deposit does not change the second Ask on this field); the receiving
deposit's derivative; any provenance across receivers (§6's limit stands).

### 7a. Measured: the credit is exact; its step improves what it credits; the prospects refuse it

[measured; developer reads under the common lease, not claim-bearing; `tests/material_tangent_world.rs`]

**Built.**
- `MaterialTangent::origin` names the held opening a tangent started from, and every continuation
  keeps it.
- `world_descent` sums the observations' credits per coordinate before law (6).
- `PhysicalReceiver::world_proposal` binds a chain of observations. Its first observation's tangents
  share one origin at or before its own opening, so a continued tangent alone is the delayed credit
  of its encounter.
- `land_world_descent` reads the located key's prospect at each admitted wave and admits through
  `decide_over`.
- `WorldLandingReading` carries the declared candidate and one `WaveProspect` per wave.

**(b) The chain binds** (`a_two_observation_proposal_binds_a_chain`). The chain in its order is
admitted. The swapped order is refused, and so are fresh tangents at the second encounter. A
continued tangent offered across a gap is refused where it would ride: `rebind` admits only the
Word that opens on its carry.

**(a) The credit is exact** (`the_two_observation_credit_is_read_at_its_consumer`). All three parts are
confirmed to second order on `ε = 2⁻⁴ … 2⁻⁸`: magnitude, produced phase and observed phase, for both
observations together and for the continued credit alone. From `ε = 2⁻⁵` on, each halving divides
every residual by a ratio in `(63/16, 65/16)`. The acceptance required this only of the observed
phase. The produced parts hold too, and the reason was measured: the receiving relation the first
encounter publishes does not move. Its central change on `θ ± εH` is `1/64` at `ε = 2⁻⁴` and exactly
`0` from `2⁻⁵` on. (At `ε = 2⁻⁴` the relation's own step moves, and the first halving of the magnitude
residual is correspondingly larger than four.) The receiving deposit is a lattice step, locally constant in the material, so its
path contributes nothing at first order here. Holding it as an exterior control loses nothing on
this fixture; that is a measurement, not a law.

**(c), (d) The landings are refused** (`the_two_observation_landing_reads_both_waves`). Changes are
read on the located key's prospects from the present opening at `u = 1` and `u = −1`, and on the two
credited encounters re-entered from the initial material with only the candidate's contact factors:

| landing | grain raise | prospect `u = 1` | prospect `u = −1` | credited encounters |
|---|---|---|---|---|
| both observations | none moved the code inputs | code equal; excess up by `[2⁻¹⁸, 2⁻¹⁷)`: `PhaseWorse` | code equal; excess up by `[2⁻¹⁷, 2⁻¹⁶)`: `PhaseWorse` | codes equal; excess `−[2⁻¹⁶, 2⁻¹⁵)` and `+[2⁻¹⁴, 2⁻¹³)`, sum `+[2⁻¹⁵, 2⁻¹⁴)` |
| continued credit alone | 5 | code equal; excess up by `[2⁻¹², 2⁻¹¹)`: `PhaseWorse` | excess down by `[2⁻¹³, 2⁻¹²)`, but code up by `[2⁻¹⁰, 2⁻⁹)` at both endpoints: `CodeWorse` | both codes strictly lower, both excesses lower, sum `−[2⁻⁹, 2⁻⁸)` |

Neither landing is admitted, and nothing is published.

**The mechanism.**
- The continued credit's step does what a descent should: on the passages it credits, it lowers
  both the code and the phase excess.
- The admission does not read those passages. It reads the located key's prospect of the next
  encounter from the present opening, a different comparison, and there the same step is worse at
  both waves.
- The credit describes the experienced passages re-entered from their origin. The admitted future
  starts where the receiver now stands. On this field they disagree.
- With both observations, the summed step never moves the prospects' code inputs at the grain. Its
  phase change, zero at first order by law (6), is positive at second order at the lattice's first
  reach, on the credited passages and on both prospects alike.
- The single-observation landing of §5 agreed with its prospect on fixture 1. There the credited
  encounter and the prospect share a wave and nearly a state, so that agreement was a property of
  the fixture, not of the law.

**What it changes.**
- The admission must keep reading the future: re-entering the past from its origin would need the
  origin state retained, a frozen cut the retention law refuses.
- So the step should descend what the admission reads: the located key's prospect at each admitted
  wave, differentiated from the present opening. The opening's own tangent is the crossing at held
  momentum, `C′ w′ = π`, so `δw = −C⁻¹ δC w`. The tick law (§3e) carries it through the prospective
  Word, and the key's charts stand for the World (§3a).
- The key is located to a point, and its prospect equals the actual next comparison exactly (§5).
  That derivative is therefore the derivative of the actual next comparison.
- The experienced comparisons keep their role: they locate the key and publish the receiving
  relation and the carry. That is the next loop, recorded here before it is built.

All fourteen World tests pass: 01:42:54–01:43:53, exit 0, measured 58,474,035,026 ns against a
300 s projection ([receipt](receipts/2026-10-09-material-tangent/TWO_OBSERVATION_DEV_TESTS.v1.json)).

### 7b. The admitted future, descended: learning across two observations lands at both waves

[definition; agent-inferred, October 10] §7a's mechanism fixes the law: **the step descends the
comparisons the landing admits by.** The experienced encounters locate the World key and publish the
receiving relation and the carry. The material's step then descends the located key's prospect of the
next encounter at every admitted wave, from where the receiver now stands. Since the key is located
to a point, its prospect is the actual next comparison exactly (§5), so this is the derivative of the
next comparison itself. The experience is the condition of that derivative, and retention keeps no
past passage to re-enter (§7a).

**Built.**
- `Word::prospective_coupled_passage` takes a `PassageObserver`. It sees the Word after each step's
  return and before the next tick, where a consumer beside an actual encounter sees it.
- `WorldModel::located_prospect_with_tangents` runs the coupled passage from the key's located
  point. The material tangents ride it through the key's charts at the commits its returns read
  (`MaterialTangent::step_through_port`, §3a). Each is held at every compared station with the
  observed face's tangent through the key's declared face. This is the actual encounter's tangent law,
  with the key standing for the World in both. Stations are numbered as the prospect's comparison
  numbers them: by rank among the compared ones.
- `PhysicalReceiver::world_prospect_taught` returns the prospect's comparison and its tangents, which
  open held at the present opening (`χ₀ = 0`).
- `PhysicalReceiver::located_prospect` exposes the raw prospect behind `world_prospect_ratio`, and
  `prospect_ratio` holds the comparison they share.
- `PhysicalReceiver::world_prospect_proposal` sums the prospects' credits over the admitted waves and
  applies law (6) (`world_descent`). It is staged where the latest encounter left the receiver, with
  that encounter's reach, opening clock and normalization (`bound_proposal`, shared with
  `world_proposal`).
- The landing is unchanged: `land_world_descent` over both waves, `decide_over`.
- **Law (6) over several observations** (`common_descent` behind `world_descent`). The admission
  reads every wave's comparison on its own (`decide_over`). The step starts at `−Σ_o L_o` and is
  projected exactly off the span of every per-observation gradient it would raise at first order:
  classical ones first, then phase ones, one at a time, re-projecting until none is raised. With one
  observation this is law (6) exactly: `⟨L, −L⟩ ≤ 0` never violates, and `X` is projected off iff
  `⟨L, X⟩ < 0`. The single-observation loops read the same decisions round for round. §7a's
  landings were measured under the summed law (6) at `b38645c7`. Under the common descent, the
  experience-credit landing over both observations is still refused: `PhaseWorse` at both waves, the
  same as in §7a.

**Measured** ([developer reads, not claim-bearing](receipts/2026-10-09-material-tangent/PROSPECT_DEV_TESTS.v1.json)).
All sixteen World tests pass: 01:58:23–01:59:29, exit 0, measured 65,783,518,355 ns against a 300 s
projection.

- **The prospect's credit at its consumer** (`the_prospect_is_credited_at_its_consumer`). After the
  same two encounters, the prospect at each wave was taught along one storage direction. On
  `θ ± εH` (the present receiving relation kept), its three parts are confirmed to second order at
  both waves: from `ε = 2⁻⁵` on, each halving divides every residual by a ratio in `(63/16, 65/16)`.
  Two defects were found on the way, and both are recorded:
  - The station numbering. The prospect's comparison numbers stations by rank among the compared
    ones; the actual encounter's ratio uses the full index.
  - The opening term. Held at `χ₀ = 0`, the residuals stayed constant as `ε` halved, at about a
    quarter of the credit: a missing first-order term. The prospective Word opens on the actual carry
    crossed into the varied material at held momentum, `C′ w′ = π`, so a storage direction moves the
    opening rate by `C δw = −δC w` (`MaterialTangent::crossed_at_held_momentum`). The conductances
    are the rings', so the carried waves do not move. A continued tangent needs no such term: there
    the crossing joins the same material and is the identity.
- **The landing over both waves** (`the_prospect_landing_reads_both_waves`). The step was declared
  at grain raise 2 and **admitted**, `Classical`:

| wave | prospect: code | prospect: excess | decision | actual next, against the no-deposit twin |
|---|---|---|---|---|
| `u = 1` | equal (witnessed) | down by `[2⁻²⁰, 2⁻¹⁹)` | `Phase` | equal code; excess lower by `[2⁻²⁰, 2⁻¹⁹)` |
| `u = −1` | strictly below at both endpoints, by `[2⁻⁸, 2⁻⁷)` | down by `[2⁻¹³, 2⁻¹²)` | `Classical` | strictly lower code, gap `[2⁻⁸, 2⁻⁷)`; excess lower by `[2⁻¹³, 2⁻¹²)` |

The actual next encounter at each wave, read on identical replays, equals its prospect exactly. The
deposition work at the held-momentum crossing is positive, in `[2⁻⁴, 2⁻³)`.

**Two refusals on the way to this law.**
- With the exact credit and the summed law (6), wave `u = 1`'s excess rose by `[2⁻²⁰, 2⁻¹⁹)` while
  `u = −1` improved. The summed projection holds only the summed phase still at first order, and the
  admission reads each wave on its own. The common descent was derived from that admission.
- Before the opening term was added, the inexact credit's step was also admitted. That result is not
  counted: its credit had failed its own consumer identity.

**What this establishes, and what it does not.**
- On this fixture, learning across two observations at different waves lands as one certified step.
  The experience locates the key, and the step descends the located key's prospects of the next
  encounter at both waves. The changed material answers better at both, against the no-deposit twin.
  This is §1's stretch with its selection half reserved (§3c).
- The prospect is exact here because the key's fibre is a point. With a plural fibre, a prospect is
  a family and this derivative is not defined; that case is refused, not approximated.
- One fixture and one round. A loop of such landings and a second fixture are the next measurement.

### 7c. The controls, and the loop: one step improves its own next encounter, not the trajectory

[measured; developer reads, not claim-bearing;
[receipt](receipts/2026-10-09-material-tangent/PROSPECT_LOOP_DEV_TESTS.v1.json)] Epime's review of
`324f6138` kept §7b's claim narrow: one admitted step after two observed waves, with no no-history
control, which does not show that both observations are needed. The landing test now asserts the
admission and the per-wave production against the twin in the admission's order, so a refusal fails
it. The controls:

- **One observation is enough** (`the_prospect_landing_after_one_observation`). After the first
  encounter alone (`u = 1`), the prospect landing is admitted, `Classical` at grain raise 0:
  - `u = 1`: code strictly lower by `[2⁻⁸, 2⁻⁷)`, excess lower by `[2⁻¹⁴, 2⁻¹³)`;
  - `u = −1`: `Phase`, excess lower by `[2⁻¹⁶, 2⁻¹⁵)` at equal code.

  The step descends the future from the present opening, so the experience matters here only by
  locating the key. The second observation is not necessary on this fixture.
- **Without its history** (`the_prospect_landed_material_is_read_without_its_history`). The
  contemporary material and the landed one were each read on a fresh World with no earlier encounter,
  at both waves. At `u = 1` the landed material is **worse**: equal code, excess higher by
  `[2⁻¹⁵, 2⁻¹⁴)`. At `u = −1` it is better: equal code, excess lower by `[2⁻¹², 2⁻¹¹)`. The gain
  belongs to the state the receiver stands in, as a descent of that state's future would.
- **The loop against its twin** (`the_prospect_loop_is_read_against_its_twin`, `…_on_a_second_fixture`).
  Five rounds per fixture. A round is the two chain encounters and the prospect landing; the twin runs
  the same encounters with no landing. Below, each round's encounters are learner against twin in the
  admission's order. "Better" means a strictly lower code with no higher excess, or an equal code with
  a lower excess.

| round | fixture 1, `u = 1` | fixture 1, `u = −1` | its landing | fixture 2, `u = 1` | fixture 2, `u = −1` | its landing |
|---|---|---|---|---|---|---|
| 0 | equal | equal | Classical (raise 2) | equal | equal | Phase |
| 1 | better (excess `−[2⁻²⁰, 2⁻¹⁹)`) | code lower `[2⁻¹⁰, 2⁻⁹)`, excess higher `[2⁻¹⁰, 2⁻⁹)` | Classical (raise 5) | better (`−[2⁻¹⁷, 2⁻¹⁶)`) | better (`−[2⁻¹⁷, 2⁻¹⁶)`) | PhaseWorse |
| 2 | code **above** by `[2⁻⁸, 2⁻⁷)`, excess lower | overlap, excess higher `[2⁻⁷, 2⁻⁶)` | Phase | worse (`+[2⁻¹⁴, 2⁻¹³)`) | better (`−[2⁻¹⁵, 2⁻¹⁴)`) | Classical (raise 4) |
| 3 | worse (`+[2⁻¹¹, 2⁻¹⁰)`) | overlap, excess higher | Phase | code lower `[2⁻¹⁰, 2⁻⁹)`, excess higher | better (`−[2⁻¹⁰, 2⁻⁹)`) | PhaseWorse |
| 4 | overlap, excess higher `[2⁻¹⁰, 2⁻⁹)` | code lower `[2⁻¹⁰, 2⁻⁹)`, excess higher | PhaseWorse | worse (`+[2⁻¹¹, 2⁻¹⁰)`) | code **above** by `[2⁻¹¹, 2⁻¹⁰)`, excess lower | PhaseWorse |

**The mechanism.**
- Every admitted landing improves the learner's next encounter against **its own** no-landing
  counterfactual, which is exactly what it was admitted on. The improvement is checked: the actual
  next comparison equals the prospect.
- Against the never-landing twin, the trajectory is mixed and is not dominated. On fixture 1 the
  learner's code at `u = 1` is strictly above the twin's by round 2.
- Two causes are named, and neither is a defect of the step:
  1. **The schedule.** The prospect at `u = −1` assumes that wave is next, but the round runs `u = 1`
     first, so the second wave's admitted future is not the one the round reads.
  2. **The horizon.** The admission sees one encounter ahead. A step that helps the next encounter can
     cost later ones, and the twin comparison accumulates those costs.
- One-step admissions do not compose into a trajectory gain. That is the measured blocker.

**The next law** (agent-inferred, recorded before it is built). The admitted future is the schedule
the receiver will actually follow: the round's encounters in order, read as one chained prospect. The
second encounter's prospect is read from the first's prospective end, with the tangents continued
across it. The horizon is a declared number of rounds of that schedule, and the step descends their
summed comparisons with the common descent. The twin comparison over rounds stays the production
measure.

**Projection error.** The first loop run reached its 300 s deadline at about 33 s per round, against
a projected 5 s. It is reported incomplete. The deadline was not raised; the loop was split per
fixture, and the two halves ran in parallel within it.

### 7d. The horizon, not the schedule: the material is admitted on its cycle

[measured; developer reads, not claim-bearing;
[receipt](receipts/2026-10-09-material-tangent/PER_ENCOUNTER_LOOP_DEV_TESTS.v1.json)]
`per_encounter_loop` removes the schedule mismatch of §7c. Before every encounter after the first, it
lands on the prospect of that very encounter, the one that comes next. Over ten encounters
alternating `u = 1, −1` on both fixtures, against the twin:
- Fixture 1: the learner is better at encounters 1 and 4. It is **worse** (equal code, higher excess)
  at encounters 2, 3, 6, 7 and 8, most of them right after an admitted `Phase` landing. Encounter 5 is
  unresolved, and encounter 9 has a lower code with a higher excess.
- Fixture 2: better at encounters 2, 3, 5, 7 and 9, worse at 4 and 8, a lower code with a higher
  excess at 6, and equal at 1.

Some landings are refused or unreached: `EqualEndpoints`, `PhaseWorse`, and an unreached
`CovectorScale`.

Each admitted landing improves the next encounter against the learner's own no-landing
counterfactual, and the actual next comparison is that prospect. With the schedule matched, the
trajectory against the never-landing twin is still mixed, so the cause is the **horizon**. The
material persists into every later encounter. A step judged on the next encounter alone reshapes the
transient it leaves behind, and later encounters pay for it.

**The next law** (agent-inferred, recorded before it is built; it replaces §7c's "declared number of
rounds").
- The schedule repeated is a **cycle**: a closed loop whose reading is completeness, not duration
  (the [aeon, epoch and cycle record](2026-09-24_THE_AEON_EPOCH_AND_CYCLE_STANDARDIZE_THE_PASSAGE_OF_TIME.md)).
- With the key located, one round of the schedule is an affine map of the joint state (the native
  carry and the World key's state), `x ↦ M x + c`. Each prospective passage is exactly linear in its
  opening and its returns, and the key's charts are affine.
- Its closed orbit is the exact fixed point `x* = (I − M)⁻¹ c` wherever `1` is not an eigenvalue of
  `M`. It depends on the material alone, not on the transient state the receiver stands in.
- The material is admitted on the comparisons read on that orbit, and the step descends them. The
  orbit's tangent is `(I − M) δx* = δM x* + δc` (the implicit function law). It reuses the prospect's
  tangent law (§7b) with the opening at `x*`.
- An admitted step then never worsens the cycle's own reading. Successive admissions are monotone on
  it, and a trajectory that converges to the orbit inherits the gain. The twin's orbit is the first
  material's.
- Refused when `1` is an eigenvalue of `M` (no unique closed orbit). Convergence to the orbit is a
  property of the dissipation, to be read from `M`'s spectrum, not assumed.

### 7e. The readings recur once the receiving relation stops moving

[measured; developer reads, not claim-bearing;
[receipt](receipts/2026-10-09-material-tangent/PASSAGE_DEV_TESTS.v1.json)] The cycle law of §7d
assumes an orbit exists, so two reads were made before it was built.

- **The receiving relation learns at nearly every encounter at first** (`the_receiving_relation_between_encounters`).
  Over ten plain encounters alternating `u = 1, −1`, the receiving publication moved `R` at every
  encounter on fixture 1, and at nine of ten on fixture 2 (all but the last). The never-landing twin
  is therefore not a still learner: its readout learns as the learner's does. The comparisons of
  §7c and §7d are small material effects (`[2⁻²⁰, 2⁻¹¹)`) on a common drift that is larger: the
  excess rose by up to `[2⁻⁶, 2⁻⁵)` between repeats of a wave, for learner and twin alike.
- **Then it stops moving, and the readings recur** (`the_passage_over_forty_encounters`, fixture 1).
  This is finite measured recurrence at the receiver's grain, not an exact state periodicity, an
  indefinite settlement of `R` or a certificate of convergence (Epime's precision).
  - `R` moves at encounters 0 to 9 and at none of encounters 10 to 39.
  - From about encounter 23 on, the exact code enclosures repeat two apart, and the excess's dyadic
    brackets recur: at `u = 1`, excess in `[2⁻⁷, 2⁻⁶)`; at `u = −1`, in `[2⁻⁶, 2⁻⁵)`. The exact
    rational excesses still change two apart (Epime's precision). Only the brackets recur, not the
    complete exact receipt.
  - The recurring readings are **worse** than the opening: the excess began at `[2⁻⁹, 2⁻⁸)` and
    `[2⁻⁷, 2⁻⁶)`.

**What it means for the law.**
- While `R` does not move, the joint native and World passage under the repeated schedule is the
  affine round map of §7d. The readings recur at the grain on this fixture. An exact closed orbit
  still needs its own owner: `I − M` invertible on its stated domain, the admitted future including
  any receiving deposits, and no convergence claimed beyond what is measured.
- Before settlement, `R`'s deposits are lattice steps driven by each comparison. They are part of
  the admitted future, and a prospect that holds `R` fixed is exact only once `R` no longer moves.
- The recurring readings being worse than the opening is the plainest target the loop has had.
- The forty-encounter read held the common lease for 136.75 s while the queue waited to launch.
  Developer reads that long are scheduled between the queue's runs, not across them.

### 7f. The schedule's chained prospect: exact after the receiving relation stops moving

[definition; agent-inferred, October 10] The admitted future of a schedule is its encounters in
order. `PhysicalReceiver::world_prospect_schedule` builds it:
- Each prospective encounter opens on the previous one's prospective end carry. `CoupledPassage::end`
  is the Word's `reception_end`; `action_opening_on` opens on a declared carry.
- The key continues from its prospective end state at the clock its passage reached
  (`WorldModel::located_passage_with_tangents`, `coupled_at`).
- The tangents open at the present opening and are continued across every later opening (eq. 3,
  `MaterialTangent::continued`, `rebind`). The material is the same on both sides of those
  crossings.
- Each encounter returns its comparison, its tangents and its raw prospect (`ScheduledProspect`).
  `world_prospect_taught` is the schedule of one encounter.
- `world_schedule_proposal` descends every encounter's credit with the common descent.
- `land_world_descent_on` admits on a declared `AdmittedFuture`: independent waves from the present
  opening (§7b), or the schedule. `land_world_descent` is its waves case.

The receiving relation is the material's own throughout. That is exact while `R` does not move, and
it is not a prediction of `R`'s deposits.

[measured; developer reads, not claim-bearing;
[receipt](receipts/2026-10-09-material-tangent/SCHEDULE_DEV_TESTS.v1.json)]
- **The chained prospect is the actual schedule once `R` stops moving**
  (`the_schedule_prospect_is_the_actual_schedule`). After twelve encounters, both encounters of the
  next round (`u = 1`, then `u = −1`) equal their prospects exactly, in code enclosure and excess.
  After two encounters, while `R` still moves, the first equals its prospect and the second does not.
- **The schedule's credit is exact at its consumer** (`the_schedule_is_credited_at_its_consumer`). The
  two encounters' credits along one storage direction, summed, are confirmed to second order on
  `θ ± εH` (the present `R` kept), `ε = 2⁻⁴ … 2⁻⁸`.
- **The one-round schedule loop** (`the_schedule_loop_is_read_against_its_twin`, `…_on_a_second_fixture`;
  learner and twin each start after twelve encounters):
  - On fixture 1, every landing is unreached (`NoReach`: no family reaches its lattice), so learner
    and twin read identically.
  - On fixture 2, round 0's landing is admitted (`Phase` at both encounters) and improves both of
    them against the twin: excess lower by `[2⁻¹⁵, 2⁻¹⁴)` and `[2⁻¹², 2⁻¹¹)`. In every later round,
    `u = 1` is worse than the twin (excess higher by `[2⁻¹⁵, 2⁻¹²)`), and `u = −1` is better or has a
    higher code with a lower excess. The landings of rounds 1 to 3 are refused (`PhaseWorse`).

**What it shows.** A one-round horizon fixes the schedule mismatch and keeps the horizon effect: a
step admitted on its own round costs the rounds after it. The cycle owner of §7d stays the next law,
with Epime's conditions:
- `I − M` invertible on a stated domain;
- the admitted future including any receiving deposits, or restricted to where `R` does not move;
- no convergence claimed beyond what is measured.

### 7g. The cycle of the schedule: an exact closed orbit, its credit, and where the passage goes

[definition; agent-inferred, October 10] `hnn::physical::action::cycle` builds §7d's law on §7f's
schedule run (`round_from`).
- **The round map.** One run of the repeated schedule is affine in the joint opening state
  `x = (χ, ξ)`: the native opening change, flattened, and the key's state.
- **`M`.** Its columns are state tangents (`MaterialTangent::state_seed`: `χ₀ = eᵢ` or `ψ₀ = eⱼ`, no
  material term) ridden through one run, each read at the next opening (eq. 3) and in the World's
  state.
- **The closed orbit** is `x* = x_p + (I − M)⁻¹ (F(x_p) − x_p)`. It is opened by a carry whose crossing
  into the same material is the identity (`π_a = C_a w_a`).
- **Its credit along a material direction** is `credit(T_H; r_e) + Σᵢ (δx*)ᵢ credit(Sᵢ; r_e)` with
  `(I − M) δx* = δF`. The tangents are linear in their opening, so this combination is exact.
- **The descent from these credits** is `descent_from_credits`, the common descent on credits
  already formed. `world_descent` is now its tangents case.
- `world_cycle_proposal` and `AdmittedFuture::Cycle` admit on the orbit's encounters.

**Checked, each a refusal when it fails:**
- the key's charts recur one run later;
- the pump phases recur at the next opening;
- `I − M` is invertible;
- the opening on `x*` is exactly `x*`;
- the run from `x*` returns to `x*` exactly;
- its state tangents give the same `M`.

**Not claimed:** convergence of the actual passage (the spectrum of `M` is not certified), or
anything about `R`'s deposits. The cycle holds the receiving material fixed. It is the fixed-`R`
orbit.

[measured; developer reads, not claim-bearing;
[receipt](receipts/2026-10-09-material-tangent/CYCLE_DEV_TESTS.v1.json)]
- **The cycle closes and its credit is exact** (`the_cycle_closes_and_is_credited_at_its_consumer`,
  fixture 1, after twelve encounters). The round map's dimension is 40, and every check passes. The
  orbit's encounters read code within `2⁻⁹⁶` of `1` at both waves (one enclosure), with excess in
  `[2⁻⁷, 2⁻⁶)` at `u = 1` and `[2⁻⁶, 2⁻⁵)` at `u = −1`. Along one storage direction the orbit's
  classical credit is exactly `0`, and its phase credit is confirmed to second order on `θ ± εH`: from
  `ε = 2⁻⁵` on, each halving divides the residual by a ratio in `(63/16, 65/16)`.
- **The orbit is where the passage goes** (`the_cycle_is_where_the_passage_goes`). The orbit computed
  after encounter 12 was compared with the actual readings of encounters 38 and 39 of the same
  passage, with no landing. The code enclosures are equal at both. The excesses lie in the orbit's
  brackets and are still approaching them: actual minus orbit is `−[2⁻¹⁵, 2⁻¹⁴)` at `u = 1` and
  `−[2⁻¹⁰, 2⁻⁹)` at `u = −1`. Over these encounters the exact closed orbit of the fixed-`R` schedule is
  where the passage's readings go. That is a measurement on one fixture, not a convergence
  certificate.

**The next source issue** (Epime's review, October 10). The schedule run, and the cycle on it, carry
one immutable material. The actual execution constructs the observed receiving return, deposits it,
and publishes the receiving material before the next encounter. The after-2 mismatch of §7f measures
exactly that omission. The prospective run must join the existing receiving publication and its
retained update state. Alternatively, a fixed-receiving admitted future must be made enforceable. A
longer horizon does not repair it.

### 7h. The receiving publication joined, and the fixed-readout cycle

[definition; agent-inferred, October 10; Epime's review d79924aa] The schedule run now makes the
receiving publication between its encounters the way the actual execution makes it:
- `Word::prospective_coupled_passage` returns its own Word, keeping the source binding;
- the observed receiving return is formed from that Word against the key's predicted faces
  (`return_observed_receiving`);
- the deposit is published on the material the next encounter opens and reads on.

It is an observer translation: no producing propagation or power form changes.

[measured; developer reads, not claim-bearing]
- **The mismatch closes.** After two encounters, while `R` still moves, the chained prospect now
  equals both actual encounters exactly. Before the join, the second differed (§7f).
- **The retained state never stands still.** One actual encounter's publication was diffed after 12
  and after 30 encounters. The receiving relation's Gram statistics grow at every encounter, and its
  solved chart's exponent rises by one at each (28 to 29 at encounter 12; 46 to 47 at 30), while the
  readout `R` stays fixed at the grain. A cycle that required the whole material unchanged refused, as
  it should. The exact cycle is therefore the **fixed-readout** cycle:
  - the run from `x_p` and the orbit's run must leave `R`, its carrier and every contact factor
    unchanged;
  - the accumulating statistics are not claimed still;
  - a deposit that moves `R` ends the cycle.
  With that check, the cycle closes on fixture 1 after 12 encounters, and its credit is still second
  order.

### 7i. One cycle landing, then the trajectory: the descent's next term, and the normalization it lacks

[measured; developer reads, not claim-bearing] `cycle_trajectory`: learner and twin each run twelve
encounters; the learner lands once on `AdmittedFuture::Cycle`; then both run fourteen rounds with no
further landing.
- **Fixture 2:** refused. `R` still moves during the round after twelve encounters (its readout
  check). This test reached its 300 s deadline after 12 of 14 rounds and is reported incomplete.
- **Fixture 1, under law (6) as it stood:** unreached (`NoReach`). On the orbit the classical credit
  is exactly zero. Law (6) only descends the classical part, holding phase as a constraint, so the
  step is zero. Learner and twin read identically for all fourteen rounds.

[definition; agent-inferred] **The descent is lexicographic, like the admission.** When the classical
start projects to zero, `common_descent` takes the next term, `−Σ_o X_o`, projected the same way, with
every classical and phase gradient still a constraint. With a classical gradient present, nothing
changes.

[measured] Under the lexicographic descent, fixture 1's cycle step exists. The landing then refuses
it: *a World landing's families carry a positive covector scale, which bounds their step*. Each
step's normalization (its `FactorStep` energy and covector scale) is read from the encounter's own
classical contact return, and on the orbit that covector scale is zero. Learner and twin again read
identically.

**The blocker, by its measurement.** On fixture 1's orbit the code is flat at the grain, and the phase
excess is the objective left: it is worse on the orbit than at the opening (§7e). The step that would
descend it has no declared normalization, because the normalization is classical. The next source
issue is a phase step's normalization: the bound `2^k c ≤ 1` read on the phase part of the reached
covector. It must be derived from the declared normalization's own law (`FactorStep`, record §5c),
not chosen.

**The regression under the lexicographic descent** (all World tests but the fixture-2 trajectory run
in parallel, 03:09:34–03:15:52, measured 377,987,199,462 ns against a 450 s deadline projected from the
measured per-test maxima). Thirty tests passed and one failed: the fixture-1 schedule loop, whose
landing now returns the same covector-scale refusal as an error where the test unwrapped it. The test
now reports it. Exactly one earlier reading changed: the fixture-2 single-observation loop at round 1
went from `unreached NoReach` to `PhaseWorse` at grain raise 5. A step now exists and is refused, so no
landing is admitted either way. Every other loop decision is identical.

Receipt for §7h and §7i: [CYCLE_TRAJECTORY_DEV_TESTS](receipts/2026-10-09-material-tangent/CYCLE_TRAJECTORY_DEV_TESTS.v1.json) (developer reads, not claim-bearing).

**Where the zero scale comes from** (source-inspected, `word/action_return.rs`,
`return_observed_receiving`). The held contact steps that normalize a World-sensitive descent are
the composed return of the comparison's covector, pulled back through the native readout
(`pull_back_full` through `R`, then `reference::compose_return`). The World-sensitive credit reaches the
material by two paths: the produced read through `R`, and the observed face through the World's
state (§3d). The held return sees only the first. On fixture 1's orbit that native pullback vanishes,
so `c = max_t |g_t|_∞` is zero, while the face path still carries the gradient. The normalization the
step needs is the scale of the covector arriving at the family through **both** paths. With forward
tangents only, that covector is not formed. Deriving it, by an adjoint through the World port or by
a bound read from the tangents, is the next source issue. The step size is never chosen in its place.

### 7j. The adjoint through the World port (acceptance fixed before code)

[definition; agent-inferred, October 10] The native reverse sweep (`port::reverse_core_joined`)
treats each actual source return as exterior. At every tick with a return it zeroes the covector on
the overwritten source storage, with the note *no World adjoint … is inferred*. The World-sensitive
step needs the covector that reaches each family through both paths (§7i), so the sweep gains the
World port through the located key's charts at the commits the returns read. The forward tick is
§3a's:

```text
a_t = s_r(t)                  the source ring's storage after the native tick (the emitted wave)
ξ_(t+1) = F_t ξ_t + G_t a_t   the World's state           b_t = P_t ξ_t + Q_t a_t   overwrites s_r(t)
f_j = H ξ_(t_j + 1)           the key's declared face, read after the step at each compared station j
```

Its transpose, swept backward with `λ_b` the covector the sweep holds on the overwritten storage and
`μ` the World's covector (zero after the last tick):

```text
μ̃_(t+1) = μ_(t+1) + Hᵀ φ_j                           (φ_j the observed face's covector at station j, read after step t)
s̄_r(t)  = Q_tᵀ λ_b(t) + G_tᵀ μ̃_(t+1)                 replaces the zeroing; then the native tick's transpose as now
μ_t      = F_tᵀ μ̃_(t+1) + P_tᵀ λ_b(t)
```

(Corrected October 10 on Codex's source review: the face reads `ξ_(t_j + 1)`, so its covector joins
`μ_(t+1)` before the `G` and `F` transposes, as the implementation does; the first printing added it
after `Fᵀ`.)

The observed face's covector is the comparison's own: `φ_j = −Im g_j` on the imaginary logit
entries (series (5)'s observed phase, with its sign), and `0` on the real ones.

**Acceptance, fixed before code:**
- **(a) The consumer identity.** For every declared contact coordinate, the adjoint's pairing with the
  coordinate's forcing equals the forward tangent's comparison credit exactly, magnitude plus both
  phase parts, on the published fixture after twelve encounters, at the present opening and at the
  cycle's orbit. Exact equality, not a ladder.
- **(b) The normalization.** The covector scale `c = max_t |g_t|_∞` read from the World-sensitive
  return is positive on fixture 1's orbit, where the native-only return's is zero (§7i).
- **(c) The landing, reported as measured.** With that normalization, the cycle landing on fixture 1,
  then the fourteen-round trajectory against the twin.

The World adjoint is the key's, and exact only where the key is located to a point (§3a). The
native-only return stays the exterior-return law wherever no key is located.

**Built (§7j).**
- `port::WorldPort` (the source ring, the key's charts per tick, the face's linear part `H`) forms the
  `WorldAdjoint` from a comparison's covector.
- `reverse_core_joined` carries the World's covector across every source return in place of zeroing
  it.
- `Word::pull_back_world` is the return through both paths.
- `return_observed_receiving` takes an optional port. It runs the World sweep beside the native one,
  so the receiving deposit stays the actual execution's, and returns `world_contacts`.
- The schedule run builds the port for each prospective encounter. `ScheduledProspect::world_contacts`
  holds the result, and the cycle proposal normalizes with it: per contact family, energies summed and
  the largest covector scale.
- Actual execution passes no port and is unchanged.

[measured; developer reads, not claim-bearing;
[receipt](receipts/2026-10-09-material-tangent/WORLD_ADJOINT_DEV_TESTS.v1.json)]
- **(a) The consumer identity** (`the_world_return_is_the_tangents_credit`, fixture 1, the next
  encounter's prospect after twelve encounters).
  - For all 32 stiffness and dissipation coordinates, the World return's gradient entry equals
    **exactly −1 times** the forward tangent's whole credit.
  - The native part of every credit (magnitude plus produced phase) is exactly `0` at this state:
    the whole gradient runs through the World's face. That is why the native-only normalization was
    zero (§7i).
  - For the 16 storage coordinates the ratio is not `−1`. The forward storage tangent also carries the
    held-momentum crossing at the opening (`C δw = −δC w`, §7b), which the within-Word sweep does not
    include. That identity is owed through the sweep's opening covector. (a) holds for stiffness and
    dissipation, and is open for storage.
- **(b) The normalization is positive.** With the World-sensitive steps, fixture 1's cycle landing
  reaches a declared step (first reach at exponent 7, grain raise 0) where the native-only steps
  refused.
- **(c) The landing on the orbit.** The step improves the orbit's second encounter (excess down by
  `[2⁻⁷, 2⁻⁶)`) and worsens its first (up by `[2⁻¹⁰, 2⁻⁹)`): refused, `PhaseWorse`. Learner and twin
  read identically. This run reached its 300 s deadline after round 13 of 14 and is reported
  incomplete.

### 7k. The phase level's common descent, and the trade-off at the material grain

[definition; agent-inferred, October 10] The phase stage of §7i projected the summed phase gradient
off any wave's phase gradient it would raise. That holds the projected wave's first-order change at
zero, so curvature then raises it, and the admission refuses: (c) above. Within one lexicographic
level the admission reads every wave on its own. The step should therefore be a **strict common
descent**, the negated minimum-norm point of the waves' phase gradients' convex hull (two observations
here, exact: `λ = clamp(⟨b − a, b⟩/|b − a|², 0, 1)`). It lowers every wave's phase at first order. This
is not the retired min-norm hull of §5a, which mixed the classical and phase levels and broke their
order. This one stays within the phase level, and the classical gradients remain constraints.

[measured] Under it, fixture 1's cycle landing is **unreached**: `CovectorScale` for the stiffness
family at exponent 8. On the orbit the two waves' phase gradients nearly oppose, so their common
strict descent is small. Reaching one lattice unit of material along it would need a step beyond
the certified bound `2^k c ≤ 1`. Learner and twin read identically for the eight declared rounds; the
read was cut from 14 rounds to 8 on the measured rate, not by raising the deadline.

**The blocker, by its measurement.** On fixture 1's fixed-readout orbit the two waves trade phase
against each other. At the material's lattice, no admitted step lowers both. The material's grain,
not the descent, now bounds the cycle on this fixture. Not yet read: the second fixture's cycle,
which needs more encounters before its readout stops moving, and the storage identity.

**The second fixture's readout does not stop** ([receipt](receipts/2026-10-09-material-tangent/SECOND_PASSAGE_DEV_TESTS.v1.json),
`the_second_passage_over_forty_encounters`). Over forty plain encounters alternating `u = 1, −1`,
`R` moved at encounters 0–8, 11, 13, 17–19, 23, 26, 27, 29, 31, 33, 35, 37 and 39: from encounter 29
on, at every `u = −1` encounter. No fixed-readout cycle exists on this fixture in this window, and the
cycle owner's refusal there is the law working. A cycle on it would have to be the joint cycle, with
`R`'s deposits part of the orbit, and only if `R` itself recurs, which forty encounters do not show.


### 7l. The storage identity, the boundary's normalization, and the readout at every publication

[definition; agent-inferred, October 10] §7j left storage owed: the forward tangent moves the opening
rate with the storage (`C_a δw_a = −δC w_a`, the held-momentum crossing of §7b), while the World
return started from a fixed opening and discarded its opening covector. The crossing is itself a
storage solve, so its adjoint is a solve's. With `ū_a` the return's opening covector on contact `a`'s
rate and `C_aᵀ z = ū_a`, the full credit is the within-Word credit plus the opening pairing, and the
storage covector gains `∂ℓ/∂C = −z w_aᵀ`. That is the storage tick term `2 r̄ (w − ω)ᵀ` of
`compose_contact` at `r̄ = −z/2`, `w = w_a`, `ω = 0`. It enters the storage family alone and is pulled
onto the factor as the ticks' terms are (`hnn::port::opening_crossings`,
`hnn::reference::join_crossing`).

- **The same solve law.** The crossing's own solve (`held_rate`) fixes `w` only modulo `ker C_a`, which
  no later tick reads, since the transit reads `w` only through `C w`. Hence `ū_a ∈ range C_aᵀ`, and
  `z` is any point of its fibre: `ker C_aᵀ` pairs to zero with every admitted target
  `−δC w_a ∈ range C_a`. A covector off that range, or a target off `range C_a`, is refused
  (`HeldMomentum`), exactly where the crossing refuses a momentum. No inverse is assumed.
- **Its own normalization.** The enlarged return is not certified by the within-Word energy and
  covector scale. Its bound is the existing owner's law for an opening's dual, the reached-contact
  metric of `hnn::word::variation`: the storage step's energy gains the opening columns' squared norm
  in the native wave chart (`Σ_c |δw_c / G_a|²`, one column per raw storage coordinate), and its
  covector ceiling gains the opening dual's l1 bound in that chart (`Σ |ū_a|·G_a`), read on the
  columns' support (the contact's opening rate, the only part of the opening a storage direction
  moves). Stiffness and dissipation move nothing at the opening, so their steps keep their
  within-Word metric.
- **The readout at every publication.** The fixed-readout cycle (§7h) compared only each run's end
  material with its start. Equal ends do not certify that `R` stayed fixed within the run. Each run
  now reads every receiving publication against the material it was deposited on
  (`ScheduleRound::readout_fixed`), and the cycle refuses unless all of them leave the readout
  unchanged.

**Scope (Codex's review).**
- The 48-entry identity is the next encounter's return at the present opening.
- The cycle's credit (§7g) adds the implicit orbit shift `(I − M)⁻¹ δF`, and the cycle's
  World-sensitive normalization (§7j) is formed from per-encounter sweeps whose terminal World
  covector is zero. That normalization is therefore a per-encounter bound, not yet the adjoint of
  the cycle credit. Joining the orbit shift (the native and World boundary duals carried across the
  round) or deriving its bound is owed before a cycle landing's step is claimed certified. The cycle
  landing is unreached (§7k), so no claim rests on it now.
- The receiving tangents hold `R` exterior (`MaterialTangent::rebind`). The forward prediction with a
  moving `R` is exact (§7h), and its derivative remains conditional on a locally fixed receiving
  publication.

**Acceptance, fixed before the run.** `the_world_return_is_the_tangents_credit` asserts, for all 48
raw coordinates of contact 0 (16 per family) after twelve encounters, that the World return's
gradient entry is exactly −1 times the forward tangent's whole credit.

[measured] **The acceptance passes** ([receipt](receipts/2026-10-09-material-tangent/STORAGE_IDENTITY_DEV_TESTS.v1.json)).
For all 48 coordinates, the gradient entry is exactly −1 times the whole credit. The 16 storage
coordinates, which §7j left apart by the opening term, now meet it as well. Taken before the
restructuring above (then the crossing term rode one extra transit tick, sharing its covector scale
with all three families), with the same gradient.

[measured] **At the restructured source** ([receipt](receipts/2026-10-09-material-tangent/FULL_SUITE_CROSSING.v1.json)):
33 of 33 pass (one filtered, the second fixture's cycle trajectory, which reached its deadline in
§7i). The 48 ratios are exactly −1. Against the whole suite at `deb51f40`
([receipt](receipts/2026-10-09-material-tangent/FULL_SUITE_deb51f40.v1.json), 33 of 33), only the 16
storage lines of the identity test changed. Every other printed reading is identical, including
fixture 1's cycle landing: unreached, `CovectorScale` for stiffness at exponent 8. The crossing
enlarges the storage family alone, and no landing decision moved. An intermediate run of the
superseded structure was stopped by hand at 31 of 33 (none failed), and the receipt names it.

### 7m. The blocker, classified: lattice reach, incompatible directions, or omitted coupling

[definition; agent-inferred, October 10] Codex asked that the next progress tell §7k's refusal apart
by its actual source, with the objective and its comparisons fixed. The three are distinct and
exactly readable on fixture 1's orbit after twelve encounters, per contact family, from the orbit
credits already formed (`the_cycle_blocker_is_classified`; nothing is stepped):

- **Incompatible directions.** The two orbit encounters' phase gradients `a`, `b` over the family's
  raw coordinates admit a strict common descent exactly when the minimum-norm point `m` of `[a, b]`
  is nonzero. `m = 0` exactly when they are exactly opposed: parallel defect
  `|a|²|b|² − ⟨a, b⟩² = 0` with `⟨a, b⟩ < 0`. Then no step at any grain lowers both phases at first
  order. That is a Pareto-stationary orbit, a property of the objective and not of the lattice.
- **Lattice reach.** With `m ≠ 0`, a common descent exists at first order. The landing refuses when
  the first exponent at which the step commits a lattice unit (§7k: 8 for stiffness) exceeds the
  certified exponent `k_c`, the largest `k` with `2^k c ≤ 1` for the family's covector scale `c`
  through the World port. The gap `8 − k_c` measures how much finer the material grain would have
  to be.
- **Omitted coupling.** This is read from source, not from a number. The cycle's normalization omits
  the orbit shift's adjoint (§7l, scope), and the receiving tangents hold `R` exterior. The orbit's
  classical gradients `L0`, `L1` are read beside it: §7i found the orbit's summed classical credit
  exactly 0, and this reading says whether each encounter's is.

**Acceptance, fixed before the run.** The reading prints, per family: `|L0|², |L1|²`, `|a|², |b|²`,
`⟨a, b⟩`, the parallel defect and whether it is exactly zero, `λ`, `|m|²` and its ratio to the smaller
of `|a|², |b|²`, the widest entry of `m`, and `c` with `k_c`, all as exact dyadic enclosures. It
classifies each family by the rules above and changes no law.

[measured] **The reading** ([receipt](receipts/2026-10-09-material-tangent/BLOCKER_CLASSIFIED_DEV_TESTS.v1.json)),
fixture 1's orbit after twelve encounters, as exact dyadic enclosures:

| family | `\|L0\|²`, `\|L1\|²` | `\|a\|²` | `\|b\|²` | `⟨a, b⟩` | parallel defect | `λ` | `\|m\|²` | widest `\|m_i\|` | `c` | `k_c` |
|---|---|---|---|---|---|---|---|---|---|---|
| storage | 0, 0 | `[2⁻¹⁰, 2⁻⁹)` | `[2⁻⁹, 2⁻⁸)` | `[2⁻¹⁰, 2⁻⁹)` | `[2⁻²⁰, 2⁻¹⁹)` | 1 | `[2⁻¹⁰, 2⁻⁹)` | `[2⁻⁶, 2⁻⁵)` | `[2⁻⁴, 2⁻³)` | 3 |
| stiffness | 0, 0 | `[2⁻¹⁴, 2⁻¹³)` | `[2⁻¹³, 2⁻¹²)` | `[2⁻¹⁴, 2⁻¹³)` | `[2⁻²⁹, 2⁻²⁸)` | 1 | `[2⁻¹⁴, 2⁻¹³)` | `[2⁻⁸, 2⁻⁷)` | `[2⁻⁸, 2⁻⁷)` | 7 |
| dissipation | 0, 0 | `[2⁻¹³, 2⁻¹²)` | `[2⁻¹², 2⁻¹¹)` | `[2⁻¹³, 2⁻¹²)` | `[2⁻²⁷, 2⁻²⁶)` | 1 | `[2⁻¹³, 2⁻¹²)` | `[2⁻⁸, 2⁻⁷)` | `[2⁻⁸, 2⁻⁷)` | 7 |

**Classified.**
- **Not incompatible directions.** In every family `⟨a, b⟩ > 0`, and the parallel defect is nonzero.
  The minimum-norm point is `a` itself (`λ = 1`, `⟨a, b⟩ ≥ |a|²`), so `−a` lowers both orbit
  encounters' phase at first order. The orbit is not Pareto-stationary.
- **Lattice reach, by one dyadic order.** For stiffness, the family §7k's refusal names, the certified
  exponent is `k_c = 7` (`c ∈ [2⁻⁸, 2⁻⁷)`), while the step first commits a lattice unit at exponent 8.
  The widest descent entry lies in the same enclosure as `c`. A certified step `2^k ≤ 1/c` then moves
  each entry by less than one unit, so the step reaches only when the descent's entries exceed its
  covector scale. The material grain is one binary order too coarse for the certified common descent.
- **Omitted coupling.** Each orbit encounter's classical gradient is exactly 0, not only their sum,
  so on this orbit the classical level carries nothing and the phase alone can be descended. The
  orbit shift's adjoint and `R`'s exterior hold (§7l) are the omitted terms named in source. They
  bound the normalization's scope, not the direction, which comes from the exact forward credits.

**Correction (October 10).** §7k said the two waves' phase gradients "nearly oppose". That was my
inference from the refusal, not a reading, and the reading contradicts it: they are positively
aligned in every family. The §7k refusal itself stands as measured. §7j's account of the
projection-stage worsening at encounter 0 ("projecting off encounter 0's phase holds its first-order
change at zero") is not supported either. With `⟨a, b⟩ > 0`, `−(a + b)` raises neither wave at first
order, so no projection acts. The measured worsening of `[2⁻¹⁰, 2⁻⁹)` at exponent 7 is therefore
second order or lattice rounding of a step that commits about one unit, so the committed change is
not `2⁷ d`. Which of the two is not yet read.
