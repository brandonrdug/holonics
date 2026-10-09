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

## 4. The owners it consumes, and the implementation

- `propagation::{transit_solve, transit_update, ContactOperands::solve}` for (1).
- `prediction::physical_signed_tick` for the fixed-operand tick in (2).
- `word::{Word::recorded, Passage, Word::reception_end, ReceptionCarry::crossed}` and the private
  `interior_of` for the crossing in (3).
- `port::ChangeCovector::pairing` for the credit.
- `word::continuation::{ContactCut, FiniteDecrease}` and `Constitution::first_reach` for the landing.

The new consumer is one carrier in `hnn::word::continuation`, `MaterialTangent`. It holds the
declared direction's identity (contact, its `δC`, `δK`, `δD`, and the producing commit) and the
state-shaped `χ`. Its operations are `held_opening`, `step` (eq. 2, called in lockstep with the
Word's full ticks, as `prediction` advances its completion columns), `carried`, `opened` (eq. 3) and
`credit`. Its fixture checks (e) first, on one contact and one direction. The loop's fixture (a)–(d)
then consumes it.

**Owed (#62).** The tangent identity (2) as a Lean statement at the executed transit (the `HNN/Propagation`
owner), and the crossing (3) at `HNN/MoveDirection`'s held-momentum law.

**Recorded failures checked.** An uncertified deposition step: the tangent proposes, and only the
landing's exact strict improvement admits. A tape kept as retention: the forward route keeps none. An
authored routine standing in for learning: the direction comes from the World's actual return, and
nothing task-specific enters. A fixture becoming the goal: (a)–(e) are fixed here before code.
