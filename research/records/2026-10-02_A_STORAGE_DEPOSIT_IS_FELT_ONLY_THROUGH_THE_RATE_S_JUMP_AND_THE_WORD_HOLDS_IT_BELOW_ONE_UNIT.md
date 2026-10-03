# A storage deposit is felt only through the rate's jump, and the word holds it below one unit

**Date:** 2026-10-02. **Refs:** #62, #73, #63.
**Grade:** [proved-derived; formal-checked] for the laws (`HNN/StorageResolution`); [measured] for
§5, on Astra's control (`hnn::reference::continuation`, merged as `046d8d2e`); [agent-inferred]
where marked.

**October 3.** §9 redoes the law at held momentum. The continuation now holds the contact's
momentum across its deposit, not its rate, so §1's response and §2's telescoping describe the held
rate the continuation no longer executes. §3 and §4 stand unchanged. §5's table is unchanged on the
lattice, for the reason §9.3 gives. The test §1, §5 and §8 name,
`storage_deposit_reaches_the_next_contact_only_through_the_rate_jump`, is now
`storage_deposit_at_held_momentum_is_felt_through_the_motion`: its exact arm asserts §9.2's identity
in place of §1's, which its Lean (`storage_transit_response`) still holds, and its lattice arm
asserts §3's remainder equality and §9.3's rate remainders at every equal tick.

## 0. The question

Astra's joint continuation deposits on contact 0's storage factor and opens the next contact
passage from the same representatives as the word it replaces. Two of its readings asked for a
derivation:
- **The channel unit.** Seven rebase levels moved the channel unit from `1/64` to `1/8192`, so that
  the released factor displacements, which lie between `2^(−14)` and `2^(−13)`, survive on the
  storage lattice. What channel unit does a deposit need for it to change the next contact passage,
  read from the receiver's resolution (the grain, the word unit, the contact cut's enclosure)?
- **The equal representative.** In the lattice control the material changes, but the next contact
  representative stays equal at word unit `1/2048`. Is that a resolution floor? If so, what is the
  least deposit, or the finest word unit, at which the next contact must change? If not, what holds
  it fixed?

## 1. The response: storage is felt only through the change of rate

The transit solves `m ζ = b` with `b = h(α_g − α_h) + 2Cw − hKu` and
`m = 1 + (G/2h)(2C + hD + ½h²K)` (`hnn::propagation::{transit_solve, contact_operator}`). A deposit
`C → C + ΔC` on the storage factor moves the right side by `2ΔC w` and the operator by `(G/h)ΔC`.
At one representative `(u, w, α)` the two solves therefore differ by

```text
m′(ζ′ − ζ) = 2ΔC(w − ω) = ΔC(w − w⁺),     ω = (G/2h)ζ,   w⁺ = 2ω − w = (G/h)ζ − w,
```

exactly, where `m′ = m + (G/h)ΔC` and `w⁺` is the predecessor's next rate before its split
(`storage_transit_response`). The stored term `2ΔC w` and the operator's `(G/h)ΔC ζ` cancel except
for the rate's jump across the tick. At a rate that does not move the deposit is not felt at all
(`storage_response_of_still_rate`). This is the capacitor's law: a change of storage shows only in
the current `C dw/dt` it draws, never in a steady rate.

The exact control confirms the identity at the first tick: `m′(ζ′ − ζ) = ΔC(w − w⁺)` holds as an
exact equality of rationals (`storage_deposit_reaches_the_next_contact_only_through_the_rate_jump`,
exact arm).

## 2. The jumps telescope

On the word lattice the rate is split from `(G/h)ζ̂ − w` with its remainder `ρ`, and the solve `ζ̂`
from `ζ` with its remainder `r`. Over `N` ticks at which the two words keep one representative, the
jumps sum to

```text
J_N = Σ_(t<N) (w_t − w⁺_t) = (w_0 − w_N) + (ρ_0 − ρ_N) + (G/h)(r_0 − r_N)
```

(`rate_jumps_telescope`). The deposit's accumulated response under the exact solve is
`V_N = m′⁻¹ ΔC J_N`. It grows only with the rate's excursion `w_0 − w_N`, not with the number of
ticks.

## 3. Two words at one representative

Both words open with zero remainders. While their carried values agree, their remainders differ by
exactly the accumulated image difference (`feedback_remainder_difference`). Both remainders lie in
the half-open cell `[−u/2, u/2)`. So:
- **An accumulated difference of one unit forces a parting.** If `|Σ (ζ′_t − ζ_t)_i| ≥ u`, the two
  words' carried values differ at some tick before `N` (`representatives_part_of_accumulated_unit`).
- **Below one unit nothing is forced.** The difference sits in the remainder. A representative parts
  only where the predecessor's point `ζ_t + r_t` lies within the accumulated difference of a cell
  boundary.

The lattice control's one-tick reading is this case. The representatives are equal and the
remainders differ (`released().remainders` totals `477672069335763/2^58` against `14295257/2^33`),
so the change is carried in the remainder, not lost.

## 4. The floor

The contact operator is `c·1 + S` with `S ⪰ 0`, where `c` is its least eigenvalue and `c ≥ 1`
(`m ⪰ 1`). It shrinks an inverse image by `c`: `m′V = ΔC J` gives `c²|V|² ≤ |ΔC J|²`
(`le_of_margin_add_psd`). Therefore

```text
|ΔC J_N| < c·u   ⇒   |V_N,i| < u at every coordinate        (storage_floor)
```

and the material response never forces the next representative apart by tick `N`. Conversely,
`|V_N,i| ≥ u` at some coordinate forces a parting by tick `N` under the exact solve.

The executed solve is a certified chart, not `m′⁻¹`. Each word executes its own chart, so the image
difference also carries the difference of their residuals, `m′⁻¹(e′_t − e_t)` with
`e = (mR − 1)b`. That term does not telescope. Its per-tick size is bounded by the charts'
certificates (`LatticeWord.inverse_chart_deviation`).

## 5. The measurement on Astra's control

The test `storage_deposit_reaches_the_next_contact_only_through_the_rate_jump` reuses the control's
field, constitution, source and deposit. It runs the predecessor and the successor tick by tick and
reads each word's solve remainder.

**The operands are exact.**
- `h = 1` and `G = 2`, so `G/h = 2`. The word unit is `u = 1/2048`.
- The deposit is
  `ΔC = [[0, −1/8192], [−1/8192, 24577/2^26]]`: one channel unit off the diagonal.
- The deposited operator is `m′ = [[49/4, −20481/4096], [−20481/4096, 310403073/2^25]]`, with least
  eigenvalue `c` in `(5798713/2^20, 90605/2^14)`, inside `(11/2, 6)`.
- Stiffness, dissipation, conductance and step are unchanged by the deposit (asserted).

**The words keep one representative for 18 ticks and part at tick 19.** The opening rate is
`w_0 = (−1/16, 39/1024)`. The rate grows under the pumped ring, reaching `(−1727/1024, −65/32)` at
tick 19. The second coordinate carries the larger response at every tick read. In units of `u`:

| tick | rate entering `w_t` | accumulated `Σ(ζ′ − ζ)` | material `m′⁻¹ΔC J` | chart difference | representatives |
|---|---|---|---|---|---|
| 1 | `(−1/16, 39/1024)` | `+(1/90, 1/89)` | `−(1/79, 1/78)` | `+(1/42, 1/41)` | equal |
| 2 | `(299/1024, 81/256)` | `+(1/21, 1/20)` | `+(1/27, 1/26)` | `+(1/96, 1/95)` | equal |
| 4 | `(233/1024, 85/256)` | `+(1/36, 1/35)` | `+(1/129, 1/128)` | `+(1/49, 1/48)` | equal |
| 8 | `(415/1024, 125/256)` | `+(1/36, 1/35)` | `+(1/32, 1/31)` | `−(1/302, 1/301)` | equal |
| 16 | `(1017/1024, 1213/1024)` | `+(1/15, 1/14)` | `+(1/13, 1/12)` | `−(1/74, 1/73)` | equal |
| 19 | `(−1727/1024, −65/32)` | `−(1/7, 1/6)` | `−(1/9, 1/8)` | `−(1/47, 1/46)` | **parted** |

At every tick at which the representatives agreed, the successor's remainder minus the
predecessor's equalled the accumulated difference exactly (asserted). The accumulated difference
never reached one unit: at tick 19 it is below `1/6` of a unit. The parting at tick 19 is therefore
a crossing, not a forced parting. At tick 19 `|ΔC J|²/u²` lies in `(73/50, 147/100)`, against
`c² > 30`. The necessary condition `|ΔC J| ≥ c·u` fails by a factor above 4, and the sufficient
one, `|V_i| ≥ u`, by a factor above 8.

**The chart difference is the same size as the material response.** At tick 1 the chart difference
is larger than the material response by a factor in `(13/7, 2)` and opposite in sign. By tick 19 the material response leads by
a factor in `(5, 6)`, because it grows with the rate's excursion while the chart term does not.

The run took 119 ms of the test's wall time for both arms. No projection was needed below one
second.

## 6. The answers

**The equal representative is a resolution reading, not a lost deposit.**
- The deposit's next-passage response is `V_N = m′⁻¹ΔC J_N`, with `J_N` the rate's net excursion
  plus at most `(1 + G/h)·u` of remainder per coordinate. At the control's first tick it is `1/90` of a unit,
  held exactly in the solve remainder.
- Over the following ticks, at the control's own deposit, the next contact's representative parts at
  tick 19 by a crossing.
- What held it fixed for 18 ticks is the rate. Storage enters only through the rate's change, and
  `|ΔC J|` must reach `c·u` before a parting is forced.

**The least deposit and the finest word unit** at which the next contact must change by tick `N`:

```text
forced at some coordinate     ⇐   |(m′⁻¹ ΔC J_N)_i| ≥ u          (exact solve)
never forced by the material  ⇐   |ΔC J_N| < c·u ,   c = λ_min(m′) ≥ 1
```

At the control, `c` lies in `(11/2, 6)` and `u = 2^(−11)`. Through tick 19 the material response's
second coordinate exceeds `u/9`. On this trajectory a word unit of `2^(−15) = u/16` or finer meets
the sufficient condition, and at `u = 2^(−11)` a deposit nine times larger does. The bound is read
on the control's trajectory: at another unit the rates themselves would differ.

**The channel unit is not the lever.** The channel unit decides only whether a factor displacement
survives on the storage lattice. Here it does: the deposit is one channel unit off the diagonal. A
surviving `ΔC` is felt by the next passage through `ΔC J_N` alone. The rule read from the receiver's
resolution is the floor above:
- the word unit `u` (from the grain `L_R`, through `L_w = ⌈log₂(4L_R X_w e_max s)⌉`);
- the operator's margin `c`;
- the rate excursion `J_N`, which the contact cut's rate enclosure bounds.

[agent-inferred] Rebasing the channel past the unit at which one unit's `|ΔC J_N|` reaches `c·u`
over the admitted run gains no forced change at the next contact. Finer deposits are carried in the
remainder and released at the word's end. They can still part a representative by a crossing, as
at tick 19 here, but nothing certifies that they will. At the control that unit is coarser than
`1/8192`: through tick 19, one channel unit gives `|ΔC J|` short of `c·u` by a factor above 4.

## 7. What this asks of the control

[agent-inferred] The control's lattice arm asserts that the next representative is equal after one
tick. That reading depends on where the predecessor's point sits in its cell: a different source or
deposit can cross at the first tick. The invariant reading is the one this test asserts. While the
representatives agree, the remainder difference equals the accumulated image difference, and a
parting is forced once that sum reaches one unit. The control's assertion is left as Astra wrote
it.

## 8. Verification

- Lean: `lake build Holonics.HNN.StorageResolution` builds with no warnings. The module is
  registered in `Holonics/HNN.lean`.
- Rust: `cargo test -p holonics --release --lib -- hnn::reference::continuation` passes (4 tests).
  The new test asserts the exact identity of §1 and the remainder equality of §3 at every equal
  tick.
- `cargo check --workspace --all-targets` is clean.

## 9. At held momentum (October 3)

**Grade.** [proved-derived] for 9.1, whose work identity is
`HolonicsResearch/HNN/MoveDirection.held_momentum_loss`; [proved-derived; formal-checked] for 9.2
and 9.3 (`HNN/StorageResolution` §5, #290); [measured-exact] for 9.4, from
`storage_deposit_at_held_momentum_is_felt_through_the_motion`.

### 9.1 The continuation holds momentum

The continuation's deposit lands at the full-tick cut (`ContactCut::next_tick`), and the next word
opens at that tick on the same clock. So the deposit is a sudden change of the constitution between
two ticks of one continuing motion. That is exactly the event of the
[deposit record](2026-10-03_THE_DEPOSIT_HOLDS_THE_CARRIED_MOMENTUM_AND_THE_ACCRETED_MASS_IS_THE_THROWS_DAMPING.md)
item 3. The contact's canonical state `(u, π = C w)` holds across it, and the rate does not.
Nothing distinguishes a deposit within a refinement from one across receptions. The refinement only
changes which deposit is certified (the native unit certificate, contact loci only), not what the
motion keeps.

The successor therefore opens at `w′ = w + δ`, with `C′δ = −ΔC w` (`held_rate`, the particular point
of the reduced solve). `continue_deposited` now commits through `PowerForm::held` and refuses a
momentum `C′` cannot hold (`HnnError::HeldMomentum`). Its work is the deposit record's identity,
`½⟨w′, C′w′⟩ − ½⟨w, Cw⟩ = −½⟨w′, ΔC w′⟩ − ½⟨δ, Cδ⟩`, in place of the same-state `½⟨w, ΔC w⟩`.

The held rate had the opposite sign of work on this control (9.4). Holding the rate gives the motion
an impulse `ΔC w` that no source supplies (the deposit record item 5).

### 9.2 The response: storage is felt through the motion itself

At held momentum the transit's right side `h(α_g − α_h) + 2Cw − hKu` is unchanged, since
`2C′w′ = 2π = 2Cw`. Its operator moves by `(G/h)ΔC`. So, at one canonical state `(u, π, α)`,

```text
m′(ζ′ − ζ) = −(G/h) ΔC ζ = −2ΔC ω = −ΔC(w + w⁺),        ω = (G/2h)ζ,  w⁺ = 2ω − w
```

exactly (`held_storage_transit_response`, `c = G/h`). Compare §1's held rate, `ΔC(w − w⁺)`. The
two differ by `2ΔC w`, the impulse the held rate injected, which is what cancelled the steady part
of the motion there. At held momentum a heavier mass with the same momentum moves more slowly, and
it does so at once. Only rest (`ω = 0`) leaves the deposit unfelt. A steady rate does not.

Summed, the midpoints are the travel. The displacement is carried as
`û_(t+1) + σ_(t+1) = û_t + (G/2)ζ̂_t + σ_t`, and the solve as `ζ̂_t + r_(t+1) = ζ_t + r_t`. Therefore

```text
(G/2) Σ_(t<N) ζ_t = (û_N − û_0) + (σ_N − σ_0) + (G/2)(r_N − r_0)
```

That is `midpoint_sum_is_travel` with `k = G/2`. Read along the predecessor's path, the exact
response accumulates as `m′V_N = −(2/h)ΔC[(û_N − û_0) + (σ_N − σ_0) + (G/2)(r_N − r_0)]`. It
grows with the displacement's travel, not with the rate's excursion. That is the held mass lagging
in position. §4's floor applies unchanged, with `J` replaced by this sum.

[agent-inferred] This reading is first order in `ΔC`. After one tick the two exact motions no longer
share a canonical state, as §2's accumulation was first order along the shared representatives.

### 9.3 On the word lattice the momentum opens in the rate's remainder

The cut's end change lies on the transient lattice. `Word::on_change` splits the held rate with
error feedback, as it splits a carried rate at reception (record B §2.3a). The opening then has two
cases, decided exactly at the opening:
- **Forced at the opening.** If some `δ_i` lies outside the remainder's half-open cell
  `[−u/2, u/2)`, the successor's rate representative parts at the opening. The material response is
  felt at tick 0, by no crossing.
- **Held in the remainder.** Otherwise the representative is unchanged, and the opening rate
  remainder is `ρ′_0 = δ`.

In the second case the solve reads only the carried representatives. While they agree, the per-tick
response is §1's identity `ΔC(ŵ − ŵ⁺)` at the representative. The solve remainders differ by the
accumulated image difference (§3). The rate streams carry the momentum hold beside it:

```text
ρ′_N − ρ_N = δ + Σ_(t<N) (y′_t − y_t),        y_t = 2ω̂_t − ŵ_t
```

This is §3's feedback difference from two different openings
(`feedback_remainder_difference_of_openings`). Since `|δ_i| < u/2`, the hold never by
itself forces the rate apart. It parts the rate only by a crossing, or once the rate images
accumulate. So on the lattice the held momentum is carried exactly as representative plus remainder,
and the solve feels its remainder part only when the error feedback releases it. That is the
lattice's law for every carried value, not a new one.

### 9.4 The measurement on Astra's control

The fixture, deposit and operands are those of §5: `u = 2^(−11)`, `G/h = 2`, and
`ΔC = [[0, −2^(−13)], [−2^(−13), 24577/2^26]]`.
- **Exact arm, one tick.** The successor's rate moved, `C′w′ = Cw` holds exactly, and
  `m′(ζ′ − ζ) = −ΔC(w + w⁺)` holds as an equality of rationals.
- **Lattice arm, the opening.** `w_0 = (−1/16, 39/1024)`. The jump is
  `δ = (−2030099, −13·252319)/(2^10·5³·31²·37²)`, which is `(−4060198, −6560294)/(5³·31²·37²)` in
  units of `u`, inside `(−1/40, −1/41)` and `(−1/25, −1/26)` of a unit. The representative is
  unchanged, and `ρ′_0 = δ`.
- **Lattice arm, the passage.** Every tick of §5's table is unchanged. The representatives agree
  for 18 ticks and part at tick 19. At every agreeing tick both remainder identities of 9.3 held
  exactly (asserted).
- **The work.** At the held rate the deposit's work was `+3·13·2007079/2^47`, raising the reading. At
  held momentum it is `−7³·13·34403/(2^23·5²·31²·37²)`, lowering it. The opening split is
  `5148192796380257/(2^47·5²·31²·37²)`, exactly the difference of the two. The lattice representative
  reads the held rate's power, and the split carries the rest.

The run's wall time was within one second for the test's two arms, so no projection was needed.

### 9.5 Remaining sites

[agent-inferred] `reference::contact_ablation`, a measured diagnostic with no consumer, still
continues its contacts-only successor on the predecessor's end change and reads its work at the held
rate (`PowerForm::deposition_work`). It is left as it stands: it is a diagnostic reading, not an
executed continuation.

Proved in `HNN/StorageResolution` §5 (#290), as entered in #62 (comment 5973969084):
- the response at held momentum, `held_storage_transit_response`;
- the travel telescoping, `midpoint_sum_is_travel`;
- the remainder difference from two openings, `feedback_remainder_difference_of_openings`.

9.2's first-order reading of the accumulated response is agent-inferred and is not among them.

