# A storage deposit is felt only through the rate's jump, and the word holds it below one unit

**Date:** 2026-10-02. **Refs:** #62, #73, #63.
**Grade:** [proved-derived; formal-checked] for the laws (`HNN/StorageResolution`); [measured] for
§5, on Astra's control (`hnn::reference::continuation`, merged as `046d8d2e`); [agent-inferred]
where marked.

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
