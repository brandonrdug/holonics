# The move's metric is its witness's: the lock's Fisher form on the move's plane

**Date.** October 1. **Issues.** #73, #63 (THE_REBUILD U6, step 1); the owed Lean statement in #62.
**Grade.** [definition; agent-inferred] for §1–§2; [measured] for §3, read-only, on gate A's batch.
Receipts: [`2026-10-01_THE_MOVES_METRIC_receipts/`](2026-10-01_THE_MOVES_METRIC_receipts/).

## 1. The lens and the confusion it corrects

Brandon, October 1: who witnesses "the move's metric", and where does that observation come from?
An energy account is a witness's measurement, and masses, temporal lengths and momenta are one
thing read in different charts.

[definition; agent-inferred] A metric on a move is a reading. It is the quadratic form by which a
receiver measures the size of a change, which is that receiver's energy of the change. The receiver
is the witness, its form is its inertia (mass), and the covector it returns is momentum: a step is
inverse mass times momentum. Choosing a move's metric therefore chooses its witness, and the
"energy account" and "the metric" are one act. The guides already say so. There is no global
gradient, quantities belong to `view(receiver, grain, clock)`, and the Swing splits a rate "against
a receiver's metric" ([objects](../../docs/ELEMENTARY_OBJECTS.md)). Probability is a receiver
geometry whose form is Fisher's (atlas `ratio.fisher-sphere`), and the Born face once learned by
Fisher scoring (atlas `hnn.born-fisher-step`).

The span's mass is read from a station, `M_j = Σ ρ^|i − j|` (`BankPlacement::mass`). Over `n`
contiguous ticks it is `(1 − ρⁿ)/(1 − ρ)`, the witness's memory length. So `ρ` is the witness's
clock and `M_j` the same quantity read as mass. A move of `ρ` changes the frame that measures it.

**The confusion, and who held it.** Claude and Astra both listed "the receiving metric" and "the
exterior return and energy account" as separate items and argued their order. Astra's note treated
the metric as an optimization choice apart from the energy form, and asked for a separate map before
the normalization mass could be read as mass. Astra's covariance demand `Q′ = B⁻ᵀQB⁻¹` is right but
passive: it moves a given metric and does not ask whose. Astra named `G_ρ` as the coordinate metric
first. The code held the same confusion. `Δρ = −γ_ρ/G_ρ`, `G_ρ = Σ_c |∂z_c/∂ρ|²`, turns the covector
into a storage displacement with the identity form: momentum read as velocity with no mass, a
measurement by no receiver. Meanwhile `E`'s step carries the normal law's accumulated Gram, so the
joint move was measured by two witnesses in two frames, with no cross term.

## 2. The witness and its form

The executed comparison's witness is the lock at each decision. Its energy account is the relative
entropy of its reading (free energy `F(p) − F(q) = k_B T · D(p‖q)`). In the log-readings
`u_x = log a_x`, with `Π = 1 + Σ_x a_x` (the resting sheet's weight one is the return through the
lossless ring) and `θ_x = a_x/Π`, the lock face `ℓ = log Π − u_t` has

```text
∂ℓ/∂u_x = θ_x − [x = t],      ∂²ℓ/∂u_x∂u_y = θ_x[x = y] − θ_x θ_y
```

The Hessian is the curvature of the lock's log mass `log Π`, its Fisher form. Pulled back through the
readings onto the plane of the port's unit move `ΔE` and the modulus `ρ`, with
`δ_x = (⟨ĝ_x, Δz_x(ΔE)⟩, ⟨ĝ_x, ∂z_x/∂ρ⟩)` each candidate's log-reading change:

```text
G = Σ_j Σ_(x,y) δ_x (θ_x[x = y] − θ_x θ_y) δ_yᵀ,     g = Σ_j Σ_x (θ_x − [x = t]) δ_x,     (α, β) = −G⁻¹g
```

`g`'s `ρ` part is the move's `γ_ρ` exactly. Every `δ` is a change of the witness's own reading, so
`G`, `g` and the step are unchanged by any storage rechart `z′ = Bz`, while the coordinate control
`−γ_ρ/G_ρ` divides by 4 under `B = 2`. A rescaled plane direction rescales its coordinate inversely,
so the move itself is unchanged. The cross term `G_Eρ` is the coupling the old move dropped.

Owners: `hnn::executed::{witness_form, WitnessForm, PlaneTerm, witness_plane, PlaneReading}`. Tests
in `hnn::tests::lock_face` (4 new, 15 passed):
- the Fisher form pulled back;
- the step chart-free and the control not;
- dropping the cross term changes the step only where the witness couples the plane;
- the machine's plane reading agrees with its move (`γ_ρ`, `G_ρ`, the unit, the terms).

Lean: the lock face's Hessian `θ_x[x = y] − θ_xθ_y` and the pullback's chart invariance are owed in
#62. Scope: this is the plane of `E`'s own unit step and `ρ`. Full covariance of `E`'s direction is
not claimed.

## 3. The read on the guarded witness's c0 and c6

`executed witness-plane order2 2026093061 8 lock-dec <refit at ρ*> …`. At each state, the witness's
step, then two successors that share `E + αΔE` (carried onto the port's lattice): the witness's
`ρ + β` and the control's `ρ + αΔρ_c`. The chord's `ρ* − ρ` is `−68101/262144` at c0 and
`−541877/2097152` at c6.

| | c0 (the founded opening) | c6 (the guard refused every step) |
|---|---|---|
| `γ_ρ` | `−10636625/131072` | `9794427/524288` |
| the control's `Δρ_c` | `+10266827/2^33`, away from `ρ*` | `−2467809/2^33` |
| `G_ρ` (coordinates) against the witness's `G_ρρ` | between 7 and 8 times | between 6 and 7 times |
| the witness's `G_Eρ` | `1806923/4096` | `8564877/65536` |
| the witness's step `α` | `2036817/2^23` (`1/4 − 60335/2^23`) | `12625805/2^23` |
| the witness's `β` over the chord | `12487475/2^30`, toward `ρ*` | `10519437/2^27` |
| the control's `αΔρ_c` over the chord | `−1199485/2^30`, away | `14375069/2^33` |
| witness successor: `L`, solved, right, whole | `[464807/4096, …)`, 5, 15, 0 | `[415717/4096, …)`, 2, 21, 0 |
| control successor: `L`, solved, right, whole | `[494147/4096, …)`, 3, 15, 0 | `[398240/4096, …)`, 1, 20, 0 |
| the incumbent's `L` | `[500197/4096, …)` | `[373776/4096, …)` |

- **The direction.** At c0 the coordinate move sends `ρ` away from `ρ*` (`γ_ρ < 0`). The witness's
  cross term turns it toward `ρ*`. With the same `E`, the witness's `ρ` alone lowers `L` by
  `29340/4096` nats more than the control's.
- **The scale.** The witness moves `ρ` between 46 and 47 times further than the control at c6. Even
  so it covers less than `1/85` of the chord at c0 and less than `1/12` at c6. The witness is stiff in `ρ` at the
  current `E`: its readings respond strongly to `ρ`, so it admits a small move a step. Reaching `ρ*`
  takes `E` and `ρ` travelling together, as the chord showed (decisions appear only in its last
  quarter).
- **`E`'s step.** At c0 the witness sizes `α` just below `1/4`, where the guarded ladder adopted
  (`1/2` refused). It finds that size without a search.
- **Where the model holds.** At c0 the second-order model predicts `−9162359/2^19` nats and the
  release falls by `35390/4096`, just under half of it. At c6 the plane's step `α` near `3/2` leaves the
  trajectory cell, and both successors rise above the incumbent. A guarded move there would be
  refused, as the witness run's move 6 was.
- No section is whole anywhere.

**Time.** Projection `2 · (154,771 + 2 · 48,927) = 505,250` ms, `timeout 506`, per-line bound
154,771 ms, 19 threads. The first attempt stopped early at 205,761 ms. Its successor held `E` off
the port's lattice, where `α`'s bits multiply every storage, and one read passed the bound
(`first-attempt/`). The declared read was changed to carry `E` onto the lattice, as the machine's
move carries it, under the same bound and deadline. Measured 287,019 ms, exit 0, peak resident
171,397,120 bytes. Measured over projected: `287019/505250`.
