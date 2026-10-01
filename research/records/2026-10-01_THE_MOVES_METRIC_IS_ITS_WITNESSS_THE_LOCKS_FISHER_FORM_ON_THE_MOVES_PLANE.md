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

The span's mass is read from a station, `M_j = Σ_c n(c) ρ^(r_j(c)) + Σ_(i∈S) ρ^|i − j|`
(`BankPlacement::mass`, with the population's phase counts). On `n` contiguous unit-count ticks
read from an interior station `j` it is `(1 + ρ − ρ^(j+1) − ρ^(n−j))/(1 − ρ)`, from an end
`(1 − ρⁿ)/(1 − ρ)`, and `n` at `ρ = 1` (Astra's correction). It is the witness's memory length, so
`ρ` sets the witness's clock and `M_j` reads it as mass, indexed by the station and the population;
the shared parameter does not make the two one quantity. A move of `ρ` changes the frame that
measures it.

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

The executed comparison's witness is the lock at each decision. Its sheets are a canonical
(Gibbs) state: `θ_x = a_x/Π`, `Π = 1 + Σ_x a_x`, is the canonical state of energies `−u_x`
(`u_x = log a_x`, the resting sheet at `0`) at unit temperature, with partition function `Π`. Its
energy account is the relative entropy of its reading against that canonical reference: the
free-energy identity holds at the fixed reference levels (Lean
`Physics/Information/PortWork.{canonicalState_eq, extracted_work_general, quenchWork_eq}`), not for
a generic pair of distributions. The resting sheet's weight one is the release's threshold
normalization, the lock's baseline (`Objects/ParametronLock.{exchange, lockFace}`). Its realization
as the lossless ring's exterior return needs a ring, port and transfer map that no owner supplies yet
(Astra: `HolonicInteractionExterior`'s unit-radius return has no definite invariant storage, so radius
one alone cannot supply it); that join is owed. The lock face `ℓ = log Π − u_t` has

```text
∂ℓ/∂u_x = θ_x − [x = t],      ∂²ℓ/∂u_x∂u_y = θ_x[x = y] − θ_x θ_y
```

The Hessian is the curvature of the lock's log mass `log Π`: the normalized face's Jacobian
`diag θ − θθᵀ` over the sheets (`Holon/Law.softmaxJacobian`), its Fisher form. Pulled back through
the readings onto the plane of the port's unit move `ΔE` and the modulus `ρ`, with
`δ_x = (⟨ĝ_x, Δz_x(ΔE)⟩, ⟨ĝ_x, ∂z_x/∂ρ⟩)` each candidate's log-reading change (the resting sheet's
row zero), the locks join by direct sum:

```text
G = Dᵀ(⊕_j J_θj)D,     g = Dᵀ(⊕_j (θ_j − e_t)),     (α, β) = −G⁻¹g  where G ≻ 0
```

- **The common receiver** (Astra's review). The first build took each `θ_x` as the independent
  midpoint of its share enclosure, and those need not sum to one: three readings in `[1, 9]` give
  share midpoints summing to `51/40`, where `G` can be indefinite. The sheets are now normalized
  jointly at one representative of the readings (each joint growth enclosure's dyadic face), so
  `Σ = 1` and the resting sheet's share is positive. The residual is explicit: the reading counts the
  common shares that leave the comparison's share enclosures (zero on every read). The committed
  move's own lock-face weights `θ_x − [x = t]` still use independent midpoints; that is the same
  defect in the move, to be repaired with the move's law.
- **Kernel** (Astra). `vᵀGv = Σ_j Var_θj(0, (D_j v)_x)`, so `ker G = ∩_j ker D_j`: a plane direction
  no lock reads. The step is defined exactly where `G ≻ 0`, decided by exact inertia.
- **Scope.** `G` is the Gauss–Newton (Fisher) pullback, not the comparison's full Hessian on the
  plane, which adds `Σ_j Σ_x (θ_x − [x = t]) Hess(u_x)`. `δ` differentiates the exact unrounded
  placement (the storage's exact move along `ΔE` at fixed weights, the transported weights' exact
  derivative along `ρ`) through the member's covector at its dyadic faces, held at 128 bits. It is
  not the charted consumer's rounding. This is the plane of `E`'s own unit step and `ρ`; full
  covariance of `E`'s direction is not claimed.
- **Charts.** Every `δ` is a change of the witness's own reading, so `G`, `g` and the step are
  unchanged by any storage rechart `z′ = Bz`, while the coordinate control `−γ_ρ/G_ρ` divides by 4
  under `B = 2`. A rescaled plane direction rescales its coordinate inversely, so the move is
  unchanged. The cross term `G_Eρ` is the coupling the old move dropped.
- **Physical frames.** This is the receiver-relative chart law. It is not a spacetime metric. The
  physical-frame owners exist (`Physics/Spacetime/StressEnergy`: boosted observer readings and
  passive tensor transport; Rust `physics::spacetime::source::LorentzMap`, checking
  `ΛᵀηΛ = η`), and the HNN consumes none of them. Transporting the witness's energy and momentum
  through a Lorentz or tetrad map is a separate, unbuilt join.

Owners, composed from the library: the normalized face's Jacobian
`receiver::face::softmax_jacobian`, `SymmetricForm::{direct_sum, pullback}` (`pullback` added:
`MᵀAM` for any `M`) and `inertia` for the step's domain; `hnn::executed::{lock_sheets, witness_form,
WitnessForm, PlaneTerm, witness_plane, PlaneReading}`. Tests in `hnn::tests::lock_face`, 5 new:
- the normalized Jacobian pulled back;
- one common receiver keeps the form a variance (Astra's counterexample);
- the step chart-free and the control not;
- dropping the cross term changes the step only where the witness couples the plane;
- the machine's plane reading agrees with its move.

Lean owed in #62: the pullback's variance identity and kernel, the step's domain, and the chart
invariance.

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
(`first-attempt/`). The declared read was changed to carry `E` onto the lattice, as the machine's move carries it,
under the same bound and deadline: 287,019 ms, exit 0. After Astra's review the form was recomposed
on one common receiver and read again (receipts here; their identity line names the parent commit `ce19d35b`, the recomposition being this record's commit): 288,038 ms, exit 0, peak resident
201,814,016 bytes, no common share outside its enclosure, and every reading above identical at its
printed grain. Measured over projected: `288038/505250`.
