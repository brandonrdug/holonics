# The comparison is invariant under the ring's shifts and a global phase, and the Gauss–Newton step points toward a lower point exactly when its chord descends

**Date.** October 2. **Issues.** #73, #63 (THE_REBUILD U6, step 1), #62. **Grade.** [proved-derived;
formal-checked] for the theorems (`HolonicsResearch/HNN/MoveDirection`); [derived from the owners]
for §2's symmetry, read from `hnn::ring`, `hnn::prediction` and the harness's declaration;
[measured] for the opening's symmetry check (§2, receipt); [agent-inferred] where marked.
Receipts: [`2026-10-02_MOVE_DIRECTION_receipts/`](2026-10-02_MOVE_DIRECTION_receipts/).

**Occasion.** The main line read the float fit, trained on the chain's 8 requests and read through
the native release. It decides 37 of 128 held-out requests whole and 717 of 1024 stations right. The
native chain at the fit's `ρ` decides 0 whole and 272 stations. At that `ρ` the fit's training code
length is `93355/4096`, against the chain's `269593/4096`. Reach is not the limit: five moves at the
entry bound cover the largest entry of `E_fit − E`. Direction is the limit. Every one of the 16
moves points away from the fit, with signed squared cosines from `−1/4096` to `−133/4096`. The path
`w16 − m6` has a cosine with `fit − m6` that the main line puts at about `−12/100`. The coordinator asked two questions: (a) does
the comparison have a symmetry acting on `E`, and (b) when does a Gauss–Newton step under the
receiver's Fisher model point away from a lower point. Brandon then read "too short per step" as a
leap checked against a tolerance, where the release should be predictive, a throw carrying momentum.
§5 takes that lens.

**Answer.**
1. **The comparison is invariant under the ring's 60 shifts and a global phase of `E`, with
   conjugation** (§2). The bank reads `E` only through its pump carriers, and each growth only
   through a characteristic polynomial. A global phase conjugates every tick, a shift restarts the
   turn, and conjugation exchanges the members `k` and `−k`. None changes a characteristic
   polynomial. The fit's `E` is one point of an orbit `Z₆₀ × O(2)`, and the right distance is to
   the orbit (§3), in closed form. The opening `E₀` is fixed by no nontrivial lattice element, so
   the chain is not trapped in a symmetric subspace.
2. **In its own form the Gauss–Newton step points toward a lower point exactly when the chord
   descends at first order** (§4). For any chord `u`, `⟨Au, F·Av⟩ = −⟨g, u⟩`. A step pointing away
   in the Euclidean cosine is therefore one of three things, each decided by one sign at one start:
   a **pass** (the fit is lower but uphill at first order, so the chord is not convex), the
   **metric** (downhill, but the step's form turns it), or the **orbit** (the fit sits at another
   phase or shift).
3. **The native move is a leap from rest, and a throw built from the same steps points the same
   way** (§5). Each move starts at rest, is admitted only if the held code length falls, and carries
   no velocity. A velocity summed from steps that each point away also points away. Within one
   quadratic model, a throw from rest moves each mode only toward and past its equilibrium, at most
   twice as far. What a throw adds is energy. It crosses a pass when its carried kinetic energy
   exceeds the pass's height above the current level. A move from rest never does, unless one
   endpoint lands past the pass and below its start.
4. **The main line's read decides the case: it is the metric** (§8). At the opening, the native
   gradient and the normal-law step both align with the float descent, while the kinetic step is
   nearly orthogonal to the gradient. The receiver's Gauss–Newton change of each lock raises only
   its target, by `1/θ_t` (`fisher_step_target_only`), where the gradient weighs it by `1 − θ_t`.
   So the worst-read targets dominate the step. The kinetic step is the static leap to the
   stiffness's equilibrium. The normal-law step is the overdamped flow under mass-proportional
   damping. A throw over a finite flight moves each soft mode at most as far as the force's free
   fall (`throw_le_free_fall`), which removes the soft modes' domination.

The computational object is the helical pair interaction; the rings are complex parametrons. Of the
[winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md)'s six objects this touches **the helix**
(the ring's shift is its rotor, the phase its carried angle) and **faces and placement** (the
storage the bank reads). The pair, the cell holonomy, the tube and the tower thread stay attached;
no contact, restriction or transport changes.

## 0. The recorded failures this could repeat

From [the failures that repeated](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)
and [the prototypes' lessons](2026-09-24_LESSONS_FROM_THE_WORKBENCH_AND_ATHENA_PROTOTYPES.md):
- **A refusal answered with a larger limit.** A throw is not a longer leap or a raised tolerance.
  Its admitted rise is the kinetic energy the motion carries, bounded by the motion
  (`comparison_le_energy`), not a declared height.
- **Bits read as progress.** Every claim here compares states, directions or energies, not code
  lengths alone.
- **A located cause carried unrepaired.** This record changes no owner. It names the reads that
  decide between the pass, the metric and the orbit (§6) before any law is built.
- **A design thought in the programming language.** The symmetry is the ring's rotor and the
  node's phase, and the throw is a mass, a stiffness and their modes.
- **Text run on its codec's grain.** Nothing here reads a modality. The symmetry belongs to the
  receiving bank and the ring.

## 1. The question, fixed before the derivation

(a) Is the executed comparison invariant under a group acting on `E`, and what is the distance to
the fit's orbit? (b) When does the receiver's Gauss–Newton step point away from a lower point of
the same comparison: through nonconvexity, through its metric, or through the orbit? (c) Does the
native move carry a velocity? If its motion were second order, what would its mass and damping be,
and what could a throw reach that the leap cannot?

## 2. The comparison's symmetry, read from the owners

**What the bank reads.** The harness's bank (`bank_of`) is one node with `C = K = I₂` and `D = 0`,
axis `1`, strength `p = 5/8`, admittance 16 and hop 1. Its members are the four pump steps
`k ∈ {0, 1, 2, 3}`, all of whose orders divide `d = 60`. At tick `t`, member `k`'s carrier is
`c_t = i^(tk) z_t` (`PumpSchedule::placed`, `a² = 1`), `z_t` being the storage's amplitude at the
crossing. The tick adds the block `−2p R_c` to the stiffness (`pump_block`), and
`R_c = [[Re c, Im c], [Im c, −Re c]]` acts as `z ↦ c z̄`. Every other term of the tick (`2C`,
`(h/Y)I`, `hD`, `(h²/2)K`) is a multiple of `I₂`. A growth is read from the monodromy's
characteristic polynomial (`growth_of`). The release's locks, gaps and enclosures read only growths.

**What the storage is.** `z_j(S) = Σ_c w_j(c) P^(λ−c) E M[c] + Σ_(i∈S) w_j(i) P^(λ−c_i) E e_(x_i)`
(`BankPlacement`). The pair term is zero because the declaration has no pair offset. The storage is
linear in `E`, `P = (· + 1)` is the ring's rotor (`Ring::rotate`), and the turn reads the 60 nodes
as its 60 ticks (`turn`).

**Three transformations leave every growth unchanged:**
1. **A global phase**, `z ↦ e^(iφ) z`. It sends every carrier to `e^(iφ)c`. The rotor `Q` of
   `e^(iφ/2)` carries `R_c` to `R_(e^(iφ)c)` (`rotor_conj_reflection`: `Q R_c Qᵀ =
   R_((p+iq)²c)`) and commutes with every other term. So every tick is conjugated by `Q`, the
   monodromy is conjugated, and its characteristic polynomial is unchanged
   (`charpoly_conj_ticks`).
2. **Conjugation**, `z ↦ z̄`. Member `k`'s carrier becomes `i^(tk) z̄_t`, the conjugate of member
   `−k`'s. The flip `S` carries `R_c` to `R_c̄` (`flip_conj_reflection`). So member `k` at `Ē` reads
   what member `−k` reads at `E`, and the bank, whose members are closed under `k ↦ −k`, keeps its
   largest growth.
3. **A ring shift**, `E ↦ P^m E`. `P^m` commutes with every `P^(λ−c)`, so the storage shifts by
   `m` nodes. Member `k`'s carrier becomes `i^(mk) c_(t−m)`: a global phase (case 1) times the
   same turn started `m` ticks later. A restarted turn's monodromy is `BA` for `AB`, with the same
   characteristic polynomial (`charpoly_rotate_ticks`).

So `L(gE) = L(E)` for every `g` in `Z₆₀ × O(2)`, acting on each node's pair of rows and identically
on the 5 columns. The elements that map the `2⁻²¹` lattice to itself are `Z₆₀ × D₄`: the shifts, the
quarter turns and conjugation, all signed permutations of coordinates.

[agent-inferred] **The chain is equivariant under the lattice elements.** The kinetic solve is
built from `A`, `F`, `c` and the mass `M = I ⊗ H′`, which acts on columns and commutes with every
`g`. Its rounding is toward zero at fixed significant bits. So the chain started at `gE` is `g`
applied to the chain started at `E`. This is read from the owners' docstrings, not checked call by
call.

**Not shown.** The ring's reversal `t ↦ −t`: it would need the reversed tick product to share the
characteristic polynomial. The Floquet certificate also runs from a fixed seed (node 0's real
displacement), so its refusals are assumed, not shown, to be constant on orbits (#62).

**The opening is not symmetric** ([measured], `opening_symmetry.txt`). `E₀` is the declared sign
sequence times ½. No nontrivial element of `Z₆₀ × D₄` fixes it, and the most any one element leaves
unchanged is 151 of its 300 complex entries. The chain is therefore not held in a symmetric
subspace by its opening.

## 3. The fit's orbit and its distance

Write `E` as 300 complex entries (node `t`, column `x`). For each shift `m` and each `σ` (identity
or conjugation), let `y = P^m σ(E_fit)`. Over unit phases `w`, `‖E − w y‖²` is least at
`‖E‖² + ‖y‖² − 2‖⟪y, E⟫‖`, attained at `w = ⟪y, E⟫/‖⟪y, E⟫‖` (`dist_phase_orbit_sq_ge`,
`dist_phase_orbit_sq_eq`). So

```text
d²(E, orbit) = ‖E‖² + ‖E_fit‖² − 2 · max over m ∈ Z₆₀, σ of ‖⟪P^m σ(E_fit), E⟫‖
```

These are 120 exact complex inner products. The chord to the nearest copy is `u* = w* y* − E`.

**The phase is unread at first order.** The comparison is constant along the phase circle, so its
gradient is orthogonal to the circle's tangent `JE` (`fderiv_orbit_tangent`). The readings do not
read `JE` (`A·JE = 0`), so the kinetic step `v = M⁻¹Aᵀμ` is mass-orthogonal to it
(`mass_orthogonal_unread`). The native move therefore never turns `E`'s phase toward the fit's at
first order. A fit sitting at another phase counts against the Euclidean cosine although its copy
at `E`'s phase has the same comparison.

## 4. When the Gauss–Newton step points away from a lower point

Let `A` be the readings' Jacobian, `F ≻ 0` the witness's Fisher form, `c` its covector and
`g = Aᵀc` the comparison's gradient. Every solution of the normal equation `AᵀFA v = −g`, the
minimum-mass one included, satisfies, for every chord `u`:

```text
⟨Au, F·Av⟩ = −⟨g, u⟩                      (gaussNewton_pairing)
```

In its own form `AᵀFA`, the step's cosine with the chord has the sign of the comparison's descent
along the chord, whatever mass selected it. Let `s = ⟨g, u*⟩` at a start `E` where `L(E_fit) <
L(E)`. The main line's numbers say the fit is lower at its `ρ`. A Euclidean cosine below zero is
then one of three cases:
- **A pass** (`s ≥ 0`). The fit is lower, but the comparison does not descend toward it at first
  order, so the chord is not convex (`nonconvex_of_uphill_lower`). When `s > 0`, the chord rises
  first. Every descent step points away from it in its own metric, and no reach or metric changes
  that.
- **The metric** (`s < 0`). The step heads toward the fit in `AᵀFA` and away in the Euclidean
  frame of the cosine. The native gradient's Euclidean cosine with `u*` has the sign of `−s` and
  reads no metric.
- **The orbit.** The cosines with `u*` and with `u = E_fit − E` differ in sign.

The main line's three directions at one start decide it. If the native gradient `d` points away
from `u*`, it is a pass. If `d` points toward `u*` and the kinetic step away, it is the metric. If
the float objective's gradient points toward and the native gradient away, the two comparisons
differ along the chord. [agent-inferred] The float paths rose above their openings on their way to
the decisions ([the refit's ingredients](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)
§3: on seed 303 the comparison climbed above its opening from step 60 on). That is the signature of a pass, so the pass is the
expected case.

## 5. The leap and the throw

**(1) The native move carries no velocity** (read from the owners). `MoveMetric`'s law: "A step's
size is a constitutive change, not a velocity or an elapsed time." Under `Kinetic`, the first trial
is the Gauss–Newton step at `η = 1` from the current state, halved at most `LADDER_DEPTH` times.
Every admitted step certifies the held code length's fall (`NotBelow`). Only the released code
length may rise inside an excursion (`ReleaseExcursion`). Between moves only the constitution is
carried: `E`, and the retained Gram `H` that enters the mass. So each move is a leap from rest,
checked at its endpoint against its start: a leap with a tolerance, as Brandon read it.

**(2) Its second-order motion.** The kinetic solve already holds a mass. A move's kinetic energy is
`½⟨Mv, v⟩`, with `M = I ⊗ H′` the squared storage change the move causes on the passage's data:
inertia of storage. The Fisher pullback `K = AᵀFA` is the comparison's curvature, a stiffness and
not a mass, which agrees with Astra's point. The modes of `E`'s motion are the constitution's
`Kv = ω²Mv`. The leap is the static limit: it jumps to the quadratic model's equilibrium. A throw
is `M Ë + D Ė + ∇L = 0`. Its velocity is a carried moment of the returns,
`v_(k+1) = β v_k − η M⁻¹Aᵀμ_k`, of the same kind as the source's phase-carried moments, so it needs
no tape. [agent-inferred] On a quadratic model the damping that converges fastest is
`β = ((√κ − 1)/(√κ + 1))²` with `κ = ω²_max/ω²_min`. The kinetic solve's own iterates read these
frequencies, so the damping is a reading, not a chosen constant (owed, #62). This agrees with #199.
The force is always `Aᵀμ` read through `M⁻¹`, so a throw makes no hidden direction native. It
changes where along the visible directions the state travels in time, not the span at a state.

**Its admission.** A throw is admitted while its energy `H = ½⟨Mv, v⟩ + L_held` falls, in place of
`L_held` alone. Then `L` can rise during the flight by at most the kinetic energy it carries
(`comparison_le_energy`). From rest the rule is the leap's (`leap_confined`). [agent-inferred] The
discrete law, a step whose certified decrease of `H` holds at the lattice, is owed (#62).

**(3) What a throw reaches that the leap cannot.**
- **Not a new direction.** A velocity summed from the same steps is a sum with nonnegative weights.
  If every summed step points away from `u*`, so does the velocity (`pairing_nonpos_of_steps`).
  The main line measured all 16 moves pointing away, so a momentum built from those steps at those
  states points away as well. Within one quadratic model, a throw from rest moves each mode only
  toward and past its equilibrium, at most twice as far (`throw_solves`, `throw_between`).
- **It crosses passes.** The state reaches a pass `P` only if
  `L(P) ≤ L(E_k) + ½⟨Mv_k, v_k⟩ − (damping work before P)`. A leap crosses a pass only when one
  endpoint lands past it and below its start (#223 §4d: a move certifies only its endpoints).
- **The condition.** A throw reaches the fit's basin exactly when the fit lies across a pass (§4's
  first case) and two things hold: the lowest pass on its way is lower than the carried energy, and
  past the pass the force turns toward the fit. In the metric case a throw in the same metric does
  not help at first order. In the orbit case there is nothing to cross.
- [agent-inferred] **What the float fit has.** In the ablation, plain gradient steps without momentum
  reached 57 of 128 whole sections on two of three seeds, as many as Adam. Momentum was not required
  ([the refit's ingredients](2026-10-02_THE_REFITS_INGREDIENTS_ABLATED_WHICH_PART_OF_THE_EXTERIOR_FIT_REACHES_THE_REPRESENTATION.md)
  §2). Every float step was accepted whatever it did to the comparison, with a decaying step: an
  energy budget that is never checked, slowly cooled. So what the float path has and the native
  move lacks is admitting rises of the held comparison. A throw admits them, bounded by its own
  energy.

## 6. The reads that decide it

At one shared start (`m6` at the fit's `ρ`):
1. `d²(E, orbit)` and `u*` by §3's formula, and the cosine reads repeated against `u*`.
2. `s = ⟨g, u*⟩`, with the cosines of the native gradient, the kinetic step and the float
   objective's gradient against `u*`. These name the case (§4).
3. If it is a pass: `L` read along the chord `E + τu*`, its largest rise above `L(E)` and where it
   occurs. That rise is the energy a throw must carry. The kinetic energy a throw would hold there
   is `½⟨Mv, v⟩`, with `v` the summed steps of the chain.

A throw is built only if read 2 says pass and read 3 shows a rise within the energy the motion can
carry. Building it changes HNN behaviour, so it is measured on campaign 1's held-out sections before
it merges.

## 8. The main line's read: the metric turns the step

**Measured** (main line, relayed by the coordinator). At one shared start, the float probe's opening
equals the native opening exactly, both at `ρ₀`. Signed squared cosines, in units of `1/4096`:

| Pair | Signed cos² |
|---|---|
| native gradient `G` vs the float descent `−∇L_float` | `+1693` |
| native normal-law step `ΔE` vs `−∇L_float` | `+1702` |
| `G` vs the kinetic step `k` | `+37` |
| `ΔE` vs `k` | `+35` |
| `G` vs `fit − start` | `+2` |
| `ΔE` vs `fit − start` | `+4` |

The native gradient and the float objective's descent agree. The gradient points toward the fit,
weakly, so §4's case is not a pass at the start: it is the metric. The kinetic step turns away
from the gradient that both objectives share.

**(a) Why the receiver's form is so anisotropic.** On one lock, with `F = diag θ − θθᵀ` on the
non-resting sheets and `c = θ − e_t`, the Gauss–Newton change of the readings is `w = e_t/θ_t`
(`fisher_step_target_only`). It raises only the target, by the inverse of its share, and asks every
rival reading to stay where it is. The gradient weighs the same target by `1 − θ_t` and also lowers
the rivals. Relative to the gradient, the step therefore reweighs each station by about `1/θ_t`,
and the worst-read targets, those with the smallest share, dominate it. In the mass-whitened
coordinates, where the readings' Jacobian has singular values `σ_i`, the gradient's components go as
`σ_i` and the step's as `1/σ_i`. The step is carried by the weakly read directions, and the
gradient by the well-read ones. [proved-standard; Kantorovich] For a positive form `P` with
condition number `κ` on the gradient's span, `cos(g, Pg) ≥ 2√κ/(1 + κ)`. The measured
`cos² = 37/4096` therefore needs `κ > 440`: at `κ = 441`, `4κ/(1 + κ)² = 1764/195364`, which lies
below `37/4096`. Read at its grain, any `cos²` below `38/4096` still needs `κ > 429`: at `κ = 430`,
`4κ/(1 + κ)² = 1720/185761`, below `38/4096`. The suppressed directions are the well-read ones. The
fit's path follows the gradient (`+1693`), so they carry it.

**(b) The leap, the overdamped flow and the throw.** The mass is the storage's inertia
`M = I ⊗ H′`, and the stiffness is the Fisher pullback `K = AᵀFA` (§5). For the motion
`M Ë + D Ė + ∇L = 0`:
- **The kinetic step is the static leap.** It jumps to the quadratic model's equilibrium `Kx = −g`,
  where `M` only settles the directions `K` does not read. It is independent of the damping, and
  each mode `i` moves `g_i/ω_i²`, without bound as the mode softens.
- **The overdamped flow under mass-proportional damping `D = γM` is the normal-law step.** That flow
  is `Ė = −M⁻¹g/γ`, the direction of `ΔE`. The main line's `+1702` says this native direction
  already follows the fit's descent.
- **The underdamped throw over a finite flight.** From rest, each mode moves at most the force's
  free fall `|g_i| τ²/2` by time `τ`, whatever its stiffness. `throw_le_free_fall` proves it for the
  undamped mode. Damping keeps the bound, since the velocity `g_i e^(−γt/2) sin(ω_d t)/ω_d` is at
  most `|g_i| t` in size; that case is owed in Lean (#62). Stiff modes
  (`ω_i τ ≫ 1`) reach their equilibrium as the leap does. Soft modes stay at free fall instead of
  the leap's `g_i/ω_i²`. The flight time cuts exactly the soft-mode amplification that turns the
  kinetic step.
- **A persistent push accumulates.** With `v_(k+1) = β v_k + a`, the velocity is
  `a(1 − β^k)/(1 − β)` (`carried_velocity`). A push that keeps its sign builds toward `a/(1 − β)`,
  while one that alternates averages out. The suppressed well-read directions are where the gradient
  keeps its sign (the gradient's `+1693` with the fit's descent), so a carried velocity grows along
  them. The steps that point away were the kinetic steps; a velocity carried from the normal-law
  steps is a different sum.

**What is exact.** Everything in the throw is rational on the lattice:
- the mass `M = I ⊗ H′`, a Gram of the passage's rational features at rational weights;
- the velocity, carried as a rational moment of the returns (`v ← βv − hM⁻¹g`);
- the position, deposited as every deposit is, rounded toward zero on the `2⁻²¹` lattice.

**Superseded the same day** by [the throw's record](2026-10-02_THE_THROW_CARRIES_ITS_MOMENTUM_THROUGH_THE_DEPOSITS_ACCRETED_MASS_AND_A_HALVING_HALVES_IT.md): the deposit's mass accretion is the damping and the flight runs from a release to its apex, so neither the excursion's interval nor `ω_min` is needed. The paragraph is kept as it was.

[agent-inferred] **The flight and the damping.** The flight is the excursion's interval: `W` moves
between its opening and its close, admitted while the energy `H = ½⟨Mv, v⟩ + L_held` falls
(§5). The damping is read from the modes. Critical damping of the softest admitted mode,
`β = 1 − 2hω_min`, is rational once `ω_min` is enclosed at a rational grain: the kinetic solve's
iterates enclose `ω²_min`, and rational bounds on its square root follow. Owed (#62): the discrete
energy law at the lattice and the enclosure of `ω_min`.

**Outside yardstick only.** The float fit (Adam: momentum and a near-sign diagonal scale) shows what
a carried, nearly diagonal motion reaches. It is not the mechanism. The native counterpart is
built from `M`, the returns and the excursion's interval above.

**(c) Which native metric is near the identity on `E`.** The normal law's chart is `M⁻¹ = I ⊗
H′⁻¹`. It acts identically on all 120 rows, and on the 5 columns through the feature Gram, which the
one-hot station features make close to diagonal in the class basis. The `Coordinate` metric moves
`E` by this law. The `Witness` metric moves `E` along the port's unit move, the same direction, and
sizes only its plane with `ρ`. [agent-inferred] Both should therefore read like `ΔE` against `G`
(`+1702` against the float descent). Only `Kinetic` and `KineticModulus` carry the anisotropic
reweighting. The main line's read of the Coordinate and Witness steps against `G` tests this.

## 9. Verification and what is owed

- `bash tools/lean_check.sh HolonicsResearch.HNN.MoveDirection`: "Build completed successfully
  (8706 jobs)", no warnings, no `sorry`.
- `opening_symmetry.py` (exact integers, under one second): no nontrivial fixing element; at most
  151 of 300 entries agree under one element.
- **Owed (#62):** the ring's reversal symmetry; orbit invariance of the Floquet certificate's
  refusals; the equivariance of every rounding in the chain, checked call by call; the throw's
  discrete energy law and its damping read from the modes; the free-fall bound for the damped mode.
