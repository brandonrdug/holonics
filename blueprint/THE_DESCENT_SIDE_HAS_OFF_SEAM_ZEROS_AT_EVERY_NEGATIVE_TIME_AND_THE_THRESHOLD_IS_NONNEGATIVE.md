# The descent side has off-seam zeros at every negative time, and the threshold is nonnegative

**Founded:** 2026-09-03, by Brandon's direct request: *"I would indeed like to move towards RT,
but I need you to further scope what will be required and constructed more critically, and
formally deposit the RT plans."*  
**Authority:** this is a subordinate contract. [`THE_ROADMAP.md`](THE_ROADMAP.md) alone orders
construction and [`../CONSTRUCTION_STATE.md`](../CONSTRUCTION_STATE.md) alone records position;
this file composes the phases the roadmap lists under the RH line and schedules nothing by
itself.  
**Truth status:** `definition` for the contract; every returned phase carries its own grade under
[`../canon/EPISTEMIC_GRADES.md`](../canon/EPISTEMIC_GRADES.md).  
**Occasion:** the closure of the Foster-tank campaign
([`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md))
at the deposited-inequality scope, whose FT6 return carries two ports, `DeBruijnBound :
½ ∈ seamTimes` and `RodgersTaoNonneg : 0 ≤ Λ_DN`, and Brandon's question that followed: whether
Rodgers--Tao's result is available as a formalization. It is available as two published proofs
and as no formal artifact anywhere (Mathlib holds nothing on the de Bruijn--Newman constant;
searches of 2026-09-03 found no Lean development). The receipt of the scoping is
[`the RT0 record`](../research/records/2026-09-03_RT0_THE_TWO_PUBLISHED_PROOFS_ARE_MAPPED_TO_OWNERS_AND_THE_DESCENT_ROUTE_IS_FOUNDED_ON_THE_FLOWED_INTEGER_EVENTS.md).

---

## 0. The target, stated once

[definition] The target is the discharge of the port `RodgersTaoNonneg`: the theorem
`0 ≤ Λ_DN` on `propext`, `Classical.choice`, `Quot.sound` alone, so that
`ThresholdReturn.riemannHypothesis_iff_Λ_DN_eq` rests on de Bruijn's bound alone. In the flow's
coordinate the statement is: **for every standard time `τ < 0`, that is every repository time
`t = −τ > 0`, `heatE t ξ` has a zero off the seam `Re z = ½`.** Then `seamTimes ⊆ Set.Ici 0`, and
`Λ_DN = sInf seamTimes ≥ 0` (Mathlib's `Real.sInf_empty` gives `sInf ∅ = 0`, so this inequality
needs no nonemptiness; nonemptiness remains de Bruijn's port and is needed only for
`Λ_DN ≤ 0 ⇒ RH`).

[definition] The prohibition of the Foster contract binds in full: no phase returns a structure
whose field is the target or an implication to it; no numerical enclosure substitutes for a
theorem; no coordinate transport without the factor and sign of the 2026-09-02 correction; every
owner is Lean under the root umbrella; no estimate of duration is a phase artifact. Added here:
**no phase may cite Rodgers--Tao's or Dobner's theorem as a port to discharge a phase of this
contract.** The ports exist only in `ThresholdReturn` until RT6 replaces one of them.

## 0b. The critical scoping: two published proofs, one the tree can carry

[established-bounded; source-inspected] **Rodgers--Tao** (arXiv 1801.05914; Forum of
Mathematics, Pi 8 (2020)). Assume `Λ < 0`; this gives RH, so every RH-conditional theorem is
available. The chain is: Lemma 4 (saddle-point asymptotics of `H_t(x − iκ log x)` and of
`H_t′/H_t`, by contour shifting to Gamma-type integrals and Stirling); Theorem 9 and Corollary 10
(Riemann--von Mangoldt counts for `H_t` with error `O(log² T)`, by Jensen and the argument
principle); Theorem 11 (the zero ODE, from Csordas--Smith--Varga 1994, with simplicity of every
zero for `t > Λ`); Lemma 12, Lemma 14, Proposition 13 (gap dynamics, cross-energy inequality, the
lower bound `log(1/(x_{j+1} − x_j)) ≪ log² j · log log j`); Propositions 15, 17, 22 and Lemmas
16--21, 24, Corollary 25 (the cutoff Hamiltonian `H̃_T`, the renormalized energy `Ẽ_T`,
`∂_t H̃_T = −4 Ẽ_T + negligible`, the integrated bound `∫ Ẽ_T dt = o(T log³ T)`); Propositions
26--28 (energy at time zero by Bourgain's pigeonholing); and §9, where
`Ẽ(0) = o(T log³ T)` forces `x_{j+1}(0) − x_j(0) = (4π + o(1))/log T` for almost all `j`, which
contradicts Conrey--Ghosh--Goldston--Gonek--Heath-Brown 1985 (a positive proportion of gaps at
most `λ` times the mean for every `λ > 0.77`), a theorem whose own proof is Montgomery's
pair-correlation method: the explicit formula against the Montgomery--Vaughan mean-value
theorem. **Verdict:** the fleet document's `RT6` hides a second programme (Montgomery 1973 and
CGGGH-B 1985), neither formalized anywhere; `RT1` needs complex Stirling with a remainder, which
Mathlib lacks; `RT3` alone is a theorem in the tree.

[established-bounded; source-inspected] **Dobner** (arXiv 2005.05142, 2020; announced in
Rodgers--Tao's Remark 3). For standard `t < 0`: the deformation is the Gaussian convolution of
`ξ` along a vertical line (his equation (9)); each Dirichlet term of `ξ` convolves to a term with a
computable Gaussian weight, and after the shift `J_t(s) = s + (|t|/2) log Q + (|t|/2) Σ_i ω_i
Log(ω_i s)` (for `ζ`: `Q = π^{−1/2}`, one factor with `ω = ½`, `μ = 0`) his Theorem 4 gives,
uniformly for `|x| ≤ C y^{1/4}` and `y` large,
`ξ_t(J_t(s)) = γ_t(s) (F_t(s) + O(y^{−1/5} e^{(10/|t|) min(x, −2)²}))` with
`F_t(s) = Σ_n e^{−|t| log² n / 4} n^{−s}`, everywhere absolutely convergent; the term split is
`|t| log n ≤ y^{1/3}` (main), `≤ y^{3/5}` (exponentially small), and the rest (doubly
exponentially small). Lemma 3: `F_t` has a zero, and by Bohr's almost periodicity zeros at
unbounded heights in a fixed strip; Rouché transfers them to zeros of `ξ_t ∘ J_t`; and
`Re J_t(s) → ∞` with the height, so the zeros of `ξ_t` lie to the right of the seam. Inputs: Stirling
with a remainder (his Lemma 1), inverse-Mellin decay (Lemma 2), per-term steepest descent
(Lemma 4), the Taylor expansion of `γ` (Lemma 5), Bohr's theorem (his Theorem 5), Rouché. **No
zero statistics, no counts, no zero-free region, no Laguerre--Pólya structure, and no information
about the zeros of `ζ`.**

[definition] **The tree's position, and the route.** The Foster contract's FT5 already returned
the termwise structure Dobner estimates. `FlowedExplicitFormula.hasSum_flowedTerm` states: for
repository `t ≥ 0` and `Re z > 1`, `heatE t ξ (z) = Σ_{n ≠ 0} ∫ flowedTerm t z n`, where the flowed
integer event is `e^{−t u²} e^{(z − ½) u} |n|^{−1/2} φ(u + log |n|)`. Repository `t > 0` is
standard `τ < 0`: the descent side, Dobner's regime, exactly where FT5 converges (and FT5's
divergence for repository `t < 0` is the forward side, where the contract's integer-side
inequality could not be formed). The flowed integer events are Dobner's per-term Gaussian
convolutions. Therefore this contract founds the RT programme on the **descent route**, and keeps
the Rodgers--Tao route as the alternate of §2 with its obstructions named. The labels
`RT0`--`RT6` of the fleet document are re-assigned to the descent route by this deposit; the
fleet's meanings are preserved under `RTa1`--`RTa6` in §2.

## 1. The ordered phases

### RT0 — the manifest and the route

Return the source-exact map from both published proofs to current owners, Mathlib owners, and
missing owners, and the founding of the route on FT5's flowed integer events.

*Returned 2026-09-03:*
[`the RT0 record`](../research/records/2026-09-03_RT0_THE_TWO_PUBLISHED_PROOFS_ARE_MAPPED_TO_OWNERS_AND_THE_DESCENT_ROUTE_IS_FOUNDED_ON_THE_FLOWED_INTEGER_EVENTS.md).
**RT0 passes.**

### RT1 — the descent comb everywhere

For repository `t > 0` and every `z`, `Σ_{n ≠ 0} ∫ flowedTerm t z n` converges absolutely and
equals `heatE t ξ (z)`; each event carries the Gaussian weight in `n`,
`‖∫ flowedTerm t z n‖ ≤ C(t, z) e^{−c (log |n|)²}` with `c = min(t, 1)/8` (corrected in place from
the `t/4`-type first written; the record states why), by the split of the `u`-line at `−log|n|/2`;
the identity holds at every `z` by the kernel's own exchange, no continuation needed. Owner
`RH/DescentComb.lean`.

*Returned 2026-09-03:* `DescentComb.hasSum_flowedTerm_of_pos`,
`summable_norm_integral_flowedTerm`, `integral_norm_flowedTerm_le` (`K(t,z)|n|^{−3/2}`),
`integral_norm_flowedTerm_le_gaussian` (`K₂(t,z) e^{−(min(t,1)/8)(log|n|)²}`), and the profile
bounds `abs_φ_le`, `abs_φ_le_of_nonneg`; receipt
[`the RT1 record`](../research/records/2026-09-03_RT1_THE_DESCENT_COMB_CONVERGES_ABSOLUTELY_AT_EVERY_POINT_AND_EACH_EVENT_CARRIES_A_GAUSSIAN_WEIGHT_IN_N.md).
**RT1 passes.**

**Pass RT1:** `HasSum` at every `z` for every `t > 0`, formal-checked.  
**Falsifier:** one `t > 0`, one `z`, and a divergent comb.

### RT2 — Stirling with a remainder

`log Γ(s) = (s − ½) log s − s + ½ log 2π + O(1/|s|)` on `Re s ≥ 1`, with the constant exhibited,
and the consequences for `Γ_ℝ(s) = π^{−s/2} Γ(s/2)` and for the log-derivative. Mathlib holds real
Stirling for `n!` only; the tree's `GammaBound`, `GammaGrowth`, `GammaDecay` are magnitude bounds.
This is the one owner both routes need. Owner `RH/GammaStirling.lean`.  
**Pass RT2:** the remainder bound formal-checked.  
**Falsifier:** a point on `Re s ≥ 1` violating the exhibited constant.

### RT3 — the event by steepest descent

For repository `t > 0`, each flowed integer event after the shift `J_t` equals
`γ_t(z) e^{−t log² n / 4} n^{−z} (1 + r_n(z))` with `|r_n(z)|` bounded as in Dobner's Lemma 4 under
the three-range split of §0b. The shift `J_t` and `γ_t` are defined here from RT2. Owner
`RH/DescentEvent.lean`.  
**Pass RT3:** the per-event identity with its remainder bound, formal-checked.  
**Falsifier:** an `n`, `z` in the window outside the bound.

### RT4 — the approximation theorem

`heatE t ξ (J_t s) = γ_t(s) (F_t(s) + R_t(s))` with `‖R_t(s)‖ ≤ C y^{−1/5} e^{(10/t) min(x, −2)²}`
uniformly for `|x| ≤ C y^{1/4}`, `y ≥ y₀(t)`, by RT1's absolute convergence and RT3's per-event
bound summed over the three ranges. Owner `RH/DescentApproximation.lean`.  
**Pass RT4:** the uniform bound formal-checked.  
**Falsifier:** a point in the window where the remainder exceeds the bound.

### RT5 — the Dirichlet series has zeros at every height

`F_t` is an absolutely convergent Dirichlet series, not a monomial; it has a zero (Dobner's
Lemma 3), and by Bohr's almost periodicity a zero within a bounded distance of every height in a
fixed strip. Bohr's theorem is simultaneous Diophantine approximation of finitely many
`log p` multiples by pigeonhole, then the tail; Mathlib holds only the one-dimensional Dirichlet
theorem (`Real.exists_int_int_abs_mul_sub_le`). Owner `RH/BohrZeros.lean`.  
**Pass RT5:** for every `t > 0` a strip and a bound `L` with a zero of `F_t` in every window of
height `L`, formal-checked.  
**Falsifier:** a window of height `L` in the strip with no zero.

### RT6 — the transfer and the seal

Rouché's transfer on discs (from the tree's `RectangleArgumentPrinciple` and `HurwitzLine`, or
`Complex.norm_le_of_forall_mem_frontier_norm_le` with the argument principle) carries each zero of
`F_t` at large height to a zero of `heatE t ξ ∘ J_t`; `Re J_t(s) − ½ → ∞` with the height, so the
zero of `heatE t ξ` is off the seam. Hence for every repository `t > 0` a zero off the seam;
`seamTimes ⊆ Set.Ici 0`; `Λ_DN_nonneg : 0 ≤ Λ_DN`; and `ThresholdReturn` re-stated with the single
port `DeBruijnBound`. Owners `RH/DescentZeros.lean`, `RH/ThresholdReturn.lean` amended.  
**Pass RT6:** `0 ≤ Λ_DN` on the three axioms, `#print axioms` deposited, root umbrella green under
180 s per owner.  
**Falsifier:** a repository `t > 0` at which every zero of `heatE t ξ` is on the seam; it cannot
fire against the published theorem, so a firing is a construction error of RT1--RT5.

## 2. The alternate: the Rodgers--Tao route, kept with its obstructions

[definition] The fleet document's labels are preserved here and not scheduled:

1. `RTa1` (`H_t` asymptotics, Lemma 4): needs RT2 and the saddle-point shift; nothing in the tree.
2. `RTa2` (Riemann--von Mangoldt for `H_t`, Theorem 9): the tree has Jensen (`RH/Jensen.lean`,
   Mathlib's `JensenFormula`), the rectangle argument principle, and the count `K₁ + K₂ R^{3/2}`
   of the Foster class; the `O(log² T)` count needs `RTa1`.
3. `RTa3` (the zero ODE, Theorem 11): **a theorem**, `FosterClassHeatFlow.rodgersTaoZeroDynamics_heatE`
   and `SimpleZeroCurve.exists_zero_curve_riemannXi`; the global ordering `x_j(t)` and simplicity
   for all `t > Λ` (Csordas--Smith--Varga, Corollary 1) are not returned.
4. `RTa4` (gap lower bound, Proposition 13, Lemmas 12, 14): untouched.
5. `RTa5` (cutoff Hamiltonian, Propositions 15, 17, 22, Corollary 25): untouched.
6. `RTa6` (energy at time zero, Propositions 26--28, and §9): untouched; its external input is
   CGGGH-B 1985 on Montgomery's pair-correlation method, a second contract of its own.

## 3. What stays open after this campaign

[open; project-postulate] de Bruijn's bound `½ ∈ seamTimes` (Ki--Kim--Lee 2009 sharpen it to
`Λ < ½`). It is not needed for `0 ≤ Λ_DN`. Its route is Pólya's universal-factor theorem at the
entire face, which the tree's forward preservation already is, plus de Bruijn's real-rooted
starting family (Pólya 1927): a separate contract when directed.

[open] The conjecture `Λ_DN ≤ 0`, with its null falsifier, unchanged.

## 4. Relation to the engine frontier

[definition] Brandon directed this scoping on 2026-09-03 while `SKE4` is the engine frontier. The
roadmap carries this campaign as the RH line's ordered position beside the engine's. The two lines
share no owner and no process; each advances on its own gate.
