import Holonics.Holon.Cayley
import Holonics.Geometry.AffineSwing
import Holonics.Computation.HolonicAdjointNormalization
import Holonics.Computation.HolonicConstitutiveCirculation
import Holonics.Computation.HolonicWorldReturnDeposit
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# HNN.Propagation: the junction Swing, the contact transit and the causal cone

[definition] Rebuild step 4 (#73), campaign 1, design item 2 (`docs/plans/THE_REBUILD.md`,
"Step 4 design: the HNN law", *The law of one passage*). One tick of a word is one contact hop:
at each ring a junction Swing about its participation anchor, then the ring's element, then on
each contact the midpoint two-port transit. A change moves one contact per tick. There is no
global solve over the contact graph.

```text
junction   v_r = (Y_r s_r + Σ_a G_a a_(r←a)) / (Y_r + Σ_a G_a),   o_(r→a) = 2 v_r − a_(r←a),   b_r = 2 v_r − s_r
transit    α_g = ι_gᵀ o_g,  α_h = ι_hᵀ o_h,   M_a ω = 2C w + h(α_g − α_h) − h K u,
           M_a = 2C + (2h/G) I + h D + (h²/2) K,   w′ = 2ω − w,  u′ = u + hω,
           a_(g←a) = o_g − (2/G) ι_g ω,  a_(h←a) = o_h + (2/G) ι_h ω
```

[proved-derived; formal-checked] What is proved.

1. **The junction.** The anchor is the `W`-weighted mean of the ring's arrivals, its own storage
   port included (`W = diag(Y_r, G_a)`): its weights are the normalized participation, positive and
   summing to one, and it is the unique point where the weighted residual vanishes
   (`anchor_is_participation`). Each output is the point Swing `AffineSwing.swing` about it. The
   junction is the source-derived scatter `2P − I` of `HolonicAdjointNormalization`
   (`junction_eq_sourceDerivedScatter`), hence an involution (`junctionSwing_involutive`, from
   `sourceDerivedScatter_involutive`), and it is a `W`-isometry for any weights with nonzero sum
   (`junctionSwing_isometry`). With one contact port it is exactly the scalar two-port junction of
   `HolonicConstitutiveCirculation`, whose conserved weighted square energy
   (`weighted_square_energy`) is the isometry's two-port case (`junctionSwing_twoPort`).
2. **The contact.** `U_a = ι_h ι_gᵀ` is a partial isometry whose reverse is `U_aᵀ = ι_g ι_hᵀ`; the
   channel part and the untransmitted part of a wave split its norm; and the constitution-free
   transit is pure transmission, `a_(g←a) = (I − ι_gι_gᵀ) o_g + U_aᵀ o_h`, conserving the summed
   wave norm (`partialIsometry_transit`). The contact's midpoint two-port obeys
   `E_a′ − E_a + h⟨ω, D ω⟩ = (hG/4)(|α|² − |α_out|²)` in its channel waves, and the same in its
   full waves (`transit_balance`, for symmetric `C`, `K`; `D` enters only through its power).
3. **The tick is well defined, and nothing more is claimed.** The element's `I − ½K` is bijective
   for `K = W_s + Σ σ_ρ A_ρ` with `W_s` passive and `A_ρ` skew (`Holon/Cayley.cayley_bijective`,
   `inner_devK`), and `M_a` is positive definite for `C_a, D_a, K_a ⪰ 0`, `G_a, h > 0`
   (`tick_well_defined`). The element step and the transit's reverse are not claimed invertible:
   `K = −2` makes the element step zero, and `C = (h/G) I` makes the reverse transit operator zero
   (`tick_step_not_invertible`, R2 H2). Passivity and positivity are load-bearing: an active element
   or a non-PSD stiffness makes a local solve impossible (`tick_needs_passive_and_psd`).
4. **The causal cone and the diamond** on the block graph of a word (blocks: ring storage with its
   received waves, contact states; edges: the block operators of one tick). A change after `t`
   ticks is supported in the ball of radius `t` (`tick_causal_cone`), and a covector swept back
   `t − k` ticks from the receivers is supported where the receivers are observable within
   `t − k` hops (`covector_causal_cone`). The reading pairs exactly with the swept covector at every
   intermediate tick, the return composing the ticks' duals in reverse
   (`trajectory_pairing`, over `dualMap_comp_reverse_order`), and a change of the block operators
   changes a reading by exactly `Σ_(k<t) ⟨λ′_(k+1), (T′ − T) x_k⟩` (`word_variation_exact`: no
   inverse, no tape, only the word's own trajectory). The return's covector on the edge `z → y`
   vanishes unless `r_z + 1 + o_y ≤ t` (`reached_loci_diamond`), so an operator on an edge outside
   the diamond `r_x + 1 + o_y ≤ e_last` changes no admitted reading (`release_past_diamond`, R3 R1).

[definition] The reach and observe distances are carried as walk predicates: `ReachIn adj x y n`
is a walk of `n` hops, `reachWithin S t` the blocks within `t` hops of the sources, and
`Observes R y m` that some receiving block is within `m` hops of `y`.

[definition] **What §4 covers: the abstract model, not the concrete tick.** The theorems of §4
(`tick_causal_cone`, `covector_causal_cone`, `trajectory_pairing`, `word_variation_exact`,
`reached_loci_diamond`, `release_past_diamond`, `trajectory_agrees_where_observed`,
`sweep_agrees_where_reached`) are proved for an abstract word: a time-invariant linear block
operator family `BlockOp K M` (`T y z : M z →ₗ[K] M y`, fixed within the word) that is `Sparse` on
an abstract block graph `adj`, iterated by `tick`/`trajectory`. They are not proved for
`HNN/Word.fieldTick`, the concrete tick of junctions, elements and transits. What is proved of the
concrete tick is in `HNN/Word`: its local solves (`elementSolve_spec`, `transitSolve_spec`), its
power balance (`fieldTick_balance`), its locality (`fieldTick_local`) and its cone on the
ring/contact block graph `blockAdj` (`word_tick_cone`). The bridge is owed in #62, "Step 4 (#73)
owed: the diamond on the concrete tick": `fieldTick` is linear in the change at fixed operands (its
local solves are the unique solutions of linear equations), and it is the `tick` of a `BlockOp` on
`Ring ⊕ Contact` that is `Sparse blockAdj`; then §4 and `HNN/Retention` apply to the concrete word
verbatim. Until then the Rust owners cite §4 as the abstract model's law.

[open] The continuum limit (the telegraph law of the junction Swing with transit and its
overdamped connection heat equation) is a reading, owed in #62. The concrete-tick bridge above is
owed in #62.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Propagation

open Holonics.Geometry.AffineSwing
open Holonics.Computation.HolonicAdjointNormalization
open scoped BigOperators

/-! ## 1. The junction Swing about the participation anchor -/

section Junction

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {ι : Type*} [Fintype ι]

/-- [definition] The junction's admittance sum `Y_r + Σ_a G_a`: the storage port's admittance and
one conductance per contact port. -/
def admittanceSum (Y : ℝ) (G : ι → ℝ) : ℝ := Y + ∑ p, G p

/-- [definition] **The participation anchor** `v_r = (Y_r s_r + Σ_a G_a a_(r←a)) / (Y_r + Σ_a G_a)`. -/
def anchor (Y : ℝ) (G : ι → ℝ) (s : V) (a : ι → V) : V :=
  (admittanceSum Y G)⁻¹ • (Y • s + ∑ p, G p • a p)

/-- [definition] The wave the junction returns to the ring's storage port, `b_r = 2 v_r − s_r`. -/
def storageOut (Y : ℝ) (G : ι → ℝ) (s : V) (a : ι → V) : V := swing (anchor Y G s a) s

/-- [definition] The wave the junction sends into contact port `p`, `o_(r→a) = 2 v_r − a_(r←a)`. -/
def portOut (Y : ℝ) (G : ι → ℝ) (s : V) (a : ι → V) (p : ι) : V := swing (anchor Y G s a) (a p)

/-- [definition] The whole junction on the ring's ports. -/
def junction (Y : ℝ) (G : ι → ℝ) (x : V × (ι → V)) : V × (ι → V) :=
  (storageOut Y G x.1 x.2, portOut Y G x.1 x.2)

theorem admittanceSum_smul_anchor (Y : ℝ) (G : ι → ℝ) (hsum : admittanceSum Y G ≠ 0)
    (s : V) (a : ι → V) :
    admittanceSum Y G • anchor Y G s a = Y • s + ∑ p, G p • a p := by
  rw [anchor, smul_smul, mul_inv_cancel₀ hsum, one_smul]

/-- [proved-derived; formal-checked] **The anchor is the participation-weighted mean** (R2 C1).
With `Y_r > 0` and `G_a ≥ 0` the weights `Y_r/Σ` and `G_a/Σ` are the ring's normalized
participation, its own storage port included: nonnegative, summing to one, and the anchor is their
mean. It is the unique point at which the `W`-weighted residual vanishes. -/
theorem anchor_is_participation (Y : ℝ) (G : ι → ℝ) (hY : 0 < Y) (hG : ∀ p, 0 ≤ G p)
    (s : V) (a : ι → V) :
    anchor Y G s a = (Y / admittanceSum Y G) • s + ∑ p, (G p / admittanceSum Y G) • a p ∧
      Y / admittanceSum Y G + ∑ p, G p / admittanceSum Y G = 1 ∧
      0 < Y / admittanceSum Y G ∧ (∀ p, 0 ≤ G p / admittanceSum Y G) ∧
      Y • (anchor Y G s a - s) + ∑ p, G p • (anchor Y G s a - a p) = 0 ∧
      ∀ v : V, Y • (v - s) + ∑ p, G p • (v - a p) = 0 → v = anchor Y G s a := by
  have hsum_pos : 0 < admittanceSum Y G :=
    add_pos_of_pos_of_nonneg hY (Finset.sum_nonneg fun p _ => hG p)
  have hsum : admittanceSum Y G ≠ 0 := hsum_pos.ne'
  have hres : ∀ v : V, Y • (v - s) + ∑ p, G p • (v - a p) =
      admittanceSum Y G • v - (Y • s + ∑ p, G p • a p) := by
    intro v
    simp only [smul_sub, Finset.sum_sub_distrib, admittanceSum, add_smul, Finset.sum_smul]
    abel
  refine ⟨?_, ?_, div_pos hY hsum_pos, fun p => div_nonneg (hG p) hsum_pos.le, ?_, ?_⟩
  · rw [anchor, smul_add, Finset.smul_sum, smul_smul]
    congr 1
    · rw [div_eq_inv_mul]
    · exact Finset.sum_congr rfl fun p _ => by rw [smul_smul, div_eq_inv_mul]
  · rw [← Finset.sum_div, ← add_div]
    exact div_self hsum
  · rw [hres, admittanceSum_smul_anchor Y G hsum, sub_self]
  · intro v hv
    rw [hres, sub_eq_zero] at hv
    rw [anchor, ← hv, smul_smul, inv_mul_cancel₀ hsum, one_smul]

/-- [proved-derived; formal-checked] **The junction keeps its anchor.** The Swing's outputs have
the same participation anchor, because a point Swing negates each displacement from the anchor
(`AffineSwing.theSwingNegatesTheDisplacementFromTheAnchor`) and the weighted displacements sum to
zero. -/
theorem junction_anchor_preserved (Y : ℝ) (G : ι → ℝ) (hsum : admittanceSum Y G ≠ 0)
    (s : V) (a : ι → V) :
    anchor Y G (storageOut Y G s a) (portOut Y G s a) = anchor Y G s a := by
  set v := anchor Y G s a
  have hv := admittanceSum_smul_anchor Y G hsum s a
  have hout : Y • storageOut Y G s a + ∑ p, G p • portOut Y G s a p =
      admittanceSum Y G • v := by
    simp only [storageOut, portOut, swing]
    have : Y • (v + v - s) + ∑ p, G p • (v + v - a p) =
        (2 : ℝ) • (admittanceSum Y G • v) - (Y • s + ∑ p, G p • a p) := by
      simp only [smul_sub, smul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        admittanceSum, add_smul, Finset.sum_smul, two_smul]
      abel
    rw [this, hv, two_smul, add_sub_cancel_right]
  rw [anchor, hout, smul_smul, inv_mul_cancel₀ hsum, one_smul]

/-- [definition] The junction's participation map `D a = Σ_p (G_p/Y) a_p` from the contact ports to
the storage port. -/
def participationMap (Y : ℝ) (G : ι → ℝ) : (ι → V) →ₗ[ℝ] V where
  toFun a := ∑ p, (G p / Y) • a p
  map_add' a b := by simp [smul_add, Finset.sum_add_distrib]
  map_smul' c a := by simp [Finset.smul_sum, smul_smul, mul_comm]

/-- [definition] The common-potential map `v ↦ (v)_p` onto the contact ports. -/
def diagonalPorts : V →ₗ[ℝ] (ι → V) := LinearMap.pi fun _ => LinearMap.id

/-- [definition] The junction's normalized solve `Y/(Y + Σ G)`. -/
def junctionSolve (Y : ℝ) (G : ι → ℝ) : V →ₗ[ℝ] V := (Y / admittanceSum Y G) • LinearMap.id

/-- [proved-derived; formal-checked] The junction's normal solve hypothesis in the owner's form:
`Kinv (I + D Dᵀ) = I`. -/
theorem junction_normalSolve (Y : ℝ) (G : ι → ℝ) (hY : Y ≠ 0) (hsum : admittanceSum Y G ≠ 0) :
    normalSolveHypothesis (participationMap (V := V) Y G) diagonalPorts (junctionSolve Y G) := by
  apply LinearMap.ext
  intro v
  simp only [participationMap, diagonalPorts, junctionSolve, LinearMap.comp_apply,
    LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, LinearMap.coe_mk,
    AddHom.coe_mk, LinearMap.pi_apply]
  rw [← Finset.sum_smul, show v + (∑ i, G i / Y) • v = (1 + ∑ i, G i / Y) • v by
    rw [add_smul, one_smul], smul_smul]
  have : Y / admittanceSum Y G * (1 + ∑ p, G p / Y) = 1 := by
    rw [← Finset.sum_div, admittanceSum] at *
    field_simp
  rw [this, one_smul]

/-- [proved-derived; formal-checked] **The junction is the source-derived scatter `2P − I`** of
`HolonicAdjointNormalization`, with `D = Σ_p (G_p/Y) proj_p`, `Dᵀ` the common potential and
`Kinv = Y/(Y + Σ G)`: the projection `P` is onto the junction's common-potential subspace. -/
theorem junction_eq_sourceDerivedScatter (Y : ℝ) (G : ι → ℝ) (hY : Y ≠ 0)
    (hsum : admittanceSum Y G ≠ 0) (x : V × (ι → V)) :
    junction Y G x = sourceDerivedScatter (participationMap Y G) diagonalPorts (junctionSolve Y G) x := by
  have hv : junctionSolve Y G (x.1 + participationMap Y G x.2) = anchor Y G x.1 x.2 := by
    simp only [junctionSolve, participationMap, LinearMap.smul_apply, LinearMap.id_apply,
      LinearMap.coe_mk, AddHom.coe_mk, anchor, smul_add, Finset.smul_sum, smul_smul]
    congr 1
    · rw [admittanceSum] at *
      congr 1
      field_simp
    · refine Finset.sum_congr rfl fun p _ => ?_
      congr 1
      rw [admittanceSum] at *
      field_simp
  simp only [junction, sourceDerivedScatter, sourceDerivedProjection, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.id_apply, hv,
    storageOut, swing, diagonalPorts]
  refine Prod.ext ?_ ?_
  · simp [two_smul]
  · funext p
    simp [portOut, swing, two_smul]

/-- [proved-derived; formal-checked] **The junction Swing is an involution**: swinging the
outputs again returns the arriving waves (`sourceDerivedScatter_involutive`). -/
theorem junctionSwing_involutive (Y : ℝ) (G : ι → ℝ) (hY : Y ≠ 0)
    (hsum : admittanceSum Y G ≠ 0) (x : V × (ι → V)) :
    junction Y G (junction Y G x) = x := by
  rw [junction_eq_sourceDerivedScatter Y G hY hsum, junction_eq_sourceDerivedScatter Y G hY hsum]
  exact sourceDerivedScatter_involutive _ _ _ (junction_normalSolve Y G hY hsum) x

end Junction

section JunctionIsometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
variable {ι : Type*} [Fintype ι]

theorem norm_swing_sq (v x : V) :
    ‖swing v x‖ ^ 2 = ‖x‖ ^ 2 - 4 * inner ℝ v x + 4 * ‖v‖ ^ 2 := by
  simp only [swing]
  rw [show v + v - x = (2 : ℝ) • v - x by rw [two_smul], @norm_sub_sq_real, norm_smul,
    inner_smul_left, Real.norm_two]
  simp only [conj_trivial]
  ring

/-- [proved-derived; formal-checked] **The junction Swing is a `W`-isometry** (R2 C1), with
`W = diag(Y_r, G_a)` and one conductance per contact port:
`Y_r|b_r|² + Σ_a G_a|o_(r→a)|² = Y_r|s_r|² + Σ_a G_a|a_(r←a)|²`. Only the admittance sum must be
nonzero; the weights need no sign. -/
theorem junctionSwing_isometry (Y : ℝ) (G : ι → ℝ) (hsum : admittanceSum Y G ≠ 0)
    (s : V) (a : ι → V) :
    Y * ‖storageOut Y G s a‖ ^ 2 + ∑ p, G p * ‖portOut Y G s a p‖ ^ 2 =
      Y * ‖s‖ ^ 2 + ∑ p, G p * ‖a p‖ ^ 2 := by
  set v := anchor Y G s a
  have hv : admittanceSum Y G • v = Y • s + ∑ p, G p • a p :=
    admittanceSum_smul_anchor Y G hsum s a
  have hpair : Y * inner ℝ v s + ∑ p, G p * inner ℝ v (a p) = admittanceSum Y G * ‖v‖ ^ 2 := by
    have := congrArg (fun w => inner ℝ v w) hv
    simp only [inner_add_right, inner_sum, inner_smul_right, real_inner_self_eq_norm_sq] at this
    linarith
  simp only [storageOut, portOut, norm_swing_sq]
  have hexp : ∑ p, G p * (‖a p‖ ^ 2 - 4 * inner ℝ v (a p) + 4 * ‖v‖ ^ 2) =
      ∑ p, G p * ‖a p‖ ^ 2 - 4 * ∑ p, G p * inner ℝ v (a p) + 4 * (∑ p, G p) * ‖v‖ ^ 2 := by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum,
      Finset.sum_mul]
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun p _ => by ring
    · exact Finset.sum_congr rfl fun p _ => by ring
  rw [hexp]
  simp only [admittanceSum] at hpair
  nlinarith [hpair]

/-- [proved-derived; formal-checked] **The two-port case is the scalar circulation junction.** On a
one-dimensional ring with one contact port (admittance `a`, incoming wave `i`) and the storage port
(admittance `b`, held wave `h`), the junction's outputs are the `emitted` and `successorHeld`
outputs of `HolonicConstitutiveCirculation`, and their conserved weighted square energy
(`weighted_square_energy`, exact over `ℚ`) is the isometry above. -/
theorem junctionSwing_twoPort {a b i h : ℚ} (ha : 0 < a) (hb : 0 < b) :
    portOut (b : ℝ) (fun _ : Unit => (a : ℝ)) (h : ℝ) (fun _ => (i : ℝ)) () =
        ((Holonics.Computation.HolonicConstitutiveCirculation.emitted a b i h : ℚ) : ℝ) ∧
      storageOut (b : ℝ) (fun _ : Unit => (a : ℝ)) (h : ℝ) (fun _ => (i : ℝ)) =
        ((Holonics.Computation.HolonicConstitutiveCirculation.successorHeld a b i h : ℚ) : ℝ) ∧
      a * Holonics.Computation.HolonicConstitutiveCirculation.emitted a b i h ^ 2 +
          b * Holonics.Computation.HolonicConstitutiveCirculation.successorHeld a b i h ^ 2 =
        a * i ^ 2 + b * h ^ 2 := by
  have hab : (a : ℝ) + b ≠ 0 := by exact_mod_cast (add_pos ha hb).ne'
  have hab' : (b : ℝ) + a ≠ 0 := by rw [add_comm]; exact hab
  refine ⟨?_, ?_, Holonics.Computation.HolonicConstitutiveCirculation.weighted_square_energy ha hb⟩
  · simp only [portOut, anchor, admittanceSum, swing, Finset.univ_unique,
      Finset.sum_singleton, smul_eq_mul, Holonics.Computation.HolonicConstitutiveCirculation.emitted,
      Holonics.Computation.HolonicConstitutiveCirculation.junctionVelocity]
    push_cast
    field_simp
    ring
  · simp only [storageOut, anchor, admittanceSum, swing, Finset.univ_unique,
      Finset.sum_singleton, smul_eq_mul,
      Holonics.Computation.HolonicConstitutiveCirculation.successorHeld,
      Holonics.Computation.HolonicConstitutiveCirculation.junctionVelocity]
    push_cast
    field_simp
    ring

end JunctionIsometry

/-! ## 2. The contact: its channel, its partial isometry and its midpoint two-port -/

section Transit

variable {Ch Vg Vh : Type*}
  [NormedAddCommGroup Ch] [InnerProductSpace ℝ Ch] [FiniteDimensional ℝ Ch]
  [NormedAddCommGroup Vg] [InnerProductSpace ℝ Vg] [FiniteDimensional ℝ Vg]
  [NormedAddCommGroup Vh] [InnerProductSpace ℝ Vh] [FiniteDimensional ℝ Vh]

/-- [definition] A **channel embedding** `ι_(a,g)`: the partial port matching of contact `a` into
ring `g`'s nodes, an isometric embedding (`ιᵀ ι = I`; a 0/1 column selection in the exact chart). -/
def IsChannelEmbedding {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (ι : Ch →L[ℝ] V) : Prop :=
  (ContinuousLinearMap.adjoint ι).comp ι = ContinuousLinearMap.id ℝ Ch

/-- [definition] **The contact's transport** `U_a = ι_(a,h) ι_(a,g)ᵀ` from ring `g`'s nodes to
ring `h`'s. -/
def contactTransport (ιg : Ch →L[ℝ] Vg) (ιh : Ch →L[ℝ] Vh) : Vg →L[ℝ] Vh :=
  ιh.comp (ContinuousLinearMap.adjoint ιg)

theorem channel_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Ch →L[ℝ] V} (hι : IsChannelEmbedding ι) (x y : Ch) :
    inner ℝ (ι x) (ι y) = inner ℝ x y := by
  rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, hι,
    ContinuousLinearMap.id_apply]

theorem channel_adjoint_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Ch →L[ℝ] V} (hι : IsChannelEmbedding ι) (x : Ch) :
    ContinuousLinearMap.adjoint ι (ι x) = x := by
  rw [← ContinuousLinearMap.comp_apply, hι, ContinuousLinearMap.id_apply]

theorem channel_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] {ι : Ch →L[ℝ] V} (hι : IsChannelEmbedding ι) (x : Ch) :
    ‖ι x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, channel_inner hι]

/-- [definition] **The contact's midpoint operator** `M_a = 2C + (2h/G) I + h D + (h²/2) K`. -/
def transitOperator (C D K : Ch →L[ℝ] Ch) (G h : ℝ) : Ch →L[ℝ] Ch :=
  (2 : ℝ) • C + (2 * h / G) • ContinuousLinearMap.id ℝ Ch + h • D + (h ^ 2 / 2) • K

/-- [definition] The contact's local solve: `M_a ω = 2C w + h(α_g − α_h) − h K u`, one
`k_a`-sized solve. `ω` is the midpoint slip rate. -/
def TransitSolves (C D K : Ch →L[ℝ] Ch) (G h : ℝ) (u w αg αh ω : Ch) : Prop :=
  transitOperator C D K G h ω = (2 : ℝ) • C w + h • (αg - αh) - h • K u

/-- [definition] The contact's stored energy `E_a = ½⟨w, C w⟩ + ½⟨u, K u⟩`. -/
def contactEnergy (C K : Ch →L[ℝ] Ch) (u w : Ch) : ℝ :=
  (1 / 2) * inner ℝ w (C w) + (1 / 2) * inner ℝ u (K u)

/-- [definition] The waves the transit returns to the two rings. -/
def arriveG (ιg : Ch →L[ℝ] Vg) (G : ℝ) (og : Vg) (ω : Ch) : Vg := og - (2 / G) • ιg ω

/-- [definition] See `arriveG`. -/
def arriveH (ιh : Ch →L[ℝ] Vh) (G : ℝ) (oh : Vh) (ω : Ch) : Vh := oh + (2 / G) • ιh ω

omit [FiniteDimensional ℝ Ch] in
theorem norm_sub_smul_sq (x y : Ch) (c : ℝ) :
    ‖x - c • y‖ ^ 2 = ‖x‖ ^ 2 - 2 * c * inner ℝ x y + c ^ 2 * ‖y‖ ^ 2 := by
  rw [@norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

omit [FiniteDimensional ℝ Ch] in
theorem norm_add_smul_sq (x y : Ch) (c : ℝ) :
    ‖x + c • y‖ ^ 2 = ‖x‖ ^ 2 + 2 * c * inner ℝ x y + c ^ 2 * ‖y‖ ^ 2 := by
  rw [@norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

omit [FiniteDimensional ℝ Ch] in
/-- [proved-derived; formal-checked] **The contact's midpoint two-port balance** (R3 C1). For
symmetric `C` and `K` and `G ≠ 0`, the local solve gives, in the channel waves
`α_out,g = α_g − (2/G) ω`, `α_out,h = α_h + (2/G) ω`,
`E_a′ − E_a + h⟨ω, D ω⟩ = (hG/4)(|α_g|² + |α_h|² − |α_out,g|² − |α_out,h|²)`, with
`w′ = 2ω − w`, `u′ = u + hω`. -/
theorem transit_balance (C D K : Ch →L[ℝ] Ch) (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)) {G h : ℝ} (hG : G ≠ 0)
    {u w αg αh ω : Ch} (hsolve : TransitSolves C D K G h u w αg αh ω) :
    contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) - contactEnergy C K u w +
        h * inner ℝ ω (D ω) =
      h * G / 4 * (‖αg‖ ^ 2 + ‖αh‖ ^ 2 - ‖αg - (2 / G) • ω‖ ^ 2 - ‖αh + (2 / G) • ω‖ ^ 2) := by
  have hω := congrArg (fun v => inner ℝ ω v) hsolve
  simp only [transitOperator, _root_.add_apply,
    _root_.smul_apply, ContinuousLinearMap.id_apply, inner_add_right,
    inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq] at hω
  have hCw : inner ℝ w (C ω) = inner ℝ ω (C w) := by
    rw [← hC, real_inner_comm]
  have hKu : inner ℝ u (K ω) = inner ℝ ω (K u) := by
    rw [← hK, real_inner_comm]
  have hR : h * G / 4 * (‖αg‖ ^ 2 + ‖αh‖ ^ 2 - ‖αg - (2 / G) • ω‖ ^ 2 -
      ‖αh + (2 / G) • ω‖ ^ 2) = h * (inner ℝ ω αg - inner ℝ ω αh) - 2 * h / G * ‖ω‖ ^ 2 := by
    rw [norm_sub_smul_sq, norm_add_smul_sq, real_inner_comm αg ω, real_inner_comm αh ω]
    field_simp
    ring
  rw [hR]
  simp only [contactEnergy, map_add, map_sub, map_smul, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, conj_trivial, hCw, hKu]
  linear_combination hω

/-- [proved-derived; formal-checked] **The same balance in the full waves.** With channel
embeddings `ι_g`, `ι_h` and `α = ιᵀ o`, the untransmitted parts reflect with their norms, so the
balance reads `(hG/4)(|o_g|² + |o_h|² − |a_(g←a)|² − |a_(h←a)|²)`. -/
theorem transit_balance_waves (C D K : Ch →L[ℝ] Ch)
    (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y)) (hK : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y))
    {ιg : Ch →L[ℝ] Vg} {ιh : Ch →L[ℝ] Vh} (hιg : IsChannelEmbedding ιg)
    (hιh : IsChannelEmbedding ιh) {G h : ℝ} (hG : G ≠ 0) {u w ω : Ch} {og : Vg} {oh : Vh}
    (hsolve : TransitSolves C D K G h u w (ContinuousLinearMap.adjoint ιg og)
      (ContinuousLinearMap.adjoint ιh oh) ω) :
    contactEnergy C K (u + h • ω) ((2 : ℝ) • ω - w) - contactEnergy C K u w +
        h * inner ℝ ω (D ω) =
      h * G / 4 * (‖og‖ ^ 2 + ‖oh‖ ^ 2 - ‖arriveG ιg G og ω‖ ^ 2 - ‖arriveH ιh G oh ω‖ ^ 2) := by
  rw [transit_balance C D K hC hK hG hsolve]
  congr 1
  have hg : ‖arriveG ιg G og ω‖ ^ 2 =
      ‖og‖ ^ 2 - 2 * (2 / G) * inner ℝ (ContinuousLinearMap.adjoint ιg og) ω +
        (2 / G) ^ 2 * ‖ω‖ ^ 2 := by
    rw [arriveG, @norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, channel_norm_sq hιg, ContinuousLinearMap.adjoint_inner_left]
    ring
  have hh : ‖arriveH ιh G oh ω‖ ^ 2 =
      ‖oh‖ ^ 2 + 2 * (2 / G) * inner ℝ (ContinuousLinearMap.adjoint ιh oh) ω +
        (2 / G) ^ 2 * ‖ω‖ ^ 2 := by
    rw [arriveH, @norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
      sq_abs, channel_norm_sq hιh, ContinuousLinearMap.adjoint_inner_left]
    ring
  rw [hg, hh, norm_sub_smul_sq, norm_add_smul_sq]
  ring

/-- [proved-derived; formal-checked] **The contact's transport is a partial isometry with reverse
`U_aᵀ`, and the untransmitted part reflects with its norm.** For channel embeddings `ι_g`, `ι_h`:
`U_aᵀ = ι_g ι_hᵀ`; `U_a U_aᵀ U_a = U_a`; every wave splits its norm between its channel part and its
untransmitted part; and with no constitution (`C = K = D = 0`, `h, G ≠ 0`) the transit is pure
transmission, `a_(g←a) = (I − ι_g ι_gᵀ) o_g + U_aᵀ o_h`, `a_(h←a) = (I − ι_h ι_hᵀ) o_h + U_a o_g`,
conserving `|o_g|² + |o_h|²`. -/
theorem partialIsometry_transit {ιg : Ch →L[ℝ] Vg} {ιh : Ch →L[ℝ] Vh}
    (hιg : IsChannelEmbedding ιg) (hιh : IsChannelEmbedding ιh) :
    ContinuousLinearMap.adjoint (contactTransport ιg ιh) = contactTransport ιh ιg ∧
      (contactTransport ιg ιh).comp
          ((contactTransport ιh ιg).comp (contactTransport ιg ιh)) = contactTransport ιg ιh ∧
      (∀ o : Vg, ‖o‖ ^ 2 = ‖ContinuousLinearMap.adjoint ιg o‖ ^ 2 +
        ‖o - ιg (ContinuousLinearMap.adjoint ιg o)‖ ^ 2) ∧
      ∀ {G h : ℝ}, G ≠ 0 → h ≠ 0 → ∀ (u w ω : Ch) (og : Vg) (oh : Vh),
        TransitSolves 0 0 0 G h u w (ContinuousLinearMap.adjoint ιg og)
            (ContinuousLinearMap.adjoint ιh oh) ω →
          arriveG ιg G og ω = (og - ιg (ContinuousLinearMap.adjoint ιg og)) +
              contactTransport ιh ιg oh ∧
            arriveH ιh G oh ω = (oh - ιh (ContinuousLinearMap.adjoint ιh oh)) +
              contactTransport ιg ιh og ∧
            ‖arriveG ιg G og ω‖ ^ 2 + ‖arriveH ιh G oh ω‖ ^ 2 = ‖og‖ ^ 2 + ‖oh‖ ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [contactTransport, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint]
    rfl
  · ext x
    simp only [contactTransport, ContinuousLinearMap.comp_apply, channel_adjoint_apply hιh,
      channel_adjoint_apply hιg]
  · intro o
    have horth : inner ℝ (ιg (ContinuousLinearMap.adjoint ιg o))
        (o - ιg (ContinuousLinearMap.adjoint ιg o)) = 0 := by
      rw [inner_sub_right, channel_inner hιg, ← ContinuousLinearMap.adjoint_inner_right, sub_self]
    have := norm_add_sq_real (ιg (ContinuousLinearMap.adjoint ιg o))
      (o - ιg (ContinuousLinearMap.adjoint ιg o))
    rw [horth, mul_zero, add_zero, add_sub_cancel] at this
    rw [this, channel_norm_sq hιg]
  · intro G h hG hh u w ω og oh hsolve
    have hω : ω = (G / 2) • (ContinuousLinearMap.adjoint ιg og - ContinuousLinearMap.adjoint ιh oh) := by
      simp only [TransitSolves, transitOperator, smul_zero, add_zero, zero_add,
        _root_.smul_apply, _root_.zero_apply, ContinuousLinearMap.id_apply, sub_zero] at hsolve
      have := congrArg (fun v => (G / (2 * h)) • v) hsolve
      simp only [smul_smul] at this
      rw [show G / (2 * h) * (2 * h / G) = 1 by field_simp, one_smul] at this
      rw [this]
      congr 1
      field_simp
    have hbal := transit_balance_waves (0 : Ch →L[ℝ] Ch) 0 0 (by simp) (by simp) hιg hιh hG hsolve
    simp only [contactEnergy, _root_.zero_apply, inner_zero_right, mul_zero,
      add_zero, sub_self] at hbal
    refine ⟨?_, ?_, ?_⟩
    · rw [arriveG, hω, map_smul, smul_smul, show 2 / G * (G / 2) = 1 by field_simp, one_smul,
        map_sub, contactTransport, ContinuousLinearMap.comp_apply]
      abel
    · rw [arriveH, hω, map_smul, smul_smul, show 2 / G * (G / 2) = 1 by field_simp, one_smul,
        map_sub, contactTransport, ContinuousLinearMap.comp_apply]
      abel
    · have hhG : h * G / 4 ≠ 0 := by positivity
      have := (mul_eq_zero.mp hbal.symm).resolve_left hhG
      linarith

end Transit

/-! ## 3. The tick is well defined; no inverse is claimed -/

section WellDefined

open Holonics.HolonCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {Ch : Type*} [NormedAddCommGroup Ch] [InnerProductSpace ℝ Ch] [FiniteDimensional ℝ Ch]
variable {ρ : Type*} [Fintype ρ]

/-- [proved-derived; formal-checked] **The tick is well defined** (R2 H2, H3).
(1) The ring's element: for `K = W_s + Σ_ρ σ_ρ A_ρ` with `W_s` passive and `A_ρ` skew, every
`(b, c)` has exactly one successor `s′` with `(I − ½K) s′ = (I + ½K) b + W_c c`
(`Holon/Cayley.cayley_bijective`, `inner_devK`).
(2) The contact: for `C, D, K ⪰ 0` and `G, h > 0`, `⟨v, M_a v⟫ ≥ (2h/G)|v|²`, so `M_a ω = r` has
exactly one solution for every right side. -/
theorem tick_well_defined (Ws : E →L[ℝ] E) (hWs : ∀ v, inner ℝ v (Ws v) ≤ 0)
    (A : ρ → E →L[ℝ] E) (hA : ∀ r v, inner ℝ v (A r v) = 0) (σ : ρ → ℝ) (Wc : E →L[ℝ] E)
    (C D K : Ch →L[ℝ] Ch) (hC : ∀ v, 0 ≤ inner ℝ v (C v)) (hD : ∀ v, 0 ≤ inner ℝ v (D v))
    (hK : ∀ v, 0 ≤ inner ℝ v (K v)) {G h : ℝ} (hG : 0 < G) (hh : 0 < h) :
    (∀ b c : E, ∃! s' : E, s' - (1 / 2 : ℝ) • devK Ws A σ s' =
        b + (1 / 2 : ℝ) • devK Ws A σ b + Wc c) ∧
      (∀ v : Ch, 2 * h / G * ‖v‖ ^ 2 ≤ inner ℝ v (transitOperator C D K G h v)) ∧
      ∀ r : Ch, ∃! ω : Ch, transitOperator C D K G h ω = r := by
  have hpass : ∀ v, inner ℝ v (devK Ws A σ v) ≤ 0 := fun v => by
    rw [inner_devK Ws A hA σ v]; exact hWs v
  have hbij := cayley_bijective (devK Ws A σ) hpass
  have hpos : ∀ v : Ch, 2 * h / G * ‖v‖ ^ 2 ≤ inner ℝ v (transitOperator C D K G h v) := by
    intro v
    simp only [transitOperator, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq]
    have := hC v; have := hD v; have := hK v
    have : 0 ≤ h ^ 2 / 2 * inner ℝ v (K v) := by positivity
    nlinarith
  refine ⟨fun b c => ?_, hpos, fun r => ?_⟩
  · obtain ⟨s', hs'⟩ := hbij.2 (b + (1 / 2 : ℝ) • devK Ws A σ b + Wc c)
    refine ⟨s', by simpa using hs', fun y hy => hbij.1 ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      ContinuousLinearMap.coe_coe] at hs' ⊢
    rw [hy, hs']
  · have hinj : Function.Injective (transitOperator C D K G h : Ch →ₗ[ℝ] Ch) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro v hv
      have := hpos v
      rw [ContinuousLinearMap.coe_coe] at hv
      rw [hv, inner_zero_right] at this
      have hc : 0 < 2 * h / G := by positivity
      have : ‖v‖ ^ 2 ≤ 0 := by nlinarith
      exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
    have hsurj := LinearMap.injective_iff_surjective.mp hinj
    obtain ⟨ω, hω⟩ := hsurj r
    exact ⟨ω, hω, fun y hy => hinj (by simp only [ContinuousLinearMap.coe_coe]; rw [hy, ← hω]; rfl)⟩

/-- [counterexample; formal-checked] **No inverse is claimed** (R2 H2). On `ℝ` the passive element
`K = −2` makes the element step send every `b` to `0` (it is not injective), and for `h, G > 0` the
contact operator the reverse transit would need, `2C + hD − (2h/G) I − (h²/2) K`, is zero at
`C = (h/G) I`, `D = K = 0`, although `C ⪰ 0`. -/
theorem tick_step_not_invertible (h G : ℝ) (hG : G ≠ 0) :
    (∀ v : ℝ, inner ℝ v ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ v) ≤ 0) ∧
      (∀ b s' : ℝ, s' - (1 / 2 : ℝ) • ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) s' =
          b + (1 / 2 : ℝ) • ((-2 : ℝ) • ContinuousLinearMap.id ℝ ℝ) b → s' = 0) ∧
      (2 : ℝ) • ((h / G) • ContinuousLinearMap.id ℝ ℝ) + h • (0 : ℝ →L[ℝ] ℝ) -
          (2 * h / G) • ContinuousLinearMap.id ℝ ℝ - (h ^ 2 / 2) • (0 : ℝ →L[ℝ] ℝ) = 0 := by
  refine ⟨fun v => ?_, fun b s' hs => ?_, ?_⟩
  · simp only [ContinuousLinearMap.id_apply, smul_eq_mul, RCLike.inner_apply, conj_trivial]
    nlinarith [sq_nonneg v]
  · simp only [_root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul] at hs
    linarith
  · ext
    simp only [_root_.sub_apply, _root_.add_apply,
      _root_.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      _root_.zero_apply, mul_zero, add_zero, sub_zero]
    field_simp
    ring

/-- [counterexample; formal-checked] **Passivity and positivity are load-bearing for
`tick_well_defined`.** On `ℝ`, the active element `K = 2` (`⟨v, Kv⟩ = 2v² > 0`) makes `I − ½K`
zero, so the element step has no successor for `b = 1`; and the non-PSD contact stiffness
`K = −4/(hG)` makes the contact operator `M_a = (2h/G) I + (h²/2) K` zero, so its local solve has no
solution for a nonzero right side. -/
theorem tick_needs_passive_and_psd (h G : ℝ) (_hh : h ≠ 0) (hG : G ≠ 0) :
    (∀ s' : ℝ, ¬ (s' - (1 / 2 : ℝ) * (2 * s') = 1 + (1 / 2 : ℝ) * (2 * 1))) ∧
      transitOperator (0 : ℝ →L[ℝ] ℝ) 0 ((-4 / (h * G)) • ContinuousLinearMap.id ℝ ℝ) G h = 0 ∧
      ∀ ω : ℝ, transitOperator (0 : ℝ →L[ℝ] ℝ) 0 ((-4 / (h * G)) • ContinuousLinearMap.id ℝ ℝ) G h ω ≠ 1 := by
  have hM : transitOperator (0 : ℝ →L[ℝ] ℝ) 0 ((-4 / (h * G)) • ContinuousLinearMap.id ℝ ℝ) G h = 0 := by
    ext
    simp only [transitOperator, smul_zero, zero_add, add_zero, _root_.add_apply, _root_.smul_apply,
      ContinuousLinearMap.id_apply, _root_.zero_apply, smul_eq_mul]
    field_simp
    ring
  refine ⟨fun s' h' => by linarith, hM, fun ω => by rw [hM]; simp⟩

end WellDefined

/-! ## 4. The causal cone and the diamond on the block graph of a word -/

section Walks

variable {B : Type*} (adj : B → B → Prop)

/-- [definition] `ReachIn adj x y n`: a walk of `n` hops from block `x` to block `y` along the
block graph `adj` (`adj z y`: one tick carries block `z` into block `y`). -/
inductive ReachIn : B → B → ℕ → Prop
  | refl (x : B) : ReachIn x x 0
  | tail {x y z : B} {n : ℕ} : ReachIn x y n → adj y z → ReachIn x z (n + 1)

variable {adj}

theorem ReachIn.trans {x y z : B} {n m : ℕ} (hxy : ReachIn adj x y n) (hyz : ReachIn adj y z m) :
    ReachIn adj x z (n + m) := by
  induction hyz with
  | refl => simpa using hxy
  | tail _ hstep ih => exact ReachIn.tail ih hstep

theorem ReachIn.single {x y : B} (h : adj x y) : ReachIn adj x y 1 :=
  ReachIn.tail (ReachIn.refl x) h

theorem ReachIn.head {x y z : B} {n : ℕ} (h : adj x y) (hyz : ReachIn adj y z n) :
    ReachIn adj x z (n + 1) := by
  simpa [add_comm] using (ReachIn.single h).trans hyz

/-- [proved-derived; formal-checked] A walk read backwards is a walk of the reversed graph. -/
theorem ReachIn.flip {x y : B} {n : ℕ} (h : ReachIn adj x y n) :
    ReachIn (_root_.flip adj) y x n := by
  induction h with
  | refl => exact ReachIn.refl _
  | tail _ hstep ih => exact ReachIn.head (adj := _root_.flip adj) hstep ih

theorem reachIn_flip_iff {x y : B} {n : ℕ} : ReachIn (flip adj) y x n ↔ ReachIn adj x y n :=
  ⟨fun h => by simpa using h.flip, fun h => h.flip⟩

variable (adj)

/-- [definition] The blocks within `t` hops of the sources `S` (`r_b ≤ t`). -/
def reachWithin (S : Set B) (t : ℕ) : Set B := {b | ∃ x ∈ S, ∃ n ≤ t, ReachIn adj x b n}

/-- [definition] `Observes R y m`: some receiving block is within `m` hops of `y` (`o_y ≤ m`). -/
def Observes (R : Set B) (y : B) (m : ℕ) : Prop := ∃ ρ ∈ R, ∃ n ≤ m, ReachIn adj y ρ n

/-- [definition] **The causal diamond** of sources `S`, receivers `R` and last epoch `t`: an edge
`z → y` lies in it exactly when `r_z + 1 + o_y ≤ t`. -/
def InDiamond (S R : Set B) (t : ℕ) (z y : B) : Prop :=
  ∃ j m, z ∈ reachWithin adj S j ∧ Observes adj R y m ∧ j + 1 + m ≤ t

variable {adj}

theorem reachWithin_mono {S : Set B} {t t' : ℕ} (h : t ≤ t') :
    reachWithin adj S t ⊆ reachWithin adj S t' := by
  rintro b ⟨x, hx, n, hn, hr⟩
  exact ⟨x, hx, n, hn.trans h, hr⟩

theorem reachWithin_step {S : Set B} {t : ℕ} {z y : B} (hz : z ∈ reachWithin adj S t)
    (h : adj z y) : y ∈ reachWithin adj S (t + 1) := by
  obtain ⟨x, hx, n, hn, hr⟩ := hz
  exact ⟨x, hx, n + 1, by omega, hr.tail h⟩

theorem observes_mono {R : Set B} {y : B} {m m' : ℕ} (h : m ≤ m') (hy : Observes adj R y m) :
    Observes adj R y m' := by
  obtain ⟨ρ, hρ, n, hn, hr⟩ := hy
  exact ⟨ρ, hρ, n, hn.trans h, hr⟩

theorem observes_step {R : Set B} {z y : B} {m : ℕ} (h : adj z y) (hy : Observes adj R y m) :
    Observes adj R z (m + 1) := by
  obtain ⟨ρ, hρ, n, hn, hr⟩ := hy
  exact ⟨ρ, hρ, n + 1, by omega, ReachIn.head h hr⟩

theorem observes_trans {R : Set B} {y b : B} {m m' : ℕ} (hb : ∃ n ≤ m, ReachIn adj y b n)
    (hobs : Observes adj R b m') : Observes adj R y (m + m') := by
  obtain ⟨n, hn, hyb⟩ := hb
  obtain ⟨ρ, hρ, n', hn', hbρ⟩ := hobs
  exact ⟨ρ, hρ, n + n', by omega, hyb.trans hbρ⟩

theorem inDiamond_mono {S R : Set B} {t t' : ℕ} (h : t ≤ t') {z y : B}
    (hd : InDiamond adj S R t z y) : InDiamond adj S R t' z y := by
  obtain ⟨j, m, hz, hy, hjm⟩ := hd
  exact ⟨j, m, hz, hy, hjm.trans h⟩

/-- [proved-derived; formal-checked] The diamond of the reversed graph, with sources and receivers
exchanged, is the diamond read backwards. -/
theorem inDiamond_flip_iff {S R : Set B} {t : ℕ} {z y : B} :
    InDiamond (flip adj) R S t y z ↔ InDiamond adj S R t z y := by
  constructor
  · rintro ⟨j, m, ⟨ρ, hρ, n, hn, hr⟩, ⟨x, hx, n', hn', hr'⟩, hjm⟩
    exact ⟨m, j, ⟨x, hx, n', hn', reachIn_flip_iff.mp hr'⟩, ⟨ρ, hρ, n, hn, reachIn_flip_iff.mp hr⟩,
      by omega⟩
  · rintro ⟨j, m, ⟨x, hx, n', hn', hr'⟩, ⟨ρ, hρ, n, hn, hr⟩, hjm⟩
    exact ⟨m, j, ⟨ρ, hρ, n, hn, hr.flip⟩, ⟨x, hx, n', hn', hr'.flip⟩, by omega⟩

end Walks

section Blocks

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K]
variable {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

/-- [definition] A family of one-tick block operators `T y z : M z → M y` (block `z` into
block `y`), fixed within a word. -/
abbrev BlockOp (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] :=
  (y z : B) → M z →ₗ[K] M y

variable (adj) in
/-- [definition] The block operators respect the declared block graph: `T y z = 0` off its
edges. -/
def Sparse (T : BlockOp K M) : Prop := ∀ y z, ¬ adj z y → T y z = 0

/-- [definition] One tick: `(T x)_y = Σ_z T y z x_z`. -/
def tick (T : BlockOp K M) (x : (b : B) → M b) : (b : B) → M b := fun y => ∑ z, T y z (x z)

/-- [definition] The word's own trajectory from the open state `x₀`. -/
def trajectory (T : BlockOp K M) (x₀ : (b : B) → M b) : ℕ → (b : B) → M b
  | 0 => x₀
  | k + 1 => tick T (trajectory T x₀ k)

/-- [definition] A block state vanishes off `S`. -/
def SupportedIn (x : (b : B) → M b) (S : Set B) : Prop := ∀ b, b ∉ S → x b = 0

/-- [definition] The dual block operators `(T y z)ᵀ : M y* → M z*`: the return's one tick. -/
def dualOp (T : BlockOp K M) : BlockOp K (fun b => Module.Dual K (M b)) :=
  fun z y => (T y z).dualMap

/-- [definition] **The swept covector**: the reading covector `g` carried back `n` ticks. -/
def sweep (T : BlockOp K M) (g : (b : B) → Module.Dual K (M b)) (n : ℕ) :
    (b : B) → Module.Dual K (M b) :=
  trajectory (dualOp T) g n

/-- [definition] The pairing of a covector field with a block state. -/
def pair (g : (b : B) → Module.Dual K (M b)) (x : (b : B) → M b) : K := ∑ b, g b (x b)

/-- [definition] The difference of two block operator families. -/
def opSub (T' T : BlockOp K M) : BlockOp K M := fun y z => T' y z - T y z

omit [Fintype B] in
theorem sparse_dualOp {T : BlockOp K M} (hT : Sparse adj T) : Sparse (flip adj) (dualOp T) := by
  intro z y h
  simp only [dualOp, hT y z h]
  ext φ v
  simp [LinearMap.dualMap_apply]

/-- [proved-derived; formal-checked] The dual tick is the adjoint of the tick. -/
theorem pair_tick (T : BlockOp K M) (g : (b : B) → Module.Dual K (M b)) (x : (b : B) → M b) :
    pair g (tick T x) = pair (tick (dualOp T) g) x := by
  simp only [pair, tick, dualOp, map_sum, LinearMap.sum_apply, LinearMap.dualMap_apply]
  exact Finset.sum_comm

/-- [proved-derived; formal-checked] **The reading pairs exactly with the swept covector** at every
intermediate tick: `⟨λ_(k), x_k⟩ = ⟨g, x_(k+n)⟩` with `λ` the covector swept `n` ticks back. -/
theorem trajectory_pairing (T : BlockOp K M) (x₀ : (b : B) → M b)
    (g : (b : B) → Module.Dual K (M b)) (k n : ℕ) :
    pair (sweep T g n) (trajectory T x₀ k) = pair g (trajectory T x₀ (k + n)) := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    change pair (tick (dualOp T) (sweep T g n)) (trajectory T x₀ k) = _
    rw [← pair_tick, show tick T (trajectory T x₀ k) = trajectory T x₀ (k + 1) from rfl, ih]
    congr 2
    omega

/-- [proved-derived; formal-checked] **The causal cone** (§8.1): a change supported on `S` is
supported, after `t` ticks, in the ball of radius `t` hops about `S`. -/
theorem tick_causal_cone {T : BlockOp K M} (hT : Sparse adj T) {x₀ : (b : B) → M b} {S : Set B}
    (hx : SupportedIn x₀ S) (t : ℕ) : SupportedIn (trajectory T x₀ t) (reachWithin adj S t) := by
  induction t with
  | zero =>
    intro b hb
    exact hx b fun hbS => hb ⟨b, hbS, 0, le_rfl, ReachIn.refl b⟩
  | succ t ih =>
    intro y hy
    change ∑ z, T y z (trajectory T x₀ t z) = 0
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases hz : z ∈ reachWithin adj S t
    · have hnadj : ¬ adj z y := fun h => hy (reachWithin_step hz h)
      rw [hT y z hnadj, LinearMap.zero_apply]
    · rw [ih z hz, map_zero]

/-- [proved-derived; formal-checked] **The return's cone**: a covector supported on the receiving
blocks `R`, swept back `n` ticks, vanishes at every block that observes no receiver within `n`
hops. -/
theorem covector_causal_cone {T : BlockOp K M} (hT : Sparse adj T)
    {g : (b : B) → Module.Dual K (M b)} {R : Set B} (hg : SupportedIn g R) (n : ℕ) (y : B)
    (hy : ¬ Observes adj R y n) : sweep T g n y = 0 := by
  apply tick_causal_cone (sparse_dualOp hT) hg n y
  rintro ⟨ρ, hρ, m, hm, hr⟩
  exact hy ⟨ρ, hρ, m, hm, reachIn_flip_iff.mp hr⟩

theorem tick_opSub (T' T : BlockOp K M) (x : (b : B) → M b) :
    tick (opSub T' T) x = fun y => tick T' x y - tick T x y := by
  funext y
  simp [tick, opSub, Finset.sum_sub_distrib]

/-- [proved-derived; formal-checked] **The exact variation of a word** (the return, tape-free). For
two block operator families on one open state, a reading changes by exactly
`⟨g, x′_t⟩ − ⟨g, x_t⟩ = Σ_(k<t) ⟨λ′_(t−1−k), (T′ − T) x_k⟩`, where `x` is the word's own trajectory
under `T` and `λ′` the reading covector swept back under `T′`. Nothing is inverted and no earlier
word is replayed: the telescope composes the ticks' duals in reverse order. -/
theorem word_variation_exact (T' T : BlockOp K M) (x₀ : (b : B) → M b)
    (g : (b : B) → Module.Dual K (M b)) (t : ℕ) :
    pair g (trajectory T' x₀ t) - pair g (trajectory T x₀ t) =
      ∑ k ∈ Finset.range t, pair (sweep T' g (t - 1 - k)) (tick (opSub T' T) (trajectory T x₀ k)) := by
  set D : ℕ → K := fun k => pair (sweep T' g (t - k)) (trajectory T x₀ k) with hDdef
  have hD : ∀ k < t, D k - D (k + 1) =
      pair (sweep T' g (t - 1 - k)) (tick (opSub T' T) (trajectory T x₀ k)) := by
    intro k hkt
    have hsw : sweep T' g (t - k) = tick (dualOp T') (sweep T' g (t - 1 - k)) := by
      rw [show t - k = (t - 1 - k) + 1 by omega]; rfl
    simp only [hDdef]
    rw [hsw, ← pair_tick, show t - (k + 1) = t - 1 - k by omega,
      show trajectory T x₀ (k + 1) = tick T (trajectory T x₀ k) from rfl, tick_opSub]
    simp only [pair, map_sub, Finset.sum_sub_distrib]
  have h0 : D 0 = pair g (trajectory T' x₀ t) := by
    simp only [hDdef, Nat.sub_zero]
    change pair (sweep T' g t) (trajectory T' x₀ 0) = _
    rw [trajectory_pairing T' x₀ g 0 t, zero_add]
  have ht : D t = pair g (trajectory T x₀ t) := by
    simp only [hDdef, Nat.sub_self]
    rfl
  rw [← h0, ← ht, ← Finset.sum_range_sub']
  exact Finset.sum_congr rfl fun k hk => hD k (Finset.mem_range.mp hk)


/-- [definition] **The return's covector on the edge `z → y`**: the derivative of the reading
`⟨g, x_t⟩` along a change `δ` of the block operator `T y z`, `Σ_(k<t) λ_(t−1−k)(y)(δ x_k(z))`,
read over the word's own trajectory and swept covector. -/
def edgeCovector (T : BlockOp K M) (x₀ : (b : B) → M b) (g : (b : B) → Module.Dual K (M b))
    (t : ℕ) (z y : B) (δ : M z →ₗ[K] M y) : K :=
  ∑ k ∈ Finset.range t, sweep T g (t - 1 - k) y (δ (trajectory T x₀ k z))

theorem diamond_disjunction {T T' : BlockOp K M} (hT : Sparse adj T) (hT' : Sparse adj T')
    {x₀ : (b : B) → M b} {g : (b : B) → Module.Dual K (M b)} {S R : Set B}
    (hx : SupportedIn x₀ S) (hg : SupportedIn g R) {t : ℕ} {z y : B}
    (hout : ¬ InDiamond adj S R t z y) (k : ℕ) (hk : k < t) :
    sweep T' g (t - 1 - k) y = 0 ∨ trajectory T x₀ k z = 0 := by
  by_cases hz : z ∈ reachWithin adj S k
  · by_cases hy : Observes adj R y (t - 1 - k)
    · exact absurd ⟨k, t - 1 - k, hz, hy, by omega⟩ hout
    · exact Or.inl (covector_causal_cone hT' hg _ y hy)
  · exact Or.inr (tick_causal_cone hT hx k z hz)

/-- [proved-derived; formal-checked] **The return's covector lies in the causal diamond.** Outside
the diamond (`r_z + 1 + o_y > t`) the swept covector at `y` and the trajectory at `z` never meet:
at every tick one of them is zero, so the edge covector vanishes for every direction `δ`, and a
deposit reading it receives nothing. -/
theorem reached_loci_diamond {T : BlockOp K M} (hT : Sparse adj T) {x₀ : (b : B) → M b}
    {g : (b : B) → Module.Dual K (M b)} {S R : Set B} (hx : SupportedIn x₀ S)
    (hg : SupportedIn g R) {t : ℕ} {z y : B} (hout : ¬ InDiamond adj S R t z y) :
    (∀ k < t, sweep T g (t - 1 - k) y = 0 ∨ trajectory T x₀ k z = 0) ∧
      ∀ δ : M z →ₗ[K] M y, edgeCovector T x₀ g t z y δ = 0 := by
  have hdis := diamond_disjunction hT hT hx hg hout
  refine ⟨hdis, fun δ => Finset.sum_eq_zero fun k hk => ?_⟩
  rcases hdis k (Finset.mem_range.mp hk) with h | h
  · rw [h, LinearMap.zero_apply]
  · rw [h, map_zero, map_zero]

/-- [proved-derived; formal-checked] **An operator outside the diamond changes no admitted
reading** (R3 R1). If two block operator families on the declared block graph agree on every edge
`z → y` with `r_z + 1 + o_y ≤ e_last`, every reading supported on the receivers at any epoch
`t ≤ e_last` agrees, whatever the operators on the other edges (`word_variation_exact`,
`diamond_disjunction`). -/
theorem release_past_diamond {T T' : BlockOp K M} (hT : Sparse adj T) (hT' : Sparse adj T')
    {x₀ : (b : B) → M b} {g : (b : B) → Module.Dual K (M b)} {S R : Set B}
    (hx : SupportedIn x₀ S) (hg : SupportedIn g R) {eLast t : ℕ} (ht : t ≤ eLast)
    (hagree : ∀ y z, InDiamond adj S R eLast z y → T' y z = T y z) :
    pair g (trajectory T' x₀ t) = pair g (trajectory T x₀ t) := by
  rw [← sub_eq_zero, word_variation_exact]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_range.mp hk
  simp only [pair, tick, opSub, map_sum]
  refine Finset.sum_eq_zero fun y _ => Finset.sum_eq_zero fun z _ => ?_
  by_cases hd : InDiamond adj S R eLast z y
  · rw [hagree y z hd, sub_self, LinearMap.zero_apply, map_zero]
  · have hout : ¬ InDiamond adj S R t z y := fun h => hd (inDiamond_mono ht h)
    rcases diamond_disjunction hT hT' hx hg hout k hk' with h | h
    · rw [h, LinearMap.zero_apply]
    · rw [h, map_zero, map_zero]

theorem pair_single [DecidableEq B] (z : B) (φ : Module.Dual K (M z)) (x : (b : B) → M b) :
    pair (Pi.single z φ : (b : B) → Module.Dual K (M b)) x = φ (x z) := by
  rw [pair, Finset.sum_eq_single z]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

omit [Fintype B] in
theorem supportedIn_single [DecidableEq B] (z : B) (φ : Module.Dual K (M z)) :
    SupportedIn (Pi.single z φ : (b : B) → Module.Dual K (M b)) {z} := by
  intro b hb
  rw [Set.mem_singleton_iff] at hb
  simp [hb]

/-- [proved-derived; formal-checked] **The trajectory agrees wherever it is still observed.** If two
operator families agree on the diamond's edges, the change at block `z` and tick `k ≤ e_last`
agrees whenever `z` observes a receiver within `e_last − k` hops: every feature a retained locus
reads in its window is the same under both. -/
theorem trajectory_agrees_where_observed [DecidableEq B] {T T' : BlockOp K M} (hT : Sparse adj T)
    (hT' : Sparse adj T') {x₀ : (b : B) → M b} {S R : Set B} (hx : SupportedIn x₀ S)
    {eLast : ℕ} (hagree : ∀ y z, InDiamond adj S R eLast z y → T' y z = T y z) {k : ℕ}
    (hk : k ≤ eLast) {z : B} (hobs : Observes adj R z (eLast - k)) :
    trajectory T' x₀ k z = trajectory T x₀ k z := by
  rw [← sub_eq_zero]
  apply (Module.forall_dual_apply_eq_zero_iff K _).mp
  intro φ
  rw [map_sub, sub_eq_zero, ← pair_single, ← pair_single]
  refine release_past_diamond hT hT' hx (supportedIn_single z φ) le_rfl ?_
  rintro y₁ z₁ ⟨j, m, hz₁, ⟨ρ, hρ, n, hn, hr⟩, hjm⟩
  rw [Set.mem_singleton_iff] at hρ
  subst hρ
  refine hagree y₁ z₁ ⟨j, m + (eLast - k), hz₁, observes_trans ⟨n, hn, hr⟩ hobs, by omega⟩

/-- [proved-derived; formal-checked] **The swept covector agrees wherever the sources reach.** If two
operator families agree on the diamond's edges, the covector swept back `n ≤ e_last` ticks agrees
at every block reached from the sources within `e_last − n` hops (the same law on the reversed
graph, with sources and receivers exchanged: `inDiamond_flip_iff`). -/
theorem sweep_agrees_where_reached [DecidableEq B] {T T' : BlockOp K M} (hT : Sparse adj T)
    (hT' : Sparse adj T') {g : (b : B) → Module.Dual K (M b)} {S R : Set B}
    (hg : SupportedIn g R) {eLast : ℕ} (hagree : ∀ y z, InDiamond adj S R eLast z y → T' y z = T y z)
    {n : ℕ} (hn : n ≤ eLast) {y : B} (hy : y ∈ reachWithin adj S (eLast - n)) :
    sweep T' g n y = sweep T g n y := by
  refine trajectory_agrees_where_observed (adj := _root_.flip adj) (sparse_dualOp hT)
    (sparse_dualOp hT') hg (S := R) (R := S) ?_ hn ?_
  · intro z y₁ hd
    rw [inDiamond_flip_iff] at hd
    simp only [dualOp, hagree y₁ z hd]
  · obtain ⟨x, hx, m, hm, hr⟩ := hy
    exact ⟨x, hx, m, hm, hr.flip⟩

end Blocks



section Audit

#print axioms anchor_is_participation
#print axioms junction_anchor_preserved
#print axioms junction_eq_sourceDerivedScatter
#print axioms junctionSwing_involutive
#print axioms junctionSwing_isometry
#print axioms junctionSwing_twoPort
#print axioms transit_balance
#print axioms transit_balance_waves
#print axioms partialIsometry_transit
#print axioms tick_well_defined
#print axioms tick_step_not_invertible
#print axioms tick_needs_passive_and_psd
#print axioms trajectory_pairing
#print axioms tick_causal_cone
#print axioms covector_causal_cone
#print axioms word_variation_exact
#print axioms reached_loci_diamond
#print axioms release_past_diamond
#print axioms trajectory_agrees_where_observed
#print axioms sweep_agrees_where_reached

end Audit

end Holonics.HNN.Propagation
