import HolonicsResearch.Aeon.Production.ComplexEntropyBalance
import Holonics.Physics.TwoCellEntropyTransport

/-!
# de Bruijn's identity on a receiver's partition: the entropy rate of heat flow is its Fisher information

[definition] The record of October 22 (order is torsion, §5.5 and §8): under heat flow, de Bruijn's identity
`d/dt H(X + √t Z) = ½ J(X + √t Z)` makes the entropy rate the Fisher information. That continuum identity is the
classical one, for a density on `ℝⁿ` under `∂ₜ p = ½ Δp` with `J(p) = ∫ |∇p|²/p`; what a receiver reads is its
partition. On a finite partition with symmetric nonnegative contact weights `w_xy = w_yx`, **heat flow** moves a
positive law by the graph Laplacian, `ṗ_x = (L p)_x = Σ_y w_xy (p_y − p_x)` (`laplacian`), and the **partition
Fisher information** is the Dirichlet form of the law against its logarithm (`fisherPartition`),

```text
J_part(p) = Σ_(x,y) w_xy (p_x − p_y)(log p_x − log p_y),
```

the discrete `∫ ∇p · ∇log p = ∫ |∇p|²/p`, summed over ordered pairs.

[proved-derived; formal-checked] What is proved.

1. **de Bruijn on the partition** (`hasDerivAt_entropy_heat`): along any path with `ṗ = L p` at a positive law,
   `dH/dt = ½ J_part(p)`. Heat flow is the master equation of `ComplexEntropyBalance` with symmetric rates
   (`laplacian_eq_neg_outflow`), whose bath flux vanishes (`bathFlux_eq_zero`), so the entropy rate is the total
   production, and that production is `½ J_part` (`totalProduction_eq_half_fisher`).
2. **`J_part ≥ 0`, zero exactly when the law is constant across every contact of positive weight**
   (`fisherPartition_nonneg`, `fisherPartition_eq_zero_iff`): `p_x = p_y` whenever `w_xy > 0`. With a connected
   contact graph that is the uniform law; connectivity is not formalized here.
3. **The join to `PathReversal`.** `J_part = 2 σ`, twice the epoch production of the law under the symmetric rates
   (`fisherPartition_eq_two_mul_epochProduction`), so heat flow's entropy rate is its production, and
   `J_part = 0` exactly under detailed balance (`fisherPartition_eq_zero_iff_detailedBalance`).
4. **Mass is conserved and the entropy rises.** `Σ_x (L p)_x = 0` (`sum_laplacian_eq_zero`, Stokes on the pairs),
   and a law that moves by heat flow for all time, positive throughout, has nondecreasing entropy
   (`entropy_monotone_heat`).
5. **Two cells** (`fisherPartition_twoCell`, `hasDerivAt_entropy_twoCell`): with one contact of weight `κ`,
   `½ J_part = κ (a − b)(log a − log b)`, the production of `Physics/TwoCellEntropyTransport`.

Scale: with the generator `L` and the sum over ordered pairs the factor is `½`; the same identity reads
`dH/dt = ½ Σ_(edges) w (Δp)(Δ log p)` under the generator `½ L`, the discrete counterpart of `½ Δ`, with each
unordered contact counted once, and that is the form whose factor matches the continuum's.

The computational object is the helical pair interaction: each pair of cells of the receiver's partition is a pair
contact of conductance `w_xy`, heat flow is the slip `w_xy (p_x − p_y)` through it, and the entropy rate is the
contact material `Σ w (Δp)(Δ log p)`, the Fisher information the receiver reads on its cells. Of the winding guide's
six general objects this touches the pair (each contact's slip and log drop) and faces and placement (the
partition the receiver reads); the helix, the cell holonomy (every affinity of a symmetric contact is zero), the
tube and the tower thread stay attached.

What stands beside it: `Aeon/Production/ComplexEntropyBalance` owns the balance this specializes;
`Aeon/Production/PathReversal` owns the production; `Physics/TwoCellEntropyTransport` is item 5's two-cell owner;
`Holon/Law/Fisher` holds the locks' Fisher form on a move's plane, the variance of a move's readings under the
softmax faces (the Fisher metric in the move's parameter), a different reading from the Fisher information of a law
that de Bruijn's identity takes, not joined here. Left out: the continuum identity and its Gaussian instance, the flow
`exp(t L)` itself (its positivity and existence are assumed of the path), and the scaling limit of `J_part` to
`J`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Aeon.Production.PartitionDeBruijn

open Finset Holonics.Aeon.Production.PathReversal Holonics.Aeon.Production.ComplexEntropyBalance

variable {S : Type*} [Fintype S]

/-- [definition] **The heat-flow generator** of contact weights `w`: `(L p)_x = Σ_y w_xy (p_y − p_x)`. -/
def laplacian (w : S → S → ℝ) (p : S → ℝ) (x : S) : ℝ := ∑ y, w x y * (p y - p x)

/-- [definition] **The partition Fisher information**: `J_part(p) = Σ_(x,y) w_xy (p_x − p_y)(log p_x − log p_y)`. -/
def fisherPartition (w : S → S → ℝ) (p : S → ℝ) : ℝ :=
  ∑ x, ∑ y, w x y * (p x - p y) * (Real.log (p x) - Real.log (p y))

variable {w : S → S → ℝ} {p : S → ℝ}

omit [Fintype S] in
/-- [proved-derived; formal-checked] Symmetric nonnegative weights and a positive law are admissible. -/
theorem admissible_of_symm (hp : ∀ x, 0 < p x) (hw : ∀ x y, 0 ≤ w x y) (hs : ∀ x y, w x y = w y x) :
    Admissible p w where
  pos := hp
  nonneg := hw
  support x y h := hs x y ▸ h

/-- [proved-derived; formal-checked] **Heat flow is the master equation with symmetric rates.** -/
theorem laplacian_eq_neg_outflow (hs : ∀ x y, w x y = w y x) (x : S) :
    laplacian w p x = -outflow (edgeCurrent p w) x := by
  unfold laplacian outflow edgeCurrent flow
  rw [← sum_neg_distrib]
  exact sum_congr rfl fun y _ => by rw [hs y x]; ring

/-- [proved-derived; formal-checked] **Symmetric contacts give nothing to the medium.** -/
theorem bathFlux_eq_zero (hs : ∀ x y, w x y = w y x) (x : S) : bathFlux p w x = 0 := by
  unfold bathFlux
  exact sum_eq_zero fun y _ => by rw [hs y x]; ring

omit [Fintype S] in
theorem fisher_term_nonneg (hp : ∀ x, 0 < p x) (hw : ∀ x y, 0 ≤ w x y) (x y : S) :
    0 ≤ w x y * (p x - p y) * (Real.log (p x) - Real.log (p y)) := by
  rw [mul_assoc]; exact mul_nonneg (hw x y) (sub_mul_log_sub_nonneg (hp x) (hp y))

/-- [proved-derived; formal-checked] **The production of heat flow is half its partition Fisher information.** -/
theorem totalProduction_eq_half_fisher (hp : ∀ x, 0 < p x) (hw : ∀ x y, 0 ≤ w x y) (hs : ∀ x y, w x y = w y x) :
    totalProduction p w = fisherPartition w p / 2 := by
  unfold totalProduction localProduction fisherPartition
  simp_rw [← sum_div]
  congr 1
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [current_mul_affinity (admissible_of_symm hp hw hs) x y]
  unfold edgeCurrent flow
  rw [hs y x]
  ring

/-- [proved-derived; formal-checked] **de Bruijn's identity on the partition**: along any path with `ṗ = L p` at a
positive law, `dH/dt = ½ J_part(p)`. -/
theorem hasDerivAt_entropy_heat {p : ℝ → S → ℝ} {t : ℝ} (hp : ∀ x, 0 < p t x) (hw : ∀ x y, 0 ≤ w x y)
    (hs : ∀ x y, w x y = w y x) (hheat : ∀ x, HasDerivAt (fun τ => p τ x) (laplacian w (p t) x) t) :
    HasDerivAt (fun τ => entropy (p τ)) (fisherPartition w (p t) / 2) t := by
  have h := hasDerivAt_entropy (admissible_of_symm hp hw hs) fun x =>
    (laplacian_eq_neg_outflow hs x) ▸ hheat x
  simp only [bathFlux_eq_zero hs, sum_const_zero, sub_zero, totalProduction_eq_half_fisher hp hw hs] at h
  exact h

/-- [proved-derived; formal-checked] `J_part ≥ 0`. -/
theorem fisherPartition_nonneg (hp : ∀ x, 0 < p x) (hw : ∀ x y, 0 ≤ w x y) : 0 ≤ fisherPartition w p :=
  sum_nonneg fun x _ => sum_nonneg fun y _ => fisher_term_nonneg hp hw x y

/-- [proved-derived; formal-checked] **`J_part = 0` exactly when the law is constant across every contact of positive
weight.** -/
theorem fisherPartition_eq_zero_iff (hp : ∀ x, 0 < p x) (hw : ∀ x y, 0 ≤ w x y) :
    fisherPartition w p = 0 ↔ ∀ x y, 0 < w x y → p x = p y := by
  unfold fisherPartition
  rw [sum_eq_zero_iff_of_nonneg fun x _ => sum_nonneg fun y _ => fisher_term_nonneg hp hw x y]
  simp_rw [sum_eq_zero_iff_of_nonneg fun y _ => fisher_term_nonneg hp hw _ y]
  constructor
  · intro h x y hxy
    have h' := h x (mem_univ _) y (mem_univ _)
    rwa [mul_assoc, mul_eq_zero, or_iff_right hxy.ne', sub_mul_log_sub_eq_zero_iff (hp x) (hp y)] at h'
  · intro h x _ y _
    rcases (hw x y).eq_or_lt with h0 | hpos
    · rw [← h0]; ring
    · rw [h x y hpos]; ring

/-- [proved-derived; formal-checked] **`J_part` is twice `PathReversal`'s epoch production** under the symmetric
rates. -/
theorem fisherPartition_eq_two_mul_epochProduction (hp : ∀ x, 0 < p x) (hw : ∀ x y, 0 ≤ w x y)
    (hs : ∀ x y, w x y = w y x) : fisherPartition w p = 2 * RealChart.epochProduction p w := by
  rw [← totalProduction_eq_epochProduction (admissible_of_symm hp hw hs), totalProduction_eq_half_fisher hp hw hs]
  ring

/-- [proved-derived; formal-checked] **`J_part = 0` exactly under detailed balance.** -/
theorem fisherPartition_eq_zero_iff_detailedBalance (hp : ∀ x, 0 < p x) (hw : ∀ x y, 0 ≤ w x y)
    (hs : ∀ x y, w x y = w y x) : fisherPartition w p = 0 ↔ DetailedBalance p w := by
  rw [fisherPartition_eq_two_mul_epochProduction hp hw hs, mul_eq_zero, or_iff_right two_ne_zero,
    RealChart.epochProduction_eq_zero_iff (admissible_of_symm hp hw hs)]

/-- [proved-derived; formal-checked] **Heat flow conserves mass**: `Σ_x (L p)_x = 0`. -/
theorem sum_laplacian_eq_zero (hs : ∀ x y, w x y = w y x) : ∑ x, laplacian w p x = 0 := by
  simp_rw [laplacian_eq_neg_outflow hs, sum_neg_distrib, sum_outflow_eq_zero (edgeCurrent_swap p w), neg_zero]

/-- [proved-derived; formal-checked] **The entropy rises under heat flow**: a law that moves by `ṗ = L p` at every
time, positive throughout, has nondecreasing entropy. -/
theorem entropy_monotone_heat {p : ℝ → S → ℝ} (hp : ∀ t x, 0 < p t x) (hw : ∀ x y, 0 ≤ w x y)
    (hs : ∀ x y, w x y = w y x) (hheat : ∀ t x, HasDerivAt (fun τ => p τ x) (laplacian w (p t) x) t) :
    Monotone fun t => entropy (p t) :=
  monotone_of_hasDerivAt_nonneg (fun t => hasDerivAt_entropy_heat (hp t) hw hs (hheat t))
    fun t => div_nonneg (fisherPartition_nonneg (hp t) hw) (by norm_num)

/-! ## Two cells -/

/-- [definition] **One contact of weight `κ` between two cells.** -/
def twoCellWeights (κ : ℝ) (x y : Fin 2) : ℝ := if x = y then 0 else κ

/-- [proved-derived; formal-checked] **On two cells `½ J_part` is the two-cell production**
`κ (a − b)(log a − log b)` of `Physics/TwoCellEntropyTransport`. -/
theorem fisherPartition_twoCell (κ a b : ℝ) :
    fisherPartition (twoCellWeights κ) ![a, b] / 2 =
      Holonics.Physics.TwoCellEntropyTransport.flux κ a b * (Real.log a - Real.log b) := by
  simp [fisherPartition, twoCellWeights, Fin.sum_univ_two, Holonics.Physics.TwoCellEntropyTransport.flux]
  ring

/-- [proved-derived; formal-checked] **de Bruijn on two cells**: under `ȧ = κ (b − a)`, `ḃ = κ (a − b)` at positive
masses, `dH/dt = κ (a − b)(log a − log b)`. -/
theorem hasDerivAt_entropy_twoCell {κ : ℝ} (hκ : 0 ≤ κ) {p : ℝ → Fin 2 → ℝ} {t : ℝ} (hp : ∀ x, 0 < p t x)
    (hheat : ∀ x, HasDerivAt (fun τ => p τ x) (laplacian (twoCellWeights κ) (p t) x) t) :
    HasDerivAt (fun τ => entropy (p τ))
      (Holonics.Physics.TwoCellEntropyTransport.flux κ (p t 0) (p t 1) * (Real.log (p t 0) - Real.log (p t 1))) t := by
  have hw : ∀ x y, 0 ≤ twoCellWeights κ x y := fun x y => by unfold twoCellWeights; split_ifs <;> simp [hκ]
  have hs : ∀ x y, twoCellWeights κ x y = twoCellWeights κ y x := fun x y => by
    by_cases h : x = y
    · subst h; rfl
    · simp [twoCellWeights, h, Ne.symm h]
  have h := hasDerivAt_entropy_heat hp hw hs hheat
  have hpt : p t = ![p t 0, p t 1] := by ext x; fin_cases x <;> rfl
  rwa [hpt, fisherPartition_twoCell] at h

end Holonics.Aeon.Production.PartitionDeBruijn
