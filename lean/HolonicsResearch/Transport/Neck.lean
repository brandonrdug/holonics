import Holonics.Transport.JetStaircase
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# The neck: the pinhole station where flux converges and then diverges

[definition] This owner states the law the Rust module `crates/holonic-engine/src/neck.rs`
implements. It is item **T6** of
`docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. Three things are
stated here, in this order, and each one carries its hypotheses in the open.

1. **Flux constancy gives the pinhole, under hypotheses that are named.** `flux A j = A · j`; if
   the flux is the constant `Φ` and every section is strictly positive then
   `density_of_constant_flux` is `j i = Φ / A i`, and `speedup_of_narrowing` says that for a
   **positive** flux a narrower section carries a faster density. The two hypotheses — strictly
   positive sections and a positive constant flux — are exactly what the speed-up needs, and
   `no_speedup_of_negative_flux` shows the conclusion reverses when the second is dropped. The
   narrowing is therefore not a universal law of tubes; it is this law under this hypothesis.

2. **With sources the reading is the residual, not the speed-up.** `residual Φ σ i` is
   `Φ (i+1) − Φ i − σ i`; `residual_eq_zero_iff` is the station balance, and
   `flux_constant_of_sourceless_balance` proves that the flux really is constant once the sources
   vanish and the residual does. Nothing about a speed-up is available from the residual alone.

3. **A point focus keeps its angular spread.** A ray transfer is an exact `2 × 2` rational matrix;
   `transverseExtent` is the half-width of the image of the box bundle `[−y, y] × [−θ, θ]` and
   `phaseArea` is four times `|det|` times `y θ`. `focus_has_zero_extent` locates the focus of a
   point source at `B = 0`, and `point_focus_keeps_angular_spread` is the pinhole reading made
   exact: at that station the transverse extent is **zero** and the angular extent is **strictly
   positive**, so the bundle is a point at the receiver's grain while still plural inside, and the
   map's determinant stays one. A point source has **zero** phase area before and after the focus,
   so this is not positive étendue passing a zero-width section (corrected September 25, with
   Sol): a bundle of positive phase area keeps it (`phaseArea_unmoved_at_the_focus`) and cannot
   reach zero width with bounded angle under an invertible map. `phaseArea_comp` is the composition law and `reducedEtendue_interface` is the
   `n₁/n₂` form across a refracting interface.

[definition] The jet order at a neck is `Transport/JetStaircase.lean`'s reading of `A(s) − A_min`,
not a second notion founded here; `neck_jet_order_is_a_truncation_reading` records that the order
this owner reports is a property of that truncation.

Truth status: `[proved-derived] [formal-checked]` for every theorem below.
-/

namespace Holonics.Transport.Neck

open Matrix

/-! ## 1. Convergence into the pinhole and divergence out of it -/

/-- The flux through a station: its section times its current density. -/
def flux (A j : ℕ → ℚ) (i : ℕ) : ℚ := A i * j i

/-- **`j = Φ / A`**: with a constant flux and a strictly positive section, the density is
determined at every station. -/
theorem density_of_constant_flux {A j : ℕ → ℚ} {Φ : ℚ}
    (hA : ∀ i, 0 < A i) (hflux : ∀ i, flux A j i = Φ) (i : ℕ) :
    j i = Φ / A i := by
  have h := hflux i
  simp only [flux] at h
  field_simp [(hA i).ne']
  linarith [h]

/-- **The pinhole**: under a strictly positive section and a **positive** constant flux, a
narrower section carries a faster density. Both hypotheses are load-bearing. -/
theorem speedup_of_narrowing {A j : ℕ → ℚ} {Φ : ℚ} (hΦ : 0 < Φ)
    (hA : ∀ i, 0 < A i) (hflux : ∀ i, flux A j i = Φ)
    {i k : ℕ} (hnarrow : A k ≤ A i) :
    j i ≤ j k := by
  rw [density_of_constant_flux hA hflux i, density_of_constant_flux hA hflux k]
  rw [div_le_div_iff₀ (hA i) (hA k)]
  nlinarith [hΦ, hnarrow]

/-- **The hypothesis is not decoration.** With a negative constant flux the same narrowing
reverses the conclusion, so the speed-up is this law under this hypothesis and not a universal
property of narrowing tubes. -/
theorem no_speedup_of_negative_flux {A j : ℕ → ℚ} {Φ : ℚ} (hΦ : Φ < 0)
    (hA : ∀ i, 0 < A i) (hflux : ∀ i, flux A j i = Φ)
    {i k : ℕ} (hnarrow : A k ≤ A i) :
    j k ≤ j i := by
  rw [density_of_constant_flux hA hflux i, density_of_constant_flux hA hflux k]
  rw [div_le_div_iff₀ (hA k) (hA i)]
  nlinarith [hΦ, hnarrow]

/-! ## 2. With sources, the reading is the residual -/

/-- The per-station transport residual: `Φ_{i+1} − Φ_i − σ_i`. -/
def residual (Φ σ : ℕ → ℚ) (i : ℕ) : ℚ := Φ (i + 1) - Φ i - σ i

/-- The station balance: the residual vanishes exactly when the flux steps by the source. -/
theorem residual_eq_zero_iff (Φ σ : ℕ → ℚ) (i : ℕ) :
    residual Φ σ i = 0 ↔ Φ (i + 1) = Φ i + σ i := by
  simp only [residual]
  constructor <;> intro h <;> linarith

/-- **Flux constancy is a conclusion, not an assumption**: it follows from a sourceless tube whose
residual vanishes at every station, and from nothing weaker. -/
theorem flux_constant_of_sourceless_balance (Φ σ : ℕ → ℚ)
    (hσ : ∀ i, σ i = 0) (hres : ∀ i, residual Φ σ i = 0) :
    ∀ i, Φ i = Φ 0 := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
      have := (residual_eq_zero_iff Φ σ i).mp (hres i)
      rw [this, hσ i, add_zero, ih]

/-- A source that the flux does not carry is returned as the residual, whole. -/
theorem residual_of_unmatched_source (Φ σ : ℕ → ℚ) (i : ℕ) :
    residual Φ σ i = (Φ (i + 1) - Φ i) - σ i := rfl

/-! ## 3. The optical instance: étendue survives the focus -/

/-- An exact rational ray transfer on `(height, angle)`. -/
abbrev RayTransfer := Matrix (Fin 2) (Fin 2) ℚ

/-- The transverse half-extent of the image of the box bundle `[−y, y] × [−θ, θ]`. -/
def transverseExtent (M : RayTransfer) (y θ : ℚ) : ℚ := |M 0 0| * y + |M 0 1| * θ

/-- Its angular half-extent. -/
def angularExtent (M : RayTransfer) (y θ : ℚ) : ℚ := |M 1 0| * y + |M 1 1| * θ

/-- The phase-space area of that image: four times `|det|` times `y θ`. -/
def phaseArea (M : RayTransfer) (y θ : ℚ) : ℚ := 4 * |M.det| * (y * θ)

/-- A unimodular transfer leaves the phase-space area exactly where it was. -/
theorem phaseArea_of_unimodular (M : RayTransfer) (h : M.det = 1) (y θ : ℚ) :
    phaseArea M y θ = 4 * (y * θ) := by
  simp [phaseArea, h]

/-- Composition multiplies the area by the new element's `|det|`, and by nothing else. -/
theorem phaseArea_comp (M N : RayTransfer) (y θ : ℚ) :
    phaseArea (N * M) y θ = |N.det| * phaseArea M y θ := by
  simp only [phaseArea, Matrix.det_mul, abs_mul]
  ring

/-- **Étendue across a refracting interface.** With `det M = n₁ / n₂` the reduced étendue
`n₂ · det M` is the entry index `n₁`: what is conserved is `n · (phase area)`, not the area. -/
theorem reducedEtendue_interface (n₁ n₂ : ℚ) (hn₂ : n₂ ≠ 0) (M : RayTransfer)
    (hdet : M.det = n₁ / n₂) : n₂ * M.det = n₁ := by
  rw [hdet]
  field_simp

/-- **The focus of a point source is exactly `B = 0`.** -/
theorem focus_has_zero_extent (M : RayTransfer) (hB : M 0 1 = 0) (θ : ℚ) :
    transverseExtent M 0 θ = 0 := by
  simp [transverseExtent, hB]

/-- **The pinhole reading, exactly.** At a unimodular station whose `B` element vanishes, a point
source's transverse extent is zero — a point at the receiver's grain — while its angular extent is
strictly positive — plural inside — and the map's determinant stays one. The point source's phase
area is zero on both sides. -/
theorem point_focus_keeps_angular_spread (M : RayTransfer) (hdet : M.det = 1) (hB : M 0 1 = 0)
    {θ : ℚ} (hθ : 0 < θ) :
    transverseExtent M 0 θ = 0 ∧ 0 < angularExtent M 0 θ ∧ M.det = 1 := by
  refine ⟨focus_has_zero_extent M hB θ, ?_, hdet⟩
  have hdet' : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hdet
  have hD : M 1 1 ≠ 0 := by
    intro h
    rw [h, hB] at hdet'
    simp at hdet'
  have : 0 < |M 1 1| := abs_pos.mpr hD
  simp only [angularExtent, mul_zero, zero_add]
  exact mul_pos this hθ

/-- The geometric width going to zero is not the étendue going to zero: at the focus the area of a
bundle with a strictly positive height **and** angle is still exactly what it entered with. -/
theorem phaseArea_unmoved_at_the_focus (M : RayTransfer) (hdet : M.det = 1) (y θ : ℚ) :
    phaseArea M y θ = phaseArea (1 : RayTransfer) y θ := by
  simp [phaseArea, hdet]

/-! ## 4. The jet order at the neck is the jet staircase's reading -/

/-- The order this owner reports at a neck is a property of `A(s) − A_min` truncated at the
declared jet order, and that truncation is `Transport/JetStaircase.lean`'s. Two section jets with
the same truncation give the neck the same reading; no second notion of order is founded here. -/
theorem neck_jet_order_is_a_truncation_reading (r : ℕ) (c d : ℕ → ℚ)
    (h : Holonics.Transport.JetStaircase.truncate r c
        = Holonics.Transport.JetStaircase.truncate r d) :
    ∀ i, i ≤ r → c i = d i :=
  (Holonics.Transport.JetStaircase.truncate_eq_iff r c d).mp h

section Audit

#print axioms density_of_constant_flux
#print axioms speedup_of_narrowing
#print axioms no_speedup_of_negative_flux
#print axioms residual_eq_zero_iff
#print axioms flux_constant_of_sourceless_balance
#print axioms residual_of_unmatched_source
#print axioms phaseArea_of_unimodular
#print axioms phaseArea_comp
#print axioms reducedEtendue_interface
#print axioms focus_has_zero_extent
#print axioms point_focus_keeps_angular_spread
#print axioms phaseArea_unmoved_at_the_focus
#print axioms neck_jet_order_is_a_truncation_reading

end Audit

end Holonics.Transport.Neck
