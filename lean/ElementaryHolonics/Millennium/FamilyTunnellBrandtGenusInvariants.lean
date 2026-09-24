import ElementaryHolonics.Millennium.FamilyTunnellBrandtGlobalSeparation

/-!
# Exact genus invariants of the two Tunnell--Brandt receivers

The destination-classification deed needs more than a pointwise residue-field
bijection.  This file retains the two integral Gram matrices, proves their
common determinant `64` and positive definiteness, and upgrades the existing
odd-prime coordinate chart to an additive quadratic isometry.

These are necessary inputs to an exhaustive determinant-`64` ternary
reduction.  They do not assert that an arbitrary returned neighbor belongs to
one of the two global classes; that remains the next source theorem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtGenusInvariants

open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtTestVector
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors

/-- The half-polar Gram matrix of `Q₁ = 2x²+y²+32z²`. -/
def brandtFirstGram : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 0, 0;
     0, 1, 0;
     0, 0, 32]

/-- The half-polar Gram matrix of
`Q₂ = 2x²+4y²+4yz+9z²`. -/
def brandtSecondGram : Matrix (Fin 3) (Fin 3) ℤ :=
  !![2, 0, 0;
     0, 4, 2;
     0, 2, 9]

theorem brandtFirstGram_det : brandtFirstGram.det = 64 := by
  decide

theorem brandtSecondGram_det : brandtSecondGram.det = 64 := by
  decide

theorem brandtGram_determinants_agree :
    brandtFirstGram.det = brandtSecondGram.det := by
  rw [brandtFirstGram_det, brandtSecondGram_det]

/-- The first receiver is positive definite, expressed without a real-valued
approximation. -/
theorem brandtFirstQuadratic_nonnegative (v : IntTriple) :
    0 ≤ brandtFirstQuadratic v := by
  unfold brandtFirstQuadratic
  positivity

theorem brandtFirstQuadratic_eq_zero_iff (v : IntTriple) :
    brandtFirstQuadratic v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have hx : v.1 = 0 := by
      unfold brandtFirstQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hy : v.2.1 = 0 := by
      unfold brandtFirstQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    have hz : v.2.2 = 0 := by
      unfold brandtFirstQuadratic at h
      nlinarith [sq_nonneg v.1, sq_nonneg v.2.1, sq_nonneg v.2.2]
    rcases v with ⟨x, y, z⟩
    simp_all
  · rintro rfl
    norm_num [brandtFirstQuadratic]

/-- The completed-square chart makes positivity of the cross-term receiver
exact: `Q₂ = 2x² + (2y+z)² + 8z²`. -/
theorem brandtSecondQuadratic_nonnegative (v : IntTriple) :
    0 ≤ brandtSecondQuadratic v := by
  rw [brandtSecondQuadratic_completedSquare]
  positivity

theorem brandtSecondQuadratic_eq_zero_iff (v : IntTriple) :
    brandtSecondQuadratic v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [brandtSecondQuadratic_completedSquare] at h
    have hx : v.1 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg (2 * v.2.1 + v.2.2),
        sq_nonneg v.2.2]
    have hz : v.2.2 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg (2 * v.2.1 + v.2.2),
        sq_nonneg v.2.2]
    have hy : v.2.1 = 0 := by
      nlinarith [sq_nonneg v.1, sq_nonneg (2 * v.2.1 + v.2.2),
        sq_nonneg v.2.2]
    rcases v with ⟨x, y, z⟩
    simp_all
  · rintro rfl
    norm_num [brandtSecondQuadratic]

theorem brandtFirstQuadratic_pos_iff (v : IntTriple) :
    0 < brandtFirstQuadratic v ↔ v ≠ 0 := by
  constructor
  · exact fun h hzero => by
      rw [hzero, (brandtFirstQuadratic_eq_zero_iff 0).2 rfl] at h
      exact (lt_irrefl 0 h)
  · intro hne
    have hnonneg := brandtFirstQuadratic_nonnegative v
    have hzero : brandtFirstQuadratic v ≠ 0 := by
      simpa [brandtFirstQuadratic_eq_zero_iff] using hne
    omega

theorem brandtSecondQuadratic_pos_iff (v : IntTriple) :
    0 < brandtSecondQuadratic v ↔ v ≠ 0 := by
  constructor
  · exact fun h hzero => by
      rw [hzero, (brandtSecondQuadratic_eq_zero_iff 0).2 rfl] at h
      exact (lt_irrefl 0 h)
  · intro hne
    have hnonneg := brandtSecondQuadratic_nonnegative v
    have hzero : brandtSecondQuadratic v ≠ 0 := by
      simpa [brandtSecondQuadratic_eq_zero_iff] using hne
    omega

variable {p : ℕ} [Fact p.Prime]

/-- The existing first-to-second residue chart, now carrying its additive law.
This is the actual local lattice transport required by genus bookkeeping. -/
def brandtFirstSecondAddEquiv (hp2 : p ≠ 2) :
    ResidueTriple (p := p) ≃+ ResidueTriple (p := p) where
  toEquiv := brandtFirstSecondEquiv hp2
  map_add' := by
    intro u v
    apply Prod.ext
    · rfl
    · apply Prod.ext
      · simp [brandtFirstSecondEquiv, brandtFirstThinEquiv,
          brandtSecondThinEquiv, brandtFirstToThinMod,
          thinToBrandtSecondMod]
        ring
      · simp [brandtFirstSecondEquiv, brandtFirstThinEquiv,
          brandtSecondThinEquiv, brandtFirstToThinMod,
          thinToBrandtSecondMod]
        ring

/-- The additive chart preserves the complete quadratic receiver. -/
theorem brandtFirstSecondAddEquiv_preserves (hp2 : p ≠ 2)
    (v : ResidueTriple (p := p)) :
    reducedBrandtSecondQuadratic (brandtFirstSecondAddEquiv hp2 v) =
      reducedBrandtFirstQuadratic v := by
  exact reducedBrandtSecondQuadratic_brandtFirstSecondEquiv hp2 v

/-- The local quadratic isometry and the global separator coexist.  This is
the exact reconstruction fibre a destination classifier must retain. -/
theorem oddPrime_additive_local_isometry_and_global_separation (hp2 : p ≠ 2) :
    (∀ v : ResidueTriple (p := p),
      reducedBrandtSecondQuadratic (brandtFirstSecondAddEquiv hp2 v) =
        reducedBrandtFirstQuadratic v) ∧
    ¬ ∃ e : IntTriple ≃ IntTriple,
      ∀ m : IntTriple, brandtSecondQuadratic (e m) = brandtFirstQuadratic m := by
  constructor
  · exact brandtFirstSecondAddEquiv_preserves hp2
  · exact
      Soma.Holonics.Millennium.FamilyTunnellBrandtGlobalSeparation.no_integral_receiver_equivalence

#print axioms brandtFirstGram_det
#print axioms brandtSecondGram_det
#print axioms brandtFirstQuadratic_eq_zero_iff
#print axioms brandtSecondQuadratic_eq_zero_iff
#print axioms brandtFirstSecondAddEquiv_preserves
#print axioms oddPrime_additive_local_isometry_and_global_separation

end Soma.Holonics.Millennium.FamilyTunnellBrandtGenusInvariants
