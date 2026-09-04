import ElementaryHolonics.Millennium.FamilyTunnellIntegralNeighbors
import ElementaryHolonics.Millennium.FamilyTunnellBrandtNeighbors

/-!
# Distinct normalized directions give distinct integral neighbors

The neighbor carrier keeps both its polar kernel and its fractional generator.
Consequently equality of two actual neighbors cannot identify two different
normalized projective directions: membership of the first fractional
generator in the second neighbor gives a scalar relation modulo `p`, and the
normalizing pivot forces that scalar and direction to agree.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellBrandtDistinctNeighbors

open Soma.Holonics.Millennium.FamilyTunnellProjectiveNeighbors
open Soma.Holonics.Millennium.FamilyTunnellIntegralNeighbors
open Soma.Holonics.Millennium.FamilyTunnellBrandtNeighbors

variable {p : ℕ} [Fact p.Prime]

private theorem p_rat_ne_zero : (p : ℚ) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

private theorem p_int_ne_zero : (p : ℤ) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

private theorem adjusted_lifts_proportional_mod_p
    (hp2 : p ≠ 2) (C : ℤ)
    (d e : ProjectiveConicDirection (p := p) (C : ZMod p))
    (m : IntTriple) (a : ℤ)
    (h : ratTripleScale ((1 : ℚ) / (p : ℚ))
          (intTripleToRat (adjustedDirectionLift C d)) =
        ratTripleAdd (intTripleToRat m)
          (ratTripleScale ((a : ℚ) / (p : ℚ))
            (intTripleToRat (adjustedDirectionLift C e)))) :
    projectiveDirectionVector d.1 =
      (a : ZMod p) • projectiveDirectionVector e.1 := by
  have hx := congrArg Prod.fst h
  have hy := congrArg (fun v : RatTriple => v.2.1) h
  have hz := congrArg (fun v : RatTriple => v.2.2) h
  simp only [ratTripleScale, intTripleToRat, ratTripleAdd] at hx hy hz
  field_simp [p_rat_ne_zero (p := p)] at hx hy hz
  have hxz : (adjustedDirectionLift C d).1 =
      (p : ℤ) * m.1 + a * (adjustedDirectionLift C e).1 := by
    exact_mod_cast hx
  have hyz : (adjustedDirectionLift C d).2.1 =
      (p : ℤ) * m.2.1 + a * (adjustedDirectionLift C e).2.1 := by
    exact_mod_cast hy
  have hzz : (adjustedDirectionLift C d).2.2 =
      (p : ℤ) * m.2.2 + a * (adjustedDirectionLift C e).2.2 := by
    exact_mod_cast hz
  have hxmod : ((adjustedDirectionLift C d).1 : ZMod p) =
      (a : ZMod p) * ((adjustedDirectionLift C e).1 : ZMod p) := by
    rw [hxz]
    push_cast
    simp
  have hymod : ((adjustedDirectionLift C d).2.1 : ZMod p) =
      (a : ZMod p) * ((adjustedDirectionLift C e).2.1 : ZMod p) := by
    rw [hyz]
    push_cast
    simp
  have hzmod : ((adjustedDirectionLift C d).2.2 : ZMod p) =
      (a : ZMod p) * ((adjustedDirectionLift C e).2.2 : ZMod p) := by
    rw [hzz]
    push_cast
    simp
  have hrd := reduce_adjustedDirectionLift (p := p) hp2 C d
  have hre := reduce_adjustedDirectionLift (p := p) hp2 C e
  calc
    projectiveDirectionVector d.1 =
        reduceTriple (p := p) (adjustedDirectionLift C d) := hrd.symm
    _ = (a : ZMod p) • reduceTriple (p := p) (adjustedDirectionLift C e) := by
      apply Prod.ext
      · simpa [smul_eq_mul, reduceTriple] using hxmod
      · apply Prod.ext
        · simpa [smul_eq_mul, reduceTriple] using hymod
        · simpa [smul_eq_mul, reduceTriple] using hzmod
    _ = (a : ZMod p) • projectiveDirectionVector e.1 := by rw [hre]

theorem integralNeighbor_eq_iff_projectiveDirection_eq
    (hp2 : p ≠ 2) (C : ℤ)
    (d e : ProjectiveConicDirection (p := p) (C : ZMod p)) :
    integralNeighbor (p := p) C d = integralNeighbor (p := p) C e ↔ d = e := by
  constructor
  · intro hde
    have hmem : ratTripleScale ((1 : ℚ) / (p : ℚ))
          (intTripleToRat (adjustedDirectionLift C d)) ∈
        integralNeighbor (p := p) C e := by
      rw [← hde]
      exact fractionalGenerator_mem_integralNeighbor (p := p) hp2 C d
    rcases hmem with ⟨m, hm, a, ha⟩
    have hprop := adjusted_lifts_proportional_mod_p (p := p) hp2 C d e m a ha
    rcases d with ⟨d, hd⟩
    rcases e with ⟨e, he⟩
    apply Subtype.ext
    change d = e
    cases d with
    | inl qd =>
        cases e with
        | inl qe =>
            have hx := congrArg Prod.fst hprop
            have hy := congrArg (fun v => v.2.1) hprop
            simp [projectiveDirectionVector] at hx hy
            have haone : (a : ZMod p) = 1 := by simpa using hx.symm
            simp only [Sum.inl.injEq]
            apply Prod.ext
            · simpa [haone] using hy
            · have hz := congrArg (fun v => v.2.2) hprop
              simpa [projectiveDirectionVector, haone] using hz
        | inr ze =>
            have hx := congrArg Prod.fst hprop
            have hy := congrArg (fun v => v.2.1) hprop
            simp [projectiveDirectionVector] at hx hy
    | inr zd =>
        cases e with
        | inl qe =>
            have hx := congrArg Prod.fst hprop
            have hy := congrArg (fun v => v.2.1) hprop
            simp [projectiveDirectionVector] at hx hy
            rw [← hx] at hy
            have : False := by simpa using hy
            exact this.elim
        | inr ze =>
            have hy := congrArg (fun v => v.2.1) hprop
            have hz := congrArg (fun v => v.2.2) hprop
            simp [projectiveDirectionVector] at hy hz
            have haone : (a : ZMod p) = 1 := by simpa using hy.symm
            simp only [Sum.inr.injEq]
            simpa [haone] using hz
  · intro h
    simpa [h]

private theorem adjusted_second_lifts_proportional_mod_p
    (hp2 : p ≠ 2)
    (d e : BrandtSecondProjectiveDirection (p := p))
    (m : IntTriple) (a : ℤ)
    (h : ratTripleScale ((1 : ℚ) / (p : ℚ))
          (intTripleToRat (adjustedBrandtSecondDirectionLift hp2 d)) =
        ratTripleAdd (intTripleToRat m)
          (ratTripleScale ((a : ℚ) / (p : ℚ))
            (intTripleToRat (adjustedBrandtSecondDirectionLift hp2 e)))) :
    brandtSecondDirectionVector hp2 d =
      (a : ZMod p) • brandtSecondDirectionVector hp2 e := by
  have hx := congrArg Prod.fst h
  have hy := congrArg (fun v : RatTriple => v.2.1) h
  have hz := congrArg (fun v : RatTriple => v.2.2) h
  simp only [ratTripleScale, intTripleToRat, ratTripleAdd] at hx hy hz
  field_simp [p_rat_ne_zero (p := p)] at hx hy hz
  have hxz : (adjustedBrandtSecondDirectionLift hp2 d).1 =
      (p : ℤ) * m.1 + a * (adjustedBrandtSecondDirectionLift hp2 e).1 := by
    exact_mod_cast hx
  have hyz : (adjustedBrandtSecondDirectionLift hp2 d).2.1 =
      (p : ℤ) * m.2.1 + a * (adjustedBrandtSecondDirectionLift hp2 e).2.1 := by
    exact_mod_cast hy
  have hzz : (adjustedBrandtSecondDirectionLift hp2 d).2.2 =
      (p : ℤ) * m.2.2 + a * (adjustedBrandtSecondDirectionLift hp2 e).2.2 := by
    exact_mod_cast hz
  have hxmod : ((adjustedBrandtSecondDirectionLift hp2 d).1 : ZMod p) =
      (a : ZMod p) * ((adjustedBrandtSecondDirectionLift hp2 e).1 : ZMod p) := by
    rw [hxz]
    push_cast
    simp
  have hymod : ((adjustedBrandtSecondDirectionLift hp2 d).2.1 : ZMod p) =
      (a : ZMod p) * ((adjustedBrandtSecondDirectionLift hp2 e).2.1 : ZMod p) := by
    rw [hyz]
    push_cast
    simp
  have hzmod : ((adjustedBrandtSecondDirectionLift hp2 d).2.2 : ZMod p) =
      (a : ZMod p) * ((adjustedBrandtSecondDirectionLift hp2 e).2.2 : ZMod p) := by
    rw [hzz]
    push_cast
    simp
  have hrd := reduce_adjustedBrandtSecondDirectionLift (p := p) hp2 d
  have hre := reduce_adjustedBrandtSecondDirectionLift (p := p) hp2 e
  calc
    brandtSecondDirectionVector hp2 d =
        reduceTriple (p := p) (adjustedBrandtSecondDirectionLift hp2 d) := hrd.symm
    _ = (a : ZMod p) •
        reduceTriple (p := p) (adjustedBrandtSecondDirectionLift hp2 e) := by
      apply Prod.ext
      · simpa [smul_eq_mul, reduceTriple] using hxmod
      · apply Prod.ext
        · simpa [smul_eq_mul, reduceTriple] using hymod
        · simpa [smul_eq_mul, reduceTriple] using hzmod
    _ = (a : ZMod p) • brandtSecondDirectionVector hp2 e := by rw [hre]

private theorem brandtSecondToThinMod_smul (a : ZMod p)
    (v : CoordinateTriple (ZMod p)) :
    brandtSecondToThinMod (a • v) =
      a • brandtSecondToThinMod v := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;>
      simp [brandtSecondToThinMod, smul_eq_mul] <;> ring

private theorem brandt_second_scalar_relation_to_thin
    (hp2 : p ≠ 2)
    (d e : BrandtSecondProjectiveDirection (p := p))
    (a : ℤ)
    (h : brandtSecondDirectionVector hp2 d =
      (a : ZMod p) • brandtSecondDirectionVector hp2 e) :
    projectiveDirectionVector d.1 =
      (a : ZMod p) • projectiveDirectionVector e.1 := by
  have ht := congrArg (brandtSecondToThinMod (p := p)) h
  rw [brandtSecondToThinMod_smul] at ht
  simpa [brandtSecondDirectionVector,
    brandtSecondToThinMod_thinToBrandtSecondMod (p := p) hp2] using ht

theorem brandtSecondIntegralNeighbor_eq_iff_projectiveDirection_eq
    (hp2 : p ≠ 2)
    (d e : BrandtSecondProjectiveDirection (p := p)) :
    brandtSecondIntegralNeighbor (p := p) hp2 d =
      brandtSecondIntegralNeighbor (p := p) hp2 e ↔ d = e := by
  constructor
  · intro hde
    have hmem : ratTripleScale ((1 : ℚ) / (p : ℚ))
          (intTripleToRat (adjustedBrandtSecondDirectionLift hp2 d)) ∈
        brandtSecondIntegralNeighbor (p := p) hp2 e := by
      rw [← hde]
      exact fractionalGenerator_mem_brandtSecondIntegralNeighbor (p := p) hp2 d
    rcases hmem with ⟨m, hm, a, ha⟩
    have hprop := adjusted_second_lifts_proportional_mod_p
      (p := p) hp2 d e m a ha
    have hthin := brandt_second_scalar_relation_to_thin (p := p) hp2 d e a hprop
    rcases d with ⟨d, hd⟩
    rcases e with ⟨e, he⟩
    apply Subtype.ext
    change d = e
    cases d with
    | inl qd =>
        cases e with
        | inl qe =>
            have hx := congrArg Prod.fst hthin
            have hy := congrArg (fun v => v.2.1) hthin
            simp [projectiveDirectionVector] at hx hy
            have haone : (a : ZMod p) = 1 := by simpa using hx.symm
            simp only [Sum.inl.injEq]
            apply Prod.ext
            · simpa [haone] using hy
            · have hz := congrArg (fun v => v.2.2) hthin
              simpa [projectiveDirectionVector, haone] using hz
        | inr ze =>
            have hx := congrArg Prod.fst hthin
            simp [projectiveDirectionVector] at hx
    | inr zd =>
        cases e with
        | inl qe =>
            have hx := congrArg Prod.fst hthin
            have hy := congrArg (fun v => v.2.1) hthin
            simp [projectiveDirectionVector] at hx hy
            rw [← hx] at hy
            have : False := by simpa using hy
            exact this.elim
        | inr ze =>
            have hy := congrArg (fun v => v.2.1) hthin
            have hz := congrArg (fun v => v.2.2) hthin
            simp [projectiveDirectionVector] at hy hz
            have haone : (a : ZMod p) = 1 := by simpa using hy.symm
            simp only [Sum.inr.injEq]
            simpa [haone] using hz
  · intro h
    simpa [h]

#print axioms adjusted_lifts_proportional_mod_p
#print axioms integralNeighbor_eq_iff_projectiveDirection_eq
#print axioms adjusted_second_lifts_proportional_mod_p
#print axioms brandtSecondIntegralNeighbor_eq_iff_projectiveDirection_eq

end Soma.Holonics.Millennium.FamilyTunnellBrandtDistinctNeighbors
