import Holonics.Objects.Ratio.SelectedQuadratic.PositiveRoot

/-!
# Bounded join to RationalRootCensus::source_roots and PositiveRoot's decoder

Existing owners: `ratio::polynomial::{RationalRootCensus, SourceRoot,
monic_companion_of}` and `Holonics.Mathematics.Sturm.{evalAt,evalReal}`.
For D = n/d, d > 0, the primitive source is A=[-n,0,d] and the
monic companion is B=[-n*d,0,1]. The native scale is d. We prove the
degree-two specialization B(d*x)=d*A(x), then its producing-root decoder.
No second root representation and no assertion that a Sturm receipt alone
has been proved to denote an actual root.
-/
namespace Holonics.Objects.Ratio.SelectedQuadratic
open Holonics.Mathematics.Sturm

theorem source_primitive_reading (n d : ℚ) (x : ℝ) :
    evalReal x [-n, 0, d] = (d : ℝ) * x ^ 2 - (n : ℝ) := by
  simp only [evalReal, Rat.cast_neg, Rat.cast_zero, mul_zero, add_zero, zero_add]
  ring

theorem companion_reading (n d : ℚ) (z : ℝ) :
    evalReal z [-(n * d), 0, 1] = z ^ 2 - (n : ℝ) * (d : ℝ) := by
  simp only [evalReal, Rat.cast_neg, Rat.cast_mul, Rat.cast_zero, Rat.cast_one,
    mul_zero, add_zero, zero_add, mul_one]
  ring

theorem source_companion_identity (n d : ℚ) (x : ℝ) :
    evalReal ((d : ℝ) * x) [-(n * d), 0, 1] =
      (d : ℝ) * evalReal x [-n, 0, d] := by
  rw [companion_reading, source_primitive_reading]
  ring

theorem source_companion_root_iff (n d : ℚ) (hd : 0 < d) (x : ℝ) :
    evalReal ((d : ℝ) * x) [-(n * d), 0, 1] = 0 ↔
      evalReal x [-n, 0, d] = 0 := by
  rw [source_companion_identity]
  have h : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  exact mul_eq_zero.trans (or_iff_right h)

theorem companion_selected_decodes {n d D : ℚ} {z : ℝ}
    (hd : 0 < d) (hD : D = n / d) (hz : 0 < z)
    (hb : evalReal z [-(n * d), 0, 1] = 0) :
    0 < z / (d : ℝ) ∧ (z / (d : ℝ)) ^ 2 = (D : ℝ) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdR
  have hzq : z ^ 2 = (n : ℝ) * (d : ℝ) := by
    simpa only [companion_reading, sub_eq_zero] using hb
  refine ⟨div_pos hz hdR, ?_⟩
  rw [hD, Rat.cast_div]
  field_simp
  nlinarith [hzq]

/-- The source value selected by the native enclosure equals the positive
companion decoded by the native leading coefficient. This closes the named
owner connection conditional on the companion's actual root equation. -/
theorem decoder_agrees_selected {n d D : ℚ} {z s : ℝ}
    (hd : 0 < d) (hD : D = n / d) (hz : 0 < z)
    (hb : evalReal z [-(n * d), 0, 1] = 0)
    (hs : 0 < s) (hsq : s ^ 2 = (D : ℝ)) : z / (d : ℝ) = s := by
  obtain ⟨hp, he⟩ := companion_selected_decodes hd hD hz hb
  exact positive_root_unique hp hs he hsq

theorem decoded_interval_order {d lower upper : ℚ} (hd : 0 < d)
    (ho : lower < upper) : lower / d < upper / d :=
  (div_lt_div_iff_of_pos_right hd).mpr ho

theorem decoded_root_enclosure {d lower upper : ℚ} {z : ℝ}
    (hd : 0 < d) (hl : (lower : ℝ) < z) (hu : z < (upper : ℝ)) :
    ((lower / d : ℚ) : ℝ) < z / (d : ℝ) ∧
      z / (d : ℝ) < ((upper / d : ℚ) : ℝ) := by
  have h : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  simp only [Rat.cast_div]
  exact ⟨(div_lt_div_iff_of_pos_right h).mpr hl,
    (div_lt_div_iff_of_pos_right h).mpr hu⟩

#print axioms source_primitive_reading
#print axioms companion_reading
#print axioms source_companion_identity
#print axioms source_companion_root_iff
#print axioms companion_selected_decodes
#print axioms decoder_agrees_selected
#print axioms decoded_interval_order
#print axioms decoded_root_enclosure
end Holonics.Objects.Ratio.SelectedQuadratic
