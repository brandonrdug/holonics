import ElementaryHolonics.Millennium.LandenLattice
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# ThetaQuartic: the shifted product face and Jacobi's quartic identity

**The fourth cell-division law, and its classical corollary.**  The shifted lattice
divides by the parity of `m + n` into two cells, and **both** carry the same
product:

* **`theShiftedProductFace`** — `θ₂(t)² = 2·θ₂(2t)·θ₃(2t)`;
* **`theJacobiQuartic`** — `θ₃(t)⁴ = θ₂(t)⁴ + θ₄(t)⁴`, by one certified linear
  combination of the four cell-division laws.

The quartic is the algebraic backbone of the lemniscatic point: at the reflection
fixed point the two outer legs agree and the quartic forces `θ₃⁴ = 2θ₄⁴` — the
`√2` of the arithmetic–geometric mean.  Every `theorem` is discharged and none
depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.ThetaQuartic

open Real
open Soma.Holonics.Millennium.LandenLattice

/-! ## 0. Plumbing -/

private lemma key_nat {c : ℝ} (hc : 0 < c) (b : ℝ) :
    Summable fun n : ℕ => rexp (-c * ((n : ℝ) + b) ^ 2) := by
  have hbound : ∀ n : ℕ, rexp (-c * ((n : ℝ) + b) ^ 2)
      ≤ rexp (c * (1 - 2 * b)) * rexp (-(2 * c)) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_nonneg hc.le (sq_nonneg ((n : ℝ) + b - 1))]
  refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hbound ?_
  refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
  rw [← Real.exp_zero]
  exact Real.exp_lt_exp.mpr (by linarith)

private lemma summable_shift {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Summable fun n : ℤ => rexp (-π * ((n : ℝ) + a) ^ 2 * t) := by
  have hc : 0 < π * t := by positivity
  refine Summable.of_nat_of_neg_add_one
    ((key_nat hc a).congr fun n => by congr 1; push_cast; ring)
    ((key_nat hc (1 - a)).congr fun n => by congr 1; push_cast; ring)

private lemma norm_shift {t : ℝ} (ht : 0 < t) (a : ℝ) :
    Summable fun n : ℤ => ‖rexp (-π * ((n : ℝ) + a) ^ 2 * t)‖ :=
  (summable_shift ht a).congr fun n =>
    (Real.norm_of_nonneg (Real.exp_pos _).le).symm

/-! ## 1. The lattice face of the shifted square -/

private lemma T2_sq {t : ℝ} (ht : 0 < t) :
    T2 t ^ 2 = ∑' p : ℤ × ℤ,
      rexp (-π * t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  rw [T2, sq, tsum_mul_tsum_of_summable_norm (norm_shift ht (1 / 2))
    (norm_shift ht (1 / 2))]
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private lemma summable_L2 {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ =>
      rexp (-π * t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  refine (summable_mul_of_summable_norm (norm_shift ht (1 / 2))
    (norm_shift ht (1 / 2))).congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

/-! ## 2. The even and odd cells both carry the product -/

private def D : ℤ × ℤ → ℤ × ℤ := fun q => (q.1 + q.2, q.1 - q.2)

private lemma D_injective : Function.Injective D := by
  intro a b hab
  have h1 : a.1 + a.2 = b.1 + b.2 := congrArg Prod.fst hab
  have h2 : a.1 - a.2 = b.1 - b.2 := congrArg Prod.snd hab
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private def Do : ℤ × ℤ → ℤ × ℤ := fun q => (q.1 + q.2 + 1, q.1 - q.2)

private lemma Do_injective : Function.Injective Do := by
  intro a b hab
  have h1 : a.1 + a.2 + 1 = b.1 + b.2 + 1 := congrArg Prod.fst hab
  have h2 : a.1 - a.2 = b.1 - b.2 := congrArg Prod.snd hab
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma mem_range_D {x : ℤ × ℤ} : x ∈ Set.range D ↔ Even (x.1 + x.2) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, by simp only [D]; ring⟩
  · rintro ⟨u, hu⟩
    exact ⟨(u, x.1 - u), Prod.ext_iff.mpr ⟨by simp only [D]; ring, by
      simp only [D]; omega⟩⟩

private lemma mem_range_Do {x : ℤ × ℤ} : x ∈ Set.range Do ↔ ¬ Even (x.1 + x.2) := by
  constructor
  · rintro ⟨q, rfl⟩
    simp only [Do]
    rw [Int.even_iff]
    omega
  · intro hodd
    rw [Int.even_iff] at hodd
    exact ⟨((x.1 + x.2 - 1) / 2, (x.1 - x.2 - 1) / 2), Prod.ext_iff.mpr
      ⟨by simp only [Do]; omega, by simp only [Do]; omega⟩⟩

set_option maxHeartbeats 2000000 in
/-- **THE SHIFTED PRODUCT FACE**: `θ₂(t)² = 2·θ₂(2t)·θ₃(2t)` — the shifted lattice
divides by parity and both cells carry the same product. -/
theorem theShiftedProductFace {t : ℝ} (ht : 0 < t) :
    T2 t ^ 2 = 2 * (T2 (2 * t) * T3 (2 * t)) := by
  have h2t : 0 < 2 * t := by linarith
  set g : ℤ × ℤ → ℝ := fun p =>
    rexp (-π * t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) with hg
  set ge : ℤ × ℤ → ℝ := fun p => if Even (p.1 + p.2) then g p else 0 with hge
  set go : ℤ × ℤ → ℝ := fun p => if Even (p.1 + p.2) then 0 else g p with hgo
  have hsplit : ∀ p, g p = ge p + go p := by
    intro p
    rw [hge, hgo]
    simp only
    by_cases hp : Even (p.1 + p.2)
    · rw [if_pos hp, if_pos hp, add_zero]
    · rw [if_neg hp, if_neg hp, zero_add]
  have hnormg : Summable fun p : ℤ × ℤ => ‖g p‖ :=
    (summable_L2 ht).congr fun p =>
      (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hse : Summable ge := by
    refine Summable.of_norm_bounded hnormg fun p => ?_
    rw [hge]
    simp only
    by_cases hp : Even (p.1 + p.2)
    · rw [if_pos hp]
    · rw [if_neg hp, norm_zero]
      exact norm_nonneg _
  have hso : Summable go := by
    refine Summable.of_norm_bounded hnormg fun p => ?_
    rw [hgo]
    simp only
    by_cases hp : Even (p.1 + p.2)
    · rw [if_pos hp, norm_zero]
      exact norm_nonneg _
    · rw [if_neg hp]
  -- the even cell: the map `(s,d) ↦ (s+d, s−d)`
  have hterm_e : ∀ q : ℤ × ℤ, ge (D q)
      = rexp (-π * ((q.1 : ℝ) + 1 / 2) ^ 2 * (2 * t))
        * rexp (-π * (q.2 : ℝ) ^ 2 * (2 * t)) := by
    intro q
    rw [hge]
    change (if Even ((D q).1 + (D q).2) then g (D q) else 0) = _
    rw [if_pos (show Even ((D q).1 + (D q).2) from by simp [D]), hg]
    simp only [D]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hnorm0 : Summable fun n : ℤ => ‖rexp (-π * (n : ℝ) ^ 2 * (2 * t))‖ :=
    ((summable_shift h2t 0).congr fun n => by congr 1; ring).congr fun n =>
      (Real.norm_of_nonneg (Real.exp_pos _).le).symm
  have hcomp_e : Summable (ge ∘ D) := by
    refine (summable_mul_of_summable_norm (norm_shift h2t (1 / 2))
      hnorm0).congr fun q => ?_
    exact (hterm_e q).symm
  have hsupp_e : ∀ x ∉ Set.range D, ge x = 0 := by
    intro x hx
    rw [hge]
    simp only
    rw [if_neg (fun h => hx (mem_range_D.mpr h))]
  have hkey_e : ∑' p : ℤ × ℤ, ge p = ∑' q : ℤ × ℤ, ge (D q) :=
    ((D_injective.hasSum_iff hsupp_e).mp hcomp_e.hasSum).tsum_eq
  have hcell_e : ∑' q : ℤ × ℤ, ge (D q) = T2 (2 * t) * T3 (2 * t) := by
    rw [T2, T3, tsum_mul_tsum_of_summable_norm (norm_shift h2t (1 / 2)) hnorm0]
    exact tsum_congr hterm_e
  -- the odd cell: the map `(s,d) ↦ (s+d+1, s−d)`
  have hterm_o : ∀ q : ℤ × ℤ, go (Do q)
      = rexp (-π * ((q.1 : ℝ) + 1) ^ 2 * (2 * t))
        * rexp (-π * ((q.2 : ℝ) + 1 / 2) ^ 2 * (2 * t)) := by
    intro q
    rw [hgo]
    change (if Even ((Do q).1 + (Do q).2) then 0 else g (Do q)) = _
    rw [if_neg (show ¬ Even ((Do q).1 + (Do q).2) from by
      simp only [Do]
      rw [Int.even_iff]
      omega), hg]
    simp only [Do]
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hcomp_o : Summable (go ∘ Do) := by
    refine (summable_mul_of_summable_norm (norm_shift h2t 1)
      (norm_shift h2t (1 / 2))).congr fun q => ?_
    exact (hterm_o q).symm
  have hsupp_o : ∀ x ∉ Set.range Do, go x = 0 := by
    intro x hx
    rw [hgo]
    simp only
    by_cases hp : Even (x.1 + x.2)
    · rw [if_pos hp]
    · exact absurd (mem_range_Do.mpr hp) hx
  have hkey_o : ∑' p : ℤ × ℤ, go p = ∑' q : ℤ × ℤ, go (Do q) :=
    ((Do_injective.hasSum_iff hsupp_o).mp hcomp_o.hasSum).tsum_eq
  have hcell_o : ∑' q : ℤ × ℤ, go (Do q) = T3 (2 * t) * T2 (2 * t) := by
    have hT3shift : T3 (2 * t) = ∑' n : ℤ, rexp (-π * ((n : ℝ) + 1) ^ 2 * (2 * t)) := by
      rw [T3]
      refine ((Equiv.addRight (1 : ℤ)).tsum_eq
        (fun n : ℤ => rexp (-π * (n : ℝ) ^ 2 * (2 * t)))).symm.trans ?_
      refine tsum_congr fun n => ?_
      congr 1
      simp only [Equiv.coe_addRight]
      push_cast
      ring
    rw [hT3shift, T2, tsum_mul_tsum_of_summable_norm (norm_shift h2t 1)
      (norm_shift h2t (1 / 2))]
    exact tsum_congr hterm_o
  calc T2 t ^ 2 = ∑' p : ℤ × ℤ, g p := T2_sq ht
    _ = ∑' p : ℤ × ℤ, (ge p + go p) := tsum_congr hsplit
    _ = (∑' p : ℤ × ℤ, ge p) + ∑' p : ℤ × ℤ, go p := hse.tsum_add hso
    _ = T2 (2 * t) * T3 (2 * t) + T3 (2 * t) * T2 (2 * t) := by
        rw [hkey_e, hcell_e, hkey_o, hcell_o]
    _ = 2 * (T2 (2 * t) * T3 (2 * t)) := by ring

/-- **JACOBI'S QUARTIC IDENTITY**: `θ₃⁴ = θ₂⁴ + θ₄⁴` — one certified linear
combination of the four cell-division laws. -/
theorem theJacobiQuartic {t : ℝ} (ht : 0 < t) :
    T3 t ^ 4 = T2 t ^ 4 + T4 t ^ 4 := by
  have h1 := theSumFaceIsTheDoubledEvenCell ht
  have h2 := theDifferenceFaceIsTheDoubledOddCell ht
  have hp := theShiftedProductFace ht
  linear_combination (T3 t ^ 2 - T4 t ^ 2) * h1 + (2 * T3 (2 * t) ^ 2) * h2
    + (-(T2 t ^ 2 + 2 * (T2 (2 * t) * T3 (2 * t)))) * hp

end Soma.Holonics.Millennium.ThetaQuartic
