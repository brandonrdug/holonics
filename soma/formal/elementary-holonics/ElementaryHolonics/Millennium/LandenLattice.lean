import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Tactic

/-!
# LandenLattice: the cell division of the Gaussian lattice is the mean step

**The doubling-chain law behind the ledger clause.**  The square lattice `ℤ²` divides
by the parity of `m + n` into two cells: the even cell is a rotated copy of `ℤ²` at
double scale, the odd cell a shifted copy.  Reading the three theta legs through that
division returns the classical Landen identities as **exact lattice bijections** —
no analysis carries load beyond summability:

* **`theSumFaceIsTheDoubledEvenCell`** — `θ₃(t)² + θ₄(t)² = 2·θ₃(2t)²`;
* **`theDifferenceFaceIsTheDoubledOddCell`** — `θ₃(t)² − θ₄(t)² = 2·θ₂(2t)²`;
* **`theProductFaceIsTheDoubledSignedCell`** — `θ₃(t)·θ₄(t) = θ₄(2t)²`
  (the odd cell cancels under the reflection `(m,n) ↦ (n,m)`, whose hand is the sign);
* **`theDoublingChartIsTheMeanStep`** — the packaging: ascending the base-2 chart
  `t ↦ 2t` carries `(θ₃², θ₄²)` to their arithmetic and geometric means.  Iterating
  is Gauss's arithmetic–geometric mean; its fixed point computes the lemniscatic
  period the rank-zero ledger clause names.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.LandenLattice

open Real

/-! ## 1. The three theta legs -/

/-- The half-shifted leg `θ₂`. -/
def T2 (t : ℝ) : ℝ := ∑' n : ℤ, rexp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t)

/-- The plain leg `θ₃`. -/
def T3 (t : ℝ) : ℝ := ∑' n : ℤ, rexp (-π * (n : ℝ) ^ 2 * t)

/-- The signed leg `θ₄`. -/
def T4 (t : ℝ) : ℝ := ∑' n : ℤ, (-1 : ℝ) ^ n * rexp (-π * (n : ℝ) ^ 2 * t)

/-! ## 2. Summability -/

private lemma summable_shift {c : ℝ} (hc : 0 < c) (a : ℝ) :
    Summable fun n : ℤ => rexp (-c * ((n : ℝ) + a) ^ 2) := by
  have key : ∀ b : ℝ, Summable fun n : ℕ => rexp (-c * ((n : ℝ) + b) ^ 2) := by
    intro b
    have hbound : ∀ n : ℕ, rexp (-c * ((n : ℝ) + b) ^ 2)
        ≤ rexp (c * (1 - 2 * b)) * rexp (-(2 * c)) ^ n := by
      intro n
      rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      nlinarith [mul_nonneg hc.le (sq_nonneg ((n : ℝ) + b - 1))]
    refine Summable.of_nonneg_of_le (fun n => (Real.exp_pos _).le) hbound ?_
    refine Summable.mul_left _ (summable_geometric_of_lt_one (Real.exp_pos _).le ?_)
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr (by linarith)
  refine Summable.of_nat_of_neg_add_one (key a) ?_
  refine (key (1 - a)).congr fun n => ?_
  congr 1
  push_cast
  ring

private lemma summable_g3 {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => rexp (-π * (n : ℝ) ^ 2 * t) := by
  refine (summable_shift (mul_pos pi_pos ht) 0).congr fun n => ?_
  congr 1
  ring

private lemma norm_g3 {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => ‖rexp (-π * (n : ℝ) ^ 2 * t)‖ :=
  (summable_g3 ht).congr fun n => (Real.norm_of_nonneg (Real.exp_pos _).le).symm

private lemma habs4 (t : ℝ) (n : ℤ) :
    ‖(-1 : ℝ) ^ n * rexp (-π * (n : ℝ) ^ 2 * t)‖ = rexp (-π * (n : ℝ) ^ 2 * t) := by
  rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
    Real.norm_of_nonneg (Real.exp_pos _).le]

private lemma norm_g4 {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => ‖(-1 : ℝ) ^ n * rexp (-π * (n : ℝ) ^ 2 * t)‖ :=
  (summable_g3 ht).congr fun n => (habs4 t n).symm

private lemma summable_g2 {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => rexp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t) := by
  refine (summable_shift (mul_pos pi_pos ht) (1 / 2)).congr fun n => ?_
  congr 1
  ring

private lemma norm_g2 {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℤ => ‖rexp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t)‖ :=
  (summable_g2 ht).congr fun n => (Real.norm_of_nonneg (Real.exp_pos _).le).symm

/-! ## 3. The lattice faces of the squares -/

private lemma exp_merge (t : ℝ) (a b : ℝ) :
    rexp (-π * a ^ 2 * t) * rexp (-π * b ^ 2 * t)
      = rexp (-π * t * (a ^ 2 + b ^ 2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

private lemma T3_sq {t : ℝ} (ht : 0 < t) :
    T3 t ^ 2 = ∑' p : ℤ × ℤ, rexp (-π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  rw [T3, sq, tsum_mul_tsum_of_summable_norm (norm_g3 ht) (norm_g3 ht)]
  exact tsum_congr fun p => exp_merge t _ _

private lemma neg_one_zpow_self_mul (v : ℤ) : ((-1 : ℝ)) ^ v * (-1) ^ v = 1 := by
  rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
  exact Even.neg_one_zpow ⟨v, rfl⟩

private lemma T4_sq {t : ℝ} (ht : 0 < t) :
    T4 t ^ 2 = ∑' p : ℤ × ℤ,
      (-1 : ℝ) ^ (p.1 + p.2) * rexp (-π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  rw [T4, sq, tsum_mul_tsum_of_summable_norm (norm_g4 ht) (norm_g4 ht)]
  refine tsum_congr fun p => ?_
  rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), ← exp_merge t]
  ring

private lemma T2_sq {t : ℝ} (ht : 0 < t) :
    T2 t ^ 2 = ∑' p : ℤ × ℤ,
      rexp (-π * t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  rw [T2, sq, tsum_mul_tsum_of_summable_norm (norm_g2 ht) (norm_g2 ht)]
  refine tsum_congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private lemma summable_L3 {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ => rexp (-π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  refine (summable_mul_of_summable_norm (norm_g3 ht) (norm_g3 ht)).congr fun p => ?_
  exact exp_merge t _ _

private lemma summable_L4 {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ =>
      (-1 : ℝ) ^ (p.1 + p.2) * rexp (-π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  refine (summable_mul_of_summable_norm (norm_g4 ht) (norm_g4 ht)).congr fun p => ?_
  rw [zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), ← exp_merge t]
  ring

/-! ## 4. The even cell -/

private def D : ℤ × ℤ → ℤ × ℤ := fun q => (q.1 + q.2, q.1 - q.2)

private lemma D_injective : Function.Injective D := by
  intro a b hab
  have h1 : a.1 + a.2 = b.1 + b.2 := congrArg Prod.fst hab
  have h2 : a.1 - a.2 = b.1 - b.2 := congrArg Prod.snd hab
  have h3 : a.1 = b.1 := by omega
  have h4 : a.2 = b.2 := by omega
  exact Prod.ext_iff.mpr ⟨h3, h4⟩

private lemma mem_range_D {x : ℤ × ℤ} : x ∈ Set.range D ↔ Even (x.1 + x.2) := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, by simp only [D]; ring⟩
  · rintro ⟨u, hu⟩
    refine ⟨(u, x.1 - u), ?_⟩
    simp only [D]
    refine Prod.ext_iff.mpr ⟨by ring, by omega⟩

private lemma D_even (q : ℤ × ℤ) : Even ((D q).1 + (D q).2) :=
  ⟨q.1, by simp only [D]; ring⟩

/-! ## 5. The sum face -/

set_option maxHeartbeats 1000000 in
/-- **THE SUM FACE IS THE DOUBLED EVEN CELL**: `θ₃(t)² + θ₄(t)² = 2·θ₃(2t)²`.
The odd cell cancels against the sign; the even cell is `ℤ²` rotated to double
scale. -/
theorem theSumFaceIsTheDoubledEvenCell {t : ℝ} (ht : 0 < t) :
    T3 t ^ 2 + T4 t ^ 2 = 2 * T3 (2 * t) ^ 2 := by
  have h2t : 0 < 2 * t := by linarith
  set g : ℤ × ℤ → ℝ := fun p =>
    (1 + (-1 : ℝ) ^ (p.1 + p.2)) * rexp (-π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
    with hg
  have hgather : T3 t ^ 2 + T4 t ^ 2 = ∑' p : ℤ × ℤ, g p := by
    rw [T3_sq ht, T4_sq ht, ← (summable_L3 ht).tsum_add (summable_L4 ht)]
    exact tsum_congr fun p => by rw [hg]; ring
  have hsupp : ∀ x ∉ Set.range D, g x = 0 := by
    intro x hx
    have hodd : ¬ Even (x.1 + x.2) := fun h => hx (mem_range_D.mpr h)
    rw [hg]
    simp only
    rw [neg_one_zpow_eq_ite, if_neg hodd]
    ring
  have hcomp : Summable (g ∘ D) := by
    refine (((summable_L3 h2t).mul_left 2)).congr fun q => ?_
    show 2 * rexp (-π * (2 * t) * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) = g (D q)
    rw [hg]
    simp only [D]
    rw [neg_one_zpow_eq_ite,
      if_pos (show Even (q.1 + q.2 + (q.1 - q.2)) from ⟨q.1, by ring⟩)]
    have hexp2 : -π * t * (((q.1 + q.2 : ℤ) : ℝ) ^ 2 + ((q.1 - q.2 : ℤ) : ℝ) ^ 2)
        = -π * (2 * t) * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) := by
      push_cast
      ring
    rw [hexp2]
    ring
  have hkey : ∑' p : ℤ × ℤ, g p = ∑' q : ℤ × ℤ, g (D q) :=
    ((D_injective.hasSum_iff hsupp).mp hcomp.hasSum).tsum_eq
  have hcell : ∑' q : ℤ × ℤ, g (D q)
      = 2 * ∑' q : ℤ × ℤ, rexp (-π * (2 * t) * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [hg]
    simp only [D]
    rw [neg_one_zpow_eq_ite,
      if_pos (show Even (q.1 + q.2 + (q.1 - q.2)) from ⟨q.1, by ring⟩)]
    have hexp2 : -π * t * (((q.1 + q.2 : ℤ) : ℝ) ^ 2 + ((q.1 - q.2 : ℤ) : ℝ) ^ 2)
        = -π * (2 * t) * ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2) := by
      push_cast
      ring
    rw [hexp2]
    ring
  rw [hgather, hkey, hcell, ← T3_sq h2t]

/-! ## 6. The difference face -/

private lemma summable_L2' {t : ℝ} (ht : 0 < t) :
    Summable fun p : ℤ × ℤ =>
      rexp (-π * t * (((p.1 : ℝ) + 1 / 2) ^ 2 + ((p.2 : ℝ) + 1 / 2) ^ 2)) := by
  refine (summable_mul_of_summable_norm (norm_g2 ht) (norm_g2 ht)).congr fun p => ?_
  rw [← Real.exp_add]
  congr 1
  ring

private def Do : ℤ × ℤ → ℤ × ℤ := fun q => (q.1 + q.2 + 1, q.1 - q.2)

private lemma Do_injective : Function.Injective Do := by
  intro a b hab
  have h1 : a.1 + a.2 + 1 = b.1 + b.2 + 1 := congrArg Prod.fst hab
  have h2 : a.1 - a.2 = b.1 - b.2 := congrArg Prod.snd hab
  have h3 : a.1 = b.1 := by omega
  have h4 : a.2 = b.2 := by omega
  exact Prod.ext_iff.mpr ⟨h3, h4⟩

private lemma mem_range_Do {x : ℤ × ℤ} : x ∈ Set.range Do ↔ ¬ Even (x.1 + x.2) := by
  constructor
  · rintro ⟨q, rfl⟩
    simp only [Do]
    rw [Int.even_iff]
    omega
  · intro hodd
    rw [Int.even_iff] at hodd
    refine ⟨((x.1 + x.2 - 1) / 2, (x.1 - x.2 - 1) / 2), ?_⟩
    simp only [Do]
    refine Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma Do_odd (q : ℤ × ℤ) : ¬ Even ((Do q).1 + (Do q).2) := by
  simp only [Do]
  rw [Int.even_iff]
  omega

set_option maxHeartbeats 1000000 in
/-- **THE DIFFERENCE FACE IS THE DOUBLED ODD CELL**: `θ₃(t)² − θ₄(t)² = 2·θ₂(2t)²`.
The even cell cancels; the odd cell is the half-shifted lattice at double scale. -/
theorem theDifferenceFaceIsTheDoubledOddCell {t : ℝ} (ht : 0 < t) :
    T3 t ^ 2 - T4 t ^ 2 = 2 * T2 (2 * t) ^ 2 := by
  have h2t : 0 < 2 * t := by linarith
  set g : ℤ × ℤ → ℝ := fun p =>
    (1 - (-1 : ℝ) ^ (p.1 + p.2)) * rexp (-π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))
    with hg
  have hgather : T3 t ^ 2 - T4 t ^ 2 = ∑' p : ℤ × ℤ, g p := by
    rw [T3_sq ht, T4_sq ht, ← (summable_L3 ht).tsum_sub (summable_L4 ht)]
    exact tsum_congr fun p => by rw [hg]; ring
  have hsupp : ∀ x ∉ Set.range Do, g x = 0 := by
    intro x hx
    have heven : Even (x.1 + x.2) := by
      by_contra hodd
      exact hx (mem_range_Do.mpr hodd)
    rw [hg]
    simp only
    rw [neg_one_zpow_eq_ite, if_pos heven]
    ring
  have hterm : ∀ q : ℤ × ℤ, g (Do q)
      = 2 * rexp (-π * (2 * t) * (((q.1 : ℝ) + 1 / 2) ^ 2 + ((q.2 : ℝ) + 1 / 2) ^ 2)) := by
    intro q
    rw [hg]
    simp only [Do]
    rw [neg_one_zpow_eq_ite, if_neg (by rw [Int.even_iff]; omega)]
    have hexp2 : -π * t * (((q.1 + q.2 + 1 : ℤ) : ℝ) ^ 2 + ((q.1 - q.2 : ℤ) : ℝ) ^ 2)
        = -π * (2 * t) * (((q.1 : ℝ) + 1 / 2) ^ 2 + ((q.2 : ℝ) + 1 / 2) ^ 2) := by
      push_cast
      ring
    rw [hexp2]
    ring
  have hcomp : Summable (g ∘ Do) := by
    refine (((summable_L2' h2t)).mul_left 2).congr fun q => ?_
    exact (hterm q).symm
  have hkey : ∑' p : ℤ × ℤ, g p = ∑' q : ℤ × ℤ, g (Do q) :=
    ((Do_injective.hasSum_iff hsupp).mp hcomp.hasSum).tsum_eq
  have hcell : ∑' q : ℤ × ℤ, g (Do q)
      = 2 * ∑' q : ℤ × ℤ,
          rexp (-π * (2 * t) * (((q.1 : ℝ) + 1 / 2) ^ 2 + ((q.2 : ℝ) + 1 / 2) ^ 2)) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun q => hterm q
  rw [hgather, hkey, hcell, ← T2_sq h2t]

/-! ## 7. The product face -/

set_option maxHeartbeats 1000000 in
/-- **THE PRODUCT FACE IS THE DOUBLED SIGNED CELL**: `θ₃(t)·θ₄(t) = θ₄(2t)²`.
The odd cell cancels under the reflection `(m, n) ↦ (n, m)` — the hand of the
reflection is the sign — and the even cell carries the signed lattice at double
scale. -/
theorem theProductFaceIsTheDoubledSignedCell {t : ℝ} (ht : 0 < t) :
    T3 t * T4 t = T4 (2 * t) ^ 2 := by
  have h2t : 0 < 2 * t := by linarith
  set g : ℤ × ℤ → ℝ := fun p =>
    (-1 : ℝ) ^ p.2 * rexp (-π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) with hg
  have hnormg : Summable fun p : ℤ × ℤ => ‖g p‖ := by
    refine (summable_L3 ht).congr fun p => ?_
    rw [hg]
    simp only
    rw [norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul,
      Real.norm_of_nonneg (Real.exp_pos _).le]
  have hsg : Summable g := hnormg.of_norm
  have hgather : T3 t * T4 t = ∑' p : ℤ × ℤ, g p := by
    rw [T3, T4, tsum_mul_tsum_of_summable_norm (norm_g3 ht) (norm_g4 ht)]
    refine tsum_congr fun p => ?_
    rw [hg]
    simp only
    rw [← exp_merge t]
    ring
  -- split into the two cells
  set ge : ℤ × ℤ → ℝ := fun p => if Even (p.1 + p.2) then g p else 0 with hge
  set go : ℤ × ℤ → ℝ := fun p => if Even (p.1 + p.2) then 0 else g p with hgo
  have hsplit : ∀ p, g p = ge p + go p := by
    intro p
    rw [hge, hgo]
    simp only
    by_cases hp : Even (p.1 + p.2)
    · rw [if_pos hp, if_pos hp, add_zero]
    · rw [if_neg hp, if_neg hp, zero_add]
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
  -- the odd cell cancels under the reflection
  have hodd_zero : ∑' p : ℤ × ℤ, go p = 0 := by
    have hswap : ∀ p : ℤ × ℤ, go ((Equiv.prodComm ℤ ℤ) p) = - go p := by
      intro p
      rw [hgo]
      simp only [Equiv.prodComm_apply, Prod.swap]
      by_cases hp : Even (p.1 + p.2)
      · rw [if_pos (by rwa [add_comm] at hp), if_pos hp, neg_zero]
      · rw [if_neg (by rwa [add_comm] at hp), if_neg hp]
        rw [hg]
        simp only
        have hprod : (-1 : ℝ) ^ p.1 * (-1) ^ p.2 = -1 := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), neg_one_zpow_eq_ite,
            if_neg hp]
        have hs : (-1 : ℝ) ^ p.1 = -(-1) ^ p.2 := by
          calc (-1 : ℝ) ^ p.1
              = (-1) ^ p.1 * ((-1) ^ p.2 * (-1) ^ p.2) := by
                rw [neg_one_zpow_self_mul, mul_one]
            _ = ((-1) ^ p.1 * (-1) ^ p.2) * (-1) ^ p.2 := by ring
            _ = -(-1) ^ p.2 := by rw [hprod]; ring
        rw [hs, show -π * t * ((p.2 : ℝ) ^ 2 + (p.1 : ℝ) ^ 2)
            = -π * t * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) from by ring]
        ring
    have h1 : ∑' p : ℤ × ℤ, go ((Equiv.prodComm ℤ ℤ) p) = ∑' p : ℤ × ℤ, go p :=
      (Equiv.prodComm ℤ ℤ).tsum_eq go
    have h2 : ∑' p : ℤ × ℤ, go ((Equiv.prodComm ℤ ℤ) p) = ∑' p : ℤ × ℤ, - go p :=
      tsum_congr hswap
    rw [h2, tsum_neg] at h1
    linarith
  -- the even cell carries the signed double-scale lattice
  have hsupp : ∀ x ∉ Set.range D, ge x = 0 := by
    intro x hx
    have hodd : ¬ Even (x.1 + x.2) := fun h => hx (mem_range_D.mpr h)
    rw [hge]
    simp only
    rw [if_neg hodd]
  have hterm : ∀ q : ℤ × ℤ, ge (D q)
      = ((-1 : ℝ) ^ q.1 * rexp (-π * (q.1 : ℝ) ^ 2 * (2 * t)))
        * ((-1 : ℝ) ^ q.2 * rexp (-π * (q.2 : ℝ) ^ 2 * (2 * t))) := by
    intro q
    rw [hge]
    simp only [D]
    rw [if_pos (show Even (q.1 + q.2 + (q.1 - q.2)) from ⟨q.1, by ring⟩), hg]
    simp only
    have hsub : ((-1 : ℝ)) ^ (q.1 - q.2) = (-1) ^ q.1 * (-1) ^ q.2 := by
      have h1 : ((-1 : ℝ)) ^ (q.1 - q.2) * (-1) ^ q.2 = (-1) ^ q.1 := by
        rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
        congr 1
        ring
      calc ((-1 : ℝ)) ^ (q.1 - q.2)
          = ((-1) ^ (q.1 - q.2) * (-1) ^ q.2) * (-1) ^ q.2 := by
            rw [mul_assoc, neg_one_zpow_self_mul, mul_one]
        _ = (-1) ^ q.1 * (-1) ^ q.2 := by rw [h1]
    have hexp2 : -π * t * (((q.1 + q.2 : ℤ) : ℝ) ^ 2 + ((q.1 - q.2 : ℤ) : ℝ) ^ 2)
        = (-π * (q.1 : ℝ) ^ 2 * (2 * t)) + (-π * (q.2 : ℝ) ^ 2 * (2 * t)) := by
      push_cast
      ring
    rw [hsub, hexp2, Real.exp_add]
    ring
  have hcomp : Summable (ge ∘ D) := by
    refine (summable_mul_of_summable_norm (norm_g4 h2t) (norm_g4 h2t)).congr
      fun q => ?_
    exact (hterm q).symm
  have hkey : ∑' p : ℤ × ℤ, ge p = ∑' q : ℤ × ℤ, ge (D q) :=
    ((D_injective.hasSum_iff hsupp).mp hcomp.hasSum).tsum_eq
  have hT4sq : T4 (2 * t) ^ 2 = ∑' q : ℤ × ℤ,
      ((-1 : ℝ) ^ q.1 * rexp (-π * (q.1 : ℝ) ^ 2 * (2 * t)))
        * ((-1 : ℝ) ^ q.2 * rexp (-π * (q.2 : ℝ) ^ 2 * (2 * t))) := by
    rw [T4, sq, tsum_mul_tsum_of_summable_norm (norm_g4 h2t) (norm_g4 h2t)]
  calc T3 t * T4 t = ∑' p : ℤ × ℤ, g p := hgather
    _ = ∑' p : ℤ × ℤ, (ge p + go p) := tsum_congr hsplit
    _ = (∑' p : ℤ × ℤ, ge p) + ∑' p : ℤ × ℤ, go p := hse.tsum_add hso
    _ = ∑' p : ℤ × ℤ, ge p := by rw [hodd_zero, add_zero]
    _ = ∑' q : ℤ × ℤ, ge (D q) := hkey
    _ = T4 (2 * t) ^ 2 := by
        rw [hT4sq]
        exact tsum_congr hterm

/-! ## 8. The mean step -/

/-- **THE DOUBLING CHART IS THE MEAN STEP**: ascending `t ↦ 2t` carries the pair
`(θ₃², θ₄²)` to its arithmetic mean and (in square) its geometric mean — one cell
division of the lattice is one step of Gauss's arithmetic–geometric mean, whose
fixed point computes the lemniscatic period of the rank-zero ledger clause. -/
theorem theDoublingChartIsTheMeanStep {t : ℝ} (ht : 0 < t) :
    T3 (2 * t) ^ 2 = (T3 t ^ 2 + T4 t ^ 2) / 2 ∧
    (T4 (2 * t) ^ 2) ^ 2 = T3 t ^ 2 * T4 t ^ 2 := by
  constructor
  · have h := theSumFaceIsTheDoubledEvenCell ht
    linarith
  · rw [← theProductFaceIsTheDoubledSignedCell ht]
    ring

end Soma.Holonics.Millennium.LandenLattice
