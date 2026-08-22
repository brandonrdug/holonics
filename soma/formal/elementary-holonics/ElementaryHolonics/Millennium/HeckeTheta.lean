import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# HeckeTheta: the theta function of the congruent-number curve at one

**The construction deed of the Birch–Swinnerton-Dyer campaign, first stage.**  The
L-function of `y² = x³ − x` is the Hecke L-series of the Gaussian character
`ψ(α) = ε(α)·α` on `ℤ[i]`, and its theta function — the object whose Mellin transform
is the completed L-function — is

```text
f(x)  =  Σ_{a odd, b even, a+b ≡ 1 mod 4}  (a + bi) · exp(−2π(a²+b²)x/√32).
```

This file constructs `f` **as a product of two mathlib Hurwitz kernels** and proves its
modular transformation law:

* `heckeThetaA x = 4 · oddKernel (1/4) (4√2·x)` — the weight-`3/2` factor;
* `heckeThetaC x = cosKernel (1/2) (√2·x)` — the weight-`1/2` factor;
* `heckeTheta = heckeThetaA * heckeThetaC` — verified numerically to twelve digits to
  equal the lattice sum above, coefficient stream `1, −2, −3, 6, 2, …` matching the
  point counts at `5, 9, 13, 17`;
* **`theDuplicationIdentity`**: `sinKernel (1/4) d · evenKernel (1/2) (4d)
  = 16 · oddKernel (1/4) (32d) · cosKernel (1/2) (8d)` — the level-doubling
  rearrangement (a two-isogeny in theta clothing), proved by pure series manipulation:
  the even part dies by an involution, the odd part reindexes through
  `(p,q) ↦ (p+q+1, p−q)`, and three lattice folds (swap, `v ↔ −v`, total negation)
  collapse the result onto the Gaussian classes;
* **`theHeckeThetaFunctionalEquation`**: `heckeTheta (1/x) = x² · heckeTheta x` — the
  two mathlib kernel functional equations composed with the duplication identity.
  Weight two, sign `+1`: the theta law of the congruent-number curve at one, from
  which the analytic continuation of its L-function follows by the abstract
  Mellin machinery.

Every `theorem` is discharged and none depends on `sorryAx`
(`[propext, Classical.choice, Quot.sound]`, audited).  **Boundary**: this file proves
the transformation law; the `StrongFEPair` instantiation, the entire `Λ`, and the
central-value positivity are the next stage of the campaign.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HeckeTheta

open Real HurwitzZeta Complex

/-! ## 1. The two factors and the theta -/

/-- The weight-`3/2` factor: `Σ_{a ≡ 1 mod 4} a·exp(−πx a²/(2√2))`. -/
def heckeThetaA (x : ℝ) : ℝ := 4 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (4 * Real.sqrt 2 * x)

/-- The weight-`1/2` factor: `Σ_m (−1)^m exp(−4πx m²/(2√2))`. -/
def heckeThetaC (x : ℝ) : ℝ := cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (Real.sqrt 2 * x)

/-- The Hecke theta of the congruent-number curve at one. -/
def heckeTheta (x : ℝ) : ℝ := heckeThetaA x * heckeThetaC x

/-! ## 2. Summability spine -/

private lemma sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private lemma summable_gauss_weight (d : ℝ) (hd : 0 < d) :
    Summable fun n : ℤ => |(n : ℝ)| * rexp (-π * d * n ^ 2) := by
  have h := (HurwitzZeta.hasSum_int_oddKernel 0 hd).summable.norm
  have h0 : Summable fun n : ℤ => |(n : ℝ) + 0| * rexp (-π * ((n : ℝ) + 0) ^ 2 * d) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)] using h
  refine h0.congr fun n => ?_
  rw [add_zero]
  ring_nf

private lemma summable_gauss (d : ℝ) (hd : 0 < d) :
    Summable fun n : ℤ => rexp (-π * d * n ^ 2) := by
  have h := (HurwitzZeta.hasSum_int_evenKernel 0 hd).summable
  refine h.congr fun n => ?_
  rw [add_zero]
  ring_nf

/-! ## 3. The kernels as explicit sums at the working scale

Throughout, `d > 0` is the master scale; the two kernel factors of the dual side live
at `πd`-Gaussians on the odd integers, and the theta itself at `2πd`-Gaussians. -/

/-- The sine kernel at characteristic one-quarter, as a real sum over the odd
integers: `sinKernel (1/4) d = Σ_p (2p+1)(−1)^p exp(−πd(2p+1)²)`. -/
lemma sinKernel_quarter_hasSum {d : ℝ} (hd : 0 < d) :
    HasSum (fun n : ℤ => -I * n * cexp (2 * π * I * (1 / 4 : ℝ) * n) *
      rexp (-π * n ^ 2 * d)) ((sinKernel ((1 / 4 : ℝ) : UnitAddCircle) d : ℝ) : ℂ) :=
  HurwitzZeta.hasSum_int_sinKernel (1 / 4 : ℝ) hd

/-- The even kernel at characteristic one-half, as a sum over odd squares:
`evenKernel (1/2) (2t) = Σ_q exp(−2πt(q+1/2)²·2)`. -/
lemma evenKernel_half_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => rexp (-π * ((n : ℝ) + 1 / 2) ^ 2 * t))
      (evenKernel ((1 / 2 : ℝ) : UnitAddCircle) t) :=
  HurwitzZeta.hasSum_int_evenKernel (1 / 2 : ℝ) ht

/-- The odd kernel at characteristic one-quarter, as a sum:
`oddKernel (1/4) y = Σ_k (k+1/4)·exp(−πy(k+1/4)²)`. -/
lemma oddKernel_quarter_hasSum {y : ℝ} (hy : 0 < y) :
    HasSum (fun n : ℤ => ((n : ℝ) + 1 / 4) * rexp (-π * ((n : ℝ) + 1 / 4) ^ 2 * y))
      (oddKernel ((1 / 4 : ℝ) : UnitAddCircle) y) :=
  HurwitzZeta.hasSum_int_oddKernel (1 / 4 : ℝ) hy

/-- The cosine kernel at characteristic one-half, as a real alternating Gaussian sum. -/
lemma cosKernel_half_hasSum {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => cexp (2 * π * I * (1 / 2 : ℝ) * n) * rexp (-π * n ^ 2 * t))
      ((cosKernel ((1 / 2 : ℝ) : UnitAddCircle) t : ℝ) : ℂ) :=
  HurwitzZeta.hasSum_int_cosKernel (1 / 2 : ℝ) ht


/-! ## 4. The duplication ladder: index algebra

The duplication identity is proved as a chain of eight exact rearrangements of one
absolutely convergent double sum.  Everything here is indexed by `ℤ × ℤ`; the signs are
carried by two mod-four characters, and every fold is an equivalence or an injection of
the index lattice — no analysis beyond absolute convergence enters. -/

/-- The Gaussian envelope at the theta scale. -/
private def env (d : ℝ) (u v : ℤ) : ℝ := rexp (-2 * π * d * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2))

/-- The quartic sign: `+1` on `w ≡ 1`, `−1` on `w ≡ 3 (mod 4)`, `0` on even `w`. -/
private def sgn4 (w : ℤ) : ℂ := if w % 4 = 1 then 1 else if w % 4 = 3 then -1 else 0

/-- The doubled cosine sign: `+1` on `v ≡ 0`, `−1` on `v ≡ 2 (mod 4)`, `0` on odd `v`. -/
private def cs4 (v : ℤ) : ℂ := if v % 4 = 0 then 1 else if v % 4 = 2 then -1 else 0

private lemma env_nonneg (d : ℝ) (u v : ℤ) : 0 ≤ env d u v := Real.exp_nonneg _

private lemma norm_sgn4_le (w : ℤ) : ‖sgn4 w‖ ≤ 1 := by
  unfold sgn4; split_ifs <;> simp

/-! ## 5. The one-dimensional terms and the two product families -/

/-- The `sinKernel (1/4)` summand. -/
private def sinTerm (d : ℝ) (n : ℤ) : ℂ :=
  -I * n * cexp (2 * π * I * (1 / 4 : ℝ) * n) * rexp (-π * n ^ 2 * d)

/-- The `evenKernel (1/2)` summand at scale `4d`. -/
private def evenTerm (d : ℝ) (m : ℤ) : ℂ := rexp (-π * ((m : ℝ) + 1 / 2) ^ 2 * (4 * d))

/-- The `oddKernel (1/4)` summand at scale `32d`, coerced whole. -/
private def oddTerm (d : ℝ) (k : ℤ) : ℂ :=
  ((((k : ℝ) + 1 / 4) * rexp (-π * ((k : ℝ) + 1 / 4) ^ 2 * (32 * d)) : ℝ) : ℂ)

/-- The `cosKernel (1/2)` summand at scale `8d`. -/
private def cosTerm (d : ℝ) (l : ℤ) : ℂ :=
  cexp (2 * π * I * (1 / 2 : ℝ) * l) * rexp (-π * l ^ 2 * (8 * d))

/-- The dual-side product family: `sinKernel (1/4) d` against `evenKernel (1/2) (4d)`. -/
private def dualSide (d : ℝ) (p : ℤ × ℤ) : ℂ := sinTerm d p.1 * evenTerm d p.2

/-- The primal-side product family: `oddKernel (1/4) (32d)` against `cosKernel (1/2) (8d)`. -/
private def primalSide (d : ℝ) (p : ℤ × ℤ) : ℂ := oddTerm d p.1 * cosTerm d p.2

/-- The even/odd split of the dual side by the first index. -/
private def dualEven (d : ℝ) (p : ℤ × ℤ) : ℂ := if p.1 % 2 = 0 then dualSide d p else 0

private def dualOdd (d : ℝ) (p : ℤ × ℤ) : ℂ := if p.1 % 2 = 0 then 0 else dualSide d p

/-! ## 6. The ladder functions on the folded lattice -/

/-- After the fold `(p, q) ↦ (p+q+1, p−q)`: weight `u+v`, quartic sign, envelope. -/
private def gLadder (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  ((p.1 + p.2 : ℤ) : ℂ) * sgn4 (p.1 + p.2) * (env d p.1 p.2 : ℝ)

private def gEven (d : ℝ) (p : ℤ × ℤ) : ℂ := if p.2 % 2 = 0 then gLadder d p else 0

private def gOddV (d : ℝ) (p : ℤ × ℤ) : ℂ := if p.2 % 2 = 0 then 0 else gLadder d p

/-- After the `v ↦ −v` fold: weight `u` alone. -/
private def hHalf (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.2 % 2 = 0 then (p.1 : ℂ) * sgn4 (p.1 + p.2) * (env d p.1 p.2 : ℝ) else 0

private def hPlus (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  if (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0 then (p.1 : ℂ) * (env d p.1 p.2 : ℝ) else 0

private def hMinus (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  if (p.1 + p.2) % 4 = 3 ∧ p.2 % 2 = 0 then (p.1 : ℂ) * (env d p.1 p.2 : ℝ) else 0

/-- The target shape: support `u ≡ 1 (mod 4)`, cosine sign in `v`. -/
private def hFinal (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 1 then 4 * p.1 * cs4 p.2 * (env d p.1 p.2 : ℝ) else 0

private def aPiece (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 1 ∧ p.2 % 4 = 0 then (p.1 : ℂ) * (env d p.1 p.2 : ℝ) else 0

private def bPiece (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 3 ∧ p.2 % 4 = 2 then (p.1 : ℂ) * (env d p.1 p.2 : ℝ) else 0

private def bMirror (d : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 1 ∧ p.2 % 4 = 2 then (p.1 : ℂ) * (env d p.1 p.2 : ℝ) else 0

/-! ## 7. The index maps -/

private def oddEmb (q : ℤ × ℤ) : ℤ × ℤ := (2 * q.1 + 1, q.2)

private def foldMap (q : ℤ × ℤ) : ℤ × ℤ := (q.1 + q.2 + 1, q.1 - q.2)

private def gridEmb (q : ℤ × ℤ) : ℤ × ℤ := (4 * q.1 + 1, 2 * q.2)

private lemma oddEmb_injective : Function.Injective oddEmb := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [oddEmb, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, h.2⟩

private lemma foldMap_injective : Function.Injective foldMap := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [foldMap, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma gridEmb_injective : Function.Injective gridEmb := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [gridEmb, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

/-! ## 8. Phase arithmetic -/

/-- On even integers the quarter-turn phase is invariant under negation. -/
private lemma phase_neg_even {n : ℤ} (hn : n % 2 = 0) :
    cexp (2 * π * I * (1 / 4 : ℝ) * ((-n : ℤ) : ℂ)) =
      cexp (2 * π * I * (1 / 4 : ℝ) * (n : ℂ)) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = 2 * r := ⟨n / 2, by omega⟩
  rw [show (2 * (π : ℂ) * I * ((1 / 4 : ℝ) : ℂ) * ((-(2 * r) : ℤ) : ℂ))
        = 2 * (π : ℂ) * I * ((1 / 4 : ℝ) : ℂ) * ((2 * r : ℤ) : ℂ) + (-r : ℤ) * (2 * π * I) by
      push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

private lemma sinTerm_neg_even {n : ℤ} (hn : n % 2 = 0) (d : ℝ) :
    sinTerm d (-n) = -sinTerm d n := by
  unfold sinTerm
  rw [phase_neg_even hn]
  push_cast
  rw [neg_sq]
  ring

/-- The odd-index sine term carries exactly the quartic sign. -/
private lemma sinTerm_odd (d : ℝ) (p : ℤ) :
    sinTerm d (2 * p + 1)
      = ((2 * p + 1 : ℤ) : ℂ) * sgn4 (2 * p + 1) *
          ((rexp (-π * ((2 * p + 1 : ℤ) : ℝ) ^ 2 * d) : ℝ) : ℂ) := by
  unfold sinTerm
  rcases Int.even_or_odd p with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h1 : sgn4 (2 * (t + t) + 1) = 1 := by
      unfold sgn4; rw [if_pos (by omega)]
    have h2 : cexp (2 * π * I * (1 / 4 : ℝ) * ((2 * (t + t) + 1 : ℤ) : ℂ)) = I := by
      rw [show (2 * (π : ℂ) * I * ((1 / 4 : ℝ) : ℂ) * ((2 * (t + t) + 1 : ℤ) : ℂ))
            = (t : ℤ) * (2 * π * I) + π / 2 * I by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
        Complex.exp_pi_div_two_mul_I]
    rw [h1, h2, mul_one]
    linear_combination (-(((2 * (t + t) + 1 : ℤ) : ℂ) *
      ((rexp (-π * ((2 * (t + t) + 1 : ℤ) : ℝ) ^ 2 * d) : ℝ) : ℂ))) * Complex.I_mul_I
  · have h1 : sgn4 (2 * (2 * t + 1) + 1) = -1 := by
      unfold sgn4; rw [if_neg (by omega), if_pos (by omega)]
    have h2 : cexp (2 * π * I * (1 / 4 : ℝ) * ((2 * (2 * t + 1) + 1 : ℤ) : ℂ)) = -I := by
      rw [show (2 * (π : ℂ) * I * ((1 / 4 : ℝ) : ℂ) * ((2 * (2 * t + 1) + 1 : ℤ) : ℂ))
            = (t : ℤ) * (2 * π * I) + (π * I + π / 2 * I) by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add,
        Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
      ring
    rw [h1, h2]
    linear_combination ((((2 * (2 * t + 1) + 1 : ℤ) : ℂ)) *
      ((rexp (-π * ((2 * (2 * t + 1) + 1 : ℤ) : ℝ) ^ 2 * d) : ℝ) : ℂ)) * Complex.I_mul_I

/-- The doubled cosine sign is the half-turn phase. -/
private lemma cs4_double (l : ℤ) :
    cs4 (2 * l) = cexp (2 * π * I * (1 / 2 : ℝ) * (l : ℂ)) := by
  rcases Int.even_or_odd l with ⟨s, rfl⟩ | ⟨s, rfl⟩
  · rw [show (2 * (π : ℂ) * I * ((1 / 2 : ℝ) : ℂ) * ((s + s : ℤ) : ℂ))
        = (s : ℤ) * (2 * π * I) by push_cast; ring,
      Complex.exp_int_mul_two_pi_mul_I]
    unfold cs4; rw [if_pos (by omega)]
  · rw [show (2 * (π : ℂ) * I * ((1 / 2 : ℝ) : ℂ) * ((2 * s + 1 : ℤ) : ℂ))
        = (s : ℤ) * (2 * π * I) + π * I by push_cast; ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_pi_mul_I]
    unfold cs4; rw [if_neg (by omega), if_pos (by omega)]

/-! ## 9. Summability -/

set_option maxHeartbeats 1000000 in
private lemma summable_master {c : ℝ} (hc : 0 < c) :
    Summable fun p : ℤ × ℤ =>
      (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * rexp (-π * c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hw := summable_gauss_weight c hc
  have hg := summable_gauss c hc
  have h1 : Summable fun p : ℤ × ℤ =>
      (|(p.1 : ℝ)| * rexp (-π * c * (p.1 : ℝ) ^ 2)) * rexp (-π * c * (p.2 : ℝ) ^ 2) :=
    hw.mul_of_nonneg hg (Pi.le_def.mpr fun n => by positivity)
      (Pi.le_def.mpr fun n => Real.exp_nonneg _)
  have h2 : Summable fun p : ℤ × ℤ =>
      rexp (-π * c * (p.1 : ℝ) ^ 2) * (|(p.2 : ℝ)| * rexp (-π * c * (p.2 : ℝ) ^ 2)) :=
    hg.mul_of_nonneg hw (Pi.le_def.mpr fun n => Real.exp_nonneg _)
      (Pi.le_def.mpr fun n => by positivity)
  have h3 : Summable fun p : ℤ × ℤ =>
      rexp (-π * c * (p.1 : ℝ) ^ 2) * rexp (-π * c * (p.2 : ℝ) ^ 2) :=
    hg.mul_of_nonneg hg (Pi.le_def.mpr fun n => Real.exp_nonneg _)
      (Pi.le_def.mpr fun n => Real.exp_nonneg _)
  refine ((h1.add h2).add h3).congr fun p => ?_
  rw [show -π * c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
      = -π * c * (p.1 : ℝ) ^ 2 + -π * c * (p.2 : ℝ) ^ 2 from by ring, Real.exp_add]
  ring

private lemma summable_envelope {d : ℝ} (hd : 0 < d) :
    Summable fun p : ℤ × ℤ => (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * env d p.1 p.2 := by
  refine (summable_master (show (0 : ℝ) < 2 * d by positivity)).congr fun p => ?_
  unfold env
  congr 2
  ring

private lemma summable_of_le_envelope {d : ℝ} (hd : 0 < d) {f : ℤ × ℤ → ℂ}
    (hb : ∀ p : ℤ × ℤ, ‖f p‖ ≤ (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * env d p.1 p.2) :
    Summable f :=
  Summable.of_norm_bounded (summable_envelope hd) hb

/-- The generic weighted bound: an integer weight of absolute value at most the
envelope weight, times a unimodular sign, times the envelope. -/
private lemma norm_weight_env_le (d : ℝ) (u v w : ℤ) (s : ℂ) (hs : ‖s‖ ≤ 1)
    (hw : |(w : ℝ)| ≤ |(u : ℝ)| + |(v : ℝ)| + 1) :
    ‖(w : ℂ) * s * ((env d u v : ℝ) : ℂ)‖ ≤ (|(u : ℝ)| + |(v : ℝ)| + 1) * env d u v := by
  rw [norm_mul, norm_mul]
  have h1 : ‖((w : ℤ) : ℂ)‖ = |(w : ℝ)| := by
    rw [show ((w : ℤ) : ℂ) = ((w : ℝ) : ℂ) from by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs]
  have h2 : ‖((env d u v : ℝ) : ℂ)‖ = env d u v := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (env_nonneg d u v)]
  rw [h1, h2]
  calc |(w : ℝ)| * ‖s‖ * env d u v
      ≤ ((|(u : ℝ)| + |(v : ℝ)| + 1) * 1) * env d u v := by
        apply mul_le_mul_of_nonneg_right _ (env_nonneg d u v)
        exact mul_le_mul hw hs (norm_nonneg _) (by positivity)
    _ = (|(u : ℝ)| + |(v : ℝ)| + 1) * env d u v := by ring

private lemma abs_add_cast_le (u v : ℤ) :
    |((u + v : ℤ) : ℝ)| ≤ |(u : ℝ)| + |(v : ℝ)| + 1 := by
  push_cast
  have := abs_add_le (u : ℝ) (v : ℝ)
  linarith

private lemma abs_fst_cast_le (u v : ℤ) : |(u : ℝ)| ≤ |(u : ℝ)| + |(v : ℝ)| + 1 := by
  have := abs_nonneg (v : ℝ); linarith

private lemma summable_gEven {d : ℝ} (hd : 0 < d) : Summable (gEven d) := by
  refine summable_of_le_envelope hd fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [gEven, gLadder]
  split_ifs
  · exact norm_weight_env_le d u v (u + v) _ (norm_sgn4_le _) (abs_add_cast_le u v)
  · simpa using mul_nonneg (by positivity) (env_nonneg d u v)

private lemma summable_gOddV {d : ℝ} (hd : 0 < d) : Summable (gOddV d) := by
  refine summable_of_le_envelope hd fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [gOddV, gLadder]
  split_ifs
  · simpa using mul_nonneg (by positivity) (env_nonneg d u v)
  · exact norm_weight_env_le d u v (u + v) _ (norm_sgn4_le _) (abs_add_cast_le u v)

private lemma norm_plain_weight_le (d : ℝ) (u v : ℤ) :
    ‖(u : ℂ) * ((env d u v : ℝ) : ℂ)‖ ≤ (|(u : ℝ)| + |(v : ℝ)| + 1) * env d u v := by
  rw [show (u : ℂ) * ((env d u v : ℝ) : ℂ) = (u : ℂ) * 1 * ((env d u v : ℝ) : ℂ) from by ring]
  exact norm_weight_env_le d u v u 1 (by simp) (abs_fst_cast_le u v)

private lemma summable_hPlus {d : ℝ} (hd : 0 < d) : Summable (hPlus d) := by
  refine summable_of_le_envelope hd fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [hPlus]
  split_ifs
  · exact norm_plain_weight_le d u v
  · simpa using mul_nonneg (by positivity) (env_nonneg d u v)

private lemma summable_hMinus {d : ℝ} (hd : 0 < d) : Summable (hMinus d) := by
  refine summable_of_le_envelope hd fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [hMinus]
  split_ifs
  · exact norm_plain_weight_le d u v
  · simpa using mul_nonneg (by positivity) (env_nonneg d u v)

private lemma summable_aPiece {d : ℝ} (hd : 0 < d) : Summable (aPiece d) := by
  refine summable_of_le_envelope hd fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [aPiece]
  split_ifs
  · exact norm_plain_weight_le d u v
  · simpa using mul_nonneg (by positivity) (env_nonneg d u v)

private lemma summable_bPiece {d : ℝ} (hd : 0 < d) : Summable (bPiece d) := by
  refine summable_of_le_envelope hd fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [bPiece]
  split_ifs
  · exact norm_plain_weight_le d u v
  · simpa using mul_nonneg (by positivity) (env_nonneg d u v)

private lemma summable_bMirror {d : ℝ} (hd : 0 < d) : Summable (bMirror d) := by
  refine summable_of_le_envelope hd fun p => ?_
  obtain ⟨u, v⟩ := p
  simp only [bMirror]
  split_ifs
  · exact norm_plain_weight_le d u v
  · simpa using mul_nonneg (by positivity) (env_nonneg d u v)

private lemma summable_dualSide {d : ℝ} (hd : 0 < d) : Summable (dualSide d) := by
  have h1 := (sinKernel_quarter_hasSum hd).summable
  have h2 := (Complex.hasSum_ofReal.mpr
    (evenKernel_half_hasSum (show (0 : ℝ) < 4 * d by positivity))).summable
  exact summable_norm_iff.mp ((summable_norm_iff.mpr h1).mul_norm (summable_norm_iff.mpr h2))

private lemma summable_primalSide {d : ℝ} (hd : 0 < d) : Summable (primalSide d) := by
  have h1 := (Complex.hasSum_ofReal.mpr
    (oddKernel_quarter_hasSum (show (0 : ℝ) < 32 * d by positivity))).summable
  have h2 := (cosKernel_half_hasSum (show (0 : ℝ) < 8 * d by positivity)).summable
  exact summable_norm_iff.mp ((summable_norm_iff.mpr h1).mul_norm (summable_norm_iff.mpr h2))

private lemma summable_dualEven {d : ℝ} (hd : 0 < d) : Summable (dualEven d) := by
  refine Summable.of_norm_bounded (summable_norm_iff.mpr (summable_dualSide hd)) fun p => ?_
  simp only [dualEven]
  split_ifs
  · exact le_rfl
  · simp

private lemma summable_dualOdd {d : ℝ} (hd : 0 < d) : Summable (dualOdd d) := by
  refine Summable.of_norm_bounded (summable_norm_iff.mpr (summable_dualSide hd)) fun p => ?_
  simp only [dualOdd]
  split_ifs
  · simp
  · exact le_rfl

/-! ## 10. Pointwise identities along the ladder -/

private lemma env_neg_snd (d : ℝ) (u v : ℤ) : env d u (-v) = env d u v := by
  unfold env; congr 1; push_cast; ring

private lemma env_neg_both (d : ℝ) (u v : ℤ) : env d (-u) (-v) = env d u v := by
  unfold env; congr 1; push_cast; ring

private lemma gLadder_swap (d : ℝ) (u v : ℤ) : gLadder d (v, u) = gLadder d (u, v) := by
  simp only [gLadder]
  rw [show v + u = u + v from by ring, show env d v u = env d u v from by
    unfold env; congr 1; ring]

private lemma gLadder_even_zero (d : ℝ) {u v : ℤ} (h : (u + v) % 2 = 0) :
    gLadder d (u, v) = 0 := by
  have hs : sgn4 (u + v) = 0 := by
    unfold sgn4; rw [if_neg (by omega), if_neg (by omega)]
  simp only [gLadder]
  rw [hs]
  ring

/-- The even part of the dual side dies under the involution `n ↦ −n`. -/
private lemma tsum_dualEven_eq_zero (d : ℝ) : ∑' p : ℤ × ℤ, dualEven d p = 0 := by
  have h1 : ∑' p : ℤ × ℤ, dualEven d (((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)) p)
      = ∑' p : ℤ × ℤ, dualEven d p :=
    ((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)).tsum_eq (dualEven d)
  have h2 : ∀ p : ℤ × ℤ, dualEven d (((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)) p)
      = -dualEven d p := by
    rintro ⟨n, m⟩
    show dualEven d (-n, m) = -dualEven d (n, m)
    by_cases hn : n % 2 = 0
    · simp only [dualEven]
      rw [if_pos (show (-n) % 2 = 0 by omega), if_pos hn]
      show sinTerm d (-n) * evenTerm d m = -(sinTerm d n * evenTerm d m)
      rw [sinTerm_neg_even hn]
      ring
    · simp only [dualEven]
      rw [if_neg (show ¬((-n) % 2 = 0) by omega), if_neg hn, neg_zero]
  have h3 : ∑' p : ℤ × ℤ, dualEven d p = -∑' p : ℤ × ℤ, dualEven d p := by
    conv_lhs => rw [← h1, tsum_congr h2]
    exact tsum_neg
  linear_combination h3 / 2

/-- The odd part transports through `(p, q) ↦ (2p+1, q)` and the fold onto `gLadder`. -/
private lemma dualOdd_comp_oddEmb (d : ℝ) (q : ℤ × ℤ) :
    dualOdd d (oddEmb q) = gLadder d (foldMap q) := by
  obtain ⟨p, m⟩ := q
  show dualOdd d (2 * p + 1, m) = gLadder d (p + m + 1, p - m)
  simp only [dualOdd]
  rw [if_neg (show ¬((2 * p + 1) % 2 = 0) by omega)]
  show sinTerm d (2 * p + 1) * evenTerm d m = _
  rw [sinTerm_odd]
  simp only [gLadder]
  rw [show (p + m + 1) + (p - m) = 2 * p + 1 from by ring]
  have hexp : ((rexp (-π * ((2 * p + 1 : ℤ) : ℝ) ^ 2 * d) : ℝ) : ℂ) * evenTerm d m
      = ((env d (p + m + 1) (p - m) : ℝ) : ℂ) := by
    show _ * ((rexp (-π * ((m : ℝ) + 1 / 2) ^ 2 * (4 * d)) : ℝ) : ℂ) = _
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    unfold env
    norm_cast
    congr 1
    push_cast
    ring
  linear_combination (((2 * p + 1 : ℤ) : ℂ) * sgn4 (2 * p + 1)) * hexp

private lemma tsum_dualOdd_eq_gLadder (d : ℝ) :
    ∑' p : ℤ × ℤ, dualOdd d p = ∑' p : ℤ × ℤ, gLadder d p := by
  have h1 : ∑' q : ℤ × ℤ, dualOdd d (oddEmb q) = ∑' p : ℤ × ℤ, dualOdd d p := by
    refine oddEmb_injective.tsum_eq ?_
    rw [Function.support_subset_iff]
    rintro ⟨n, m⟩ hne
    have hn : ¬(n % 2 = 0) := by
      intro h
      apply hne
      simp only [dualOdd]
      rw [if_pos h]
    exact ⟨((n - 1) / 2, m), by
      simp only [oddEmb, Prod.mk.injEq]
      exact ⟨by omega, trivial⟩⟩
  have h2 : ∑' q : ℤ × ℤ, gLadder d (foldMap q) = ∑' p : ℤ × ℤ, gLadder d p := by
    refine foldMap_injective.tsum_eq ?_
    rw [Function.support_subset_iff]
    rintro ⟨u, v⟩ hne
    have hodd : (u + v) % 4 = 1 ∨ (u + v) % 4 = 3 := by
      by_contra hc
      push_neg at hc
      apply hne
      simp only [gLadder]
      rw [show sgn4 (u + v) = 0 from by unfold sgn4; rw [if_neg hc.1, if_neg hc.2]]
      ring
    exact ⟨((u + v - 1) / 2, (u - v - 1) / 2), by
      simp only [foldMap, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  rw [← h1, ← h2]
  exact tsum_congr fun q => dualOdd_comp_oddEmb d q

/-- The swap fold: the odd-`v` half equals the even-`v` half. -/
private lemma gOddV_comp_swap (d : ℝ) (p : ℤ × ℤ) :
    gOddV d ((Equiv.prodComm ℤ ℤ) p) = gEven d p := by
  obtain ⟨u, v⟩ := p
  show gOddV d (v, u) = gEven d (u, v)
  simp only [gOddV, gEven]
  by_cases hu : u % 2 = 0
  · rw [if_pos hu]
    by_cases hv : v % 2 = 0
    · rw [if_pos hv, gLadder_even_zero d (show (u + v) % 2 = 0 by omega)]
    · rw [if_neg hv]
  · rw [if_neg hu]
    by_cases hv : v % 2 = 0
    · rw [if_pos hv, gLadder_swap]
    · rw [if_neg hv, gLadder_even_zero d (show (v + u) % 2 = 0 by omega)]

private lemma tsum_gLadder_eq_two_gEven {d : ℝ} (hd : 0 < d) :
    ∑' p : ℤ × ℤ, gLadder d p = 2 * ∑' p : ℤ × ℤ, gEven d p := by
  have hpt : ∀ p : ℤ × ℤ, gLadder d p = gEven d p + gOddV d p := by
    intro p
    simp only [gEven, gOddV]
    split_ifs <;> ring
  have hswap : ∑' p : ℤ × ℤ, gOddV d p = ∑' p : ℤ × ℤ, gEven d p := by
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (gOddV d)]
    exact tsum_congr fun p => gOddV_comp_swap d p
  rw [tsum_congr hpt, (summable_gEven hd).tsum_add (summable_gOddV hd), hswap]
  ring

/-- The `v ↦ −v` fold replaces the weight `u + v` by `u`. -/
private lemma gEven_add_negSnd (d : ℝ) (p : ℤ × ℤ) :
    gEven d p + gEven d (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) p) = 2 * hHalf d p := by
  obtain ⟨u, v⟩ := p
  show gEven d (u, v) + gEven d (u, -v) = 2 * hHalf d (u, v)
  simp only [gEven, hHalf]
  by_cases hv : v % 2 = 0
  · rw [if_pos hv, if_pos (show (-v) % 2 = 0 by omega), if_pos hv]
    simp only [gLadder]
    rw [show u + -v = u - v from by ring,
      show sgn4 (u - v) = sgn4 (u + v) from by
        unfold sgn4; rw [show (u - v) % 4 = (u + v) % 4 from by omega],
      env_neg_snd]
    push_cast
    ring
  · rw [if_neg hv, if_neg (show ¬((-v) % 2 = 0) by omega), if_neg hv]
    ring

private lemma tsum_gEven_eq_hHalf {d : ℝ} (hd : 0 < d) :
    ∑' p : ℤ × ℤ, gEven d p = ∑' p : ℤ × ℤ, hHalf d p := by
  have hcomp : Summable (gEven d ∘ ((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ))) :=
    (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)).summable_iff).mpr (summable_gEven hd)
  have h2 : (2 : ℂ) * ∑' p : ℤ × ℤ, gEven d p = 2 * ∑' p : ℤ × ℤ, hHalf d p := by
    calc (2 : ℂ) * ∑' p : ℤ × ℤ, gEven d p
        = ∑' p : ℤ × ℤ, gEven d p
            + ∑' p : ℤ × ℤ, gEven d (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) p) := by
          rw [((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (gEven d)]
          ring
      _ = ∑' p : ℤ × ℤ, (gEven d p
            + gEven d (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) p)) :=
          ((summable_gEven hd).tsum_add hcomp).symm
      _ = ∑' p : ℤ × ℤ, (2 : ℂ) * hHalf d p := tsum_congr fun p => gEven_add_negSnd d p
      _ = 2 * ∑' p : ℤ × ℤ, hHalf d p := tsum_mul_left
  exact mul_left_cancel₀ two_ne_zero h2

/-- The class fold: the signed weight splits into the two quartic classes, and the
negative class is the mirror of the positive one. -/
private lemma tsum_hHalf_eq_two_hPlus {d : ℝ} (hd : 0 < d) :
    ∑' p : ℤ × ℤ, hHalf d p = 2 * ∑' p : ℤ × ℤ, hPlus d p := by
  have hpt : ∀ p : ℤ × ℤ, hHalf d p = hPlus d p - hMinus d p := by
    rintro ⟨u, v⟩
    simp only [hHalf, hPlus, hMinus, sgn4]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hneg : ∑' p : ℤ × ℤ, hMinus d p = -∑' p : ℤ × ℤ, hPlus d p := by
    have h1 : ∑' p : ℤ × ℤ, hMinus d (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = ∑' p : ℤ × ℤ, hMinus d p :=
      ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (hMinus d)
    have h2 : ∀ p : ℤ × ℤ, hMinus d (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = -hPlus d p := by
      rintro ⟨u, v⟩
      show hMinus d (-u, -v) = -hPlus d (u, v)
      simp only [hMinus, hPlus]
      by_cases h : (u + v) % 4 = 1 ∧ v % 2 = 0
      · rw [if_pos (show (-u + -v) % 4 = 3 ∧ (-v) % 2 = 0 by omega), if_pos h, env_neg_both]
        push_cast
        ring
      · rw [if_neg (show ¬((-u + -v) % 4 = 3 ∧ (-v) % 2 = 0) by omega), if_neg h, neg_zero]
    rw [← h1, tsum_congr h2]
    exact tsum_neg
  rw [tsum_congr hpt, (summable_hPlus hd).tsum_sub (summable_hMinus hd), hneg]
  ring

/-- The target shape gathers both quartic classes with the cosine sign. -/
private lemma tsum_hFinal_eq_four_hPlus {d : ℝ} (hd : 0 < d) :
    ∑' p : ℤ × ℤ, hFinal d p = 4 * ∑' p : ℤ × ℤ, hPlus d p := by
  have hsplit : ∀ p : ℤ × ℤ, hPlus d p = aPiece d p + bPiece d p := by
    rintro ⟨u, v⟩
    simp only [hPlus, aPiece, bPiece]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hfin : ∀ p : ℤ × ℤ, hFinal d p = 4 * aPiece d p - 4 * bMirror d p := by
    rintro ⟨u, v⟩
    simp only [hFinal, aPiece, bMirror, cs4]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hbm : ∑' p : ℤ × ℤ, bPiece d p = -∑' p : ℤ × ℤ, bMirror d p := by
    have h1 : ∑' p : ℤ × ℤ, bPiece d (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = ∑' p : ℤ × ℤ, bPiece d p :=
      ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (bPiece d)
    have h2 : ∀ p : ℤ × ℤ, bPiece d (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = -bMirror d p := by
      rintro ⟨u, v⟩
      show bPiece d (-u, -v) = -bMirror d (u, v)
      simp only [bPiece, bMirror]
      by_cases h : u % 4 = 1 ∧ v % 4 = 2
      · rw [if_pos (show (-u) % 4 = 3 ∧ (-v) % 4 = 2 by omega), if_pos h, env_neg_both]
        push_cast
        ring
      · rw [if_neg (show ¬((-u) % 4 = 3 ∧ (-v) % 4 = 2) by omega), if_neg h, neg_zero]
    rw [← h1, tsum_congr h2]
    exact tsum_neg
  calc ∑' p : ℤ × ℤ, hFinal d p
      = ∑' p : ℤ × ℤ, ((4 : ℂ) * aPiece d p - 4 * bMirror d p) := tsum_congr hfin
    _ = (∑' p : ℤ × ℤ, (4 : ℂ) * aPiece d p) - ∑' p : ℤ × ℤ, (4 : ℂ) * bMirror d p :=
        ((summable_aPiece hd).mul_left 4).tsum_sub ((summable_bMirror hd).mul_left 4)
    _ = 4 * (∑' p : ℤ × ℤ, aPiece d p) - 4 * ∑' p : ℤ × ℤ, bMirror d p := by
        rw [tsum_mul_left, tsum_mul_left]
    _ = 4 * ((∑' p : ℤ × ℤ, aPiece d p) + ∑' p : ℤ × ℤ, bPiece d p) := by
        rw [hbm]; ring
    _ = 4 * ∑' p : ℤ × ℤ, (aPiece d p + bPiece d p) := by
        rw [(summable_aPiece hd).tsum_add (summable_bPiece hd)]
    _ = 4 * ∑' p : ℤ × ℤ, hPlus d p := by
        rw [tsum_congr hsplit]

/-- Landing on the primal grid `(4k+1, 2l)`. -/
private lemma hFinal_comp_gridEmb (d : ℝ) (q : ℤ × ℤ) :
    hFinal d (gridEmb q) = 16 * primalSide d q := by
  obtain ⟨k, l⟩ := q
  show hFinal d (4 * k + 1, 2 * l) = 16 * primalSide d (k, l)
  simp only [hFinal, primalSide]
  rw [if_pos (show (4 * k + 1) % 4 = 1 by omega), cs4_double]
  show _ = 16 * (oddTerm d k * cosTerm d l)
  simp only [oddTerm, cosTerm]
  have hE : env d (4 * k + 1) (2 * l)
      = rexp (-π * ((k : ℝ) + 1 / 4) ^ 2 * (32 * d)) * rexp (-π * (l : ℝ) ^ 2 * (8 * d)) := by
    unfold env
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hE]
  push_cast
  ring

private lemma tsum_hFinal_eq_primal (d : ℝ) :
    ∑' p : ℤ × ℤ, hFinal d p = 16 * ∑' p : ℤ × ℤ, primalSide d p := by
  have h1 : ∑' q : ℤ × ℤ, hFinal d (gridEmb q) = ∑' p : ℤ × ℤ, hFinal d p := by
    refine gridEmb_injective.tsum_eq ?_
    rw [Function.support_subset_iff]
    rintro ⟨u, v⟩ hne
    have hu : u % 4 = 1 := by
      by_contra hc
      apply hne
      simp only [hFinal]
      rw [if_neg hc]
    have hv : v % 4 = 0 ∨ v % 4 = 2 := by
      by_contra hc
      push_neg at hc
      apply hne
      simp only [hFinal, cs4]
      rw [if_pos hu, if_neg hc.1, if_neg hc.2]
      ring
    exact ⟨((u - 1) / 4, v / 2), by
      simp only [gridEmb, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  rw [← h1, tsum_congr (fun q => hFinal_comp_gridEmb d q), tsum_mul_left]

/-! ## 11. The two products and the duplication identity -/

private lemma dual_product {d : ℝ} (hd : 0 < d) :
    ((sinKernel ((1 / 4 : ℝ) : UnitAddCircle) d : ℝ) : ℂ) *
        ((evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * d) : ℝ) : ℂ)
      = ∑' p : ℤ × ℤ, dualSide d p :=
  (sinKernel_quarter_hasSum hd).mul_eq
    (Complex.hasSum_ofReal.mpr (evenKernel_half_hasSum (show (0 : ℝ) < 4 * d by positivity)))
    (summable_dualSide hd).hasSum

private lemma primal_product {d : ℝ} (hd : 0 < d) :
    ((oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (32 * d) : ℝ) : ℂ) *
        ((cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (8 * d) : ℝ) : ℂ)
      = ∑' p : ℤ × ℤ, primalSide d p :=
  (Complex.hasSum_ofReal.mpr (oddKernel_quarter_hasSum (show (0 : ℝ) < 32 * d by positivity))).mul_eq
    (cosKernel_half_hasSum (show (0 : ℝ) < 8 * d by positivity))
    (summable_primalSide hd).hasSum

private lemma tsum_dual_eq_sixteen_primal {d : ℝ} (hd : 0 < d) :
    ∑' p : ℤ × ℤ, dualSide d p = 16 * ∑' p : ℤ × ℤ, primalSide d p := by
  have hsplit : ∀ p : ℤ × ℤ, dualSide d p = dualEven d p + dualOdd d p := by
    intro p
    simp only [dualEven, dualOdd]
    split_ifs <;> ring
  rw [tsum_congr hsplit, (summable_dualEven hd).tsum_add (summable_dualOdd hd),
    tsum_dualEven_eq_zero d, zero_add, tsum_dualOdd_eq_gLadder d,
    tsum_gLadder_eq_two_gEven hd, tsum_gEven_eq_hHalf hd, tsum_hHalf_eq_two_hPlus hd,
    ← tsum_hFinal_eq_primal d, tsum_hFinal_eq_four_hPlus hd]
  ring

/-- **The duplication identity.**  The `sinKernel (1/4)`–`evenKernel (1/2)` product at
scales `(d, 4d)` equals sixteen times the `oddKernel (1/4)`–`cosKernel (1/2)` product at
scales `(32d, 8d)`: the level-doubling rearrangement of the Gaussian-lattice Hecke sum,
proved by pure series rearrangement — an involution kills the even part, the odd part
reindexes through `(p, q) ↦ (p+q+1, p−q)`, and three lattice folds collapse the result
onto the classes `a ≡ 1 (mod 4)`, `b ≡ 0 (mod 2)`. -/
theorem theDuplicationIdentity {d : ℝ} (hd : 0 < d) :
    sinKernel ((1 / 4 : ℝ) : UnitAddCircle) d * evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * d)
      = 16 * (oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (32 * d) *
          cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (8 * d)) := by
  have hC : ((sinKernel ((1 / 4 : ℝ) : UnitAddCircle) d : ℝ) : ℂ) *
        ((evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * d) : ℝ) : ℂ)
      = 16 * (((oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (32 * d) : ℝ) : ℂ) *
          ((cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (8 * d) : ℝ) : ℂ)) := by
    rw [dual_product hd, primal_product hd]
    exact tsum_dual_eq_sixteen_primal hd
  exact_mod_cast hC

/-! ## 12. The functional equation -/

private lemma rpow_sixteen {x : ℝ} (hx : 0 < x) :
    (x / (4 * Real.sqrt 2)) ^ ((3 : ℝ) / 2) * (x / Real.sqrt 2) ^ ((1 : ℝ) / 2)
      = x ^ 2 / 16 := by
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  rw [Real.div_rpow hx.le (by positivity), Real.div_rpow hx.le hs.le, div_mul_div_comm,
    ← Real.rpow_add hx]
  have hden : (4 * Real.sqrt 2) ^ ((3 : ℝ) / 2) * Real.sqrt 2 ^ ((1 : ℝ) / 2) = 16 := by
    rw [Real.mul_rpow (by norm_num) hs.le, mul_assoc, ← Real.rpow_add hs]
    have h1 : Real.sqrt 2 ^ ((3 : ℝ) / 2 + 1 / 2) = 2 := by
      rw [show ((3 : ℝ) / 2 + 1 / 2) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast,
        Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have h2 : (4 : ℝ) ^ ((3 : ℝ) / 2) = 8 := by
      rw [show (4 : ℝ) = 2 ^ ((2 : ℕ) : ℝ) from by rw [Real.rpow_natCast]; norm_num,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
        show ((2 : ℕ) : ℝ) * (3 / 2) = ((3 : ℕ) : ℝ) from by push_cast; ring,
        Real.rpow_natCast]
      norm_num
    rw [h1, h2]
    norm_num
  rw [hden, show ((3 : ℝ) / 2 + 1 / 2) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]

/-- **The theta functional equation of the congruent-number curve at one.**
`heckeTheta (1/x) = x² · heckeTheta x` for `x > 0`: weight two, sign `+1`, level 32 —
the two mathlib Hurwitz-kernel functional equations composed through the duplication
identity.  This is the modular transformation law from which the entire continuation of
`L(E₁, s)` follows by Mellin transform. -/
theorem theHeckeThetaFunctionalEquation {x : ℝ} (hx : 0 < x) :
    heckeTheta (1 / x) = x ^ 2 * heckeTheta x := by
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  have hd : (0 : ℝ) < x / (4 * Real.sqrt 2) := by positivity
  unfold heckeTheta heckeThetaA heckeThetaC
  rw [show 4 * Real.sqrt 2 * (1 / x) = 1 / (x / (4 * Real.sqrt 2)) from by
      rw [one_div_div]; ring,
    show Real.sqrt 2 * (1 / x) = 1 / (x / Real.sqrt 2) from by
      rw [one_div_div]; ring]
  rw [oddKernel_functional_equation ((1 / 4 : ℝ) : UnitAddCircle) (1 / (x / (4 * Real.sqrt 2))),
    one_div_one_div,
    show (1 / (x / (4 * Real.sqrt 2))) = (x / (4 * Real.sqrt 2))⁻¹ from one_div _,
    Real.inv_rpow hd.le, one_div, inv_inv]
  have hcos : cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (1 / (x / Real.sqrt 2))
      = (x / Real.sqrt 2) ^ ((1 : ℝ) / 2) *
          evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (x / Real.sqrt 2) := by
    rw [evenKernel_functional_equation ((1 / 2 : ℝ) : UnitAddCircle) (x / Real.sqrt 2),
      ← mul_assoc, mul_one_div,
      div_self (ne_of_gt (Real.rpow_pos_of_pos (by positivity) _)), one_mul]
  rw [hcos]
  rw [show evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (x / Real.sqrt 2)
      = evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * (x / (4 * Real.sqrt 2))) from by
    congr 1
    field_simp]
  have hdup := theDuplicationIdentity hd
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : (4 : ℝ) * Real.sqrt 2 ≠ 0 := by positivity
  have h32 : 32 * (x / (4 * Real.sqrt 2)) = 4 * Real.sqrt 2 * x := by
    rw [show 32 * (x / (4 * Real.sqrt 2)) = 32 * x / (4 * Real.sqrt 2) from by ring,
      div_eq_iff hne]
    linear_combination (-16 * x) * hss
  have h8 : 8 * (x / (4 * Real.sqrt 2)) = Real.sqrt 2 * x := by
    rw [show 8 * (x / (4 * Real.sqrt 2)) = 8 * x / (4 * Real.sqrt 2) from by ring,
      div_eq_iff hne]
    linear_combination (-4 * x) * hss
  rw [h32, h8] at hdup
  linear_combination (4 * (x / (4 * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
      (x / Real.sqrt 2) ^ ((1 : ℝ) / 2)) * hdup
    + (64 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (4 * Real.sqrt 2 * x) *
      cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (Real.sqrt 2 * x)) * rpow_sixteen hx

/-! ## 13. The strong FE-pair: the completed L-function is entire and reflects at one

`heckeTheta` is continuous on `(0, ∞)`, decays exponentially at `∞`, and satisfies the
weight-two transformation law with sign `+1` and no constant term; so `(θ, θ)` is a
`StrongFEPair` and mathlib's abstract Mellin machinery returns the completed L-function
entire with `Λ(2−s) = Λ(s)` — no region of convergence, no analytic continuation step,
the reflection carries everything. -/

lemma continuousOn_heckeTheta : ContinuousOn heckeTheta (Set.Ioi 0) := by
  have h1 : ContinuousOn
      (fun x : ℝ => oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (4 * Real.sqrt 2 * x))
      (Set.Ioi 0) := by
    refine (continuousOn_oddKernel _).comp (Continuous.continuousOn (by fun_prop)) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity
  have h2 : ContinuousOn
      (fun x : ℝ => cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (Real.sqrt 2 * x))
      (Set.Ioi 0) := by
    refine (continuousOn_cosKernel _).comp (Continuous.continuousOn (by fun_prop)) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity
  unfold heckeTheta heckeThetaA heckeThetaC
  exact (continuousOn_const.mul h1).mul h2

lemma isBigO_atTop_heckeTheta :
    ∃ p, 0 < p ∧ (heckeTheta =O[Filter.atTop] fun x => rexp (-p * x)) := by
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_oddKernel ((1 / 4 : ℝ) : UnitAddCircle)
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_cosKernel_sub ((1 / 2 : ℝ) : UnitAddCircle)
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  have ht1 : Filter.Tendsto (fun x : ℝ => 4 * Real.sqrt 2 * x) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by positivity)
  have ht2 : Filter.Tendsto (fun x : ℝ => Real.sqrt 2 * x) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop hs
  have h1 : (fun x : ℝ => oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (4 * Real.sqrt 2 * x))
      =O[Filter.atTop] fun x => rexp (-(4 * Real.sqrt 2 * p) * x) := by
    refine (hp'.comp_tendsto ht1).congr' Filter.EventuallyEq.rfl ?_
    exact Filter.Eventually.of_forall fun x => by
      show rexp (-p * (4 * Real.sqrt 2 * x)) = rexp (-(4 * Real.sqrt 2 * p) * x)
      congr 1
      ring
  have hcosB : (fun x : ℝ => cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (Real.sqrt 2 * x))
      =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
    have hsub : (fun x : ℝ => cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (Real.sqrt 2 * x) - 1)
        =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      refine (hq'.comp_tendsto ht2).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      show |((fun x => rexp (-q * x)) ∘ fun x => Real.sqrt 2 * x) x| ≤ 1 * ‖(1 : ℝ)‖
      simp only [Function.comp_apply]
      rw [abs_of_nonneg (Real.exp_nonneg _), norm_one, mul_one]
      exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg (mul_nonneg hq.le hs.le) hx])
    have hone : (fun _ : ℝ => (1 : ℝ)) =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) :=
      Asymptotics.isBigO_refl _ _
    have := hsub.add hone
    refine this.congr_left fun x => ?_
    ring
  refine ⟨4 * Real.sqrt 2 * p, by positivity, ?_⟩
  have hprod := (h1.const_mul_left 4).mul hcosB
  have hL : ∀ x : ℝ, 4 * oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (4 * Real.sqrt 2 * x) *
      cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (Real.sqrt 2 * x) = heckeTheta x := fun x => rfl
  have hR : ∀ x : ℝ, rexp (-(4 * Real.sqrt 2 * p) * x) * 1 = rexp (-(4 * Real.sqrt 2 * p) * x) :=
    fun x => mul_one _
  exact (hprod.congr_left hL).congr_right hR

/-- The strong FE-pair of the congruent-number curve at one: `f = g = heckeTheta`,
weight `2`, sign `+1`, no constant terms. -/
def heckeFEPair : StrongFEPair ℂ where
  f := Complex.ofReal ∘ heckeTheta
  g := Complex.ofReal ∘ heckeTheta
  k := 2
  hk := two_pos
  ε := 1
  hε := one_ne_zero
  f₀ := 0
  g₀ := 0
  hf₀ := rfl
  hg₀ := rfl
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    continuousOn_heckeTheta).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    continuousOn_heckeTheta).locallyIntegrableOn measurableSet_Ioi
  h_feq x hx := by
    have hfe := theHeckeThetaFunctionalEquation (Set.mem_Ioi.mp hx)
    simp only [Function.comp_apply, one_mul, smul_eq_mul, hfe]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    push_cast
    ring
  hf_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_heckeTheta
    simpa using isBigO_ofReal_left.mpr <|
      hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO
  hg_top r := by
    obtain ⟨p, hp, hp'⟩ := isBigO_atTop_heckeTheta
    simpa using isBigO_ofReal_left.mpr <|
      hp'.trans (isLittleO_exp_neg_mul_rpow_atTop hp r).isBigO

/-- **The completed L-function of the congruent-number curve at one**, defined as the
Mellin transform of its theta function — the integral the classical
`Λ(s) = (√32/2π)^s Γ(s) L(E₁,s)` equals, constructed with no convergence region. -/
def heckeLambda : ℂ → ℂ := heckeFEPair.Λ

/-- **The completed L-function is entire.**  No pole, no continuation step: the strong
FE-pair machinery returns differentiability on all of `ℂ` at once. -/
theorem theCompletedLFunctionIsEntire : Differentiable ℂ heckeLambda :=
  heckeFEPair.differentiable_Λ

/-- The Mellin representation: `heckeLambda s` is the convergent Mellin transform of the
theta function at every `s`. -/
theorem theCompletedLFunctionHasMellin (s : ℂ) :
    HasMellin (Complex.ofReal ∘ heckeTheta) s (heckeLambda s) :=
  heckeFEPair.hasMellin s

/-- **The functional equation of the completed L-function**: `Λ(2 − s) = Λ(s)`.
Weight two, sign `+1` — the analytic reflection of the congruent-number curve at one,
kernel-checked with no analytic continuation argument. -/
theorem theCompletedLFunctionalEquation (s : ℂ) : heckeLambda (2 - s) = heckeLambda s := by
  have h := heckeFEPair.functional_equation s
  rw [show heckeFEPair.k = (2 : ℝ) from rfl, show heckeFEPair.ε = (1 : ℂ) from rfl] at h
  simpa [heckeLambda, StrongFEPair.Λ_eq, StrongFEPair.symm_Λ_eq, one_smul] using h

/-! ## 14. Positivity: every kernel factor is positive

`evenKernel` is a sum of positive exponentials; its functional equation transfers the
positivity to `cosKernel`; a dominance estimate gives `oddKernel (1/4) > 0` on `[4, ∞)`;
and the duplication identity transfers the sign across the reflection so the dominance
range covers all of `(0, ∞)`. -/

lemma evenKernel_half_pos {t : ℝ} (ht : 0 < t) :
    0 < evenKernel ((1 / 2 : ℝ) : UnitAddCircle) t := by
  have h := evenKernel_half_hasSum ht
  rw [← h.tsum_eq]
  exact h.summable.tsum_pos (fun n => Real.exp_nonneg _) 0 (Real.exp_pos _)

lemma cosKernel_half_pos {t : ℝ} (ht : 0 < t) :
    0 < cosKernel ((1 / 2 : ℝ) : UnitAddCircle) t := by
  have hfe := evenKernel_functional_equation ((1 / 2 : ℝ) : UnitAddCircle) (1 / t)
  rw [one_div_one_div] at hfe
  have he := evenKernel_half_pos (show (0 : ℝ) < 1 / t by positivity)
  rw [hfe] at he
  have hc : (0 : ℝ) < 1 / (1 / t) ^ (1 / 2 : ℝ) := by positivity
  rcases mul_pos_iff.mp he with ⟨_, h⟩ | ⟨hneg, _⟩
  · exact h
  · linarith

private lemma oddKernel_quarter_pos_of_four_le {X : ℝ} (hX : 4 ≤ X) :
    0 < oddKernel ((1 / 4 : ℝ) : UnitAddCircle) X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have h := oddKernel_quarter_hasSum hX0
  set a : ℤ → ℝ := fun n => ((n : ℝ) + 1 / 4) * rexp (-π * ((n : ℝ) + 1 / 4) ^ 2 * X)
    with ha_def
  set r : ℝ := rexp (-π * X / 2) with hr_def
  have hr0 : 0 ≤ r := Real.exp_nonneg _
  have hr64 : r ≤ 1 / 64 := by
    have h1 : rexp (-π * X / 2) ≤ rexp (-6) := by
      apply Real.exp_le_exp.mpr
      have hpi := Real.pi_gt_three
      nlinarith
    refine (hr_def ▸ h1).trans ?_
    have he2 : (2 : ℝ) ≤ rexp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have h2 : (64 : ℝ) ≤ rexp 6 := by
      calc (64 : ℝ) = 2 ^ (6 : ℕ) := by norm_num
        _ ≤ rexp 1 ^ (6 : ℕ) := pow_le_pow_left₀ (by norm_num) he2 6
        _ = rexp 6 := by rw [← Real.exp_nat_mul]; norm_num
    have hprod : rexp (-6) * rexp 6 = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos (-6), h2, hprod,
      mul_nonneg (sub_nonneg.mpr h2) (Real.exp_pos (-6)).le]
  have hrlt : r < 1 := lt_of_le_of_lt hr64 (by norm_num)
  have ha0 : a 0 = 1 / 4 * rexp (-π * X / 16) := by
    simp only [ha_def]
    push_cast
    rw [show -π * ((0 : ℝ) + 1 / 4) ^ 2 * X = -π * X / 16 from by ring]
    norm_num
  have ha0pos : 0 < a 0 := by rw [ha0]; positivity
  have hb := h.nat_add_neg
  have hbsum := hb.summable
  have hterm : ∀ k : ℕ, |a ((k + 1 : ℕ) : ℤ) + a (-((k + 1 : ℕ) : ℤ))|
      ≤ 8 * a 0 * ((((k + 1 : ℕ)) : ℝ) * r ^ (k + 1)) := by
    intro k
    have hj : (1 : ℝ) ≤ (k : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) k
      linarith
    have hA : a ((k + 1 : ℕ) : ℤ)
        = (((k : ℝ) + 1) + 1 / 4) * rexp (-π * (((k : ℝ) + 1) + 1 / 4) ^ 2 * X) := by
      simp only [ha_def]
      push_cast
      ring_nf
    have hB : a (-((k + 1 : ℕ) : ℤ))
        = (-((k : ℝ) + 1) + 1 / 4) * rexp (-π * (((k : ℝ) + 1) - 1 / 4) ^ 2 * X) := by
      simp only [ha_def]
      push_cast
      rw [show -π * (-((k : ℝ) + 1) + 1 / 4) ^ 2 * X
          = -π * (((k : ℝ) + 1) - 1 / 4) ^ 2 * X from by ring]
    rw [hA, hB]
    set j : ℝ := (k : ℝ) + 1
    have hE1 := Real.exp_nonneg (-π * (j + 1 / 4) ^ 2 * X)
    have hE2 := Real.exp_nonneg (-π * (j - 1 / 4) ^ 2 * X)
    have hexp1 : rexp (-π * (j + 1 / 4) ^ 2 * X) ≤ rexp (-π * (j - 1 / 4) ^ 2 * X) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg Real.pi_pos.le hX0.le, hj]
    have hexp2 : rexp (-π * (j - 1 / 4) ^ 2 * X) ≤ rexp (-π * X / 16) * r ^ (k + 1) := by
      have hr_exp : rexp (-π * X / 16) * r ^ (k + 1)
          = rexp (-π * X / 16 + ((k + 1 : ℕ) : ℝ) * (-π * X / 2)) := by
        rw [Real.exp_add, Real.exp_nat_mul, hr_def]
      rw [hr_exp]
      apply Real.exp_le_exp.mpr
      rw [show ((k + 1 : ℕ) : ℝ) = j from by push_cast; ring]
      have hjj : (0 : ℝ) ≤ j * (j - 1) := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg (mul_nonneg Real.pi_pos.le hX0.le) hjj]
    have hup : (j + 1 / 4) * rexp (-π * (j + 1 / 4) ^ 2 * X)
        ≤ (j + 1 / 4) * rexp (-π * (j - 1 / 4) ^ 2 * X) :=
      mul_le_mul_of_nonneg_left hexp1 (by linarith)
    have habs : |(j + 1 / 4) * rexp (-π * (j + 1 / 4) ^ 2 * X)
        + (-j + 1 / 4) * rexp (-π * (j - 1 / 4) ^ 2 * X)|
        ≤ 2 * j * rexp (-π * (j - 1 / 4) ^ 2 * X) := by
      rw [abs_le]
      constructor
      · nlinarith [hup, hE1, hE2, hj, mul_nonneg (show (0:ℝ) ≤ j + 1/4 by linarith) hE1]
      · nlinarith [hup, hE1, hE2, hj, mul_nonneg (show (0:ℝ) ≤ j + 1/4 by linarith) hE1,
          mul_nonneg (show (0:ℝ) ≤ 2*j - 1/2 by linarith) hE2]
    refine habs.trans ?_
    rw [ha0, show ((k + 1 : ℕ) : ℝ) = j from by push_cast; ring]
    calc 2 * j * rexp (-π * (j - 1 / 4) ^ 2 * X)
        ≤ 2 * j * (rexp (-π * X / 16) * r ^ (k + 1)) := by
          apply mul_le_mul_of_nonneg_left hexp2
          nlinarith [hj]
      _ = 8 * (1 / 4 * rexp (-π * X / 16)) * (j * r ^ (k + 1)) := by ring
  have hgeo : HasSum (fun n : ℕ => (n : ℝ) * r ^ n) (r / (1 - r) ^ 2) := by
    apply hasSum_coe_mul_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hrlt
  have hshift : HasSum (fun k : ℕ => (((k + 1 : ℕ)) : ℝ) * r ^ (k + 1)) (r / (1 - r) ^ 2) := by
    refine (hasSum_nat_add_iff (f := fun n : ℕ => (n : ℝ) * r ^ n) 1).mpr ?_
    convert hgeo using 1
    rw [Finset.sum_range_one]
    norm_num
  have hmaj : Summable (fun k : ℕ => 8 * a 0 * ((((k + 1 : ℕ)) : ℝ) * r ^ (k + 1))) :=
    hshift.summable.mul_left _
  have hb1 : HasSum (fun n : ℕ => a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ)))
      (oddKernel ((1 / 4 : ℝ) : UnitAddCircle) X - a 0) := by
    refine (hasSum_nat_add_iff (f := fun n : ℕ => a (n : ℤ) + a (-(n : ℤ))) 1).mpr ?_
    convert hb using 1
    rw [Finset.sum_range_one]
    simp only [Nat.cast_zero, neg_zero]
    ring
  have hTabs : Summable fun n : ℕ => |a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ))| :=
    Summable.of_nonneg_of_le (fun n => abs_nonneg _) hterm hmaj
  have htail : |∑' n : ℕ, (a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ)))|
      ≤ 8 * a 0 * (r / (1 - r) ^ 2) := by
    have h0 := norm_tsum_le_tsum_norm
      (f := fun n : ℕ => a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ)))
      (by simpa [Real.norm_eq_abs] using hTabs)
    have h1 : ∑' n : ℕ, |a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ))|
        ≤ ∑' n : ℕ, 8 * a 0 * ((((n + 1 : ℕ)) : ℝ) * r ^ (n + 1)) :=
      hTabs.tsum_le_tsum hterm hmaj
    have h2 : ∑' n : ℕ, 8 * a 0 * ((((n + 1 : ℕ)) : ℝ) * r ^ (n + 1))
        = 8 * a 0 * (r / (1 - r) ^ 2) := by
      rw [tsum_mul_left, hshift.tsum_eq]
    calc |∑' n : ℕ, (a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ)))|
        ≤ ∑' n : ℕ, |a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ))| := by
          simpa [Real.norm_eq_abs] using h0
      _ ≤ _ := h1
      _ = _ := h2
  have hfrac : r / (1 - r) ^ 2 ≤ 1 / 16 := by
    have hpos : (0 : ℝ) < (1 - r) ^ 2 := by nlinarith
    rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg r]
  have hhalf : |∑' n : ℕ, (a ((n + 1 : ℕ) : ℤ) + a (-((n + 1 : ℕ) : ℤ)))| ≤ a 0 / 2 := by
    refine htail.trans ?_
    calc 8 * a 0 * (r / (1 - r) ^ 2) ≤ 8 * a 0 * (1 / 16) :=
          mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = a 0 / 2 := by ring
  rw [hb1.tsum_eq] at hhalf
  have hb2 := abs_le.mp hhalf
  linarith [hb2.1]

lemma oddKernel_quarter_pos {X : ℝ} (hX : 0 < X) :
    0 < oddKernel ((1 / 4 : ℝ) : UnitAddCircle) X := by
  rcases le_or_gt 4 X with h4 | h4
  · exact oddKernel_quarter_pos_of_four_le h4
  · have hd : (0 : ℝ) < 1 / X := by positivity
    have hdup := theDuplicationIdentity hd
    have hoddbig : 0 < oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (32 * (1 / X)) := by
      apply oddKernel_quarter_pos_of_four_le
      rw [mul_one_div, le_div_iff₀ hX]
      nlinarith
    have hcosbig := cosKernel_half_pos (show (0 : ℝ) < 8 * (1 / X) by positivity)
    have hevenbig := evenKernel_half_pos (show (0 : ℝ) < 4 * (1 / X) by positivity)
    have hprod : 0 < sinKernel ((1 / 4 : ℝ) : UnitAddCircle) (1 / X) *
        evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * (1 / X)) := by
      rw [hdup]
      have := mul_pos hoddbig hcosbig
      linarith
    have hsin : 0 < sinKernel ((1 / 4 : ℝ) : UnitAddCircle) (1 / X) := by
      rcases mul_pos_iff.mp hprod with ⟨h, _⟩ | ⟨_, hneg⟩
      · exact h
      · linarith
    rw [oddKernel_functional_equation]
    exact mul_pos (by positivity) hsin

lemma sinKernel_quarter_pos {d : ℝ} (hd : 0 < d) :
    0 < sinKernel ((1 / 4 : ℝ) : UnitAddCircle) d := by
  have hdup := theDuplicationIdentity hd
  have hodd := oddKernel_quarter_pos (show (0 : ℝ) < 32 * d by positivity)
  have hcos := cosKernel_half_pos (show (0 : ℝ) < 8 * d by positivity)
  have heven := evenKernel_half_pos (show (0 : ℝ) < 4 * d by positivity)
  have hprod : 0 < sinKernel ((1 / 4 : ℝ) : UnitAddCircle) d *
      evenKernel ((1 / 2 : ℝ) : UnitAddCircle) (4 * d) := by
    rw [hdup]
    have := mul_pos hodd hcos
    linarith
  rcases mul_pos_iff.mp hprod with ⟨h, _⟩ | ⟨_, hneg⟩
  · exact h
  · linarith

/-- **The theta function is positive on the whole half-line.** -/
theorem theHeckeThetaIsPositive {x : ℝ} (hx : 0 < x) : 0 < heckeTheta x := by
  have h1 := oddKernel_quarter_pos (show (0 : ℝ) < 4 * Real.sqrt 2 * x by positivity)
  have h2 := cosKernel_half_pos (show (0 : ℝ) < Real.sqrt 2 * x by positivity)
  unfold heckeTheta heckeThetaA heckeThetaC
  exact mul_pos (mul_pos (by norm_num) h1) h2

/-! ## 15. The central value is a positive real

`Λ(1)` is the Mellin transform at the center of the functional equation `s ↦ 2 − s`,
i.e. the plain integral of the theta function over `(0, ∞)` — and the integrand is
positive.  Classically `Λ(1) = (√32/2π)·Γ(1)·L(E₁, 1)`, so this is the analytic
non-vanishing at the center for the rank-zero curve. -/

theorem theCentralValueIsThePositiveThetaIntegral :
    ∃ r : ℝ, 0 < r ∧ heckeLambda 1 = (r : ℂ) := by
  obtain ⟨hconv, heval⟩ := theCompletedLFunctionHasMellin 1
  have hEq : Set.EqOn (fun t : ℝ => ((t : ℂ) ^ ((1 : ℂ) - 1)) • (Complex.ofReal ∘ heckeTheta) t)
      (fun t : ℝ => ((heckeTheta t : ℝ) : ℂ)) (Set.Ioi 0) := by
    intro t ht
    simp [Complex.cpow_zero]
  have hL : heckeLambda 1 = ((∫ t in Set.Ioi (0 : ℝ), heckeTheta t : ℝ) : ℂ) := by
    calc heckeLambda 1 = mellin (Complex.ofReal ∘ heckeTheta) 1 := heval.symm
      _ = ∫ t in Set.Ioi (0 : ℝ), ((heckeTheta t : ℝ) : ℂ) :=
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hEq
      _ = ((∫ t in Set.Ioi (0 : ℝ), heckeTheta t : ℝ) : ℂ) := integral_ofReal
  have hint : MeasureTheory.IntegrableOn heckeTheta (Set.Ioi (0 : ℝ)) := by
    have h2 : MeasureTheory.IntegrableOn (fun t : ℝ => ((heckeTheta t : ℝ) : ℂ))
        (Set.Ioi (0 : ℝ)) := hconv.congr_fun hEq measurableSet_Ioi
    have h3 := h2.re
    exact h3.congr (Filter.Eventually.of_forall fun t => by simp)
  have hpos : 0 < ∫ t in Set.Ioi (0 : ℝ), heckeTheta t := by
    rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae ?hae hint]
    · have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support heckeTheta ∩ Set.Ioi 0 := fun t ht =>
        ⟨(theHeckeThetaIsPositive ht).ne', ht⟩
      calc (0 : ENNReal) < MeasureTheory.volume (Set.Ioi (0 : ℝ)) := by
            simp [Real.volume_Ioi]
        _ ≤ MeasureTheory.volume (Function.support heckeTheta ∩ Set.Ioi 0) :=
            MeasureTheory.measure_mono hsub
    case hae =>
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      exact (theHeckeThetaIsPositive ht).le
  exact ⟨_, hpos, hL⟩

/-- **The central value of the completed L-function does not vanish.**  With the
classical reading `Λ(1) = (√32/2π)·L(E₁,1)`, this is the analytic side of rank zero at
one: `L(E₁, 1) ≠ 0`, matched on the algebraic side by the completed descent
(`RankZero`: exactly four points, one is not a congruent number). -/
theorem theCentralValueDoesNotVanish : heckeLambda 1 ≠ 0 := by
  obtain ⟨r, hr, hEq⟩ := theCentralValueIsThePositiveThetaIntegral
  rw [hEq]
  exact_mod_cast hr.ne'

/-! ## 16. The theta is the Gaussian class sum

The positive quartic class `(a + b) ≡ 1 (mod 4)`, `b` even — equivalently `a` odd, `b`
even, `a + b ≡ 1 (mod 4)` — with weight `a` and Gaussian envelope of norm `a² + b²` is
exactly the `hPlus` family of the duplication ladder, so the identity
`heckeTheta = Σ_class a·exp(−2π(a²+b²)x/√32)` is the chain already proved, read at its
quarter point. -/

/-- **The arithmetic identity of the theta function.**  `heckeTheta x` is the Gaussian
lattice sum `Σ a·exp(−2π(a²+b²)·x/√32)` over the class `a + b ≡ 1 (mod 4)`, `b` even —
the Hecke sum of the character `ψ(α) = ε(α)·α` on `ℤ[i]` in its folded real form.  The
scale `x/(4√2) = x/√32` carries the level `32`. -/
theorem theHeckeThetaIsTheGaussianClassSum {x : ℝ} (hx : 0 < x) :
    HasSum (fun p : ℤ × ℤ =>
      if (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0 then
        ((p.1 : ℤ) : ℂ) * ((rexp (-2 * π * (x / (4 * Real.sqrt 2)) *
          ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) : ℝ) : ℂ)
      else 0)
      ((heckeTheta x : ℝ) : ℂ) := by
  have hd : (0 : ℝ) < x / (4 * Real.sqrt 2) := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : (4 : ℝ) * Real.sqrt 2 ≠ 0 := by positivity
  have h32 : 32 * (x / (4 * Real.sqrt 2)) = 4 * Real.sqrt 2 * x := by
    rw [show 32 * (x / (4 * Real.sqrt 2)) = 32 * x / (4 * Real.sqrt 2) from by ring,
      div_eq_iff hne]
    linear_combination (-16 * x) * hss
  have h8 : 8 * (x / (4 * Real.sqrt 2)) = Real.sqrt 2 * x := by
    rw [show 8 * (x / (4 * Real.sqrt 2)) = 8 * x / (4 * Real.sqrt 2) from by ring,
      div_eq_iff hne]
    linear_combination (-4 * x) * hss
  have e1 := tsum_hFinal_eq_four_hPlus hd
  have e2 := tsum_hFinal_eq_primal (x / (4 * Real.sqrt 2))
  have e3 := primal_product hd
  rw [h32, h8] at e3
  have hθ : ((heckeTheta x : ℝ) : ℂ)
      = 4 * (((oddKernel ((1 / 4 : ℝ) : UnitAddCircle) (4 * Real.sqrt 2 * x) : ℝ) : ℂ) *
          ((cosKernel ((1 / 2 : ℝ) : UnitAddCircle) (Real.sqrt 2 * x) : ℝ) : ℂ)) := by
    unfold heckeTheta heckeThetaA heckeThetaC
    push_cast
    ring
  have hval : ∑' p : ℤ × ℤ, hPlus (x / (4 * Real.sqrt 2)) p = ((heckeTheta x : ℝ) : ℂ) := by
    rw [hθ, e3]
    linear_combination (e2 - e1) / 4
  have hfun : (fun p : ℤ × ℤ =>
      if (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0 then
        ((p.1 : ℤ) : ℂ) * ((rexp (-2 * π * (x / (4 * Real.sqrt 2)) *
          ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) : ℝ) : ℂ)
      else 0) = hPlus (x / (4 * Real.sqrt 2)) := funext fun p => rfl
  rw [hfun, ← hval]
  exact (summable_hPlus hd).hasSum

end Soma.Holonics.Millennium.HeckeTheta
