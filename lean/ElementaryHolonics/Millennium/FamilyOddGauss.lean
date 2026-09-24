import ElementaryHolonics.Millennium.FamilyGauss
import Mathlib.Tactic

/-!
# FamilyOddGauss: the sum-of-squares eigenidentity at every odd prime

**The universal collapse engine.**  The split-residue eigenidentity
(`FamilyGauss`) needed `p ≡ 1 (mod 4)` to rotate the sum of squares onto the
difference chart.  This file removes that wall by an elementary route — character
inversion, completion of the square, and unit inversion:

* **`theSquareCompletedSum`** — `∑_r ψ(t·r² + ξ·r) = ψ(−ξ²/(4t))·χ(t)·g(χ,ψ)`;
* **`theSumOfSquaresEigenIdentityAtEveryOddPrime`** —
  `∑_{r,s} χ(r² + s²)·ψ(ξr + ηs) = p·χ(ξ² + η²)` at **every** odd prime, split or
  inert — the finite engine of the theta functional equation on **both** residue
  branches of the congruent-number family.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.FamilyOddGauss

open AddChar MulChar
open Soma.Holonics.Millennium.FamilyGauss

variable {p : ℕ} [Fact p.Prime]

/-- The complex-valued quadratic character. -/
def X (p : ℕ) [Fact p.Prime] : MulChar (ZMod p) ℂ :=
  (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)

lemma X_apply (a : ZMod p) : X p a = ((quadraticChar (ZMod p) a : ℤ) : ℂ) := rfl

private lemma X_ne_one (hp2 : p ≠ 2) : (X p) ≠ 1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  rw [X, MulChar.ringHomComp_ne_one_iff (RingHom.injective_int _)]
  exact quadraticChar_ne_one hchar

private lemma X_quadratic : (X p).IsQuadratic :=
  (quadraticChar_isQuadratic (ZMod p)).comp _

private lemma two_nz (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  exact Ring.two_ne_zero hchar

private lemma X_inv (t : ZMod p) : X p t⁻¹ = X p t := by
  by_cases ht : t = 0
  · rw [ht, inv_zero]
  · have h1 : X p t⁻¹ * X p t = 1 := by
      rw [← map_mul, inv_mul_cancel₀ ht, map_one]
    have h2 : X p t * X p t = 1 := quad_sq_one (χ := X p) X_quadratic ht
    calc X p t⁻¹ = X p t⁻¹ * (X p t * X p t) := by rw [h2, mul_one]
      _ = (X p t⁻¹ * X p t) * X p t := by ring
      _ = X p t := by rw [h1, one_mul]

/-- The pure Gaussian sum: `∑_r ψ(t·r²) = χ(t)·g(χ,ψ)`, for `t ≠ 0`. -/
private lemma square_sum (hp2 : p ≠ 2) (ψ : AddChar (ZMod p) ℂ)
    (hψ : ψ.IsPrimitive) {t : ZMod p} (ht : t ≠ 0) :
    ∑ r : ZMod p, ψ (t * r ^ 2) = X p t * gaussSum (X p) ψ := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hfiber : ∑ r : ZMod p, ψ (t * r ^ 2)
      = ∑ u : ZMod p, ((Finset.univ.filter (fun r : ZMod p => r ^ 2 = u)).card : ℂ)
          * ψ (t * u) := by
    rw [← Finset.sum_fiberwise Finset.univ (fun r : ZMod p => r ^ 2)
      (fun r => ψ (t * r ^ 2))]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hval : ∀ r ∈ Finset.univ.filter (fun r : ZMod p => r ^ 2 = u),
        ψ (t * r ^ 2) = ψ (t * u) := by
      intro r hr
      rw [(Finset.mem_filter.mp hr).2]
    rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hcount : ∀ u : ZMod p,
      ((Finset.univ.filter (fun r : ZMod p => r ^ 2 = u)).card : ℂ)
        = X p u + 1 := by
    intro u
    have h := quadraticChar_card_sqrts hchar u
    have hset : {x : ZMod p | x ^ 2 = u}.toFinset
        = Finset.univ.filter (fun r : ZMod p => r ^ 2 = u) := by
      ext r
      simp [Set.mem_toFinset]
    rw [hset] at h
    have hcast := congrArg (fun z : ℤ => ((z : ℤ) : ℂ)) h
    push_cast at hcast
    rw [hcast, X_apply]
  rw [hfiber, Finset.sum_congr rfl fun u _ => by rw [hcount u]]
  have hsplit : ∑ u : ZMod p, ((X p) u + 1) * ψ (t * u)
      = (∑ u : ZMod p, (X p) u * ψ (t * u)) + ∑ u : ZMod p, ψ (t * u) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  rw [hsplit, twisted_sum (χ := X p) (X_ne_one hp2) X_quadratic ψ t]
  have hzero : ∑ u : ZMod p, ψ (t * u) = 0 := by
    have h1 : ∑ u : ZMod p, ψ (t * u) = ∑ u : ZMod p, (mulShift ψ t) u :=
      Finset.sum_congr rfl fun u _ => by rw [mulShift_apply]
    rw [h1]
    refine (AddChar.sum_eq_zero_iff_ne_zero).mpr ?_
    rw [show (0 : AddChar (ZMod p) ℂ) = 1 from rfl]
    exact hψ ht
  rw [hzero, add_zero]

/-- **THE SQUARE-COMPLETED SUM**: `∑_r ψ(t·r² + ξ·r) = ψ(−ξ²/(4t))·χ(t)·g(χ,ψ)`
for `t ≠ 0`, at every odd prime. -/
theorem theSquareCompletedSum (hp2 : p ≠ 2) (ψ : AddChar (ZMod p) ℂ)
    (hψ : ψ.IsPrimitive) {t : ZMod p} (ht : t ≠ 0) (ξ : ZMod p) :
    ∑ r : ZMod p, ψ (t * r ^ 2 + ξ * r)
      = ψ (-ξ ^ 2 / (4 * t)) * (X p t * gaussSum (X p) ψ) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_nz hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h4
    have h22 : (2 : ZMod p) * 2 = 0 := by
      rw [show (2 : ZMod p) * 2 = 4 from by norm_num, h4]
    rcases mul_eq_zero.mp h22 with h | h <;> exact h2 h
  set c : ZMod p := ξ / (2 * t) with hc
  have h2t : (2 : ZMod p) * t ≠ 0 := mul_ne_zero h2 ht
  have h4t : (4 : ZMod p) * t ≠ 0 := mul_ne_zero h4 ht
  have hbij : ∑ r : ZMod p, ψ (t * r ^ 2 + ξ * r)
      = ∑ r : ZMod p, ψ (t * (r - c) ^ 2 + ξ * (r - c)) :=
    (Fintype.sum_equiv (Equiv.subRight c)
      (fun r => ψ (t * (r - c) ^ 2 + ξ * (r - c)))
      (fun r => ψ (t * r ^ 2 + ξ * r)) fun r => rfl).symm
  rw [hbij]
  have harg : ∀ r : ZMod p, t * (r - c) ^ 2 + ξ * (r - c)
      = (-ξ ^ 2 / (4 * t)) + t * r ^ 2 := by
    intro r
    rw [hc]
    field_simp
    ring
  have hterm : ∀ r : ZMod p, ψ (t * (r - c) ^ 2 + ξ * (r - c))
      = ψ (-ξ ^ 2 / (4 * t)) * ψ (t * r ^ 2) := by
    intro r
    rw [harg r, ψ.map_add_eq_mul]
  rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.mul_sum,
    square_sum hp2 ψ hψ ht]

set_option maxHeartbeats 4000000 in
/-- **THE SUM-OF-SQUARES EIGENIDENTITY AT EVERY ODD PRIME**:

`∑_{r,s} χ(r² + s²)·ψ(ξr + ηs) = p·χ(ξ² + η²)`

for every odd prime `p`, split or inert — character inversion writes the class
through the additive spectrum, the square completes, and the unit inversion folds
the remaining twisted sum back onto the character.  No square root of `−1` is
consumed, so both residue branches of the family carry the same collapse engine. -/
theorem theSumOfSquaresEigenIdentityAtEveryOddPrime (hp2 : p ≠ 2)
    (ψ : AddChar (ZMod p) ℂ) (hψ : ψ.IsPrimitive) (ξ η : ZMod p) :
    ∑ r : ZMod p, ∑ s : ZMod p,
        ((quadraticChar (ZMod p) (r ^ 2 + s ^ 2) : ℤ) : ℂ) * ψ (ξ * r + η * s)
      = (p : ℂ) * ((quadraticChar (ZMod p) (ξ ^ 2 + η ^ 2) : ℤ) : ℂ) := by
  have h2 : (2 : ZMod p) ≠ 0 := two_nz hp2
  have h4 : (4 : ZMod p) ≠ 0 := by
    intro h4
    have h22 : (2 : ZMod p) * 2 = 0 := by
      rw [show (2 : ZMod p) * 2 = 4 from by norm_num, h4]
    rcases mul_eq_zero.mp h22 with h | h <;> exact h2 h
  set g : ℂ := gaussSum (X p) ψ with hg
  have hm1nz : ((-1 : ZMod p)) ≠ 0 := by
    intro hc
    have h1 : (1 : ZMod p) = 0 := by linear_combination -hc
    exact one_ne_zero h1
  have hg2 : g ^ 2 = (X p) (-1) * (Fintype.card (ZMod p)) :=
    gaussSum_sq (χ := X p) (X_ne_one hp2) X_quadratic hψ
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0] at hg2
    have hcard : ((Fintype.card (ZMod p) : ℂ)) ≠ 0 := by
      rw [ZMod.card p]
      exact_mod_cast (Fact.out (p := p.Prime)).pos.ne'
    have hm1 : (X p) (-1) ≠ 0 := by
      intro hX0
      have h2' := quad_sq_one (χ := X p) X_quadratic hm1nz
      rw [hX0, zero_mul] at h2'
      exact zero_ne_one h2'
    have hne := mul_ne_zero hm1 hcard
    rw [← hg2] at hne
    norm_num at hne
  set S : ℂ := ∑ r : ZMod p, ∑ s : ZMod p,
      ((quadraticChar (ZMod p) (r ^ 2 + s ^ 2) : ℤ) : ℂ) * ψ (ξ * r + η * s)
    with hS
  have hXc : ∀ a : ZMod p, ((quadraticChar (ZMod p) a : ℤ) : ℂ) = X p a :=
    fun a => rfl
  have hkey : ∀ m : ZMod p, (X p) m * g = ∑ t : ZMod p, (X p) t * ψ (t * m) := by
    intro m
    rw [hg, ← twisted_sum (χ := X p) (X_ne_one hp2) X_quadratic ψ m]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [mul_comm t m]
  -- expand `S·g` into the `t`-spectrum
  have hmain : S * g = ∑ t : ZMod p,
      (X p) t * ((∑ r : ZMod p, ψ (t * r ^ 2 + ξ * r)) *
        (∑ s : ZMod p, ψ (t * s ^ 2 + η * s))) := by
    rw [hS, Finset.sum_mul]
    have hrow : ∀ r : ZMod p, (∑ s : ZMod p,
        ((quadraticChar (ZMod p) (r ^ 2 + s ^ 2) : ℤ) : ℂ) * ψ (ξ * r + η * s)) * g
        = ∑ s : ZMod p, ∑ t : ZMod p,
            (X p) t * (ψ (t * r ^ 2 + ξ * r) * ψ (t * s ^ 2 + η * s)) := by
      intro r
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [hXc, show (X p) (r ^ 2 + s ^ 2) * ψ (ξ * r + η * s) * g
          = ((X p) (r ^ 2 + s ^ 2) * g) * ψ (ξ * r + η * s) from by ring,
        hkey (r ^ 2 + s ^ 2), Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      have he1 : ψ (t * (r ^ 2 + s ^ 2)) = ψ (t * r ^ 2) * ψ (t * s ^ 2) := by
        rw [show t * (r ^ 2 + s ^ 2) = t * r ^ 2 + t * s ^ 2 from by ring,
          ψ.map_add_eq_mul]
      have he2 : ψ (ξ * r + η * s) = ψ (ξ * r) * ψ (η * s) := ψ.map_add_eq_mul _ _
      have he3 : ψ (t * r ^ 2 + ξ * r) = ψ (t * r ^ 2) * ψ (ξ * r) :=
        ψ.map_add_eq_mul _ _
      have he4 : ψ (t * s ^ 2 + η * s) = ψ (t * s ^ 2) * ψ (η * s) :=
        ψ.map_add_eq_mul _ _
      rw [he1, he2, he3, he4]
      ring
    rw [Finset.sum_congr rfl fun r _ => hrow r]
    have hswap1 : ∀ r : ZMod p, ∑ s : ZMod p, ∑ t : ZMod p,
        (X p) t * (ψ (t * r ^ 2 + ξ * r) * ψ (t * s ^ 2 + η * s))
        = ∑ t : ZMod p, ∑ s : ZMod p,
            (X p) t * (ψ (t * r ^ 2 + ξ * r) * ψ (t * s ^ 2 + η * s)) :=
      fun r => Finset.sum_comm
    rw [Finset.sum_congr rfl fun r _ => hswap1 r, Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Fintype.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
  -- evaluate the `t`-spectrum through the completed squares
  have hεterm : ∀ t : ZMod p,
      (X p) t * ((∑ r : ZMod p, ψ (t * r ^ 2 + ξ * r)) *
        (∑ s : ZMod p, ψ (t * s ^ 2 + η * s)))
      = g ^ 2 * ((X p) t * ψ (-(ξ ^ 2 + η ^ 2) / (4 * t))) := by
    intro t
    by_cases ht : t = 0
    · rw [ht]
      rw [MulChar.map_zero]
      ring
    · rw [theSquareCompletedSum hp2 ψ hψ ht ξ, theSquareCompletedSum hp2 ψ hψ ht η]
      have hXcube : (X p) t * ((X p) t * (X p) t) = (X p) t := by
        rw [quad_sq_one (χ := X p) X_quadratic ht, mul_one]
      have hadd : ψ (-ξ ^ 2 / (4 * t)) * ψ (-η ^ 2 / (4 * t))
          = ψ (-(ξ ^ 2 + η ^ 2) / (4 * t)) := by
        rw [← ψ.map_add_eq_mul]
        congr 1
        field_simp
        ring
      calc (X p) t * ((ψ (-ξ ^ 2 / (4 * t)) * ((X p) t * g)) *
            (ψ (-η ^ 2 / (4 * t)) * ((X p) t * g)))
          = g ^ 2 * (((X p) t * ((X p) t * (X p) t)) *
              (ψ (-ξ ^ 2 / (4 * t)) * ψ (-η ^ 2 / (4 * t)))) := by ring
        _ = g ^ 2 * ((X p) t * ψ (-(ξ ^ 2 + η ^ 2) / (4 * t))) := by
            rw [hXcube, hadd]
  rw [Finset.sum_congr rfl fun t _ => hεterm t, ← Finset.mul_sum] at hmain
  -- fold the remaining twisted sum by unit inversion
  set cc : ZMod p := -(ξ ^ 2 + η ^ 2) / 4 with hcc
  have hinv : ∑ t : ZMod p, (X p) t * ψ (-(ξ ^ 2 + η ^ 2) / (4 * t))
      = ∑ t : ZMod p, (X p) t * ψ (t * cc) := by
    refine (Fintype.sum_equiv (Function.Involutive.toPerm _ inv_involutive)
      (fun t : ZMod p => (X p) t * ψ (t * cc))
      (fun t : ZMod p => (X p) t * ψ (-(ξ ^ 2 + η ^ 2) / (4 * t)))
      (fun t => ?_)).symm
    show (X p) t * ψ (t * cc) = (X p) t⁻¹ * ψ (-(ξ ^ 2 + η ^ 2) / (4 * t⁻¹))
    rw [X_inv]
    congr 1
    rw [hcc, div_eq_mul_inv, div_eq_mul_inv, mul_inv, inv_inv]
    ring
  rw [hinv, ← hkey cc] at hmain
  have hXcc : (X p) cc
      = (X p) (-1) * ((quadraticChar (ZMod p) (ξ ^ 2 + η ^ 2) : ℤ) : ℂ) := by
    have h2inv : ((2 : ZMod p))⁻¹ ≠ 0 := inv_ne_zero h2
    have hfact : cc = ((2 : ZMod p))⁻¹ * ((2 : ZMod p))⁻¹ * (-1) * (ξ ^ 2 + η ^ 2) := by
      rw [hcc]
      field_simp
      ring
    rw [hfact, map_mul, map_mul, map_mul, quad_sq_one (χ := X p) X_quadratic h2inv, one_mul,
      hXc]
  rw [hXcc] at hmain
  -- cancel the Gauss sum and read the eigenvalue
  have hfinal : S * g = ((p : ℂ) *
      ((quadraticChar (ZMod p) (ξ ^ 2 + η ^ 2) : ℤ) : ℂ)) * g := by
    rw [hmain, hg2, ZMod.card p]
    have hXm1sq : (X p) (-1) * (X p) (-1) = 1 := quad_sq_one (χ := X p) X_quadratic hm1nz
    linear_combination ((p : ℂ) *
      ((quadraticChar (ZMod p) (ξ ^ 2 + η ^ 2) : ℤ) : ℂ) * g) * hXm1sq
  exact mul_right_cancel₀ hg0 hfinal

end Soma.Holonics.Millennium.FamilyOddGauss

