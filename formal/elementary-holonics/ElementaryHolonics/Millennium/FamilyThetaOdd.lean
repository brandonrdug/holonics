import ElementaryHolonics.Millennium.FamilyTheta
import ElementaryHolonics.Millennium.FamilyOddGauss
import Mathlib.Tactic

/-!
# FamilyThetaOdd: the phase collapse at every odd prime

**The collapse engine crosses to the inert branch.**  The split-prime collapse
(`FamilyTheta`) carried the quarter-turn `i^n`; at a general odd prime the
quarter-turn is `i^{pn}`, and the sum-of-squares eigenidentity (`FamilyOddGauss`)
replaces the rotation through `√−1`:

* **`theFamilyPhaseCollapseAtEveryOddPrime`** — the `2p²` dual-side phases of the
  `p × 2p` grid collapse to `2p·i^{pn}·[m odd]·χ_p(n² + m²)` at **every** odd prime
  `p`, split or inert.  On the split branch `i^{pn} = i^n` recovers the standing
  collapse; on the inert branch the conjugate quarter-turn is the mechanism that
  flips the functional-equation sign to `−χ_p(2)` — the classical root number.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyThetaOdd

open Real Complex AddChar MulChar
open Soma.Holonics.Millennium.FamilyTheta

variable {p : ℕ} [Fact p.Prime]

/-! ## 1. The two phase decompositions at a general odd prime -/

/-- The level-`4p` phase splits into the `p`-fold quarter-turn and the mod-`p`
phase: `e^{2πi(4e+1)n/(4p)} = i^{pn}·ζ_p^{T(4e+1)n}` with `p² + 4T = 1`. -/
private lemma phaseA_odd {k : ℕ} (hpk : p = 2 * k + 1) (n e : ℤ) :
    cexp (2 * π * I * ((4 * e + 1) * n) / (4 * p))
      = cexp (π * I * (p * n) / 2) *
        zetaP p ^ ((-((k : ℤ) * (k + 1))) * ((4 * e + 1) * n)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (2 * (k : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := 2 * k + 1) |>.mpr (by omega)
    push_cast at h
    exact h
  set T : ℤ := -((k : ℤ) * (k + 1)) with hT
  have hpT : ((p : ℤ)) ^ 2 + 4 * T = 1 := by
    rw [hT, hpk]
    push_cast
    ring
  have hpc : (p : ℂ) = 2 * (k : ℂ) + 1 := by exact_mod_cast hpk
  rw [show 2 * (π : ℂ) * I * ((4 * e + 1) * n) / (4 * p)
      = ((e * n * p : ℤ) : ℂ) * (2 * π * I)
        + (π * I * (p * n) / 2
            + 2 * π * I * ((T * ((4 * e + 1) * n) : ℤ) : ℂ) / p) from by
    have hTc : ((T : ℤ) : ℂ) = (1 - (p : ℂ) ^ 2) / 4 := by
      have := congrArg (fun z : ℤ => ((z : ℤ) : ℂ)) hpT
      push_cast at this
      field_simp
      linear_combination this
    push_cast
    rw [hTc]
    field_simp
    ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add,
    zetaP_zpow_exp]

/-- The level-`2p` phase splits into the half-turn and the mod-`p` phase:
`e^{2πi·dm/(2p)} = (−1)^{dm}·ζ_p^{−k·dm}` with `p = 2k + 1`. -/
private lemma phaseB_odd {k : ℕ} (hpk : p = 2 * k + 1) (m d : ℤ) :
    cexp (2 * π * I * (d * m) / (2 * p))
      = (-1 : ℂ) ^ (d * m) * zetaP p ^ ((-(k : ℤ)) * (d * m)) := by
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hk0 : (2 * (k : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := 2 * k + 1) |>.mpr (by omega)
    push_cast at h
    exact h
  have hpc : (p : ℂ) = 2 * (k : ℂ) + 1 := by exact_mod_cast hpk
  rw [show 2 * (π : ℂ) * I * (d * m) / (2 * p)
      = π * I * ((d * m : ℤ) : ℂ)
        + 2 * π * I * (((-(k : ℤ)) * (d * m) : ℤ) : ℂ) / p from by
    push_cast
    rw [hpc]
    field_simp
    ring]
  rw [Complex.exp_add, zetaP_zpow_exp, neg_one_zpow_exp]

/-! ## 2. The collapse at every odd prime -/

set_option maxHeartbeats 4000000 in
/-- **THE FAMILY PHASE COLLAPSE AT EVERY ODD PRIME.**  At every odd prime `p`,
split or inert,

`∑_{e<p, d<2p} χ_p((4e+1)² + 4d²)·(−1)^d·e^{2πi(4e+1)n/(4p)}·e^{2πi·dm/(2p)}
  = 2p·i^{pn}·[m odd]·χ_p(n² + m²)`

— the finite engine of the theta functional equation on both residue branches.
On the split branch the quarter-turn `i^{pn}` reduces to `i^n`, recovering the
standing collapse; on the inert branch it is the conjugate turn. -/
theorem theFamilyPhaseCollapseAtEveryOddPrime (hp2 : p ≠ 2) (n m : ℤ) :
    ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p), phaseTerm p n m e d
      = 2 * p * cexp (π * I * (p * n) / 2) * oddInd m
          * ((quadraticChar (ZMod p) ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) := by
  have hp : p.Prime := Fact.out
  have hpge : 2 ≤ p := hp.two_le
  have hpodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  obtain ⟨k, hpk⟩ : ∃ k : ℕ, p = 2 * k + 1 := ⟨p / 2, by omega⟩
  have hζ0 : zetaP p ≠ 0 := Complex.exp_ne_zero _
  have hprim : IsPrimitiveRoot (zetaP p) p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have hζp : zetaP p ^ p = 1 := hprim.pow_eq_one
  set ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζp with hψdef
  have hψprim : ψ.IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root p hprim
  have hψz : ∀ K : ℤ, ψ ((K : ZMod p)) = zetaP p ^ K := fun K =>
    psi_intCast p hp.ne_zero hζp K
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hneg : (-1 : ℂ) ≠ 0 := by norm_num
  have hpoddZ : Odd p := ⟨k, by omega⟩
  set T : ℤ := -((k : ℤ) * (k + 1)) with hTdef
  set U : ℤ := -(k : ℤ) with hUdef
  -- pair `d` against `d + p`: the `2p`-fold `d`-sum folds to the `p`-fold one
  have hpair : ∀ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p), phaseTerm p n m e d
      = (1 - (-1 : ℂ) ^ m) * ∑ d ∈ Finset.range p, phaseTerm p n m e d := by
    intro e _
    have hsplit : ∑ d ∈ Finset.range (2 * p), phaseTerm p n m e d
        = ∑ d ∈ Finset.range p, phaseTerm p n m e d
          + ∑ d ∈ Finset.range p, phaseTerm p n m e (p + d) := by
      rw [show 2 * p = p + p from by ring, Finset.sum_range_add]
    have hshift : ∀ d : ℕ, phaseTerm p n m e (p + d)
        = -((-1 : ℂ) ^ m) * phaseTerm p n m e d := by
      intro d
      unfold FamilyTheta.phaseTerm
      have hc : ((p + d : ℕ) : ℤ) = (d : ℤ) + p := by push_cast; ring
      rw [hc]
      have hchi : (((4 * (e : ℤ) + 1) ^ 2 + 4 * ((d : ℤ) + p) ^ 2 : ℤ) : ZMod p)
          = (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) := by
        rw [ZMod.intCast_eq_intCast_iff']
        exact Int.modEq_iff_dvd.mpr ⟨-(8 * (d : ℤ) + 4 * (p : ℤ)), by ring⟩
      have hsign : (-1 : ℂ) ^ ((p + d : ℕ)) = -(-1 : ℂ) ^ (d : ℕ) := by
        rw [pow_add, hpoddZ.neg_one_pow]
        ring
      have hph : cexp (2 * π * I * (((d : ℤ) + p) * m) / (2 * p))
          = (-1 : ℂ) ^ m * cexp (2 * π * I * ((d : ℤ) * m) / (2 * p)) := by
        rw [show 2 * (π : ℂ) * I * (((d : ℤ) + p) * m) / (2 * p)
            = π * I * ((m : ℤ) : ℂ) + 2 * π * I * ((d : ℤ) * m) / (2 * p) from by
          field_simp
          ring]
        rw [Complex.exp_add, neg_one_zpow_exp]
      rw [hchi, hsign]
      push_cast at hph ⊢
      rw [hph]
      ring
    rw [hsplit, Finset.sum_congr rfl fun d _ => hshift d, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hpair, ← Finset.mul_sum]
  rcases Int.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
  · have h1 : (-1 : ℂ) ^ m = 1 := by
      rw [hj, show j + j = 2 * j from by ring, zpow_mul]
      norm_num
    have h0 : oddInd m = 0 := by
      unfold FamilyTheta.oddInd
      rw [if_pos (by omega)]
    rw [h1, h0]
    ring
  · have hm1 : (-1 : ℂ) ^ m = -1 := by
      rw [hj, zpow_add₀ hneg, zpow_mul]
      norm_num
    have h1 : oddInd m = 1 := by
      unfold FamilyTheta.oddInd
      rw [if_neg (by omega)]
    have htriv : ∀ d : ℕ, (-1 : ℂ) ^ (d : ℕ) * (-1 : ℂ) ^ ((d : ℤ) * m) = 1 := by
      intro d
      rw [← zpow_natCast (-1 : ℂ) d, ← zpow_add₀ hneg,
        show (d : ℤ) + (d : ℤ) * m = (d : ℤ) * (1 + m) from by ring, hj,
        show (d : ℤ) * (1 + (2 * j + 1)) = 2 * ((d : ℤ) * (j + 1)) from by ring,
        zpow_mul]
      norm_num
    -- collapse each term through the two phase decompositions
    have hterm : ∀ e ∈ Finset.range p, ∀ d ∈ Finset.range p, phaseTerm p n m e d
        = cexp (π * I * (p * n) / 2) *
            (((quadraticChar (ZMod p)
                (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
              (zetaP p ^ (T * ((4 * (e : ℤ) + 1) * n)) *
                zetaP p ^ (U * ((d : ℤ) * m)))) := by
      intro e _ d _
      unfold FamilyTheta.phaseTerm
      rw [phaseA_odd hpk, phaseB_odd hpk]
      rw [← hTdef, ← hUdef]
      calc ((quadraticChar (ZMod p)
              (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
            (-1 : ℂ) ^ (d : ℕ) *
            (cexp (π * I * (p * n) / 2) *
              zetaP p ^ (T * ((4 * (e : ℤ) + 1) * n))) *
            ((-1 : ℂ) ^ ((d : ℤ) * m) * zetaP p ^ (U * ((d : ℤ) * m)))
          = ((-1 : ℂ) ^ (d : ℕ) * (-1 : ℂ) ^ ((d : ℤ) * m)) *
            (((quadraticChar (ZMod p)
                (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
              (cexp (π * I * (p * n) / 2) *
                (zetaP p ^ (T * ((4 * (e : ℤ) + 1) * n)) *
                  zetaP p ^ (U * ((d : ℤ) * m))))) := by ring
        _ = _ := by rw [htriv d]; ring
    have hsum2 : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range p, phaseTerm p n m e d
        = cexp (π * I * (p * n) / 2) *
            ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range p,
              ((quadraticChar (ZMod p)
                  (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
                (zetaP p ^ (T * ((4 * (e : ℤ) + 1) * n)) *
                  zetaP p ^ (U * ((d : ℤ) * m))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d hd => hterm e he d hd
    -- express through the residue chart
    set ξ : ZMod p := ((T * n : ℤ) : ZMod p) with hξdef
    set η : ZMod p := ((U * m : ℤ) : ZMod p) * (2 : ZMod p)⁻¹ with hηdef
    have h2 : (2 : ZMod p) ≠ 0 := by
      have hchar : ringChar (ZMod p) ≠ 2 := by
        rw [ZMod.ringChar_zmod_n]
        exact hp2
      exact Ring.two_ne_zero hchar
    have hres : ∀ e ∈ Finset.range p, ∀ d ∈ Finset.range p,
        ((quadraticChar (ZMod p)
            (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
          (zetaP p ^ (T * ((4 * (e : ℤ) + 1) * n)) *
            zetaP p ^ (U * ((d : ℤ) * m)))
        = ((quadraticChar (ZMod p)
            ((4 * ((e : ℕ) : ZMod p) + 1) ^ 2 + (2 * ((d : ℕ) : ZMod p)) ^ 2) : ℤ) : ℂ) *
          (ψ (ξ * (4 * ((e : ℕ) : ZMod p) + 1)) * ψ (η * (2 * ((d : ℕ) : ZMod p)))) := by
      intro e _ d _
      have hχarg : (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p)
          = (4 * ((e : ℕ) : ZMod p) + 1) ^ 2 + (2 * ((d : ℕ) : ZMod p)) ^ 2 := by
        push_cast
        ring
      have hz1 : zetaP p ^ (T * ((4 * (e : ℤ) + 1) * n))
          = ψ (ξ * (4 * ((e : ℕ) : ZMod p) + 1)) := by
        rw [show ξ * (4 * ((e : ℕ) : ZMod p) + 1)
            = ((T * ((4 * (e : ℤ) + 1) * n) : ℤ) : ZMod p) from by
          rw [hξdef]
          push_cast
          ring]
        rw [hψz]
      have hz2 : zetaP p ^ (U * ((d : ℤ) * m))
          = ψ (η * (2 * ((d : ℕ) : ZMod p))) := by
        rw [show η * (2 * ((d : ℕ) : ZMod p))
            = ((U * ((d : ℤ) * m) : ℤ) : ZMod p) from by
          rw [hηdef]
          push_cast
          rw [show ((U : ℤ) : ZMod p) * ((m : ℤ) : ZMod p) * (2 : ZMod p)⁻¹ *
              (2 * ((d : ℕ) : ZMod p))
              = ((U : ℤ) : ZMod p) * ((m : ℤ) : ZMod p) * ((d : ℕ) : ZMod p) *
                ((2 : ZMod p)⁻¹ * 2) from by ring, inv_mul_cancel₀ h2, mul_one]
          ring]
        rw [hψz]
      rw [hχarg, hz1, hz2]
    have hZ : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range p,
          ((quadraticChar (ZMod p)
              (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
            (zetaP p ^ (T * ((4 * (e : ℤ) + 1) * n)) *
              zetaP p ^ (U * ((d : ℤ) * m)))
        = ∑ a : ZMod p, ∑ b : ZMod p,
            ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + (2 * b) ^ 2) : ℤ) : ℂ) *
              (ψ (ξ * (4 * a + 1)) * ψ (η * (2 * b))) := by
      rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd =>
        hres e he d hd]
      rw [Finset.sum_congr rfl fun e _ => sum_range_zmod p
        (fun b => ((quadraticChar (ZMod p)
            ((4 * ((e : ℕ) : ZMod p) + 1) ^ 2 + (2 * b) ^ 2) : ℤ) : ℂ) *
          (ψ (ξ * (4 * ((e : ℕ) : ZMod p) + 1)) * ψ (η * (2 * b))))]
      exact sum_range_zmod p
        (fun a => ∑ b : ZMod p,
          ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + (2 * b) ^ 2) : ℤ) : ℂ) *
            (ψ (ξ * (4 * a + 1)) * ψ (η * (2 * b))))
    -- the affine chart lands on the sum-of-squares eigenidentity
    have h4 : (4 : ZMod p) ≠ 0 := by
      intro h4
      have h22 : (2 : ZMod p) * 2 = 0 := by
        rw [show (2 : ZMod p) * 2 = 4 from by norm_num, h4]
      rcases mul_eq_zero.mp h22 with h | h <;> exact h2 h
    have hbij4 : Function.Bijective (fun a : ZMod p => 4 * a + 1) := by
      have hb1 : Function.Bijective (fun a : ZMod p => 4 * a) :=
        mulLeft_bijective₀ 4 h4
      have hb2 : Function.Bijective (fun a : ZMod p => a + 1) :=
        (Equiv.addRight (1 : ZMod p)).bijective
      exact hb2.comp hb1
    have hbij2 : Function.Bijective (fun b : ZMod p => 2 * b) :=
      mulLeft_bijective₀ 2 h2
    have haff : ∑ a : ZMod p, ∑ b : ZMod p,
          ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + (2 * b) ^ 2) : ℤ) : ℂ) *
            (ψ (ξ * (4 * a + 1)) * ψ (η * (2 * b)))
        = ∑ r : ZMod p, ∑ s : ZMod p,
            ((quadraticChar (ZMod p) (r ^ 2 + s ^ 2) : ℤ) : ℂ) * ψ (ξ * r + η * s) := by
      have hstep1 : ∀ a : ZMod p,
          ∑ b : ZMod p,
            ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + (2 * b) ^ 2) : ℤ) : ℂ) *
              (ψ (ξ * (4 * a + 1)) * ψ (η * (2 * b)))
          = ∑ s : ZMod p,
              ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + s ^ 2) : ℤ) : ℂ) *
                ψ (ξ * (4 * a + 1) + η * s) := by
        intro a
        refine Fintype.sum_bijective (fun b : ZMod p => 2 * b) hbij2 _ _ fun b => ?_
        rw [ψ.map_add_eq_mul]
      rw [Finset.sum_congr rfl fun a _ => hstep1 a]
      refine Fintype.sum_bijective (fun a : ZMod p => 4 * a + 1) hbij4 _ _ fun a => rfl
    have heigen := FamilyOddGauss.theSumOfSquaresEigenIdentityAtEveryOddPrime
      (p := p) hp2 ψ hψprim ξ η
    -- identify the returned class through the sixteen-fold clearing
    have hp16 : ((16 : ZMod p)) ≠ 0 := by
      intro h16
      have h44 : (4 : ZMod p) * 4 = 0 := by
        rw [show (4 : ZMod p) * 4 = 16 from by norm_num, h16]
      rcases mul_eq_zero.mp h44 with h | h <;> exact h4 h
    have hξ4 : ξ * 4 = ((n : ℤ) : ZMod p) := by
      rw [hξdef]
      have hpT : ((p : ℤ)) ^ 2 + 4 * T = 1 := by
        rw [hTdef]
        push_cast [hpk]
        ring
      have hcast := congrArg (fun z : ℤ => ((z : ℤ) : ZMod p)) hpT
      push_cast at hcast
      rw [ZMod.natCast_self] at hcast
      push_cast
      linear_combination (((n : ℤ) : ZMod p)) * hcast
    have hη4 : η * 4 = ((m : ℤ) : ZMod p) := by
      rw [hηdef]
      have hpU : ((p : ℤ)) + 2 * U = 1 := by
        rw [hUdef]
        push_cast [hpk]
        ring
      have hcast := congrArg (fun z : ℤ => ((z : ℤ) : ZMod p)) hpU
      push_cast at hcast
      rw [ZMod.natCast_self] at hcast
      push_cast
      have h24 : ((2 : ZMod p))⁻¹ * 4 = 2 := by
        rw [show (4 : ZMod p) = 2 * 2 from by norm_num,
          show ((2 : ZMod p))⁻¹ * (2 * 2) = ((2 : ZMod p))⁻¹ * 2 * 2 from by ring,
          inv_mul_cancel₀ h2, one_mul]
      rw [show ((U : ℤ) : ZMod p) * ((m : ℤ) : ZMod p) * (2 : ZMod p)⁻¹ * 4
          = ((U : ℤ) : ZMod p) * ((m : ℤ) : ZMod p) * (((2 : ZMod p))⁻¹ * 4) from by
        ring, h24]
      linear_combination (((m : ℤ) : ZMod p)) * hcast
    have hclass : ((quadraticChar (ZMod p) (ξ ^ 2 + η ^ 2) : ℤ) : ℂ)
        = ((quadraticChar (ZMod p) ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) := by
      have hval : (ξ ^ 2 + η ^ 2) * 16 = ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) := by
        rw [show (ξ ^ 2 + η ^ 2) * 16 = (ξ * 4) ^ 2 + (η * 4) ^ 2 from by ring,
          hξ4, hη4]
        push_cast
        ring
      have h4inv : (((4 : ZMod p))⁻¹) ≠ 0 := inv_ne_zero h4
      have hsq : ξ ^ 2 + η ^ 2
          = (((4 : ZMod p))⁻¹) ^ 2 * ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) := by
        refine mul_right_cancel₀ hp16 ?_
        rw [hval, show ((((4 : ZMod p))⁻¹) ^ 2 *
            ((n ^ 2 + m ^ 2 : ℤ) : ZMod p)) * 16
            = ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) * ((((4 : ZMod p))⁻¹ * 4) ^ 2) from by
          ring, inv_mul_cancel₀ h4, one_pow, mul_one]
      have hZlevel : quadraticChar (ZMod p) (ξ ^ 2 + η ^ 2)
          = quadraticChar (ZMod p) ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) := by
        rw [hsq, map_mul, quadraticChar_sq_one' h4inv, one_mul]
      rw [hZlevel]
    rw [hm1, hsum2, hZ, haff, heigen, hclass, h1]
    ring

end Soma.Holonics.Millennium.FamilyThetaOdd

