import ElementaryHolonics.Millennium.FamilyGauss
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# FamilyTheta: the phase collapse at every split prime

**The finite engine of the family theta functional equation.**  At five, the theta
transformation law was carried by a finite computation: the fifty dual-side phases of
the `5 × 10` grid collapse through the quadratic Gauss eigen-identity to
`10·i^n·[m odd]·χ₅(n² + m²)`.  That computation was never about five.  This file
proves it at **every** prime `p ≡ 1 (mod 4)`:

* **`theFamilyPhaseCollapseAtEverySplitPrime`** — the `2p²` dual-side phases of the
  `p × 2p` grid collapse to `2p·i^n·[m odd]·χ_p(n² + m²)`.  The mechanism is the
  standing family eigen-identity (`FamilyGauss`), entered through the additive
  character `ψ(x) = ζ_p^x`; the split residue `w² = −1` (which exists exactly
  because `p ≡ 1 (mod 4)`) rotates the sum of squares onto the split chart's
  difference of squares.

The modulus is a chart parameter, not an instance wall.  Every `theorem` is
discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTheta

open Real Complex AddChar MulChar

/-! ## 1. The odd indicator and the two elementary phase laws -/

/-- The odd indicator, as a complex weight. -/
def oddInd (m : ℤ) : ℂ := if m % 2 = 0 then 0 else 1

/-- Integer powers of `−1` through `cexp`. -/
private lemma neg_one_zpow_exp (k : ℤ) : cexp (π * I * k) = (-1 : ℂ) ^ k := by
  rw [show (π : ℂ) * I * k = (k : ℂ) * (π * I) from by ring, Complex.exp_int_mul,
    Complex.exp_pi_mul_I]

/-- The primitive `p`-th root of unity. -/
def zetaP (p : ℕ) : ℂ := cexp (2 * π * I / p)

private lemma zetaP_ne_zero (p : ℕ) : zetaP p ≠ 0 := Complex.exp_ne_zero _

/-- Integer-exponent powers of `ζ_p` through `cexp`. -/
private lemma zetaP_zpow_exp (p : ℕ) (K : ℤ) :
    cexp (2 * π * I * K / p) = zetaP p ^ K := by
  rw [show 2 * (π : ℂ) * I * K / p = (K : ℂ) * (2 * π * I / p) from by ring, zetaP,
    ← Complex.exp_int_mul]

/-- Powers of `ζ_p` reduce mod `p`. -/
private lemma zetaP_zpow_congr (p : ℕ) (hp : p ≠ 0) {a b : ℤ}
    (hab : a % (p : ℤ) = b % (p : ℤ)) : zetaP p ^ a = zetaP p ^ b := by
  have hprim : IsPrimitiveRoot (zetaP p) p := Complex.isPrimitiveRoot_exp p hp
  obtain ⟨c, hc⟩ := Int.ModEq.dvd (show a ≡ b [ZMOD (p : ℤ)] from hab)
  rw [show a = b + (p : ℤ) * (-c) from by rw [mul_neg]; omega, zpow_add₀ (zetaP_ne_zero p), zpow_mul,
    show zetaP p ^ (p : ℤ) = 1 from (zpow_natCast _ p).trans hprim.pow_eq_one,
    one_zpow, mul_one]

/-- The standard additive character returns `ζ_p` to an integer power. -/
private lemma psi_intCast (p : ℕ) [NeZero p] (hp : p ≠ 0)
    (hζ : zetaP p ^ p = 1) (K : ℤ) :
    AddChar.zmodChar p hζ ((K : ZMod p)) = zetaP p ^ K := by
  rw [AddChar.zmodChar_apply, ← zpow_natCast]
  refine zetaP_zpow_congr p hp ?_
  have hv : ((((K : ZMod p)).val : ℤ)) = K % p := ZMod.val_intCast K
  rw [hv, Int.emod_emod_of_dvd K (dvd_refl _)]

/-! ## 2. The two phase decompositions at levels `4p` and `2p` -/

/-- The level-`4p` phase splits into the quarter-turn and the mod-`p` phase. -/
private lemma phaseA (p q : ℕ) (hpq : p = 4 * q + 1) (n e : ℤ) :
    cexp (2 * π * I * ((4 * e + 1) * n) / (4 * p))
      = cexp (π * I * n / 2) * zetaP p ^ (-((q : ℤ) * ((4 * e + 1) * n))) := by
  have hpc : (p : ℂ) = 4 * (q : ℂ) + 1 := by exact_mod_cast hpq
  have h4q : (4 * (q : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := 4 * q + 1) |>.mpr (by omega)
    push_cast at h
    exact h
  rw [show 2 * (π : ℂ) * I * ((4 * e + 1) * n) / (4 * p)
      = ((e * n : ℤ) : ℂ) * (2 * π * I)
        + (π * I * n / 2
            + 2 * π * I * ((-((q : ℤ) * ((4 * e + 1) * n)) : ℤ) : ℂ) / p) from by
    rw [hpc]
    push_cast
    field_simp
    ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add,
    zetaP_zpow_exp]

/-- The level-`2p` phase splits into the half-turn and the mod-`p` phase. -/
private lemma phaseB (p q : ℕ) (hpq : p = 4 * q + 1) (m d : ℤ) :
    cexp (2 * π * I * (d * m) / (2 * p))
      = (-1 : ℂ) ^ (d * m) * zetaP p ^ (-(2 * (q : ℤ) * (d * m))) := by
  have hpc : (p : ℂ) = 4 * (q : ℂ) + 1 := by exact_mod_cast hpq
  have h4q : (4 * (q : ℂ) + 1) ≠ 0 := by
    have h := Nat.cast_ne_zero (R := ℂ) (n := 4 * q + 1) |>.mpr (by omega)
    push_cast at h
    exact h
  rw [show 2 * (π : ℂ) * I * (d * m) / (2 * p)
      = π * I * ((d * m : ℤ) : ℂ)
        + 2 * π * I * ((-(2 * (q : ℤ) * (d * m)) : ℤ) : ℂ) / p from by
    rw [hpc]
    push_cast
    field_simp
    ring]
  rw [Complex.exp_add, zetaP_zpow_exp, neg_one_zpow_exp]

/-! ## 3. The grid term and the range-to-residue conversion -/

/-- One dual-side phase coefficient of the `p × 2p` grid. -/
def phaseTerm (p : ℕ) [Fact p.Prime] (n m : ℤ) (e d : ℕ) : ℂ :=
  ((quadraticChar (ZMod p) (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ)
    * (-1 : ℂ) ^ (d : ℕ)
    * cexp (2 * π * I * ((4 * (e : ℤ) + 1) * n) / (4 * p))
    * cexp (2 * π * I * ((d : ℤ) * m) / (2 * p))

/-- A range-`p` sum of residue data is the residue sum. -/
private lemma sum_range_zmod (p : ℕ) [NeZero p] (F : ZMod p → ℂ) :
    ∑ e ∈ Finset.range p, F ((e : ℕ) : ZMod p) = ∑ a : ZMod p, F a := by
  refine Finset.sum_nbij' (fun e => ((e : ℕ) : ZMod p)) (fun a => a.val)
    ?_ ?_ ?_ ?_ ?_
  · intro e _
    exact Finset.mem_univ _
  · intro a _
    simp only [Finset.mem_range]
    exact ZMod.val_lt a
  · intro e he
    simp only [Finset.mem_range] at he
    exact ZMod.val_cast_of_lt he
  · intro a _
    exact ZMod.natCast_zmod_val a
  · intro e _
    rfl

/-! ## 4. The phase collapse at every split prime -/

set_option maxHeartbeats 4000000 in
/-- **THE FAMILY PHASE COLLAPSE AT EVERY SPLIT PRIME.**  At every prime
`p ≡ 1 (mod 4)`, the `2p²` dual-side phases of the `p × 2p` grid collapse through
the family eigen-identity:

`∑_{e<p, d<2p} χ_p((4e+1)² + 4d²)·(−1)^d·e^{2πi(4e+1)n/(4p)}·e^{2πi·dm/(2p)}
  = 2p·i^n·[m odd]·χ_p(n² + m²)`

— the finite engine that carried the theta functional equation at five, with the
modulus a parameter. -/
theorem theFamilyPhaseCollapseAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) (n m : ℤ) :
    ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p), phaseTerm p n m e d
      = 2 * p * cexp (π * I * n / 2) * oddInd m
          * ((quadraticChar (ZMod p) ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) := by
  have hp : p.Prime := Fact.out
  have hp2 : 2 ≤ p := hp.two_le
  have hp5 : 5 ≤ p := by omega
  set q : ℕ := p / 4 with hqdef
  have hpq : p = 4 * q + 1 := by omega
  have hq1 : 1 ≤ q := by omega
  have hζ0 : zetaP p ≠ 0 := zetaP_ne_zero p
  have hprim : IsPrimitiveRoot (zetaP p) p := Complex.isPrimitiveRoot_exp p hp.ne_zero
  have hζp : zetaP p ^ p = 1 := hprim.pow_eq_one
  set ψ : AddChar (ZMod p) ℂ := AddChar.zmodChar p hζp with hψdef
  have hψprim : ψ.IsPrimitive :=
    AddChar.zmodChar_primitive_of_primitive_root p hprim
  have hψz : ∀ K : ℤ, ψ ((K : ZMod p)) = zetaP p ^ K := fun K =>
    psi_intCast p hp.ne_zero hζp K
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hneg : (-1 : ℂ) ≠ 0 := by norm_num
  have hpodd : Odd p := ⟨2 * q, by omega⟩
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
      unfold phaseTerm
      have hc : ((p + d : ℕ) : ℤ) = (d : ℤ) + p := by push_cast; ring
      rw [hc]
      have hchi : (((4 * (e : ℤ) + 1) ^ 2 + 4 * ((d : ℤ) + p) ^ 2 : ℤ) : ZMod p)
          = (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) := by
        rw [ZMod.intCast_eq_intCast_iff']
        exact Int.modEq_iff_dvd.mpr ⟨-(8 * (d : ℤ) + 4 * (p : ℤ)), by ring⟩
      have hsign : (-1 : ℂ) ^ ((p + d : ℕ)) = -(-1 : ℂ) ^ (d : ℕ) := by
        rw [pow_add, hpodd.neg_one_pow]
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
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- even hand: both sides vanish
    have h1 : (-1 : ℂ) ^ m = 1 := by
      rw [hk, show k + k = 2 * k from by ring, zpow_mul]
      norm_num
    have h0 : oddInd m = 0 := by
      unfold oddInd
      rw [if_pos (by omega)]
    rw [h1, h0]
    ring
  · -- odd hand: the eigen-identity carries the sum
    have hm1 : (-1 : ℂ) ^ m = -1 := by
      rw [hk, zpow_add₀ hneg, zpow_mul]
      norm_num
    have h1 : oddInd m = 1 := by
      unfold oddInd
      rw [if_neg (by omega)]
    -- the sign pair `(−1)^d·(−1)^{dm}` is trivial on the odd hand
    have htriv : ∀ d : ℕ, (-1 : ℂ) ^ (d : ℕ) * (-1 : ℂ) ^ ((d : ℤ) * m) = 1 := by
      intro d
      rw [← zpow_natCast (-1 : ℂ) d, ← zpow_add₀ hneg,
        show (d : ℤ) + (d : ℤ) * m = (d : ℤ) * (1 + m) from by ring, hk,
        show (d : ℤ) * (1 + (2 * k + 1)) = 2 * ((d : ℤ) * (k + 1)) from by ring, zpow_mul]
      norm_num
    -- collapse each term through the two phase decompositions
    have hterm : ∀ e ∈ Finset.range p, ∀ d ∈ Finset.range p, phaseTerm p n m e d
        = cexp (π * I * n / 2) *
            (((quadraticChar (ZMod p)
                (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
              (zetaP p ^ (-((q : ℤ) * ((4 * (e : ℤ) + 1) * n))) *
                zetaP p ^ (-(2 * (q : ℤ) * ((d : ℤ) * m))))) := by
      intro e _ d _
      unfold phaseTerm
      rw [phaseA p q hpq, phaseB p q hpq]
      calc ((quadraticChar (ZMod p)
              (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
            (-1 : ℂ) ^ (d : ℕ) *
            (cexp (π * I * n / 2) * zetaP p ^ (-((q : ℤ) * ((4 * (e : ℤ) + 1) * n)))) *
            ((-1 : ℂ) ^ ((d : ℤ) * m) * zetaP p ^ (-(2 * (q : ℤ) * ((d : ℤ) * m))))
          = ((-1 : ℂ) ^ (d : ℕ) * (-1 : ℂ) ^ ((d : ℤ) * m)) *
            (((quadraticChar (ZMod p)
                (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
              (cexp (π * I * n / 2) *
                (zetaP p ^ (-((q : ℤ) * ((4 * (e : ℤ) + 1) * n))) *
                  zetaP p ^ (-(2 * (q : ℤ) * ((d : ℤ) * m)))))) := by ring
        _ = _ := by rw [htriv d]; ring
    have hsum2 : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range p, phaseTerm p n m e d
        = cexp (π * I * n / 2) *
            ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range p,
              ((quadraticChar (ZMod p)
                  (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
                (zetaP p ^ (-((q : ℤ) * ((4 * (e : ℤ) + 1) * n))) *
                  zetaP p ^ (-(2 * (q : ℤ) * ((d : ℤ) * m)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d hd => hterm e he d hd
    -- express each factor through the residue chart
    set ξ : ZMod p := ((-(q : ℤ) * n : ℤ) : ZMod p) with hξdef
    set η₀ : ZMod p := ((-(2 * (q : ℤ) * m) : ℤ) : ZMod p) with hη₀def
    have hres : ∀ e ∈ Finset.range p, ∀ d ∈ Finset.range p,
        ((quadraticChar (ZMod p)
            (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
          (zetaP p ^ (-((q : ℤ) * ((4 * (e : ℤ) + 1) * n))) *
            zetaP p ^ (-(2 * (q : ℤ) * ((d : ℤ) * m))))
        = ((quadraticChar (ZMod p)
            ((4 * ((e : ℕ) : ZMod p) + 1) ^ 2 + 4 * ((d : ℕ) : ZMod p) ^ 2) : ℤ) : ℂ) *
          (ψ (ξ * (4 * ((e : ℕ) : ZMod p) + 1)) * ψ (η₀ * ((d : ℕ) : ZMod p))) := by
      intro e _ d _
      have hχarg : (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p)
          = (4 * ((e : ℕ) : ZMod p) + 1) ^ 2 + 4 * ((d : ℕ) : ZMod p) ^ 2 := by
        push_cast
        ring
      have hz1 : zetaP p ^ (-((q : ℤ) * ((4 * (e : ℤ) + 1) * n)))
          = ψ (ξ * (4 * ((e : ℕ) : ZMod p) + 1)) := by
        rw [show ξ * (4 * ((e : ℕ) : ZMod p) + 1)
            = ((-(q : ℤ) * ((4 * (e : ℤ) + 1) * n) : ℤ) : ZMod p) from by
          rw [hξdef]
          push_cast
          ring]
        rw [hψz]
        congr 1
        ring
      have hz2 : zetaP p ^ (-(2 * (q : ℤ) * ((d : ℤ) * m)))
          = ψ (η₀ * ((d : ℕ) : ZMod p)) := by
        rw [show η₀ * ((d : ℕ) : ZMod p)
            = ((-(2 * (q : ℤ) * m) * (d : ℤ) : ℤ) : ZMod p) from by
          rw [hη₀def]
          push_cast
          ring]
        rw [hψz]
        congr 1
        ring
      rw [hχarg, hz1, hz2]
    -- convert the two range sums to residue sums
    have hZ : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range p,
          ((quadraticChar (ZMod p)
              (((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) *
            (zetaP p ^ (-((q : ℤ) * ((4 * (e : ℤ) + 1) * n))) *
              zetaP p ^ (-(2 * (q : ℤ) * ((d : ℤ) * m))))
        = ∑ a : ZMod p, ∑ b : ZMod p,
            ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + 4 * b ^ 2) : ℤ) : ℂ) *
              (ψ (ξ * (4 * a + 1)) * ψ (η₀ * b)) := by
      rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => hres e he d hd]
      rw [Finset.sum_congr rfl fun e _ => sum_range_zmod p
        (fun b => ((quadraticChar (ZMod p) ((4 * ((e : ℕ) : ZMod p) + 1) ^ 2 + 4 * b ^ 2) : ℤ) : ℂ) *
          (ψ (ξ * (4 * ((e : ℕ) : ZMod p) + 1)) * ψ (η₀ * b)))]
      exact sum_range_zmod p
        (fun a => ∑ b : ZMod p,
          ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + 4 * b ^ 2) : ℤ) : ℂ) *
            (ψ (ξ * (4 * a + 1)) * ψ (η₀ * b)))
    -- the two nonzero constants of the affine chart
    have h4 : (4 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((4 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
      have := Int.le_of_dvd (by norm_num) h'
      omega
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro h
      have h' : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
      have := Int.le_of_dvd (by norm_num) h'
      omega
    -- the split residue: `w² = −1`
    obtain ⟨w, hw⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr
      (show p % 4 ≠ 3 from by omega)
    have hw2 : w * w = -1 := hw.symm
    have hw0 : w ≠ 0 := by
      intro h
      rw [h, mul_zero] at hw2
      have h1 : (1 : ZMod p) = 0 := by linear_combination hw2
      exact one_ne_zero h1
    have h2w0 : (2 * w : ZMod p) ≠ 0 := mul_ne_zero h2 hw0
    set η' : ZMod p := η₀ * (2 * w)⁻¹ with hη'def
    have hη' : η' * (2 * w) = η₀ := by
      rw [hη'def, mul_assoc, inv_mul_cancel₀ h2w0, mul_one]
    -- the affine chart `a ↦ 4a + 1` and the rotation `b ↦ (2w)·b`
    have hbij4 : Function.Bijective (fun a : ZMod p => 4 * a + 1) := by
      have hb1 : Function.Bijective (fun a : ZMod p => 4 * a) :=
        mulLeft_bijective₀ 4 h4
      have hb2 : Function.Bijective (fun a : ZMod p => a + 1) :=
        (Equiv.addRight (1 : ZMod p)).bijective
      exact hb2.comp hb1
    have hbij2w : Function.Bijective (fun b : ZMod p => 2 * w * b) :=
      mulLeft_bijective₀ (2 * w) h2w0
    have haff : ∑ a : ZMod p, ∑ b : ZMod p,
          ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + 4 * b ^ 2) : ℤ) : ℂ) *
            (ψ (ξ * (4 * a + 1)) * ψ (η₀ * b))
        = ∑ r : ZMod p, ∑ s : ZMod p,
            ((quadraticChar (ZMod p) (r ^ 2 - s ^ 2) : ℤ) : ℂ) * ψ (ξ * r + η' * s) := by
      have hstep1 : ∀ a : ZMod p,
          ∑ b : ZMod p,
            ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 + 4 * b ^ 2) : ℤ) : ℂ) *
              (ψ (ξ * (4 * a + 1)) * ψ (η₀ * b))
          = ∑ s : ZMod p,
              ((quadraticChar (ZMod p) ((4 * a + 1) ^ 2 - s ^ 2) : ℤ) : ℂ) *
                ψ (ξ * (4 * a + 1) + η' * s) := by
        intro a
        refine Fintype.sum_bijective (fun b : ZMod p => 2 * w * b) hbij2w _ _ fun b => ?_
        have hsq : (4 * a + 1) ^ 2 - (2 * w * b) ^ 2 = (4 * a + 1) ^ 2 + 4 * b ^ 2 := by
          linear_combination (-4 * b ^ 2) * hw2
        have harg : ξ * (4 * a + 1) + η' * (2 * w * b) = ξ * (4 * a + 1) + η₀ * b := by
          rw [show η' * (2 * w * b) = (η' * (2 * w)) * b from by ring, hη']
        rw [hsq, harg, ψ.map_add_eq_mul]
      rw [Finset.sum_congr rfl fun a _ => hstep1 a]
      refine Fintype.sum_bijective (fun a : ZMod p => 4 * a + 1) hbij4 _ _ fun a => rfl
    -- land on the family eigen-identity
    have heigen := FamilyGauss.theFamilyEigenIdentityOnTheSplitResidues p hp1 ψ hψprim
      ξ η'
    -- identify the returned class
    have hq0 : ((q : ℕ) : ZMod p) ≠ 0 := by
      intro h
      have h' : ((q : ℤ) : ZMod p) = 0 := by exact_mod_cast h
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
      have := Int.le_of_dvd (by exact_mod_cast hq1) h'
      omega
    have hneg4 : (-4 : ZMod p) ≠ 0 := by
      intro h
      exact h4 (by linear_combination -h)
    have hclass : ξ ^ 2 - η' ^ 2
        = ((q : ℕ) : ZMod p) ^ 2 * ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) := by
      have h2w : (2 * w) ^ 2 = (-4 : ZMod p) := by
        linear_combination 4 * hw2
      have hη'sq : η' ^ 2 * (-4) = η₀ ^ 2 := by
        rw [← h2w, show η' ^ 2 * (2 * w) ^ 2 = (η' * (2 * w)) ^ 2 from by ring, hη']
      refine mul_right_cancel₀ hneg4 ?_
      have hexp : (ξ ^ 2 - η' ^ 2) * (-4) = ξ ^ 2 * (-4) - η₀ ^ 2 := by
        linear_combination -hη'sq
      rw [hexp, hξdef, hη₀def]
      push_cast
      ring
    have hXsplit : ((quadraticChar (ZMod p) (ξ ^ 2 - η' ^ 2) : ℤ) : ℂ)
        = ((quadraticChar (ZMod p) ((n ^ 2 + m ^ 2 : ℤ) : ZMod p) : ℤ) : ℂ) := by
      rw [hclass, map_mul, quadraticChar_sq_one' hq0, one_mul]
    -- assemble
    rw [hm1, hsum2, hZ, haff, heigen, hXsplit, h1]
    ring
