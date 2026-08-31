import ElementaryHolonics.Millennium.FamilyTunnellJacobiFourSquareSource

/-!
# The source-side return of the Jacobi four-square product

The live Jacobi source has an exact finite-shell decomposition, and the
Lambert receiver has an exact divisor current.  The missing general passage
is the classical shell/divisor theorem.  This plate first removes the
residue-address chart by an explicit all-address bijection, returning the
complete ordered shell at every coefficient.  It also records the first
positive coefficient as an independent finite sanity check, without
introducing the missing theorem as an assumption.

The general shell/divisor identity remains the explicit open algebraic edge:

`Σ_r card (fourSquareResidueShell r n) =
  8 * Σ_{d ∣ n, 4 ∤ d} d`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiQuarticProduct

open Finset
open PowerSeries
open Soma.Holonics.Mathematics.JacobiUnitSpecialization
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaCensus
open Soma.Holonics.Millennium.FamilyTunnellHopfThetaLift
open Soma.Holonics.Millennium.FamilyTunnellFourSquareThetaReceiver
open Soma.Holonics.Millennium.FamilyTunnellJacobiUnitThetaReceiver
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareSource

/-- The unaddressed ordered four-square shell.  The residue-indexed shells in
the source file are a disjoint chart of this population. -/
def totalFourSquareShell (n : ℕ) : Finset IntegerQuadruple :=
  ((((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
      Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
    ((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ
      Finset.Icc (-(n : ℤ)) (n : ℤ))).filter fun q =>
        q.1.1 ^ 2 + q.1.2 ^ 2 + q.2.1 ^ 2 + q.2.2 ^ 2 = (n : ℤ))

/-- The same shell with its unique modulo-four address retained. -/
def taggedTotalFourSquareShell (n : ℕ) :
    Finset (Σ r : ResidueQuaternion, IntegerQuadruple) :=
  Finset.univ.sigma fun r =>
    fourSquareResidueShell r.1 r.2.1 r.2.2.1 r.2.2.2 n

private theorem quarterResidueAddress_eq_of_returns
    (x : ℤ) (r : QuarterResidue) (h : (x : ZMod 4) = r.val) :
    quarterResidueAddress x = r := by
  apply Fin.ext
  change (x : ZMod 4).val = r.val
  calc
    (x : ZMod 4).val = ((r.val : ℕ) : ZMod 4).val := congrArg ZMod.val h
    _ = r.val := ZMod.val_natCast_of_lt r.isLt

private theorem totalToTagged_mem {n : ℕ} {q : IntegerQuadruple}
    (hq : q ∈ totalFourSquareShell n) :
    (Sigma.mk
      ⟨quarterResidueAddress q.1.1, quarterResidueAddress q.1.2,
        quarterResidueAddress q.2.1, quarterResidueAddress q.2.2⟩ q) ∈
      taggedTotalFourSquareShell n := by
  rcases Finset.mem_filter.mp hq with ⟨hbox, hnorm⟩
  rw [taggedTotalFourSquareShell, Finset.mem_sigma]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [fourSquareResidueShell, Finset.mem_filter]
  refine ⟨hbox, hnorm, ?_, ?_, ?_, ?_⟩ <;>
    exact quarterResidueAddress_returns _

private theorem taggedToTotal_mem {n : ℕ}
    {q : Σ r : ResidueQuaternion, IntegerQuadruple}
    (hq : q ∈ taggedTotalFourSquareShell n) : q.2 ∈ totalFourSquareShell n := by
  rcases Finset.mem_sigma.mp hq with ⟨_hr, hq⟩
  rcases Finset.mem_filter.mp hq with ⟨hbox, hnorm, _h₀, _h₁, _h₂, _h₃⟩
  rw [totalFourSquareShell, Finset.mem_filter]
  exact ⟨hbox, hnorm⟩

private def totalFourSquareShellEquiv (n : ℕ) :
    {q // q ∈ totalFourSquareShell n} ≃
      {q // q ∈ taggedTotalFourSquareShell n} where
  toFun q :=
    ⟨Sigma.mk
      ⟨quarterResidueAddress q.1.1.1, quarterResidueAddress q.1.1.2,
        quarterResidueAddress q.1.2.1, quarterResidueAddress q.1.2.2⟩ q.1,
      totalToTagged_mem q.2⟩
  invFun q := ⟨q.1.2, taggedToTotal_mem q.2⟩
  left_inv q := by
    apply Subtype.ext
    rfl
  right_inv q := by
    rcases q with ⟨⟨r, x⟩, hq⟩
    have hres := (Finset.mem_filter.mp (Finset.mem_sigma.mp hq).2).2
    rcases hres with ⟨_hnorm, hr₀, hr₁, hr₂, hr₃⟩
    apply Subtype.ext
    dsimp
    change
      ((⟨⟨quarterResidueAddress x.1.1, quarterResidueAddress x.1.2,
          quarterResidueAddress x.2.1, quarterResidueAddress x.2.2⟩, x⟩ :
        Σ _ : ResidueQuaternion, IntegerQuadruple)) =
      ((⟨r, x⟩ : Σ _ : ResidueQuaternion, IntegerQuadruple))
    apply Sigma.ext
    · apply Prod.ext
      · change quarterResidueAddress x.1.1 = r.1
        exact quarterResidueAddress_eq_of_returns x.1.1 r.1 hr₀
      · apply Prod.ext
        · change quarterResidueAddress x.1.2 = r.2.1
          exact quarterResidueAddress_eq_of_returns x.1.2 r.2.1 hr₁
        · apply Prod.ext
          · change quarterResidueAddress x.2.1 = r.2.2.1
            exact quarterResidueAddress_eq_of_returns x.2.1 r.2.2.1 hr₂
          · change quarterResidueAddress x.2.2 = r.2.2.2
            exact quarterResidueAddress_eq_of_returns x.2.2 r.2.2.2 hr₃
    · rfl

/-- The complete source coefficient is the cardinality of the unaddressed
ordered lattice shell.  This removes the residue chart without evaluating the
shell and is valid at every coefficient address. -/
theorem coeff_fullFourSquareTheta_eq_totalFourSquareShell_card (n : ℕ) :
    PowerSeries.coeff n fullFourSquareTheta =
      ((totalFourSquareShell n).card : ℤ) := by
  rw [coeff_fullFourSquareTheta_eq_sum_exactShell_card]
  have hcard :
      (taggedTotalFourSquareShell n).card = (totalFourSquareShell n).card := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_congr (totalFourSquareShellEquiv n)).symm
  calc
    ∑ r : ResidueQuaternion,
        ((fourSquareResidueShell
          r.1 r.2.1 r.2.2.1 r.2.2.2 n).card : ℤ) =
        ((taggedTotalFourSquareShell n).card : ℤ) := by
          rw [taggedTotalFourSquareShell, Finset.card_sigma]
          rw [Nat.cast_sum]
    _ = (totalFourSquareShell n).card := by exact_mod_cast hcard

/-- After this source reassembly, the sole remaining identity is the classical
Jacobi shell/divisor law itself. -/
theorem coeff_fullFourSquareTheta_eq_lambert_iff_totalShellDivisorLaw (n : ℕ) :
    PowerSeries.coeff n fullFourSquareTheta =
        PowerSeries.coeff n jacobiFourSquareLambertSeries ↔
      ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n := by
  rw [coeff_fullFourSquareTheta_eq_totalFourSquareShell_card,
    coeff_jacobiFourSquareLambertSeries]

/-- The coefficient defect after the residue chart has been removed.  Thus the
remaining obstruction is a single unaddressed shell identity, rather than a
choice of residue coordinates. -/
theorem coeff_fullFourSquareTheta_sub_lambert_eq_totalShellDivisorDefect (n : ℕ) :
    PowerSeries.coeff n fullFourSquareTheta -
        PowerSeries.coeff n jacobiFourSquareLambertSeries =
      ((totalFourSquareShell n).card : ℤ) - 8 * jacobiDivisorCurrent n := by
  rw [coeff_fullFourSquareTheta_eq_totalFourSquareShell_card,
    coeff_jacobiFourSquareLambertSeries]

/-- The unique norm-zero ordered quadruple supplies the constant face of the source. -/
@[simp] theorem coeff_fullFourSquareTheta_zero :
    PowerSeries.coeff 0 fullFourSquareTheta = 1 := by
  rw [coeff_fullFourSquareTheta_eq_totalFourSquareShell_card]
  simp [totalFourSquareShell]
  decide

/-- The whole-series Jacobi passage is exactly the positive shell/divisor family after the
Lambert receiver has been completed by its unique norm-zero face.  This is the properly based
global target: the uncompleted divisor current has constant coefficient zero. -/
theorem fullFourSquareTheta_eq_completedLambert_iff_totalShellDivisorLaw :
    fullFourSquareTheta = completedJacobiFourSquareLambertSeries ↔
      ∀ n : ℕ, 0 < n →
        ((totalFourSquareShell n).card : ℤ) = 8 * jacobiDivisorCurrent n := by
  constructor
  · intro h n hn
    have hcoeff := congrArg (PowerSeries.coeff n) h
    simpa [coeff_fullFourSquareTheta_eq_totalFourSquareShell_card,
      coeff_completedJacobiFourSquareLambertSeries_of_pos hn] using hcoeff
  · intro hshell
    apply PowerSeries.ext
    intro n
    by_cases hn : n = 0
    · subst n
      rw [coeff_fullFourSquareTheta_zero,
        coeff_completedJacobiFourSquareLambertSeries_zero]
    · rw [coeff_fullFourSquareTheta_eq_totalFourSquareShell_card,
        coeff_completedJacobiFourSquareLambertSeries_of_pos (Nat.pos_of_ne_zero hn),
        hshell n (Nat.pos_of_ne_zero hn)]

/-- The complete Jacobi four-square source and its Lambert receiver agree at
the first positive address.  This is an exact finite shell computation, not
a specialization of the requested general identity. -/
theorem coeff_fullFourSquareTheta_eq_lambert_one :
    PowerSeries.coeff 1 fullFourSquareTheta =
      PowerSeries.coeff 1 jacobiFourSquareLambertSeries := by
  rw [coeff_jacobiFourSquareLambertSeries]
  norm_num [jacobiDivisorCurrent, nonFourDivisors]
  let F : PowerSeries ℤ := unitSquareTheta (1 : ℤˣ)
  have h0 : PowerSeries.coeff 0 F = 1 := by
    dsimp [F]
    rw [coeff_unitSquareTheta_one]
    have hcard : ({m ∈ ({0} : Finset ℤ) | 0 = m.natAbs ^ 2}).card = 1 := by
      decide
    simpa [hcard]
  have h1 : PowerSeries.coeff 1 F = 2 := by
    dsimp [F]
    rw [coeff_unitSquareTheta_one]
    have hcard : ({m ∈ (Finset.Icc (-1 : ℤ) 1) | 1 = m.natAbs ^ 2}).card = 2 := by
      decide
    simpa [squareRootPopulation, hcard]
  have h0pow (k : ℕ) : PowerSeries.coeff 0 (F ^ k) = 1 := by
    calc
      PowerSeries.coeff 0 (F ^ k) = PowerSeries.constantCoeff (F ^ k) := by
        exact congrFun PowerSeries.coeff_zero_eq_constantCoeff (F ^ k)
      _ = (PowerSeries.constantCoeff F) ^ k := by simp
      _ = 1 := by
        rw [← PowerSeries.coeff_zero_eq_constantCoeff, h0]
        simp
  have hpow : ∀ k : ℕ, PowerSeries.coeff 1 (F ^ k) = (k : ℤ) * 2 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hconst : PowerSeries.constantCoeff F = 1 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff]
          exact h0
        have hconstpow : PowerSeries.constantCoeff (F ^ k) = 1 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff]
          exact h0pow k
        rw [pow_succ, PowerSeries.coeff_one_mul, ih, h1,
          hconst, hconstpow]
        push_cast
        ring_nf
  change PowerSeries.coeff 1 (F ^ 4) = _
  rw [hpow]
  norm_num [Finset.sum_filter]

#print axioms coeff_fullFourSquareTheta_eq_lambert_one
#print axioms coeff_fullFourSquareTheta_eq_totalFourSquareShell_card
#print axioms coeff_fullFourSquareTheta_eq_lambert_iff_totalShellDivisorLaw
#print axioms coeff_fullFourSquareTheta_sub_lambert_eq_totalShellDivisorDefect
#print axioms fullFourSquareTheta_eq_completedLambert_iff_totalShellDivisorLaw

end Soma.Holonics.Millennium.FamilyTunnellJacobiQuarticProduct
