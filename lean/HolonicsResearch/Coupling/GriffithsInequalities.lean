import HolonicsResearch.Coupling.LeeYangIsing

/-!
# Griffiths' inequalities: a ferromagnet's correlations are nonnegative, correlate, and grow with every coupling

Source record:
`research/records/2026-11-19_A_FERROMAGNETS_CORRELATIONS_ARE_NONNEGATIVE_AND_GROW_WITH_EVERY_COUPLING_SO_ADDING_A_CONTACT_NEVER_LOWERS_AN_AGREEMENT.md`.

`Coupling/LeeYangIsing` locates the zeros of a ferromagnet's partition function in the field.
This module proves the other half of what a ferromagnet's sign gives: the correlation
inequalities of Griffiths (1967) and of Kelly and Sherman (1968), in Ginibre's form (1970), for
interactions on arbitrary sets of sites, and the monotonicity in the couplings they imply.

[definition] A finite set `V` of sites and a finite family `ι` of interactions; interaction `a`
acts on the sites `A a` with coupling `J a`.  A configuration is its set `S` of up sites, with
`spin S i` from `Coupling/LeeYangIsing`; `spinProd S A = ∏ i ∈ A, sᵢ`.  The energy (its negative,
with `β` absorbed into `J`) is `energy A J S = ∑ a, J a · spinProd S (A a)`, the partition function
`Z A J = ∑ S, exp (energy A J S)`, the correlation of a set `B` of sites
`corr A J B = ∑ S, spinProd S B · exp (energy A J S)` and its average `avg A J B = corr A J B / Z A J`.
The Ising model with fields is the case where every `A a` has one or two sites.

[proved-standard; formal-checked] What is proved, for a ferromagnet (`∀ a, 0 ≤ J a`).

1. **A spin sum of a monomial is nonnegative** (`sum_monomial`, `sum_monomial_nonneg`):
   `∑ S, ∏ i, sᵢ ^ kᵢ = ∏ i, (1 + (−1) ^ kᵢ)`.
2. **Each Boltzmann weight is a sum of monomials with nonnegative coefficients**
   (`exp_mul_spinProd`, `sum_monomial_mul_exp_nonneg`): `exp (J s^A) = cosh J + sinh J · s^A` for
   a product of spins, and the product over the interactions expands into monomials whose
   coefficients are products of `cosh` and `sinh` of the couplings.
3. **Griffiths' first inequality** (`griffiths_first`, `avg_nonneg`): `⟨s^B⟩ ≥ 0` for every `B`.
4. **Griffiths' second inequality** (`griffiths_second`, `avg_mul_le_avg₂`):
   `⟨s^B⟩ ⟨s^C⟩ ≤ ⟨s^B s^C⟩`, by Ginibre's duplicated configuration: the second copy is written
   as the first flipped on a set `D`, and for each `D` the pair's weight is a ferromagnet's again.
5. **The correlations grow with every coupling** (`hasDerivAt_avg_path`, `avg_mono`): along a
   segment of couplings, `d⟨s^B⟩/dt = ∑ a, δ a (⟨s^B s^(A a)⟩ − ⟨s^B⟩ ⟨s^(A a)⟩)`, which the second
   inequality makes nonnegative; so `0 ≤ J ≤ J'` gives `⟨s^B⟩_J ≤ ⟨s^B⟩_J'`.

[interpretation] `agent-inferred` for the reading on the objects; the physics is standard.  Item 5
is what the inequalities are used for.  A lattice grown site by site is the larger lattice with
the new couplings switched on from zero, so a ferromagnet's correlations with free boundary
grow with the lattice and are bounded by one; they converge as the lattice fills space
(the infinite-volume limit), and an order that appears at one size persists at every larger one.

**What this does not state.**  No limit over growing `V` is formalized; item 5 is the monotone
step it rests on.  Spins are `±1`; the extensions to other single-spin measures (Griffiths for
spin `n/2`, Ginibre's general form, the Lebowitz and FKG inequalities beyond what Mathlib's
`Finset.fkg` states) are not here.  The couplings are real and nonnegative; nothing is said of an
antiferromagnet, where the first inequality fails.  The pair-coupling forms of items 3 to 5 are
also formalized in the Lean 4 project `phasetr/ising-model` (from Glimm and Jaffe); this module's
form is the many-body one, in Ginibre's proof.

**Computational object.**  The helical pair interaction, read at many bodies: an interaction is
a contact among the locks in `A a` whose weight is paid on the product of their sheets, and the
coupling's sign decides whether every contact agrees.  Of the winding guide's six objects: the
pair (the contacts), faces and placement (a correlation is a face of the configurations' density)
and the cell holonomy (the flip of a set `D`, `S ↦ S ∆ D`, is the half-turn that carries one copy
of the configuration to the other); the helix, the tube and the tower thread stay attached.

**Consumers.**  The atlas row `thermal.griffiths-correlation`, beside `thermal.ising-lee-yang`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Coupling.Griffiths

open Finset Holonics.Coupling.LeeYangIsing

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Spin products and monomials -/

/-- [definition] The product of the spins on the sites `A` in the configuration `S`. -/
def spinProd (S A : Finset V) : ℝ := ∏ i ∈ A, spin S i

/-- [definition] The monomial `∏ i, sᵢ ^ kᵢ` of the configuration `S`. -/
def monomial (S : Finset V) (k : V → ℕ) : ℝ := ∏ i, spin S i ^ k i

/-- [definition] The exponent vector of a set of sites. -/
def indicator (A : Finset V) : V → ℕ := fun i => if i ∈ A then 1 else 0

omit [Fintype V] in
theorem spin_mul_self (S : Finset V) (i : V) : spin S i * spin S i = 1 := by
  unfold spin
  split_ifs <;> norm_num

omit [Fintype V] in
theorem spinProd_mul_self (S A : Finset V) : spinProd S A * spinProd S A = 1 := by
  rw [spinProd, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun i _ => spin_mul_self S i

omit [Fintype V] in
/-- A product of spins is `1` or `−1`. -/
theorem spinProd_eq_one_or (S A : Finset V) : spinProd S A = 1 ∨ spinProd S A = -1 :=
  mul_self_eq_one_iff.mp (spinProd_mul_self S A)

omit [Fintype V] in
theorem one_add_spinProd_nonneg (S A : Finset V) : 0 ≤ 1 + spinProd S A := by
  rcases spinProd_eq_one_or S A with h | h <;> rw [h] <;> norm_num

omit [Fintype V] in
theorem one_sub_spinProd_nonneg (S A : Finset V) : 0 ≤ 1 - spinProd S A := by
  rcases spinProd_eq_one_or S A with h | h <;> rw [h] <;> norm_num

theorem spinProd_eq_monomial (S A : Finset V) : spinProd S A = monomial S (indicator A) := by
  rw [spinProd, monomial]
  simp only [indicator, pow_ite, pow_one, pow_zero]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

theorem monomial_mul (S : Finset V) (k l : V → ℕ) :
    monomial S k * monomial S l = monomial S (k + l) := by
  rw [monomial, monomial, monomial, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [Pi.add_apply, pow_add]

/-- A product of spin products is one monomial. -/
theorem prod_spinProd {ι : Type*} (F : Finset ι) (A : ι → Finset V) (S : Finset V) :
    ∏ a ∈ F, spinProd S (A a) = monomial S (fun i => ∑ a ∈ F, indicator (A a) i) := by
  simp_rw [spinProd_eq_monomial, monomial]
  rw [Finset.prod_comm]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_pow_eq_pow_sum _ _ _

/-- [proved-standard; formal-checked] **The spin sum of a monomial.**
`∑ S, ∏ i, sᵢ ^ kᵢ = ∏ i, (1 + (−1) ^ kᵢ)`. -/
theorem sum_monomial (k : V → ℕ) :
    ∑ S : Finset V, monomial S k = ∏ i, (1 + (-1 : ℝ) ^ k i) := by
  rw [Finset.prod_add (fun _ => (1 : ℝ)) (fun i => (-1 : ℝ) ^ k i), Finset.powerset_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [monomial, ← Finset.prod_mul_prod_compl S, ← Finset.compl_eq_univ_sdiff]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by rw [spin_of_mem hi, one_pow]
  · exact Finset.prod_congr rfl fun i hi => by rw [spin_of_mem_compl hi]

/-- [proved-standard; formal-checked] **A monomial's spin sum is nonnegative.** -/
theorem sum_monomial_nonneg (k : V → ℕ) : 0 ≤ ∑ S : Finset V, monomial S k := by
  rw [sum_monomial]
  exact Finset.prod_nonneg fun i _ => by
    rcases neg_one_pow_eq_or ℝ (k i) with h | h <;> rw [h] <;> norm_num

omit [Fintype V] in
/-- On a product of spins, `exp (c · s^A) = cosh c + sinh c · s^A`. -/
theorem exp_mul_spinProd (c : ℝ) (S A : Finset V) :
    Real.exp (c * spinProd S A) = Real.cosh c + Real.sinh c * spinProd S A := by
  rcases spinProd_eq_one_or S A with h | h <;> rw [h]
  · rw [mul_one, mul_one, Real.cosh_add_sinh]
  · rw [mul_neg_one, mul_neg_one, ← sub_eq_add_neg, Real.cosh_sub_sinh]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [proved-standard; formal-checked] **The positivity of a ferromagnet's weights.**  With every
`K a ≥ 0`, `∑ S, (∏ i, sᵢ ^ kᵢ) · exp (∑ a, K a · s^(A a)) ≥ 0` for every exponent vector `k`. -/
theorem sum_monomial_mul_exp_nonneg (A : ι → Finset V) (K : ι → ℝ) (hK : ∀ a, 0 ≤ K a)
    (k : V → ℕ) :
    0 ≤ ∑ S : Finset V, monomial S k * Real.exp (∑ a, K a * spinProd S (A a)) := by
  have hexp : ∀ S : Finset V, Real.exp (∑ a, K a * spinProd S (A a)) =
      ∑ F : Finset ι, (∏ a ∈ F, Real.cosh (K a)) * ((∏ a ∈ Fᶜ, Real.sinh (K a)) *
        monomial S (fun i => ∑ a ∈ Fᶜ, indicator (A a) i)) := by
    intro S
    rw [Real.exp_sum]
    simp_rw [exp_mul_spinProd]
    rw [Finset.prod_add, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun F _ => ?_
    rw [← Finset.compl_eq_univ_sdiff, Finset.prod_mul_distrib, prod_spinProd]
  have hterm : ∀ (F : Finset ι) (S : Finset V),
      monomial S k * ((∏ a ∈ F, Real.cosh (K a)) * ((∏ a ∈ Fᶜ, Real.sinh (K a)) *
        monomial S (fun i => ∑ a ∈ Fᶜ, indicator (A a) i))) =
      ((∏ a ∈ F, Real.cosh (K a)) * ∏ a ∈ Fᶜ, Real.sinh (K a)) *
        monomial S (k + fun i => ∑ a ∈ Fᶜ, indicator (A a) i) := by
    intro F S
    rw [← monomial_mul]
    ring
  simp_rw [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_nonneg fun F _ => ?_
  rw [Finset.sum_congr rfl fun S _ => hterm F S, ← Finset.mul_sum]
  exact mul_nonneg
    (mul_nonneg (Finset.prod_nonneg fun a _ => (Real.cosh_pos _).le)
      (Finset.prod_nonneg fun a _ => Real.sinh_nonneg_iff.mpr (hK a)))
    (sum_monomial_nonneg _)

/-! ## The model and the two inequalities -/

/-- [definition] The energy of a configuration (with `β` absorbed into the couplings). -/
def energy (A : ι → Finset V) (J : ι → ℝ) (S : Finset V) : ℝ := ∑ a, J a * spinProd S (A a)

/-- [definition] The partition function. -/
def Z (A : ι → Finset V) (J : ι → ℝ) : ℝ := ∑ S : Finset V, Real.exp (energy A J S)

/-- [definition] The correlation of the sites `B`, unnormalized. -/
def corr (A : ι → Finset V) (J : ι → ℝ) (B : Finset V) : ℝ :=
  ∑ S : Finset V, spinProd S B * Real.exp (energy A J S)

/-- [definition] The joint correlation of `B` and `C`, unnormalized. -/
def corr₂ (A : ι → Finset V) (J : ι → ℝ) (B C : Finset V) : ℝ :=
  ∑ S : Finset V, spinProd S B * spinProd S C * Real.exp (energy A J S)

/-- [definition] The average `⟨s^B⟩`. -/
def avg (A : ι → Finset V) (J : ι → ℝ) (B : Finset V) : ℝ := corr A J B / Z A J

/-- [definition] The average `⟨s^B s^C⟩`. -/
def avg₂ (A : ι → Finset V) (J : ι → ℝ) (B C : Finset V) : ℝ := corr₂ A J B C / Z A J

omit [DecidableEq ι] in
theorem Z_pos (A : ι → Finset V) (J : ι → ℝ) : 0 < Z A J :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

omit [DecidableEq ι] in
/-- [proved-standard; formal-checked] **Griffiths' first inequality** (Griffiths 1967): a
ferromagnet's correlations are nonnegative. -/
theorem griffiths_first (A : ι → Finset V) (J : ι → ℝ) (hJ : ∀ a, 0 ≤ J a) (B : Finset V) :
    0 ≤ corr A J B := by
  classical
  have h := sum_monomial_mul_exp_nonneg A J hJ (indicator B)
  simp_rw [← spinProd_eq_monomial] at h
  exact h

omit [DecidableEq ι] in
theorem avg_nonneg (A : ι → Finset V) (J : ι → ℝ) (hJ : ∀ a, 0 ≤ J a) (B : Finset V) :
    0 ≤ avg A J B :=
  div_nonneg (griffiths_first A J hJ B) (Z_pos A J).le

/-- The second copy of a configuration is the first flipped on `D`. -/
theorem spin_symmDiff (S D : Finset V) (i : V) :
    spin (symmDiff S D) i = spin S i * spin Dᶜ i := by
  unfold spin
  by_cases hS : i ∈ S <;> by_cases hD : i ∈ D <;> simp [Finset.mem_symmDiff, hS, hD]

theorem spinProd_symmDiff (S D A : Finset V) :
    spinProd (symmDiff S D) A = spinProd S A * spinProd Dᶜ A := by
  rw [spinProd, spinProd, spinProd, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => spin_symmDiff S D i

theorem sum_symmDiff (S : Finset V) (f : Finset V → ℝ) :
    ∑ T : Finset V, f T = ∑ D : Finset V, f (symmDiff S D) :=
  (Fintype.sum_bijective (symmDiff S) (symmDiff_right_involutive S).bijective _ f
    fun _ => rfl).symm

/-- [proved-standard; formal-checked] **Griffiths' second inequality** (Kelly and Sherman 1968;
Ginibre's proof, 1970): for a ferromagnet, `corr B · corr C ≤ Z · corr₂ B C`, that is
`⟨s^B⟩ ⟨s^C⟩ ≤ ⟨s^B s^C⟩`. -/
theorem griffiths_second (A : ι → Finset V) (J : ι → ℝ) (hJ : ∀ a, 0 ≤ J a) (B C : Finset V) :
    corr A J B * corr A J C ≤ Z A J * corr₂ A J B C := by
  rw [← sub_nonneg]
  have hterm : ∀ D S : Finset V,
      spinProd S B * spinProd S C * Real.exp (energy A J S) *
          Real.exp (energy A J (symmDiff S D)) -
        spinProd S B * Real.exp (energy A J S) *
          (spinProd (symmDiff S D) C * Real.exp (energy A J (symmDiff S D))) =
      (1 - spinProd Dᶜ C) * (monomial S (indicator B + indicator C) *
        Real.exp (∑ a, (J a * (1 + spinProd Dᶜ (A a))) * spinProd S (A a))) := by
    intro D S
    have hw : Real.exp (energy A J S) * Real.exp (energy A J (symmDiff S D)) =
        Real.exp (∑ a, (J a * (1 + spinProd Dᶜ (A a))) * spinProd S (A a)) := by
      rw [← Real.exp_add, energy, energy, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [spinProd_symmDiff]
      ring
    rw [← hw, ← monomial_mul, ← spinProd_eq_monomial, ← spinProd_eq_monomial, spinProd_symmDiff]
    ring
  have key : Z A J * corr₂ A J B C - corr A J B * corr A J C =
      ∑ D : Finset V, (1 - spinProd Dᶜ C) * ∑ S : Finset V,
        monomial S (indicator B + indicator C) *
          Real.exp (∑ a, (J a * (1 + spinProd Dᶜ (A a))) * spinProd S (A a)) := by
    calc Z A J * corr₂ A J B C - corr A J B * corr A J C
        = ∑ S : Finset V, ∑ T : Finset V,
            (spinProd S B * spinProd S C * Real.exp (energy A J S) * Real.exp (energy A J T) -
              spinProd S B * Real.exp (energy A J S) *
                (spinProd T C * Real.exp (energy A J T))) := by
          rw [Z, corr₂, corr, corr, mul_comm, Finset.sum_mul_sum, Finset.sum_mul_sum,
            ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun S _ => by rw [← Finset.sum_sub_distrib]
      _ = ∑ S : Finset V, ∑ D : Finset V,
            (spinProd S B * spinProd S C * Real.exp (energy A J S) *
                Real.exp (energy A J (symmDiff S D)) -
              spinProd S B * Real.exp (energy A J S) *
                (spinProd (symmDiff S D) C * Real.exp (energy A J (symmDiff S D)))) :=
          Finset.sum_congr rfl fun S _ => sum_symmDiff S _
      _ = ∑ S : Finset V, ∑ D : Finset V, (1 - spinProd Dᶜ C) *
            (monomial S (indicator B + indicator C) *
              Real.exp (∑ a, (J a * (1 + spinProd Dᶜ (A a))) * spinProd S (A a))) :=
          Finset.sum_congr rfl fun S _ => Finset.sum_congr rfl fun D _ => hterm D S
      _ = _ := by
          rw [Finset.sum_comm]
          simp_rw [Finset.mul_sum]
  rw [key]
  exact Finset.sum_nonneg fun D _ => mul_nonneg (one_sub_spinProd_nonneg _ _)
    (sum_monomial_mul_exp_nonneg A _ (fun a => mul_nonneg (hJ a) (one_add_spinProd_nonneg _ _)) _)

theorem avg_mul_le_avg₂ (A : ι → Finset V) (J : ι → ℝ) (hJ : ∀ a, 0 ≤ J a) (B C : Finset V) :
    avg A J B * avg A J C ≤ avg₂ A J B C := by
  have hZ := Z_pos A J
  rw [avg, avg, avg₂, div_mul_div_comm, div_le_div_iff₀ (by positivity) hZ]
  have := griffiths_second A J hJ B C
  calc corr A J B * corr A J C * Z A J ≤ Z A J * corr₂ A J B C * Z A J :=
        mul_le_mul_of_nonneg_right this hZ.le
    _ = corr₂ A J B C * (Z A J * Z A J) := by ring

/-! ## The correlations grow with every coupling -/

omit [Fintype V] [DecidableEq ι] in
theorem energy_path (A : ι → Finset V) (J δ : ι → ℝ) (t : ℝ) (S : Finset V) :
    energy A (fun a => J a + t * δ a) S = energy A J S + t * energy A δ S := by
  simp only [energy, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

omit [DecidableEq ι] in
/-- The derivative of a weighted spin sum along a segment of couplings. -/
theorem hasDerivAt_sum_weight (A : ι → Finset V) (J δ : ι → ℝ) (g : Finset V → ℝ) (t : ℝ) :
    HasDerivAt (fun t => ∑ S : Finset V, g S * Real.exp (energy A (fun a => J a + t * δ a) S))
      (∑ S : Finset V, g S * Real.exp (energy A (fun a => J a + t * δ a) S) * energy A δ S) t := by
  simp_rw [energy_path]
  apply HasDerivAt.fun_sum
  intro S _
  have := (((hasDerivAt_id t).mul_const (energy A δ S)).const_add (energy A J S)).exp.const_mul
    (g S)
  refine this.congr_deriv ?_
  simp only [id_eq, one_mul]
  ring

omit [DecidableEq ι] in
theorem sum_mul_energy (A : ι → Finset V) (δ : ι → ℝ) (g : Finset V → ℝ) :
    ∑ S : Finset V, g S * energy A δ S = ∑ a, δ a * ∑ S : Finset V, g S * spinProd S (A a) := by
  simp only [energy, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun S _ => by ring

omit [DecidableEq ι] in
/-- [proved-standard; formal-checked] **The derivative of a correlation in the couplings.**
Along `t ↦ J + t δ`, `d⟨s^B⟩/dt = ∑ a, δ a (corr₂ B (A a) · Z − corr B · corr (A a)) / Z²`. -/
theorem hasDerivAt_avg_path (A : ι → Finset V) (J δ : ι → ℝ) (B : Finset V) (t : ℝ) :
    HasDerivAt (fun t => avg A (fun a => J a + t * δ a) B)
      ((∑ a, δ a * (corr₂ A (fun a => J a + t * δ a) B (A a) * Z A (fun a => J a + t * δ a) -
          corr A (fun a => J a + t * δ a) B * corr A (fun a => J a + t * δ a) (A a))) /
        Z A (fun a => J a + t * δ a) ^ 2) t := by
  have hc := hasDerivAt_sum_weight A J δ (fun S => spinProd S B) t
  have hz := hasDerivAt_sum_weight A J δ (fun _ => 1) t
  simp only [one_mul] at hz
  have h := hc.fun_div hz (Z_pos A (fun a => J a + t * δ a)).ne'
  have hfun : (fun t => avg A (fun a => J a + t * δ a) B) = fun y =>
      (∑ S : Finset V, spinProd S B * Real.exp (energy A (fun a => J a + y * δ a) S)) /
        ∑ S : Finset V, Real.exp (energy A (fun a => J a + y * δ a) S) := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  have h1 : ∑ S : Finset V, spinProd S B * Real.exp (energy A (fun a => J a + t * δ a) S) *
      energy A δ S = ∑ a, δ a * corr₂ A (fun a => J a + t * δ a) B (A a) := by
    rw [sum_mul_energy]
    exact Finset.sum_congr rfl fun a _ => by
      rw [corr₂]
      exact congrArg _ (Finset.sum_congr rfl fun S _ => by ring)
  have h2 : ∑ S : Finset V, Real.exp (energy A (fun a => J a + t * δ a) S) * energy A δ S =
      ∑ a, δ a * corr A (fun a => J a + t * δ a) (A a) := by
    rw [sum_mul_energy]
    exact Finset.sum_congr rfl fun a _ => by
      rw [corr]
      exact congrArg _ (Finset.sum_congr rfl fun S _ => by ring)
  rw [h1, h2]
  change ((∑ a, δ a * corr₂ A (fun a => J a + t * δ a) B (A a)) * Z A (fun a => J a + t * δ a) -
      corr A (fun a => J a + t * δ a) B * ∑ a, δ a * corr A (fun a => J a + t * δ a) (A a)) /
        Z A (fun a => J a + t * δ a) ^ 2 = _
  congr 1
  rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- [proved-standard; formal-checked] **A ferromagnet's correlations grow with every coupling.**
`0 ≤ J ≤ J'` coupling by coupling gives `⟨s^B⟩_J ≤ ⟨s^B⟩_J'`. -/
theorem avg_mono (A : ι → Finset V) {J J' : ι → ℝ} (hJ : ∀ a, 0 ≤ J a)
    (hJJ' : ∀ a, J a ≤ J' a) (B : Finset V) : avg A J B ≤ avg A J' B := by
  set δ : ι → ℝ := fun a => J' a - J a with hδ
  have hδ0 : ∀ a, 0 ≤ δ a := fun a => sub_nonneg.mpr (hJJ' a)
  set f : ℝ → ℝ := fun t => avg A (fun a => J a + t * δ a) B with hf
  have hpath : ∀ t, 0 ≤ t → ∀ a, 0 ≤ J a + t * δ a := fun t ht a =>
    add_nonneg (hJ a) (mul_nonneg ht (hδ0 a))
  have hderiv := fun t => hasDerivAt_avg_path A J δ B t
  have hmono : MonotoneOn f (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
    · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
    · exact fun t _ => (hderiv t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hderiv t).deriv]
      refine div_nonneg (Finset.sum_nonneg fun a _ => mul_nonneg (hδ0 a) ?_) (sq_nonneg _)
      have := griffiths_second A _ (hpath t (le_of_lt ht)) B (A a)
      linarith [mul_comm (Z A (fun a => J a + t * δ a)) (corr₂ A (fun a => J a + t * δ a) B (A a))]
  have h01 := hmono (Set.mem_Ici.mpr le_rfl) (show (1 : ℝ) ∈ Set.Ici 0 by norm_num) zero_le_one
  have e0 : (fun a => J a + (0 : ℝ) * δ a) = J := by funext a; ring
  have e1 : (fun a => J a + (1 : ℝ) * δ a) = J' := by funext a; rw [hδ]; ring
  simpa only [hf, e0, e1] using h01

end Holonics.Coupling.Griffiths

section Audit

open Holonics.Coupling.Griffiths

#print axioms sum_monomial
#print axioms sum_monomial_mul_exp_nonneg
#print axioms griffiths_first
#print axioms griffiths_second
#print axioms avg_mul_le_avg₂
#print axioms hasDerivAt_avg_path
#print axioms avg_mono

end Audit
