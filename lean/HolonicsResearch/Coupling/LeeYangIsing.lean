import HolonicsResearch.Coupling.LeeYangCircle

/-!
# The Lee–Yang theorem for the Ising partition function: its zeros in the field lie on the imaginary axis

Source record:
`research/records/2026-11-19_THE_ISING_PARTITION_FUNCTION_IS_THE_LOCK_POLYNOMIAL_SO_A_FERROMAGNETS_ZEROS_IN_THE_FIELD_LIE_ON_THE_IMAGINARY_AXIS_AND_AN_ANTIFERROMAGNETS_DO_NOT.md`.

`Coupling/LeeYangCircle` proves the circle theorem for the lock polynomial
`lockPoly a z = ∑ S, (∏ i ∈ S, ∏ j ∈ Sᶜ, a i j) · ∏ i ∈ S, z i` and states, in its header only,
that the polynomial is the Ising partition function up to a monomial.  This module writes the
partition function and proves the identity, so the theorem reaches the physical statement.

[definition] A finite set `V` of sites, exchange energies `J : V → V → ℝ` (symmetric), an inverse
temperature `β` and complex fields `h : V → ℂ`.  A configuration is the set `S` of sites whose
spin is up; `spin S i` is `1` on `S` and `−1` off it (a configuration `σ : V → {±1}` is its set of
up sites, one to one).  The partition function is

  `isingZ J β h = ∑ S, exp (β/2 · ∑ i, ∑ j, J i j sᵢ sⱼ + β · ∑ i, h i sᵢ)`,

the double sum over ordered pairs, so each pair `{i, j}` is weighed once by `J i j` with the
factor `½`; a diagonal entry `J i i` adds the constant `β J i i / 2` and moves no zero.

[proved-standard; formal-checked] What is proved.

1. **The cut identity** (`coupling_sum_eq`, `field_sum_eq`): with `J` symmetric,
   `∑ i, ∑ j, J i j sᵢ sⱼ = ∑ i, ∑ j, J i j − 4 ∑ i ∈ S, ∑ j ∈ Sᶜ, J i j` and
   `∑ i, h i sᵢ = 2 ∑ i ∈ S, h i − ∑ i, h i`: only the pairs a configuration's cut separates
   cost energy, and only its up sites feel the field.
2. **The partition function is the lock polynomial** (`isingZ_eq_lockPoly`):
   `isingZ J β h = exp (β/2 · ∑ J − β ∑ h) · lockPoly (exp (−2β J)) (exp (2β h))`.
3. **No zero in either half-plane** (`isingZ_ne_zero_of_re_pos`, `isingZ_ne_zero_of_re_neg`): for
   a ferromagnet (`J ≥ 0`) at `β > 0`, if every field has positive real part, or every field has
   negative real part, the partition function does not vanish (Lee and Yang 1952 with
   site-dependent fields, through Asano's contraction).
4. **The Lee–Yang theorem** (`lee_yang_ising`): with one common field, `isingZ J β h = 0` gives
   `Re h = 0`; the zeros in the fugacity `exp (2β h)` lie on the unit circle
   (`lee_yang_ising_fugacity`).
5. **The ferromagnet is load-bearing** (`antiferromagnet_zero_off_axis`): two sites with exchange
   `−K < 0` at any `β > 0` have a zero of the partition function in a field with nonzero real part.

[interpretation] `agent-inferred` for the reading on the objects; the physics is standard.  The
free energy per site is `−(1/β) log Z / |V|`; a phase transition is a point where its limit over
growing `V` is not analytic.  At finite `V` the partition function has finitely many zeros in
the field, and by item 4 every one of them sits on the imaginary axis, so a real nonzero field
stays at a fixed distance from them; the only place where the zeros can close in on the real axis
as `V` grows is the origin, `h = 0`.  That is why a ferromagnet can order only at zero field.

**What this does not state.**  No limit over growing `V`: the density of zeros on the circle, the
thermodynamic limit of the free energy and its analyticity off `h = 0` are not formalized.  Spins
are `±1` (the Ising model); the extensions of Lee and Yang's theorem to other single-spin
distributions (Griffiths, Simon and Griffiths, Newman) and to quantum models are not here.  The
exchange `J` is symmetric and the fields enter linearly.

**Computational object.**  The helical pair interaction: a site is a lock with two sheets, an
exchange is a pair contact whose weight `exp (−2β J)` is paid when the cut separates its ends,
and the field is each lock's fugacity.  Of the winding guide's six objects: the pair (the
exchanges), faces and placement (a configuration's up set is a face; the zeros' placement on the
axis) and the cell holonomy (the half-turn of every spin at once, `S ↦ Sᶜ`, is the reversal that
fixes the axis); the helix, the tube and the tower thread stay attached.

**Consumers.**  The atlas row `thermal.ising-lee-yang`, beside `parametron.lee-yang-circle` and
`parametron.ising-lock`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Coupling.LeeYangIsing

open Finset Holonics.Coupling.LeeYangCircle

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The partition function -/

/-- [definition] The spin of site `i` in the configuration whose up sites are `S`. -/
def spin (S : Finset V) (i : V) : ℝ := if i ∈ S then 1 else -1

/-- [definition] The exponent of a configuration's Boltzmann weight,
`β/2 · ∑ i, ∑ j, J i j sᵢ sⱼ + β · ∑ i, h i sᵢ`. -/
def exponent (J : V → V → ℝ) (β : ℝ) (h : V → ℂ) (S : Finset V) : ℂ :=
  ((β / 2 * ∑ i, ∑ j, J i j * spin S i * spin S j : ℝ) : ℂ) + β * ∑ i, h i * spin S i

/-- [definition] **The Ising partition function** with exchanges `J`, inverse temperature `β`
and complex fields `h`, summed over the configurations (their sets of up sites). -/
def isingZ (J : V → V → ℝ) (β : ℝ) (h : V → ℂ) : ℂ :=
  ∑ S : Finset V, Complex.exp (exponent J β h S)

/-! ## The cut identity -/

omit [Fintype V] in
theorem spin_of_mem {S : Finset V} {i : V} (hi : i ∈ S) : spin S i = 1 := if_pos hi

theorem spin_of_mem_compl {S : Finset V} {i : V} (hi : i ∈ Sᶜ) : spin S i = -1 :=
  if_neg (Finset.mem_compl.mp hi)

/-- A sum weighed by the spins is the sum over the up sites less the sum over the down sites. -/
theorem sum_mul_spin (S : Finset V) (f : V → ℝ) :
    ∑ j, f j * spin S j = ∑ j ∈ S, f j - ∑ j ∈ Sᶜ, f j := by
  rw [← Finset.sum_add_sum_compl S (fun j => f j * spin S j)]
  have h1 : ∑ j ∈ S, f j * spin S j = ∑ j ∈ S, f j :=
    Finset.sum_congr rfl fun j hj => by rw [spin_of_mem hj, mul_one]
  have h2 : ∑ j ∈ Sᶜ, f j * spin S j = -∑ j ∈ Sᶜ, f j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => by rw [spin_of_mem_compl hj, mul_neg_one]
  rw [h1, h2, sub_eq_add_neg]

theorem sum_mul_spin_complex (S : Finset V) (f : V → ℂ) :
    ∑ j, f j * spin S j = ∑ j ∈ S, f j - ∑ j ∈ Sᶜ, f j := by
  rw [← Finset.sum_add_sum_compl S (fun j => f j * (spin S j : ℂ))]
  have h1 : ∑ j ∈ S, f j * (spin S j : ℂ) = ∑ j ∈ S, f j :=
    Finset.sum_congr rfl fun j hj => by rw [spin_of_mem hj, Complex.ofReal_one, mul_one]
  have h2 : ∑ j ∈ Sᶜ, f j * (spin S j : ℂ) = -∑ j ∈ Sᶜ, f j := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j hj => by
      rw [spin_of_mem_compl hj, Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one]
  rw [h1, h2, sub_eq_add_neg]

/-- [proved-standard; formal-checked] **The cut identity for the exchange.**  For a symmetric
exchange, `∑ i, ∑ j, J i j sᵢ sⱼ = ∑ i, ∑ j, J i j − 4 ∑ i ∈ S, ∑ j ∈ Sᶜ, J i j`. -/
theorem coupling_sum_eq (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i) (S : Finset V) :
    ∑ i, ∑ j, J i j * spin S i * spin S j =
      ∑ i, ∑ j, J i j - 4 * ∑ i ∈ S, ∑ j ∈ Sᶜ, J i j := by
  have hinner : ∀ i, ∑ j, J i j * spin S i * spin S j =
      (∑ j ∈ S, J i j - ∑ j ∈ Sᶜ, J i j) * spin S i := by
    intro i
    rw [← sum_mul_spin S (fun j => J i j), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [hinner]
  rw [sum_mul_spin]
  have hfull : ∀ i, ∑ j, J i j = ∑ j ∈ S, J i j + ∑ j ∈ Sᶜ, J i j := fun i =>
    (Finset.sum_add_sum_compl S (J i)).symm
  simp_rw [hfull]
  rw [← Finset.sum_add_sum_compl S (fun i => ∑ j ∈ S, J i j + ∑ j ∈ Sᶜ, J i j)]
  have hswap : ∑ i ∈ Sᶜ, ∑ j ∈ S, J i j = ∑ i ∈ S, ∑ j ∈ Sᶜ, J i j := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hJ j i
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  linear_combination (-2) * hswap

/-- [proved-standard; formal-checked] **The field term.**  `∑ i, h i sᵢ = 2 ∑ i ∈ S, h i − ∑ i, h i`. -/
theorem field_sum_eq (h : V → ℂ) (S : Finset V) :
    ∑ i, h i * spin S i = 2 * ∑ i ∈ S, h i - ∑ i, h i := by
  rw [sum_mul_spin_complex, ← Finset.sum_add_sum_compl S h]
  ring

/-! ## The partition function is the lock polynomial -/

/-- [definition] The lock couplings of an exchange at `β`: `a i j = exp (−2β J i j)`. -/
def lockCoupling (J : V → V → ℝ) (β : ℝ) : V → V → ℝ := fun i j => Real.exp (-2 * β * J i j)

/-- [definition] The fugacities of the fields at `β`: `z i = exp (2β h i)`. -/
def fugacity (β : ℝ) (h : V → ℂ) : V → ℂ := fun i => Complex.exp (2 * β * h i)

/-- One configuration's Boltzmann weight is the prefactor times its lock-polynomial term. -/
theorem exp_exponent (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i) (β : ℝ) (h : V → ℂ)
    (S : Finset V) :
    Complex.exp (exponent J β h S) =
      Complex.exp (((β / 2 * ∑ i, ∑ j, J i j : ℝ) : ℂ) - β * ∑ i, h i) *
        ((∏ i ∈ S, ∏ j ∈ Sᶜ, (lockCoupling J β i j : ℂ)) * ∏ i ∈ S, fugacity β h i) := by
  have hcut : ∏ i ∈ S, ∏ j ∈ Sᶜ, (lockCoupling J β i j : ℂ) =
      Complex.exp (((-2 * β * ∑ i ∈ S, ∑ j ∈ Sᶜ, J i j : ℝ) : ℂ)) := by
    rw [Finset.mul_sum, Complex.ofReal_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Complex.ofReal_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [lockCoupling, Complex.ofReal_exp]
  have hfug : ∏ i ∈ S, fugacity β h i = Complex.exp (2 * β * ∑ i ∈ S, h i) := by
    rw [Finset.mul_sum, Complex.exp_sum]
    rfl
  rw [hcut, hfug, ← Complex.exp_add, ← Complex.exp_add, exponent, coupling_sum_eq J hJ S,
    field_sum_eq h S]
  congr 1
  push_cast
  ring

/-- [proved-standard; formal-checked] **The Ising partition function is the lock polynomial.**
`isingZ J β h = exp (β/2 · ∑ J − β ∑ h) · lockPoly (exp (−2β J)) (exp (2β h))`. -/
theorem isingZ_eq_lockPoly (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i) (β : ℝ) (h : V → ℂ) :
    isingZ J β h =
      Complex.exp (((β / 2 * ∑ i, ∑ j, J i j : ℝ) : ℂ) - β * ∑ i, h i) *
        lockPoly (lockCoupling J β) (fugacity β h) := by
  rw [isingZ, lockPoly, Finset.mul_sum]
  exact Finset.sum_congr rfl fun S _ => exp_exponent J hJ β h S

/-! ## The Lee–Yang theorem -/

omit [Fintype V] [DecidableEq V] in
/-- The lock couplings of a ferromagnet lie in `(0, 1]`. -/
theorem lockCoupling_mem (J : V → V → ℝ) (hJ0 : ∀ i j, 0 ≤ J i j) {β : ℝ} (hβ : 0 ≤ β)
    (i j : V) : -1 ≤ lockCoupling J β i j ∧ lockCoupling J β i j ≤ 1 := by
  refine ⟨le_trans (by norm_num) (Real.exp_pos _).le, ?_⟩
  rw [lockCoupling, Real.exp_le_one_iff]
  have := mul_nonneg hβ (hJ0 i j)
  nlinarith

omit [Fintype V] [DecidableEq V] in
theorem lockCoupling_symm (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i) (β : ℝ) (i j : V) :
    lockCoupling J β i j = lockCoupling J β j i := by
  rw [lockCoupling, lockCoupling, hJ]

omit [Fintype V] [DecidableEq V] in
theorem norm_fugacity (β : ℝ) (h : V → ℂ) (i : V) :
    ‖fugacity β h i‖ = Real.exp (2 * β * (h i).re) := by
  rw [fugacity, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re]

/-- [proved-standard; formal-checked] **No zero with every field in the right half-plane**
(Lee and Yang 1952).  A ferromagnet at `β > 0` whose fields all have positive real part has a
nonzero partition function. -/
theorem isingZ_ne_zero_of_re_pos (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i)
    (hJ0 : ∀ i j, 0 ≤ J i j) {β : ℝ} (hβ : 0 < β) (h : V → ℂ) (hh : ∀ i, 0 < (h i).re) :
    isingZ J β h ≠ 0 := by
  rw [isingZ_eq_lockPoly J hJ]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  refine lockPoly_ne_zero_of_one_lt_norm _ (fun i j _ => lockCoupling_symm J hJ β i j)
    (fun i j _ => (lockCoupling_mem J hJ0 hβ.le i j).1)
    (fun i j _ => (lockCoupling_mem J hJ0 hβ.le i j).2) _ fun i => ?_
  rw [norm_fugacity, Real.one_lt_exp_iff]
  have := hh i
  positivity

/-- [proved-standard; formal-checked] **No zero with every field in the left half-plane.** -/
theorem isingZ_ne_zero_of_re_neg (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i)
    (hJ0 : ∀ i j, 0 ≤ J i j) {β : ℝ} (hβ : 0 < β) (h : V → ℂ) (hh : ∀ i, (h i).re < 0) :
    isingZ J β h ≠ 0 := by
  rw [isingZ_eq_lockPoly J hJ]
  refine mul_ne_zero (Complex.exp_ne_zero _) ?_
  refine lockPoly_ne_zero_of_norm_lt_one _ (fun i j _ => lockCoupling_symm J hJ β i j)
    (fun i j _ => (lockCoupling_mem J hJ0 hβ.le i j).1)
    (fun i j _ => (lockCoupling_mem J hJ0 hβ.le i j).2) _ fun i => ?_
  rw [norm_fugacity, Real.exp_lt_one_iff]
  exact mul_neg_of_pos_of_neg (by positivity) (hh i)

/-- [proved-standard; formal-checked] **The Lee–Yang theorem for the Ising model.**  For a
ferromagnet at `β > 0` in one common complex field `h`, every zero of the partition function lies
on the imaginary axis. -/
theorem lee_yang_ising (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i) (hJ0 : ∀ i j, 0 ≤ J i j)
    {β : ℝ} (hβ : 0 < β) (h : ℂ) (hz : isingZ J β (fun _ => h) = 0) : h.re = 0 := by
  rcases lt_trichotomy h.re 0 with hlt | heq | hgt
  · exact absurd hz (isingZ_ne_zero_of_re_neg J hJ hJ0 hβ _ fun _ => hlt)
  · exact heq
  · exact absurd hz (isingZ_ne_zero_of_re_pos J hJ hJ0 hβ _ fun _ => hgt)

/-- [proved-standard; formal-checked] **The same zeros in the fugacity** `exp (2β h)` lie on
the unit circle. -/
theorem lee_yang_ising_fugacity (J : V → V → ℝ) (hJ : ∀ i j, J i j = J j i)
    (hJ0 : ∀ i j, 0 ≤ J i j) {β : ℝ} (hβ : 0 < β) (h : ℂ)
    (hz : isingZ J β (fun _ => h) = 0) : ‖Complex.exp (2 * β * h)‖ = 1 := by
  have hre := lee_yang_ising J hJ hJ0 hβ h hz
  have := norm_fugacity (V := V) β (fun _ => h)
  rw [Complex.norm_exp]
  simp [Complex.mul_re, hre]

/-! ## The ferromagnet is load-bearing -/

/-- [counterexample; formal-checked] **An antiferromagnet's zeros leave the axis.**  Two sites
with exchange `−K`, `K > 0`, at any `β > 0`: some complex field with nonzero real part is a zero
of the partition function. -/
theorem antiferromagnet_zero_off_axis {K : ℝ} (hK : 0 < K) {β : ℝ} (hβ : 0 < β) :
    ∃ h : ℂ, h.re ≠ 0 ∧ isingZ (V := Fin 2) (fun _ _ => -K) β (fun _ => h) = 0 := by
  have hy : 1 < Real.exp (2 * β * K) := Real.one_lt_exp_iff.mpr (by positivity)
  obtain ⟨ζ, hζ, hζn⟩ := two_locks_off_circle_of_one_lt _ hy
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  refine ⟨Complex.log ζ / (2 * β), ?_, ?_⟩
  · rw [Complex.div_re]
    have hden : (2 * (β : ℂ)).re = 2 * β := by simp
    have hden' : (2 * (β : ℂ)).im = 0 := by simp
    rw [hden, hden', Complex.log_re]
    have hlog : Real.log ‖ζ‖ ≠ 0 := by
      intro h0
      rcases Real.log_eq_zero.mp h0 with h1 | h1 | h1
      · exact hζ0 (norm_eq_zero.mp h1)
      · exact hζn h1
      · have := norm_nonneg ζ
        linarith
    have hn : Complex.normSq (2 * (β : ℂ)) ≠ 0 := by
      rw [Ne, Complex.normSq_eq_zero]
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr hβ.ne')
    simp only [mul_zero, zero_div, add_zero]
    exact div_ne_zero (mul_ne_zero hlog (by positivity)) hn
  · rw [isingZ_eq_lockPoly _ (fun _ _ => rfl)]
    refine mul_eq_zero_of_right _ ?_
    have hfug : fugacity (V := Fin 2) β (fun _ => Complex.log ζ / (2 * β)) = fun _ => ζ := by
      funext i
      rw [fugacity]
      have hβc : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hβ.ne'
      have : (2 : ℂ) * β * (Complex.log ζ / (2 * β)) = Complex.log ζ := by
        field_simp
      rw [this, Complex.exp_log hζ0]
    rw [hfug, lockPoly_two]
    have hc : (lockCoupling (V := Fin 2) (fun _ _ => -K) β 0 1 : ℂ) =
        (Real.exp (2 * β * K) : ℂ) := by
      rw [lockCoupling]
      congr 2
      ring
    have hc' : (lockCoupling (V := Fin 2) (fun _ _ => -K) β 1 0 : ℂ) =
        (Real.exp (2 * β * K) : ℂ) := by
      rw [lockCoupling]
      congr 2
      ring
    rw [hc, hc']
    linear_combination hζ

end Holonics.Coupling.LeeYangIsing

section Audit

open Holonics.Coupling.LeeYangIsing

#print axioms coupling_sum_eq
#print axioms field_sum_eq
#print axioms isingZ_eq_lockPoly
#print axioms isingZ_ne_zero_of_re_pos
#print axioms isingZ_ne_zero_of_re_neg
#print axioms lee_yang_ising
#print axioms lee_yang_ising_fugacity
#print axioms antiferromagnet_zero_off_axis

end Audit
