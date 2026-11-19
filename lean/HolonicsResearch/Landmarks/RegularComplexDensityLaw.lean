import Mathlib
import HolonicsResearch.Landmarks.RegularComplexZeros

/-!
# The density law of a tempered complex: mixing, the boundary, the free sets, relaxation and the floor

Source record: `research/records/2026-11-18_AN_ABELIAN_COVER_FACTORS_THROUGH_ITS_CHARACTERS_A_TEMPERED_COMPLEX_MIXES_AT_ITS_HALF_THE_FLUIDS_TRIADS_DO_NO_WORK_SO_EVERY_TRUNCATION_FLOWS_FOR_ALL_TIME_AND_HARD_LEFSCHETZ_IS_A_POSITIVE_COMMUTATOR.md` (§4; it follows
`research/records/2026-11-18_THE_HALF_IS_THE_POSITIVITY_OF_THE_REVERSALS_OWN_FORM_A_FINITE_COMPLEX_HAS_ITS_ZEROS_AND_COUNT_IN_LEAN_COUPLED_LOCKS_KEEP_THE_CIRCLE_TWO_TORIS_INDEX_THEOREM_IS_A_NORM_AND_BELOW_REYNOLDS_ONE_THE_COUNT_DECIDES.md`,
whose §5.3 places a regular complex's zeros on the circle and bounds its closed-walk count).

[proved-standard; formal-checked] `Landmarks/RegularComplexZeros` reads a regular complex's modes
through its dart determinant and the count of its closed walks.  This module reads the same modes
through how the complex spreads density: how many contacts two sets of cells share, how many leave
a set, how large a set without inner contacts can be, how fast a walk forgets where it started,
and how small the modes can be.  Each is one inequality on mean-free cell functions, so the module
works in three layers.

**Layer 1, a balanced operator.**  `A` is a real symmetric matrix whose rows all sum to `d`
(`Balanced A d`), `n` the count of cells, and a bound on the mean-free functions (`∑ f = 0`): the
two-sided `|A f|² ≤ μ² |f|²` (`MeanFreeBound`), the one-sided `f·A f ≤ μ₂ |f|²`
(`MeanFreeUpper`) or the lower `−ν |f|² ≤ f·A f` (`MeanFreeLower`).  `contacts A S T` is
`∑_{v ∈ S} ∑_{w ∈ T} A v w`.

* **The split** (`Balanced.contacts_eq`): `contacts S T = d|S||T|/n + (centred S)·A(centred T)`,
  where `centred S` is the indicator of `S` less its mean, of square `|S|(1 − |S|/n)`
  (`centred_dotProduct_self`).
* **M2, mixing** (`Balanced.mixing_sq`, `Balanced.mixing`, `Balanced.mixing_plain`):
  `|contacts S T − d|S||T|/n| ≤ μ √(|S|(1 − |S|/n) · |T|(1 − |T|/n)) ≤ μ √(|S||T|)`.
* **M3, the boundary** (`Balanced.cheeger`): `(d − μ₂)|S|(n − |S|)/n ≤ contacts S Sᶜ`, the easy
  side of Cheeger's inequality.
* **M4, free sets** (`Balanced.hoffman`, `Balanced.hoffman_density`): a set with no inner contacts
  has `|S|(d + ν) ≤ nν`, so `|S|/n ≤ ν/(d + ν)` (Hoffman's bound).
* **M5, relaxation** (`Balanced.relaxation`, `relEntropy_le`, `Balanced.relEntropy_walk_le`): the
  walk `P = A/d` from a density `p` has `|Pᵗp − u|² ≤ (μ/d)^(2t)|p − u|²` against the uniform
  density `u = 1/n`; with `A ≥ 0` and `p ≥ 0` its relative entropy `∑ p log(np)` is at most
  `n|Pᵗp − u|²` (from `log x ≤ x − 1`) and so at most `(n − 1)(μ/d)^(2t)` nats.
* **M7, the floor** (`Balanced.normSq_mulVec_le`, `Balanced.floor`): with natural entries (any
  `A v w ≤ (A v w)²`), `nd ≤ ∑ A v w² ≤ d² + (n − 1)μ²`, so `d(n − d) ≤ (n − 1)μ²`.
* The two-sided bound gives the other two at the same `μ` (`MeanFreeBound.upper`,
  `MeanFreeBound.lower`).

**Layer 2, the bridge from the modes** (`Balanced.meanFreeBound_of_eigen`,
`Balanced.meanFreeUpper_of_eigen`, `Balanced.meanFreeLower_of_eigen`).  In the eigenbasis of `A`
a mean-free function has no coefficient on the mode `i₀` at `d` when that mode is the only one
there (`Balanced.coeff_trivial_eq_zero`; the constant's coefficients sit on the modes at `d`,
`Balanced.eigen_mul_coeff_ones`).  If a second mode sits at `d`, the hypothesis on it already bounds
`d` itself.  Either way a bound `F (λ j) ≤ M` on every mode but `i₀` gives `∑ F(λ j) c_j² ≤ M ∑ c_j²`
on mean-free functions (`Balanced.sum_coeff_le`), and the three bounds follow.

**Layer 3, the complex.**  For a finite complex with `q + 1` darts at every cell the cell operator
`IharaBass.adjacency ℝ a b` is balanced at `d = q + 1` with natural entries (`balanced_adjacency`,
`adjacency_nonneg`, `adjacency_le_sq`), and its modes are `RegularComplexZeros.eigen a b`.  With the
count's mode `eigen i₀ = q + 1` and every other mode `λ² ≤ μ²` (`meanFreeBound_of_modes`, and the
one-sided and lower forms), and at the tempered value `μ = 2√q` of `walkCount_bound`
(`tempered_meanFreeBound`):
* mixing within `2√q √(|S||T|)` (`tempered_mixing`, `tempered_mixing_plain`);
* the walk closes on the uniform density at `2√q/(q + 1)` a tick (`tempered_relaxation`), and its
  relative entropy is at most `(n − 1)(4q/(q + 1)²)ᵗ` nats (`tempered_relEntropy`);
* every set has at least `(q + 1 − 2√q)|S|(n − |S|)/n` contacts leaving it (`tempered_boundary`);
* a set with no inner contacts holds at most a share `2√q/(q + 1 + 2√q)` of the cells
  (`tempered_hoffman`);
* the floor: `(q + 1)(n − (q + 1)) ≤ (n − 1)μ²` for any bound `μ` on the other modes
  (`floor_of_modes`): the modes other than the count cannot all sit near zero, and the smallest
  admissible `μ` tends to `√(q + 1)` as `n` grows.  This sits below the tempered value `2√q`
  (`q + 1 ≤ 4q`), so it constrains complexes that are better than tempered, never a tempered one;
  the floor at `2√q` itself is Alon and Boppana's and is not stated here.

## What this does not state

* No converse of mixing: that a complex whose contacts mix within `μ√(|S||T|)` has its modes
  within a multiple of `μ` (Bilu and Linial) is not proved.
* No Alon–Boppana limit here: the floor here is the trace's, `μ² ≥ (q + 1)(n − q − 1)/(n − 1)`,
  which tends to `q + 1`, not to `4q`.  The floor at `2√q` from walks on the covering tree is
  `Landmarks/TreeWalkFloor` (`alon_boppana`: below `μ² < 4q`, every large enough complex has a
  mode other than the count past `μ`).
* No hard side of Cheeger: only the bound of the boundary from below by the gap.
* The bridge asks `λ² ≤ μ²` of every mode but one, so a second component (another mode at `q + 1`)
  or two sides (a mode at `−(q + 1)`) put `μ ≥ q + 1` and the statements, though true, say little.
* Nothing about the integers' own zeta function: a regular complex is a finite specimen of the half.

Limits: the bounds are stated for real `d`, `μ`, `ν`; the walk is the plain step `A/d` (no lazy
step), and the entropy is in nats against the uniform density.

The computational object is the helical pair interaction read as a density: a contact spreads what
a cell holds to its neighbours, and the bounds say how evenly a tempered complex spreads it.  Of the
winding guide's six general objects this touches the pair (contacts between sets) and the cell
holonomy (the modes of the cell operator, through the eigenbasis); the helix, faces and placement,
the tube and the tower thread stay attached.

Consumers: the atlas rows `trace.tempered-density-law` (its own), `trace.regular-zeros-on-circle`
(its neighbour: the same tempered hypothesis read by density), `key.connection-cheeger` and
`rh.escape-threshold-half`, and the third record of November 18 on the half (§4).

No `sorry`, no `axiom`, no `native_decide`.
-/

open Matrix

namespace Holonics.Landmarks.RegularComplexDensityLaw

section Balanced

variable {V : Type*} [Fintype V]

/-- [definition] The constant cell function. -/
def ones : V → ℝ := fun _ => 1

omit [Fintype V] in
/-- [proved-derived; formal-checked] The constant function reads `1` at every cell. -/
@[simp] theorem ones_apply (v : V) : (ones : V → ℝ) v = 1 := rfl

/-- [proved-derived; formal-checked] Pairing with the constant is the sum. -/
theorem ones_dotProduct (f : V → ℝ) : ones ⬝ᵥ f = ∑ v, f v := by
  simp [dotProduct, ones]

/-- [proved-derived; formal-checked] Pairing with the constant is the sum. -/
theorem dotProduct_ones (f : V → ℝ) : f ⬝ᵥ ones = ∑ v, f v := by
  simp [dotProduct, ones]

/-- [proved-derived; formal-checked] The constant's square is the count of cells. -/
theorem ones_dotProduct_ones : (ones : V → ℝ) ⬝ᵥ ones = Fintype.card V := by
  simp [dotProduct, ones]

/-- [definition] A symmetric cell operator with every row summing to `d`. -/
structure Balanced (A : Matrix V V ℝ) (d : ℝ) : Prop where
  symm : Aᵀ = A
  rows : ∀ v, ∑ w, A v w = d

variable {A : Matrix V V ℝ} {d : ℝ}

/-- [proved-derived; formal-checked] A balanced operator fixes the constant at `d`: `A 1 = d·1`. -/
theorem Balanced.mulVec_ones (h : Balanced A d) : A *ᵥ ones = d • ones := by
  funext v
  simp [Matrix.mulVec, dotProduct, ones, h.rows v]

/-- [proved-derived; formal-checked] A balanced operator multiplies the total by `d`: `∑ (A f) = d ∑ f`
(its columns sum to `d` too, by symmetry). -/
theorem Balanced.sum_mulVec (h : Balanced A d) (f : V → ℝ) :
    ∑ v, (A *ᵥ f) v = d * ∑ v, f v := by
  rw [← ones_dotProduct, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h.symm,
    h.mulVec_ones, smul_dotProduct, ones_dotProduct, smul_eq_mul]

/-- [proved-derived; formal-checked] A balanced operator keeps a mean-free function mean-free. -/
theorem Balanced.ones_dotProduct_mulVec (h : Balanced A d) {f : V → ℝ} (hf : ∑ v, f v = 0) :
    ones ⬝ᵥ (A *ᵥ f) = 0 := by
  rw [ones_dotProduct, h.sum_mulVec, hf, mul_zero]

/-- [proved-derived; formal-checked] A mean-free function is orthogonal to `A 1`. -/
theorem Balanced.dotProduct_mulVec_ones (h : Balanced A d) {f : V → ℝ} (hf : ∑ v, f v = 0) :
    f ⬝ᵥ (A *ᵥ ones) = 0 := by
  rw [h.mulVec_ones, dotProduct_smul, dotProduct_ones, hf, smul_zero]

end Balanced

section Sets

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- [definition] The indicator of a set of cells. -/
def ind (S : Finset V) : V → ℝ := fun v => if v ∈ S then 1 else 0

/-- [definition] The contacts from `S` to `T`: the sum of `A v w` over `v ∈ S`, `w ∈ T`. -/
def contacts (A : Matrix V V ℝ) (S T : Finset V) : ℝ := ∑ v ∈ S, ∑ w ∈ T, A v w

/-- [proved-derived; formal-checked] The indicator of `S` sums to `|S|`. -/
theorem sum_ind (S : Finset V) : ∑ v, ind S v = S.card := by
  simp [ind]

/-- [proved-derived; formal-checked] The contacts are the pairing `1_S · A 1_T`. -/
theorem contacts_eq_dotProduct (A : Matrix V V ℝ) (S T : Finset V) :
    contacts A S T = ind S ⬝ᵥ (A *ᵥ ind T) := by
  simp only [contacts, dotProduct, Matrix.mulVec, ind, ite_mul, one_mul, zero_mul, mul_ite,
    mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← Finset.sum_filter]
  simp

/-- [definition] The centred indicator: `ind S − (|S|/n)·1`, the indicator less its mean. -/
noncomputable def centred (S : Finset V) : V → ℝ :=
  ind S - ((S.card : ℝ) / Fintype.card V) • ones

variable [Nonempty V]

omit [DecidableEq V] in
/-- [proved-derived; formal-checked] A nonempty complex has a positive count of cells. -/
theorem card_pos_real : (0 : ℝ) < Fintype.card V := by
  exact_mod_cast Fintype.card_pos

/-- [proved-derived; formal-checked] The centred indicator is mean-free. -/
theorem sum_centred (S : Finset V) : ∑ v, centred S v = 0 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  simp only [centred, Pi.sub_apply, Pi.smul_apply, ones_apply, smul_eq_mul, mul_one,
    Finset.sum_sub_distrib, sum_ind, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

omit [Nonempty V] in
/-- [proved-derived; formal-checked] The indicator is its centred part plus its mean. -/
theorem ind_eq_centred_add (S : Finset V) :
    ind S = centred S + ((S.card : ℝ) / Fintype.card V) • ones := by
  simp [centred]

omit [Nonempty V] in
/-- [proved-derived; formal-checked] The indicator's square is `|S|`. -/
theorem ind_dotProduct_ind (S : Finset V) : ind S ⬝ᵥ ind S = S.card := by
  simp [dotProduct, ind]

/-- [proved-derived; formal-checked] The centred indicator's square is `|S|(1 − |S|/n)`. -/
theorem centred_dotProduct_self (S : Finset V) :
    centred S ⬝ᵥ centred S =
      (S.card : ℝ) * (1 - (S.card : ℝ) / Fintype.card V) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  simp only [centred, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    ind_dotProduct_ind, ones_dotProduct, dotProduct_ones, sum_ind, smul_eq_mul, ones_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp
  ring

omit [DecidableEq V] [Nonempty V] in
/-- [proved-derived; formal-checked] A set holds at most all the cells. -/
theorem card_le_card_univ_real (S : Finset V) : (S.card : ℝ) ≤ Fintype.card V := by
  exact_mod_cast Finset.card_le_univ S

omit [DecidableEq V] in
/-- [proved-derived; formal-checked] A set's share of the cells is at most one. -/
theorem one_sub_ratio_nonneg (S : Finset V) :
    0 ≤ 1 - (S.card : ℝ) / Fintype.card V := by
  rw [sub_nonneg, div_le_one card_pos_real]
  exact card_le_card_univ_real S

variable {A : Matrix V V ℝ} {d : ℝ}

/-- [proved-standard; formal-checked] **The contacts split into their mean and a centred part.**
`contacts S T = d|S||T|/n + (centred S)·A(centred T)`. -/
theorem Balanced.contacts_eq (h : Balanced A d) (S T : Finset V) :
    contacts A S T =
      d * S.card * T.card / Fintype.card V + centred S ⬝ᵥ (A *ᵥ centred T) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  rw [contacts_eq_dotProduct, ind_eq_centred_add S, ind_eq_centred_add T]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
    dotProduct_smul, smul_dotProduct, h.ones_dotProduct_mulVec (sum_centred T), h.mulVec_ones,
    dotProduct_ones, sum_centred S, smul_eq_mul, ones_apply,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  field_simp
  ring

end Sets

section Bounds

variable {V : Type*} [Fintype V]

/-- [proved-derived; formal-checked] A square is nonnegative. -/
theorem dotProduct_self_nonneg' (x : V → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

/-- [proved-standard; formal-checked] Cauchy–Schwarz for the pairing of cell functions. -/
theorem dotProduct_sq_le (x y : V → ℝ) : (x ⬝ᵥ y) ^ 2 ≤ (x ⬝ᵥ x) * (y ⬝ᵥ y) := by
  simpa [dotProduct, sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y

/-- [definition] The two-sided bound on mean-free cell functions: `|A f|² ≤ μ² |f|²`. -/
def MeanFreeBound (A : Matrix V V ℝ) (μ : ℝ) : Prop :=
  ∀ f : V → ℝ, ∑ v, f v = 0 → (A *ᵥ f) ⬝ᵥ (A *ᵥ f) ≤ μ ^ 2 * (f ⬝ᵥ f)

/-- [definition] The one-sided bound on mean-free cell functions: `f·A f ≤ μ₂ |f|²`. -/
def MeanFreeUpper (A : Matrix V V ℝ) (μ₂ : ℝ) : Prop :=
  ∀ f : V → ℝ, ∑ v, f v = 0 → f ⬝ᵥ (A *ᵥ f) ≤ μ₂ * (f ⬝ᵥ f)

/-- [definition] The lower bound on mean-free cell functions: `−ν |f|² ≤ f·A f`. -/
def MeanFreeLower (A : Matrix V V ℝ) (ν : ℝ) : Prop :=
  ∀ f : V → ℝ, ∑ v, f v = 0 → -ν * (f ⬝ᵥ f) ≤ f ⬝ᵥ (A *ᵥ f)

variable {A : Matrix V V ℝ} {μ : ℝ}

/-- [proved-derived; formal-checked] The two-sided bound bounds the quadratic form: `|f·A f| ≤ μ|f|²`. -/
theorem MeanFreeBound.abs_quadratic_le (hμ : MeanFreeBound A μ) (hμ0 : 0 ≤ μ) {f : V → ℝ}
    (hf : ∑ v, f v = 0) : |f ⬝ᵥ (A *ᵥ f)| ≤ μ * (f ⬝ᵥ f) := by
  have h1 := dotProduct_sq_le f (A *ᵥ f)
  have h2 := hμ f hf
  have hff := dotProduct_self_nonneg' f
  have h3 : (f ⬝ᵥ (A *ᵥ f)) ^ 2 ≤ (μ * (f ⬝ᵥ f)) ^ 2 := by
    calc _ ≤ (f ⬝ᵥ f) * ((A *ᵥ f) ⬝ᵥ (A *ᵥ f)) := h1
      _ ≤ (f ⬝ᵥ f) * (μ ^ 2 * (f ⬝ᵥ f)) := mul_le_mul_of_nonneg_left h2 hff
      _ = _ := by ring
  exact _root_.abs_le.mpr (abs_le_of_sq_le_sq' h3 (mul_nonneg hμ0 hff))

/-- [proved-derived; formal-checked] The two-sided bound gives the one-sided bound at the same `μ`. -/
theorem MeanFreeBound.upper (hμ : MeanFreeBound A μ) (hμ0 : 0 ≤ μ) : MeanFreeUpper A μ :=
  fun _ hf => (_root_.abs_le.mp (hμ.abs_quadratic_le hμ0 hf)).2

/-- [proved-derived; formal-checked] The two-sided bound gives the lower bound at the same `μ`. -/
theorem MeanFreeBound.lower (hμ : MeanFreeBound A μ) (hμ0 : 0 ≤ μ) : MeanFreeLower A μ :=
  fun _ hf => by
    have := (_root_.abs_le.mp (hμ.abs_quadratic_le hμ0 hf)).1
    linarith

end Bounds

section Laws

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Matrix V V ℝ} {d μ : ℝ}

/-- [proved-standard; formal-checked] **M2, the mixing law, squared.** -/
theorem Balanced.mixing_sq (h : Balanced A d) (hμ : MeanFreeBound A μ) (S T : Finset V) :
    (contacts A S T - d * S.card * T.card / Fintype.card V) ^ 2 ≤
      μ ^ 2 * ((S.card : ℝ) * (1 - S.card / Fintype.card V)) *
        ((T.card : ℝ) * (1 - T.card / Fintype.card V)) := by
  rw [h.contacts_eq, add_sub_cancel_left, ← centred_dotProduct_self, ← centred_dotProduct_self]
  calc _ ≤ (centred S ⬝ᵥ centred S) * ((A *ᵥ centred T) ⬝ᵥ (A *ᵥ centred T)) :=
        dotProduct_sq_le _ _
    _ ≤ (centred S ⬝ᵥ centred S) * (μ ^ 2 * (centred T ⬝ᵥ centred T)) :=
        mul_le_mul_of_nonneg_left (hμ _ (sum_centred T)) (dotProduct_self_nonneg' _)
    _ = _ := by ring

/-- [proved-standard; formal-checked] **M2, the mixing law.** -/
theorem Balanced.mixing (h : Balanced A d) (hμ : MeanFreeBound A μ) (hμ0 : 0 ≤ μ)
    (S T : Finset V) :
    |contacts A S T - d * S.card * T.card / Fintype.card V| ≤
      μ * √(((S.card : ℝ) * (1 - S.card / Fintype.card V)) *
        ((T.card : ℝ) * (1 - T.card / Fintype.card V))) := by
  have h1 := Real.abs_le_sqrt (h.mixing_sq hμ S T)
  rw [mul_assoc (μ ^ 2), Real.sqrt_mul (sq_nonneg μ), Real.sqrt_sq hμ0] at h1
  exact h1

/-- [proved-standard; formal-checked] **M2, the plain mixing law**: within `μ √(|S||T|)`. -/
theorem Balanced.mixing_plain (h : Balanced A d) (hμ : MeanFreeBound A μ) (hμ0 : 0 ≤ μ)
    (S T : Finset V) :
    |contacts A S T - d * S.card * T.card / Fintype.card V| ≤
      μ * √((S.card : ℝ) * T.card) := by
  refine (h.mixing hμ hμ0 S T).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hμ0)
  have hS := one_sub_ratio_nonneg S
  have hT := one_sub_ratio_nonneg T
  have hS1 : 1 - (S.card : ℝ) / Fintype.card V ≤ 1 := by
    have : 0 ≤ (S.card : ℝ) / Fintype.card V := div_nonneg (Nat.cast_nonneg _) card_pos_real.le
    linarith
  have hT1 : 1 - (T.card : ℝ) / Fintype.card V ≤ 1 := by
    have : 0 ≤ (T.card : ℝ) / Fintype.card V := div_nonneg (Nat.cast_nonneg _) card_pos_real.le
    linarith
  have hs : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have ht : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  have e1 : (S.card : ℝ) * (1 - S.card / Fintype.card V) ≤ S.card := by nlinarith
  have e2 : (T.card : ℝ) * (1 - T.card / Fintype.card V) ≤ T.card := by nlinarith
  exact mul_le_mul e1 e2 (mul_nonneg ht hT) hs

omit [Nonempty V] [DecidableEq V] in
/-- [proved-derived; formal-checked] A set's contacts with every cell are `d|S|`. -/
theorem Balanced.contacts_univ (h : Balanced A d) (S : Finset V) :
    contacts A S Finset.univ = d * S.card := by
  simp [contacts, h.rows, mul_comm]

omit [Nonempty V] in
/-- [proved-derived; formal-checked] A set's contacts split between `T` and its complement. -/
theorem contacts_add_compl (A : Matrix V V ℝ) (S T : Finset V) :
    contacts A S T + contacts A S Tᶜ = contacts A S Finset.univ := by
  simp only [contacts, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun v _ => Finset.sum_add_sum_compl T (A v)

/-- [proved-standard; formal-checked] **M3, the easy side of Cheeger's inequality.** -/
theorem Balanced.cheeger (h : Balanced A d) {μ₂ : ℝ} (hμ₂ : MeanFreeUpper A μ₂) (S : Finset V) :
    (d - μ₂) * S.card * (Fintype.card V - S.card) / Fintype.card V ≤ contacts A S Sᶜ := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  have hsplit := contacts_add_compl A S S
  rw [h.contacts_univ] at hsplit
  have hSS := h.contacts_eq S S
  have hup := hμ₂ _ (sum_centred S)
  rw [centred_dotProduct_self] at hup
  have e : (d - μ₂) * S.card * (Fintype.card V - S.card) / Fintype.card V =
      d * S.card - d * S.card * S.card / Fintype.card V -
        μ₂ * ((S.card : ℝ) * (1 - S.card / Fintype.card V)) := by
    field_simp
  rw [e]
  linarith

/-- [proved-standard; formal-checked] **M4, Hoffman's bound**: a set with no contacts inside has
`|S|(d + ν) ≤ n ν`. -/
theorem Balanced.hoffman (h : Balanced A d) {ν : ℝ} (hν : MeanFreeLower A ν) (hν0 : 0 ≤ ν)
    {S : Finset V} (hS : contacts A S S = 0) :
    (S.card : ℝ) * (d + ν) ≤ Fintype.card V * ν := by
  have hnpos := (card_pos_real (V := V))
  have hn : (Fintype.card V : ℝ) ≠ 0 := hnpos.ne'
  have hSS := h.contacts_eq S S
  have hlow := hν _ (sum_centred S)
  rw [centred_dotProduct_self] at hlow
  set s : ℝ := (S.card : ℝ) with hs_def
  set n : ℝ := (Fintype.card V : ℝ) with hn_def
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have key0 : d * s * s / n ≤ ν * (s * (1 - s / n)) := by linarith
  have key1 : d * s * s ≤ ν * s * (n - s) := by
    have e1 : d * s * s = (d * s * s / n) * n := by field_simp
    have e2 : ν * s * (n - s) = ν * (s * (1 - s / n)) * n := by field_simp
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_right key0 hnpos.le
  rcases hs0.lt_or_eq with hs | hs
  · have : s * (s * (d + ν) - n * ν) ≤ 0 := by nlinarith
    have : s * (d + ν) - n * ν ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos hs hc
      linarith
    linarith
  · rw [← hs]
    simp only [zero_mul]
    exact mul_nonneg hnpos.le hν0

/-- [proved-standard; formal-checked] **M4, Hoffman's density**: `|S|/n ≤ ν/(d + ν)`. -/
theorem Balanced.hoffman_density (h : Balanced A d) {ν : ℝ} (hν : MeanFreeLower A ν)
    (hν0 : 0 ≤ ν) (hdν : 0 < d + ν) {S : Finset V} (hS : contacts A S S = 0) :
    (S.card : ℝ) / Fintype.card V ≤ ν / (d + ν) := by
  rw [div_le_div_iff₀ card_pos_real hdν]
  have := h.hoffman hν hν0 hS
  linarith

end Laws

section Walk

variable {V : Type*} [Fintype V] [Nonempty V]
variable {A : Matrix V V ℝ} {d μ : ℝ}

/-- [definition] The uniform density `1/n` on the cells. -/
noncomputable def uniform (V : Type*) [Fintype V] : V → ℝ := (Fintype.card V : ℝ)⁻¹ • ones

/-- [definition] The walk's step `P = A/d` taken `t` times from the density `p`. -/
noncomputable def walk (A : Matrix V V ℝ) (d : ℝ) (t : ℕ) (p : V → ℝ) : V → ℝ :=
  (fun f => d⁻¹ • (A *ᵥ f))^[t] p

omit [Nonempty V] in
/-- [proved-derived; formal-checked] The walk at zero ticks is the density itself. -/
theorem walk_zero (p : V → ℝ) : walk A d 0 p = p := rfl

omit [Nonempty V] in
/-- [proved-derived; formal-checked] One more tick is one more step `A/d`. -/
theorem walk_succ (t : ℕ) (p : V → ℝ) : walk A d (t + 1) p = d⁻¹ • (A *ᵥ walk A d t p) :=
  Function.iterate_succ_apply' _ _ _

/-- [proved-derived; formal-checked] The uniform density sums to one. -/
theorem sum_uniform : ∑ v, uniform V v = 1 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  simp [uniform, Finset.sum_const, Finset.card_univ, hn]

omit [Nonempty V] in
/-- [proved-derived; formal-checked] The walk keeps the total. -/
theorem Balanced.sum_walk (h : Balanced A d) (hd : d ≠ 0) {p : V → ℝ} (t : ℕ) :
    ∑ v, walk A d t p v = ∑ v, p v := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [walk_succ]
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, h.sum_mulVec, ih]
    field_simp

/-- [proved-derived; formal-checked] The walk fixes the uniform density. -/
theorem Balanced.step_uniform (h : Balanced A d) (hd : d ≠ 0) :
    d⁻¹ • (A *ᵥ uniform V) = uniform V := by
  rw [uniform, Matrix.mulVec_smul, h.mulVec_ones, smul_smul, smul_smul]
  congr 1
  field_simp

/-- [proved-derived; formal-checked] The walk's distance from the uniform density moves by the step itself. -/
theorem Balanced.walk_sub_uniform (h : Balanced A d) (hd : d ≠ 0) (t : ℕ) (p : V → ℝ) :
    walk A d (t + 1) p - uniform V = d⁻¹ • (A *ᵥ (walk A d t p - uniform V)) := by
  rw [walk_succ, Matrix.mulVec_sub, smul_sub, h.step_uniform hd]

/-- [proved-derived; formal-checked] A density less the uniform one is mean-free. -/
theorem sum_sub_uniform {p : V → ℝ} (hp : ∑ v, p v = 1) : ∑ v, (p - uniform V) v = 0 := by
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, hp, sum_uniform, sub_self]

/-- [proved-standard; formal-checked] **M5, relaxation.**  For a density `p` (`∑ p = 1`) the walk
`P = A/d` closes on the uniform density at the ratio `μ/d` a tick:
`|Pᵗ p − u|² ≤ (μ/d)^(2t) |p − u|²`. -/
theorem Balanced.relaxation (h : Balanced A d) (hd : d ≠ 0) (hμ : MeanFreeBound A μ)
    {p : V → ℝ} (hp : ∑ v, p v = 1) (t : ℕ) :
    (walk A d t p - uniform V) ⬝ᵥ (walk A d t p - uniform V) ≤
      (μ / d) ^ (2 * t) * ((p - uniform V) ⬝ᵥ (p - uniform V)) := by
  induction t with
  | zero => simp [walk_zero]
  | succ t ih =>
    have hsum : ∑ v, (walk A d t p - uniform V) v = 0 := by
      apply sum_sub_uniform
      rw [h.sum_walk hd, hp]
    rw [h.walk_sub_uniform hd, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have hstep := hμ _ hsum
    have hc : (0 : ℝ) ≤ (μ / d) ^ 2 := sq_nonneg _
    calc d⁻¹ * (d⁻¹ * ((A *ᵥ (walk A d t p - uniform V)) ⬝ᵥ (A *ᵥ (walk A d t p - uniform V))))
        = (d⁻¹) ^ 2 * ((A *ᵥ (walk A d t p - uniform V)) ⬝ᵥ
            (A *ᵥ (walk A d t p - uniform V))) := by ring
      _ ≤ (d⁻¹) ^ 2 * (μ ^ 2 * ((walk A d t p - uniform V) ⬝ᵥ (walk A d t p - uniform V))) :=
          mul_le_mul_of_nonneg_left hstep (sq_nonneg _)
      _ = (μ / d) ^ 2 * ((walk A d t p - uniform V) ⬝ᵥ (walk A d t p - uniform V)) := by ring
      _ ≤ (μ / d) ^ 2 * ((μ / d) ^ (2 * t) * ((p - uniform V) ⬝ᵥ (p - uniform V))) :=
          mul_le_mul_of_nonneg_left ih hc
      _ = (μ / d) ^ (2 * (t + 1)) * ((p - uniform V) ⬝ᵥ (p - uniform V)) := by ring

/-- [definition] The relative entropy of a density against the uniform one, in nats:
`∑ p log (n p)`. -/
noncomputable def relEntropy (p : V → ℝ) : ℝ :=
  ∑ v, p v * Real.log (Fintype.card V * p v)

/-- [proved-derived; formal-checked] A density's squared distance from the uniform one is `|q|² − 1/n`. -/
theorem dist_uniform_sq {q : V → ℝ} (hq : ∑ v, q v = 1) :
    (q - uniform V) ⬝ᵥ (q - uniform V) = q ⬝ᵥ q - (Fintype.card V : ℝ)⁻¹ := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  simp only [uniform, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
    dotProduct_ones, ones_dotProduct, hq, smul_eq_mul, mul_one, ones_apply, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- [proved-standard; formal-checked] The relative entropy of a density is at most `n` times its
squared distance from the uniform density (from `log x ≤ x − 1`). -/
theorem relEntropy_le {q : V → ℝ} (hq0 : ∀ v, 0 ≤ q v) (hq : ∑ v, q v = 1) :
    relEntropy q ≤ Fintype.card V * ((q - uniform V) ⬝ᵥ (q - uniform V)) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  have hnpos := (card_pos_real (V := V))
  rw [dist_uniform_sq hq]
  have hterm : ∀ v, q v * Real.log (Fintype.card V * q v) ≤
      Fintype.card V * (q v * q v) - q v := by
    intro v
    rcases (hq0 v).lt_or_eq with hpos | hzero
    · have hl := Real.log_le_sub_one_of_pos (mul_pos hnpos hpos)
      nlinarith [hq0 v]
    · rw [← hzero]
      simp
  calc relEntropy q ≤ ∑ v, (Fintype.card V * (q v * q v) - q v) :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = Fintype.card V * (q ⬝ᵥ q - (Fintype.card V : ℝ)⁻¹) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hq]
        simp only [dotProduct]
        field_simp

omit [Nonempty V] in
/-- [proved-derived; formal-checked] With `A ≥ 0` and `d > 0` the walk keeps a density nonnegative. -/
theorem walk_nonneg (hA : ∀ v w, 0 ≤ A v w) (hd : 0 < d) {p : V → ℝ} (hp : ∀ v, 0 ≤ p v)
    (t : ℕ) (v : V) : 0 ≤ walk A d t p v := by
  induction t generalizing v with
  | zero => exact hp v
  | succ t ih =>
    rw [walk_succ]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    exact mul_nonneg (inv_nonneg.mpr hd.le)
      (Finset.sum_nonneg fun w _ => mul_nonneg (hA v w) (ih w))

/-- [proved-derived; formal-checked] A nonnegative density is within `1 − 1/n` of the uniform one, squared. -/
theorem dist_uniform_sq_le {p : V → ℝ} (hp0 : ∀ v, 0 ≤ p v) (hp : ∑ v, p v = 1) :
    (p - uniform V) ⬝ᵥ (p - uniform V) ≤ 1 - (Fintype.card V : ℝ)⁻¹ := by
  rw [dist_uniform_sq hp]
  have hle : ∀ v, p v ≤ 1 := fun v => by
    rw [← hp]
    exact Finset.single_le_sum (fun w _ => hp0 w) (Finset.mem_univ v)
  have : p ⬝ᵥ p ≤ 1 := by
    rw [← hp]
    exact Finset.sum_le_sum fun v _ => by nlinarith [hp0 v, hle v]
  linarith

/-- [proved-standard; formal-checked] **M5, the entropy's decay.**  With `A ≥ 0`, `d > 0` and a
density `p ≥ 0`, the walk's relative entropy against the uniform density is at most
`(n − 1)(μ/d)^(2t)` nats. -/
theorem Balanced.relEntropy_walk_le (h : Balanced A d) (hA : ∀ v w, 0 ≤ A v w) (hd : 0 < d)
    (hμ : MeanFreeBound A μ) {p : V → ℝ} (hp0 : ∀ v, 0 ≤ p v) (hp : ∑ v, p v = 1) (t : ℕ) :
    relEntropy (walk A d t p) ≤ (Fintype.card V - 1) * (μ / d) ^ (2 * t) := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  have hnpos := (card_pos_real (V := V))
  have hsum : ∑ v, walk A d t p v = 1 := by rw [h.sum_walk hd.ne', hp]
  have h1 := relEntropy_le (walk_nonneg hA hd hp0 t) hsum
  have h2 := h.relaxation hd.ne' hμ hp t
  have h3 := dist_uniform_sq_le hp0 hp
  have hc : (0 : ℝ) ≤ (μ / d) ^ (2 * t) := by
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg _) _
  calc relEntropy (walk A d t p)
      ≤ Fintype.card V * ((μ / d) ^ (2 * t) * ((p - uniform V) ⬝ᵥ (p - uniform V))) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hnpos.le)
    _ ≤ Fintype.card V * ((μ / d) ^ (2 * t) * (1 - (Fintype.card V : ℝ)⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hc) hnpos.le
    _ = (Fintype.card V - 1) * (μ / d) ^ (2 * t) := by
        field_simp

end Walk

section Floor

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
variable {A : Matrix V V ℝ} {d μ : ℝ}

omit [DecidableEq V] in
/-- [proved-derived; formal-checked] Any cell function splits into its mean and a centred part,
and `|A f|² ≤ μ² (|f|² − (∑ f)²/n) + d² (∑ f)²/n`. -/
theorem Balanced.normSq_mulVec_le (h : Balanced A d) (hμ : MeanFreeBound A μ) (f : V → ℝ) :
    (A *ᵥ f) ⬝ᵥ (A *ᵥ f) ≤
      μ ^ 2 * (f ⬝ᵥ f - (∑ v, f v) ^ 2 / Fintype.card V) +
        d ^ 2 * (∑ v, f v) ^ 2 / Fintype.card V := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  set m : ℝ := ∑ v, f v with hm
  set g : V → ℝ := f - (m / Fintype.card V) • ones with hg
  have hgsum : ∑ v, g v = 0 := by
    simp only [hg, Pi.sub_apply, Pi.smul_apply, ones_apply, smul_eq_mul, mul_one,
      Finset.sum_sub_distrib, ← hm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have hf : f = g + (m / Fintype.card V) • ones := by simp [hg]
  have hgg : g ⬝ᵥ g = f ⬝ᵥ f - m ^ 2 / Fintype.card V := by
    simp only [hg, sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul,
      dotProduct_ones, ones_dotProduct, ← hm, smul_eq_mul, ones_apply, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp
    ring
  have hAg := hμ g hgsum
  have hcross : (A *ᵥ g) ⬝ᵥ ones = 0 := by
    rw [dotProduct_ones, h.sum_mulVec, hgsum, mul_zero]
  have hcross' : ones ⬝ᵥ (A *ᵥ g) = 0 := by
    rw [dotProduct_comm, hcross]
  have hexp : (A *ᵥ f) ⬝ᵥ (A *ᵥ f) =
      (A *ᵥ g) ⬝ᵥ (A *ᵥ g) + d ^ 2 * m ^ 2 / Fintype.card V := by
    rw [hf]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, h.mulVec_ones, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, hcross, hcross', ones_dotProduct_ones,
      smul_eq_mul]
    field_simp
    ring
  rw [hexp, ← hgg]
  linarith

/-- [proved-standard; formal-checked] **M7, the floor.**  If the entries of `A` are naturals (any
`A v w ≤ (A v w)²` will do), the square sum counts at least every contact once, and
`d (n − d) ≤ (n − 1) μ²`: the mean-free modes cannot all be small. -/
theorem Balanced.floor (h : Balanced A d) (hμ : MeanFreeBound A μ)
    (hint : ∀ v w, A v w ≤ A v w ^ 2) :
    d * (Fintype.card V - d) ≤ (Fintype.card V - 1) * μ ^ 2 := by
  have hn : (Fintype.card V : ℝ) ≠ 0 := card_pos_real.ne'
  set Q : ℝ := ∑ v, ∑ w, A v w ^ 2 with hQ
  have hlow : Fintype.card V * d ≤ Q := by
    have : ∑ v, ∑ w, A v w = Fintype.card V * d := by
      simp [h.rows, Finset.sum_const, Finset.card_univ]
    rw [← this]
    exact Finset.sum_le_sum fun v _ => Finset.sum_le_sum fun w _ => hint v w
  have hcol : ∀ v, (A *ᵥ ind {v}) ⬝ᵥ (A *ᵥ ind {v}) = ∑ w, A w v ^ 2 := by
    intro v
    have : A *ᵥ ind {v} = fun w => A w v := by
      funext w
      simp [Matrix.mulVec, dotProduct, ind]
    rw [this]
    simp [dotProduct, sq]
  have hone : ∀ v : V, ∑ x, ind {v} x = 1 := fun v => by simp [sum_ind]
  have hone' : ∀ v : V, ind {v} ⬝ᵥ ind {v} = 1 := fun v => by simp [ind_dotProduct_ind]
  have hup : Q ≤ Fintype.card V * (μ ^ 2 * (1 - 1 / Fintype.card V) +
      d ^ 2 * 1 / Fintype.card V) := by
    have hQ' : Q = ∑ v, (A *ᵥ ind {v}) ⬝ᵥ (A *ᵥ ind {v}) := by
      simp only [hcol, hQ]
      exact Finset.sum_comm
    rw [hQ']
    calc ∑ v, (A *ᵥ ind {v}) ⬝ᵥ (A *ᵥ ind {v})
        ≤ ∑ _v : V, (μ ^ 2 * (1 - 1 / Fintype.card V) + d ^ 2 * 1 / Fintype.card V) := by
          refine Finset.sum_le_sum fun v _ => ?_
          have := h.normSq_mulVec_le hμ (ind {v})
          rwa [hone, hone', one_pow] at this
      _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
  have : Fintype.card V * (μ ^ 2 * (1 - 1 / Fintype.card V) + d ^ 2 * 1 / Fintype.card V) =
      (Fintype.card V - 1) * μ ^ 2 + d ^ 2 := by
    field_simp
  rw [this] at hup
  nlinarith

end Floor

section Bridge

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {A : Matrix V V ℝ} {d : ℝ}

omit [DecidableEq V] in
theorem Balanced.isHermitian (h : Balanced A d) : A.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact h.symm

variable (hA : A.IsHermitian)

/-- [definition] The coefficients of a cell function in the eigenbasis of a symmetric `A`. -/
noncomputable def coeff (f : V → ℝ) : V → ℝ :=
  star (hA.eigenvectorUnitary : Matrix V V ℝ) *ᵥ f

/-- [proved-derived; formal-checked] Over the reals the adjoint of the eigenvector matrix is its transpose. -/
theorem star_eigenvectorUnitary_eq :
    star (hA.eigenvectorUnitary : Matrix V V ℝ) = (hA.eigenvectorUnitary : Matrix V V ℝ)ᵀ := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]

/-- [proved-derived; formal-checked] The eigenvector matrix keeps the pairing. -/
theorem unitary_dotProduct (x y : V → ℝ) :
    ((hA.eigenvectorUnitary : Matrix V V ℝ) *ᵥ x) ⬝ᵥ ((hA.eigenvectorUnitary : Matrix V V ℝ) *ᵥ y) =
      x ⬝ᵥ y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    ← star_eigenvectorUnitary_eq hA, Unitary.coe_star_mul_self, Matrix.one_mulVec]

/-- [proved-derived; formal-checked] A function is recovered from its coefficients. -/
theorem unitary_mulVec_coeff (f : V → ℝ) :
    (hA.eigenvectorUnitary : Matrix V V ℝ) *ᵥ coeff hA f = f := by
  rw [coeff, Matrix.mulVec_mulVec, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.prop,
    Matrix.one_mulVec]

/-- [proved-standard; formal-checked] The spectral theorem read over the reals:
`A = U diag(λ) Uᵀ`. -/
theorem spectral_real :
    A = (hA.eigenvectorUnitary : Matrix V V ℝ) * Matrix.diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix V V ℝ) := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  simp

/-- [proved-derived; formal-checked] `A f` read through the coefficients. -/
theorem mulVec_eq_unitary_diagonal (f : V → ℝ) :
    A *ᵥ f = (hA.eigenvectorUnitary : Matrix V V ℝ) *ᵥ
      (Matrix.diagonal hA.eigenvalues *ᵥ coeff hA f) := by
  conv_lhs => rw [spectral_real hA]
  rw [coeff, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- [proved-derived; formal-checked] The coefficients of `A f` are the modes times the coefficients of `f`. -/
theorem coeff_diagonal (f : V → ℝ) :
    Matrix.diagonal hA.eigenvalues *ᵥ coeff hA f = coeff hA (A *ᵥ f) := by
  conv_rhs => rw [coeff, mulVec_eq_unitary_diagonal hA f, Matrix.mulVec_mulVec,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.prop, Matrix.one_mulVec]

/-- [proved-derived; formal-checked] Parseval: `|f|² = ∑ c_j²`. -/
theorem dotProduct_self_eq_coeff (f : V → ℝ) : f ⬝ᵥ f = ∑ j, coeff hA f j ^ 2 := by
  conv_lhs => rw [← unitary_mulVec_coeff hA f]
  rw [unitary_dotProduct]
  simp [dotProduct, sq]

/-- [proved-derived; formal-checked] The quadratic form in the eigenbasis: `f·A f = ∑ λ_j c_j²`. -/
theorem quadratic_eq_coeff (f : V → ℝ) :
    f ⬝ᵥ (A *ᵥ f) = ∑ j, hA.eigenvalues j * coeff hA f j ^ 2 := by
  rw [mulVec_eq_unitary_diagonal hA f]
  nth_rewrite 1 [← unitary_mulVec_coeff hA f]
  rw [unitary_dotProduct]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived; formal-checked] The square of `A f` in the eigenbasis: `|A f|² = ∑ λ_j² c_j²`. -/
theorem normSq_eq_coeff (f : V → ℝ) :
    (A *ᵥ f) ⬝ᵥ (A *ᵥ f) = ∑ j, hA.eigenvalues j ^ 2 * coeff hA f j ^ 2 := by
  rw [mulVec_eq_unitary_diagonal hA f, unitary_dotProduct]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- [proved-derived; formal-checked] The constant function's coefficients sit on the modes at `d`:
`λ j · c¹ j = d · c¹ j`. -/
theorem Balanced.eigen_mul_coeff_ones (h : Balanced A d) (j : V) :
    hA.eigenvalues j * coeff hA ones j = d * coeff hA ones j := by
  have h1 := coeff_diagonal hA ones
  rw [h.mulVec_ones] at h1
  have h2 : coeff hA (d • ones) = d • coeff hA ones := Matrix.mulVec_smul _ _ _
  rw [h2] at h1
  have := congrFun h1 j
  simpa [Matrix.mulVec_diagonal] using this

/-- [proved-derived; formal-checked] **The bridge's core.**  If the mode `i₀` at `d` is the only
mode at `d`, a mean-free function has no coefficient on it. -/
theorem Balanced.coeff_trivial_eq_zero [Nonempty V] (h : Balanced A d) {i₀ : V}
    (hsimple : ∀ j, j ≠ i₀ → hA.eigenvalues j ≠ d) {f : V → ℝ} (hf : ∑ v, f v = 0) :
    coeff hA f i₀ = 0 := by
  have hz : ∀ j, j ≠ i₀ → coeff hA ones j = 0 := fun j hj => by
    have := h.eigen_mul_coeff_ones hA j
    have hne := hsimple j hj
    have : (hA.eigenvalues j - d) * coeff hA ones j = 0 := by linarith
    rcases mul_eq_zero.mp this with h' | h'
    · exact absurd (sub_eq_zero.mp h') hne
    · exact h'
  have hsum : ones ⬝ᵥ f = coeff hA ones i₀ * coeff hA f i₀ := by
    conv_lhs => rw [← unitary_mulVec_coeff hA ones, ← unitary_mulVec_coeff hA f]
    rw [unitary_dotProduct, dotProduct]
    rw [Finset.sum_eq_single i₀ (fun j _ hj => by rw [hz j hj, zero_mul])
      (fun h' => absurd (Finset.mem_univ _) h')]
  rw [ones_dotProduct, hf] at hsum
  have hne : coeff hA ones i₀ ≠ 0 := by
    intro h0
    have hall : coeff hA ones = 0 := by
      funext j
      by_cases hj : j = i₀
      · rw [hj, h0]; rfl
      · exact hz j hj
    have := unitary_mulVec_coeff hA (ones : V → ℝ)
    rw [hall, Matrix.mulVec_zero] at this
    have := congrFun this (Classical.arbitrary V)
    simp at this
  rcases mul_eq_zero.mp hsum.symm with h' | h'
  · exact absurd h' hne
  · exact h'

/-- [proved-derived; formal-checked] **The bridge.**  With the mode `i₀` at `d` and a bound
`F (λ j) ≤ M` on every other mode, `∑ F(λ j) c j² ≤ M ∑ c j²` on mean-free functions.  If a second
mode sits at `d`, the bound holds at `i₀` too. -/
theorem Balanced.sum_coeff_le [Nonempty V] (h : Balanced A d) {i₀ : V}
    (h0 : hA.eigenvalues i₀ = d) (F : ℝ → ℝ) (M : ℝ)
    (hF : ∀ j, j ≠ i₀ → F (hA.eigenvalues j) ≤ M) {f : V → ℝ} (hf : ∑ v, f v = 0) :
    ∑ j, F (hA.eigenvalues j) * coeff hA f j ^ 2 ≤ M * ∑ j, coeff hA f j ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases hj : j = i₀
  · subst hj
    by_cases hs : ∀ k, k ≠ j → hA.eigenvalues k ≠ d
    · rw [h.coeff_trivial_eq_zero hA hs hf]
      simp
    · push Not at hs
      obtain ⟨k, hk, hkd⟩ := hs
      have : F (hA.eigenvalues j) ≤ M := by rw [h0, ← hkd]; exact hF k hk
      exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_right (hF j hj) (sq_nonneg _)

/-- [proved-derived; formal-checked] The two-sided bound from the modes. -/
theorem Balanced.meanFreeBound_of_eigen [Nonempty V] (h : Balanced A d) {i₀ : V}
    (h0 : hA.eigenvalues i₀ = d) {μ : ℝ} (hμ : ∀ j, j ≠ i₀ → hA.eigenvalues j ^ 2 ≤ μ ^ 2) :
    MeanFreeBound A μ := fun f hf => by
  rw [normSq_eq_coeff hA, dotProduct_self_eq_coeff hA]
  exact h.sum_coeff_le hA h0 (· ^ 2) (μ ^ 2) hμ hf

/-- [proved-derived; formal-checked] The one-sided bound from the modes. -/
theorem Balanced.meanFreeUpper_of_eigen [Nonempty V] (h : Balanced A d) {i₀ : V}
    (h0 : hA.eigenvalues i₀ = d) {μ₂ : ℝ} (hμ : ∀ j, j ≠ i₀ → hA.eigenvalues j ≤ μ₂) :
    MeanFreeUpper A μ₂ := fun f hf => by
  rw [quadratic_eq_coeff hA, dotProduct_self_eq_coeff hA]
  exact h.sum_coeff_le hA h0 id μ₂ hμ hf

/-- [proved-derived; formal-checked] The lower bound from the modes. -/
theorem Balanced.meanFreeLower_of_eigen [Nonempty V] (h : Balanced A d) {i₀ : V}
    (h0 : hA.eigenvalues i₀ = d) {ν : ℝ} (hν : ∀ j, j ≠ i₀ → -ν ≤ hA.eigenvalues j) :
    MeanFreeLower A ν := fun f hf => by
  rw [quadratic_eq_coeff hA, dotProduct_self_eq_coeff hA]
  have := h.sum_coeff_le hA h0 (fun x => -x) ν (fun j hj => by linarith [hν j hj]) hf
  have e : ∑ j, (fun x => -x) (hA.eigenvalues j) * coeff hA f j ^ 2 =
      -∑ j, hA.eigenvalues j * coeff hA f j ^ 2 := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e] at this
  linarith

end Bridge


/-! ## Layer 3: the complex with `q + 1` darts at every cell -/

/-- [proved-derived; formal-checked] The tempered value squared: `(2√q)² = 4q`. -/
theorem two_sqrt_sq (q : ℕ) : (2 * √(q : ℝ)) ^ 2 = 4 * (q : ℝ) := by
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
  norm_num

section Complex

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (a b : E → V)

/-- [proved-derived; formal-checked] A complex with `q + 1` darts leaving every cell has a balanced
cell operator at `d = q + 1`. -/
theorem balanced_adjacency {q : ℕ}
    (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1) :
    Balanced (IharaBass.adjacency ℝ a b) ((q : ℝ) + 1) where
  symm := IharaBass.adjacency_transpose ℝ a b
  rows v := by
    have := congrFun (RegularComplexZeros.adjacency_mulVec_one a b hreg) v
    simpa [Matrix.mulVec, dotProduct] using this

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] The cell operator's entries are counts, so nonnegative. -/
theorem adjacency_nonneg (v w : V) : 0 ≤ IharaBass.adjacency ℝ a b v w := by
  rw [IharaBass.adjacency_apply]
  exact Nat.cast_nonneg _

omit [Fintype V] [DecidableEq E] in
/-- [proved-derived; formal-checked] The cell operator's entries are naturals, so each is at most
its square. -/
theorem adjacency_le_sq (v w : V) :
    IharaBass.adjacency ℝ a b v w ≤ IharaBass.adjacency ℝ a b v w ^ 2 := by
  rw [IharaBass.adjacency_apply]
  exact_mod_cast Nat.le_self_pow two_ne_zero _

variable [Nonempty V] {q : ℕ}
  (hreg : ∀ v : V, (Finset.univ.filter fun d : E ⊕ E => IharaBass.src a b d = v).card = q + 1)
  {i₀ : V} (h0 : RegularComplexZeros.eigen a b i₀ = (q : ℝ) + 1)
include hreg h0

/-- [proved-derived; formal-checked] **The bridge on a complex**, two-sided: every mode but the
count's within `λ² ≤ μ²` gives `|A f|² ≤ μ²|f|²` on mean-free functions. -/
theorem meanFreeBound_of_modes {μ : ℝ}
    (hμ : ∀ i, i ≠ i₀ → RegularComplexZeros.eigen a b i ^ 2 ≤ μ ^ 2) :
    MeanFreeBound (IharaBass.adjacency ℝ a b) μ :=
  (balanced_adjacency a b hreg).meanFreeBound_of_eigen
    (RegularComplexZeros.adjacency_isHermitian a b) h0 hμ

/-- [proved-derived; formal-checked] The bridge on a complex, one-sided. -/
theorem meanFreeUpper_of_modes {μ₂ : ℝ}
    (hμ : ∀ i, i ≠ i₀ → RegularComplexZeros.eigen a b i ≤ μ₂) :
    MeanFreeUpper (IharaBass.adjacency ℝ a b) μ₂ :=
  (balanced_adjacency a b hreg).meanFreeUpper_of_eigen
    (RegularComplexZeros.adjacency_isHermitian a b) h0 hμ

/-- [proved-derived; formal-checked] The bridge on a complex, from below. -/
theorem meanFreeLower_of_modes {ν : ℝ}
    (hν : ∀ i, i ≠ i₀ → -ν ≤ RegularComplexZeros.eigen a b i) :
    MeanFreeLower (IharaBass.adjacency ℝ a b) ν :=
  (balanced_adjacency a b hreg).meanFreeLower_of_eigen
    (RegularComplexZeros.adjacency_isHermitian a b) h0 hν

/-- [proved-standard; formal-checked] **M7 on a complex, the floor.**  If every mode but the
count's has `λ² ≤ μ²`, then `(q + 1)(n − (q + 1)) ≤ (n − 1)μ²`. -/
theorem floor_of_modes {μ : ℝ}
    (hμ : ∀ i, i ≠ i₀ → RegularComplexZeros.eigen a b i ^ 2 ≤ μ ^ 2) :
    ((q : ℝ) + 1) * (Fintype.card V - ((q : ℝ) + 1)) ≤ (Fintype.card V - 1) * μ ^ 2 :=
  (balanced_adjacency a b hreg).floor (meanFreeBound_of_modes a b hreg h0 hμ)
    (adjacency_le_sq a b)


variable (htemp : ∀ i, i ≠ i₀ → RegularComplexZeros.eigen a b i ^ 2 ≤ 4 * (q : ℝ))
include htemp

/-- [proved-derived; formal-checked] **A tempered complex's mean-free bound**: `μ = 2√q`, the
hypothesis of `RegularComplexZeros.walkCount_bound`. -/
theorem tempered_meanFreeBound :
    MeanFreeBound (IharaBass.adjacency ℝ a b) (2 * √(q : ℝ)) :=
  meanFreeBound_of_modes a b hreg h0 fun i hi => by rw [two_sqrt_sq]; exact htemp i hi

/-- [proved-standard; formal-checked] **Mixing on a tempered complex.** -/
theorem tempered_mixing (S T : Finset V) :
    |contacts (IharaBass.adjacency ℝ a b) S T - ((q : ℝ) + 1) * S.card * T.card / Fintype.card V| ≤
      2 * √(q : ℝ) * √(((S.card : ℝ) * (1 - S.card / Fintype.card V)) *
        ((T.card : ℝ) * (1 - T.card / Fintype.card V))) :=
  (balanced_adjacency a b hreg).mixing (tempered_meanFreeBound a b hreg h0 htemp)
    (by positivity) S T

/-- [proved-standard; formal-checked] **Mixing on a tempered complex**, plain: the contacts of two
sets are their share `(q + 1)|S||T|/n` within `2√q √(|S||T|)`. -/
theorem tempered_mixing_plain (S T : Finset V) :
    |contacts (IharaBass.adjacency ℝ a b) S T - ((q : ℝ) + 1) * S.card * T.card / Fintype.card V| ≤
      2 * √(q : ℝ) * √((S.card : ℝ) * T.card) :=
  (balanced_adjacency a b hreg).mixing_plain (tempered_meanFreeBound a b hreg h0 htemp)
    (by positivity) S T

/-- [proved-standard; formal-checked] **Relaxation on a tempered complex**: the walk closes on the
uniform density at the ratio `2√q/(q + 1)` a tick. -/
theorem tempered_relaxation {p : V → ℝ} (hp : ∑ v, p v = 1) (t : ℕ) :
    (walk (IharaBass.adjacency ℝ a b) ((q : ℝ) + 1) t p - uniform V) ⬝ᵥ
        (walk (IharaBass.adjacency ℝ a b) ((q : ℝ) + 1) t p - uniform V) ≤
      (2 * √(q : ℝ) / ((q : ℝ) + 1)) ^ (2 * t) * ((p - uniform V) ⬝ᵥ (p - uniform V)) :=
  (balanced_adjacency a b hreg).relaxation (by positivity)
    (tempered_meanFreeBound a b hreg h0 htemp) hp t

/-- [proved-standard; formal-checked] **The entropy's decay on a tempered complex**: at most
`(n − 1)(4q/(q + 1)²)ᵗ` nats after `t` ticks. -/
theorem tempered_relEntropy {p : V → ℝ} (hp0 : ∀ v, 0 ≤ p v) (hp : ∑ v, p v = 1) (t : ℕ) :
    relEntropy (walk (IharaBass.adjacency ℝ a b) ((q : ℝ) + 1) t p) ≤
      (Fintype.card V - 1) * (4 * (q : ℝ) / ((q : ℝ) + 1) ^ 2) ^ t := by
  have h := (balanced_adjacency a b hreg).relEntropy_walk_le (adjacency_nonneg a b)
    (by positivity) (tempered_meanFreeBound a b hreg h0 htemp) hp0 hp t
  have e : (2 * √(q : ℝ) / ((q : ℝ) + 1)) ^ (2 * t) = (4 * (q : ℝ) / ((q : ℝ) + 1) ^ 2) ^ t := by
    rw [pow_mul, div_pow, two_sqrt_sq]
  rwa [e] at h

/-- [proved-standard; formal-checked] **The boundary of a tempered complex**: every set has at
least `(q + 1 − 2√q)|S|(n − |S|)/n` contacts leaving it. -/
theorem tempered_boundary (S : Finset V) :
    ((q : ℝ) + 1 - 2 * √(q : ℝ)) * S.card * (Fintype.card V - S.card) / Fintype.card V ≤
      contacts (IharaBass.adjacency ℝ a b) S Sᶜ :=
  (balanced_adjacency a b hreg).cheeger
    ((tempered_meanFreeBound a b hreg h0 htemp).upper (by positivity)) S

/-- [proved-standard; formal-checked] **Free sets of a tempered complex** (Hoffman): a set with no
inner contacts holds at most a share `2√q/(q + 1 + 2√q)` of the cells. -/
theorem tempered_hoffman {S : Finset V}
    (hS : contacts (IharaBass.adjacency ℝ a b) S S = 0) :
    (S.card : ℝ) / Fintype.card V ≤ 2 * √(q : ℝ) / ((q : ℝ) + 1 + 2 * √(q : ℝ)) :=
  (balanced_adjacency a b hreg).hoffman_density
    ((tempered_meanFreeBound a b hreg h0 htemp).lower (by positivity)) (by positivity)
    (by positivity) hS

end Complex

section Audit

#print axioms Balanced.contacts_eq
#print axioms Balanced.mixing_sq
#print axioms Balanced.mixing
#print axioms Balanced.mixing_plain
#print axioms Balanced.cheeger
#print axioms Balanced.hoffman
#print axioms Balanced.hoffman_density
#print axioms Balanced.relaxation
#print axioms relEntropy_le
#print axioms Balanced.relEntropy_walk_le
#print axioms Balanced.normSq_mulVec_le
#print axioms Balanced.floor
#print axioms Balanced.coeff_trivial_eq_zero
#print axioms Balanced.sum_coeff_le
#print axioms Balanced.meanFreeBound_of_eigen
#print axioms Balanced.meanFreeUpper_of_eigen
#print axioms Balanced.meanFreeLower_of_eigen
#print axioms balanced_adjacency
#print axioms floor_of_modes
#print axioms tempered_meanFreeBound
#print axioms tempered_mixing
#print axioms tempered_mixing_plain
#print axioms tempered_relaxation
#print axioms tempered_relEntropy
#print axioms tempered_boundary
#print axioms tempered_hoffman

end Audit

end Holonics.Landmarks.RegularComplexDensityLaw
