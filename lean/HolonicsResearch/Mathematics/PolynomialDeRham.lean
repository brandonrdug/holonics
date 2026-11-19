import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Gradient, curl and divergence on homogeneous polynomials of three variables: each kernel is the image before it

The Einstein record of November 11
(`research/records/2026-11-11_EINSTEINS_FIELD_PROGRAM_ON_THE_COMPLEX_THE_UNIFIED_FIELD_IS_A_TWO_WAY_FLOW_A_GRAIN_GIVES_THE_MASS_AND_A_PROBABILITY_IS_ITS_FLAT_PART.md`,
§14.4 and §14.12; atlas `gr.strength-alternating-count`) counts the free data a law leaves as an alternating count:
unknowns less equations plus the identities among the equations. Its ruler 10 checked, by rank over the rationals at
orders 2 to 6, the chain of homogeneous polynomials of three variables

```text
P_(n+1) --grad--> P_n³ --curl--> P_(n−1)³ --div--> P_(n−2)
```

and found each kernel the image before it, the curl leaving `3C(n+2, 2) − 3C(n+1, 2) + C(n, 2) = C(n+3, 2)` fields free.
This file proves it at every order, over any field of characteristic zero.

[proved-standard; formal-checked] What is proved.

1. **The chain is a complex** (`pderiv_comm`, `curl_grad`, `div_curl`): partial derivatives commute on polynomials, so
   `curl ∘ grad = 0` and `div ∘ curl = 0`; counts of counts cancel because a boundary of a boundary is zero.
2. **The contracting homotopy** (`dotX_grad`, `grad_dotX_sub_crossX_curl`, `smulX_div_sub_curl_crossX`,
   `div_smulX`): contraction with the position `x` (`f ↦ x f`, `F ↦ x · F`, `G ↦ x × G`) is Koszul's homotopy, and on a
   homogeneous form of degree `n` and rank `k` the two composites sum to `(n + k)` times the form:
   `x · ∇f = n f` (Euler), `∇(x · F) − x × (∇ × F) = (n + 1) F`, `x (∇ · G) − ∇ × (x × G) = (n + 2) G` and
   `∇ · (x h) = (n + 3) h`.
3. **Each kernel is the image before it** (`grad_eq_zero_iff`, `curl_eq_zero_iff`, `div_eq_zero_iff`,
   `div_surjective`): on a positive degree the gradient's kernel is zero; a homogeneous field of degree `n` has no curl
   exactly when it is the gradient of a homogeneous polynomial of degree `n + 1` (namely `(x · F)/(n + 1)`), and no
   divergence exactly when it is the curl of a homogeneous field of degree `n + 1` (namely `−(x × G)/(n + 2)`); and
   every homogeneous polynomial of degree `n` is a divergence, of `x h/(n + 3)`.
4. **The curl leaves `C(n + 3, 2)` free** (`finrank_homogeneous`, `curlFree_eq_range`, `finrank_curlFree`): the
   homogeneous polynomials of degree `d` in three variables have dimension `C(d + 2, 2)`, and the fields of degree `n`
   without curl are the gradients of degree `n + 1`, the gradient injective there, so they have dimension `C(n + 3, 2)`.
5. **The alternating count** (`free_count`, `alternating_count`): `3C(n+2, 2) − 3C(n+1, 2) + C(n, 2) = C(n+3, 2)` (the
   unknowns less the equations plus the identities among them) and the whole chain's alternating count
   `C(n+3, 2) − 3C(n+2, 2) + 3C(n+1, 2) − C(n, 2)` is zero.

The computational object is the helical pair interaction read on its complex: the gradient, curl and divergence are the
coboundaries `d` of the polynomial chart, and the position's contraction is the cone that makes the chain exact. Of the
winding guide's six general objects this touches the cell holonomy (a field with no curl is a gradient: its holonomy
on every circuit vanishes) and the tower thread (the orders `n` the chain is read at); the helix, the pair, faces and
placement and the tube stay attached.

Consumers: the atlas row `gr.strength-alternating-count`, and the record's §5.6 (Einstein's strength as the alternating
count in four variables), §14.4 and §14.12.

What stands beside it: Hilbert's syzygy theorem, which bounds the chain of relations among relations at `n` steps in
`n` variables, and the four-variable counts of §5.6 (the wave equation, Maxwell's and empty-space gravitation), which
are the record's ruler figures.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.PolynomialDeRham

open MvPolynomial

variable {K : Type*} [Field K]

local notation "𝒫" => MvPolynomial (Fin 3) K

/-! ## The chain -/

/-- The gradient. -/
noncomputable def grad (f : 𝒫) : Fin 3 → 𝒫 := fun i => pderiv i f

/-- The curl. -/
noncomputable def curl (F : Fin 3 → 𝒫) : Fin 3 → 𝒫 :=
  ![pderiv 1 (F 2) - pderiv 2 (F 1), pderiv 2 (F 0) - pderiv 0 (F 2), pderiv 0 (F 1) - pderiv 1 (F 0)]

/-- The divergence. -/
noncomputable def div (F : Fin 3 → 𝒫) : 𝒫 := pderiv 0 (F 0) + pderiv 1 (F 1) + pderiv 2 (F 2)

/-- Contraction of a field with the position, `x · F`. -/
noncomputable def dotX (F : Fin 3 → 𝒫) : 𝒫 := X 0 * F 0 + X 1 * F 1 + X 2 * F 2

/-- The position's cross product, `x × G`. -/
noncomputable def crossX (G : Fin 3 → 𝒫) : Fin 3 → 𝒫 :=
  ![X 1 * G 2 - X 2 * G 1, X 2 * G 0 - X 0 * G 2, X 0 * G 1 - X 1 * G 0]

/-- The position scaled by a polynomial, `x h`. -/
noncomputable def smulX (h : 𝒫) : Fin 3 → 𝒫 := fun i => X i * h

@[simp] lemma pd01 : pderiv (0 : Fin 3) (X 1 : 𝒫) = 0 := pderiv_X_of_ne (by decide)
@[simp] lemma pd02 : pderiv (0 : Fin 3) (X 2 : 𝒫) = 0 := pderiv_X_of_ne (by decide)
@[simp] lemma pd10 : pderiv (1 : Fin 3) (X 0 : 𝒫) = 0 := pderiv_X_of_ne (by decide)
@[simp] lemma pd12 : pderiv (1 : Fin 3) (X 2 : 𝒫) = 0 := pderiv_X_of_ne (by decide)
@[simp] lemma pd20 : pderiv (2 : Fin 3) (X 0 : 𝒫) = 0 := pderiv_X_of_ne (by decide)
@[simp] lemma pd21 : pderiv (2 : Fin 3) (X 1 : 𝒫) = 0 := pderiv_X_of_ne (by decide)

/-- [proved-standard; formal-checked] **Partial derivatives commute** on polynomials. -/
theorem pderiv_comm (i j : Fin 3) (f : 𝒫) : pderiv i (pderiv j f) = pderiv j (pderiv i f) := by
  induction f using MvPolynomial.induction_on' with
  | monomial s a =>
    simp only [pderiv_monomial]
    by_cases hij : i = j
    · subst hij; rfl
    · have h1 : (s - Finsupp.single j 1 : Fin 3 →₀ ℕ) i = s i := by
        simp [Ne.symm hij]
      have h2 : (s - Finsupp.single i 1 : Fin 3 →₀ ℕ) j = s j := by
        simp [hij]
      rw [h1, h2, tsub_right_comm]
      congr 1
      ring
  | add p q hp hq => simp only [map_add, hp, hq]

/-- [proved-standard; formal-checked] **`curl ∘ grad = 0`.** -/
theorem curl_grad (f : 𝒫) : curl (grad f) = 0 := by
  funext i
  fin_cases i <;> simp [curl, grad, pderiv_comm (2 : Fin 3) 1, pderiv_comm (0 : Fin 3) 2,
    pderiv_comm (1 : Fin 3) 0]

/-- [proved-standard; formal-checked] **`div ∘ curl = 0`.** -/
theorem div_curl (F : Fin 3 → 𝒫) : div (curl F) = 0 := by
  simp only [div, curl, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, map_sub]
  rw [pderiv_comm (0 : Fin 3) 1, pderiv_comm (0 : Fin 3) 2, pderiv_comm (1 : Fin 3) 2]
  ring

/-! ## The contracting homotopy -/

/-- Euler's identity on three variables. -/
theorem euler {f : 𝒫} {n : ℕ} (hf : f.IsHomogeneous n) :
    X 0 * pderiv 0 f + X 1 * pderiv 1 f + X 2 * pderiv 2 f = (n : 𝒫) * f := by
  have h := hf.sum_X_mul_pderiv
  rw [Fin.sum_univ_three, nsmul_eq_mul] at h
  exact h

/-- [proved-standard; formal-checked] **Euler**: `x · ∇f = n f`. -/
theorem dotX_grad {f : 𝒫} {n : ℕ} (hf : f.IsHomogeneous n) : dotX (grad f) = (n : 𝒫) * f := by
  simpa [dotX, grad] using euler hf

/-- [proved-standard; formal-checked] **The homotopy on fields**: `∇(x · F) − x × (∇ × F) = (n + 1) F`. -/
theorem grad_dotX_sub_crossX_curl {F : Fin 3 → 𝒫} {n : ℕ} (hF : ∀ i, (F i).IsHomogeneous n) (i : Fin 3) :
    grad (dotX F) i - crossX (curl F) i = ((n + 1 : ℕ) : 𝒫) * F i := by
  fin_cases i
  · have := euler (hF 0)
    simp [grad, dotX, crossX, curl]
    linear_combination this
  · have := euler (hF 1)
    simp [grad, dotX, crossX, curl]
    linear_combination this
  · have := euler (hF 2)
    simp [grad, dotX, crossX, curl]
    linear_combination this

/-- [proved-standard; formal-checked] **The homotopy on fluxes**: `x (∇ · G) − ∇ × (x × G) = (n + 2) G`. -/
theorem smulX_div_sub_curl_crossX {G : Fin 3 → 𝒫} {n : ℕ} (hG : ∀ i, (G i).IsHomogeneous n) (i : Fin 3) :
    smulX (div G) i - curl (crossX G) i = ((n + 2 : ℕ) : 𝒫) * G i := by
  fin_cases i
  · have := euler (hG 0)
    simp [smulX, div, crossX, curl]
    linear_combination this
  · have := euler (hG 1)
    simp [smulX, div, crossX, curl]
    linear_combination this
  · have := euler (hG 2)
    simp [smulX, div, crossX, curl]
    linear_combination this

/-- [proved-standard; formal-checked] **The homotopy on densities**: `∇ · (x h) = (n + 3) h`. -/
theorem div_smulX {h : 𝒫} {n : ℕ} (hh : h.IsHomogeneous n) : div (smulX h) = ((n + 3 : ℕ) : 𝒫) * h := by
  have := euler hh
  simp [div, smulX]
  linear_combination this

/-! ## Each kernel is the image before it -/

section Exact

lemma X_mul_isHomogeneous {g : 𝒫} {n : ℕ} (hg : g.IsHomogeneous n) (a : Fin 3) :
    (X a * g : 𝒫).IsHomogeneous (n + 1) := by
  rw [add_comm]
  exact (isHomogeneous_X (R := K) a).mul hg

lemma dotX_isHomogeneous {F : Fin 3 → 𝒫} {n : ℕ} (hF : ∀ i, (F i).IsHomogeneous n) :
    (dotX F).IsHomogeneous (n + 1) :=
  ((X_mul_isHomogeneous (hF 0) 0).add (X_mul_isHomogeneous (hF 1) 1)).add (X_mul_isHomogeneous (hF 2) 2)

lemma crossX_isHomogeneous {G : Fin 3 → 𝒫} {n : ℕ} (hG : ∀ i, (G i).IsHomogeneous n) (i : Fin 3) :
    (crossX G i).IsHomogeneous (n + 1) := by
  fin_cases i
  · exact (X_mul_isHomogeneous (hG 2) 1).sub (X_mul_isHomogeneous (hG 1) 2)
  · exact (X_mul_isHomogeneous (hG 0) 2).sub (X_mul_isHomogeneous (hG 2) 0)
  · exact (X_mul_isHomogeneous (hG 1) 0).sub (X_mul_isHomogeneous (hG 0) 1)

/-- A derivative lowers the degree of a homogeneous polynomial by one. -/
lemma pderiv_isHomogeneous {f : 𝒫} {n : ℕ} (hf : f.IsHomogeneous (n + 1)) (i : Fin 3) :
    (pderiv i f).IsHomogeneous n := by
  intro d hd
  rw [coeff_pderiv] at hd
  have h2 := hf (left_ne_zero_of_mul hd)
  rw [map_add] at h2
  have h3 : Finsupp.weight (1 : Fin 3 → ℕ) (Finsupp.single i 1) = 1 := by simp [Finsupp.weight_apply]
  omega

lemma curl_C_mul (c : K) (F : Fin 3 → 𝒫) (i : Fin 3) :
    curl (fun j => C c * F j) i = C c * curl F i := by
  fin_cases i <;> simp [curl, mul_sub]

variable [CharZero K]

lemma C_inv_cast_mul {m : ℕ} (hm : m ≠ 0) (p : 𝒫) : C ((m : K)⁻¹) * ((m : 𝒫) * p) = p := by
  rw [← mul_assoc, ← map_natCast (C : K →+* 𝒫) m, ← C_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), C_1, one_mul]

/-- [proved-standard; formal-checked] **The gradient's kernel at a positive degree is zero.** -/
theorem grad_eq_zero_iff {f : 𝒫} {n : ℕ} (hf : f.IsHomogeneous (n + 1)) : grad f = 0 ↔ f = 0 := by
  constructor
  · intro h
    have e := dotX_grad hf
    rw [h] at e
    have h0 : ((n + 1 : ℕ) : 𝒫) * f = 0 := by rw [← e]; simp [dotX]
    rw [← C_inv_cast_mul (K := K) (Nat.succ_ne_zero n) f, h0, mul_zero]
  · rintro rfl
    funext i
    simp [grad]

/-- [proved-standard; formal-checked] **A field without curl is a gradient.** A homogeneous field of degree `n` has no
curl exactly when it is the gradient of a homogeneous polynomial of degree `n + 1`, namely `(x · F)/(n + 1)`. -/
theorem curl_eq_zero_iff {F : Fin 3 → 𝒫} {n : ℕ} (hF : ∀ i, (F i).IsHomogeneous n) :
    curl F = 0 ↔ ∃ f : 𝒫, f.IsHomogeneous (n + 1) ∧ grad f = F := by
  constructor
  · intro h
    refine ⟨C (((n + 1 : ℕ) : K))⁻¹ * dotX F, (dotX_isHomogeneous hF).C_mul _, ?_⟩
    funext i
    have e := grad_dotX_sub_crossX_curl hF i
    rw [h] at e
    have hc : crossX (0 : Fin 3 → 𝒫) i = 0 := by fin_cases i <;> simp [crossX]
    rw [hc, sub_zero] at e
    simp only [grad] at e ⊢
    rw [pderiv_C_mul, e]
    exact C_inv_cast_mul (Nat.succ_ne_zero n) _
  · rintro ⟨f, -, rfl⟩
    exact curl_grad f

/-- [proved-standard; formal-checked] **A flux without divergence is a curl.** A homogeneous field of degree `n` has
no divergence exactly when it is the curl of a homogeneous field of degree `n + 1`, namely `−(x × G)/(n + 2)`. -/
theorem div_eq_zero_iff {G : Fin 3 → 𝒫} {n : ℕ} (hG : ∀ i, (G i).IsHomogeneous n) :
    div G = 0 ↔ ∃ F : Fin 3 → 𝒫, (∀ i, (F i).IsHomogeneous (n + 1)) ∧ curl F = G := by
  constructor
  · intro h
    refine ⟨fun i => C (-(((n + 2 : ℕ) : K))⁻¹) * crossX G i,
      fun i => (crossX_isHomogeneous hG i).C_mul _, ?_⟩
    funext i
    have e := smulX_div_sub_curl_crossX hG i
    rw [h] at e
    simp only [smulX, mul_zero, zero_sub] at e
    rw [curl_C_mul, map_neg, neg_mul, ← mul_neg, e]
    exact C_inv_cast_mul (by omega) _
  · rintro ⟨F, -, rfl⟩
    exact div_curl F

/-- [proved-standard; formal-checked] **Every density is a divergence**: a homogeneous `h` of degree `n` is the
divergence of `x h/(n + 3)`, homogeneous of degree `n + 1`. -/
theorem div_surjective {h : 𝒫} {n : ℕ} (hh : h.IsHomogeneous n) :
    ∃ G : Fin 3 → 𝒫, (∀ i, (G i).IsHomogeneous (n + 1)) ∧ div G = h := by
  refine ⟨smulX (C (((n + 3 : ℕ) : K))⁻¹ * h), fun i => X_mul_isHomogeneous (hh.C_mul _) i, ?_⟩
  rw [div_smulX (hh.C_mul _), mul_left_comm]
  exact C_inv_cast_mul (by omega) h

end Exact

/-! ## The curl leaves `C(n + 3, 2)` free -/

section Count

/-- [proved-standard; formal-checked] **The homogeneous polynomials of degree `d` in three variables** have dimension
`C(d + 2, 2)`: their monomials are the `d`-multisets of three variables. -/
theorem finrank_homogeneous (d : ℕ) :
    Module.finrank K (homogeneousSubmodule (Fin 3) K d) = (d + 2).choose 2 := by
  classical
  have hS : ∀ m : Fin 3 →₀ ℕ, m ∈ Finset.univ.finsuppAntidiag d ↔ m ∈ {m : Fin 3 →₀ ℕ | m.degree = d} := by
    intro m
    simp [Finset.mem_finsuppAntidiag, Finsupp.degree_eq_sum]
  let _ : Fintype {m : Fin 3 →₀ ℕ | m.degree = d} := Fintype.ofFinset _ hS
  rw [homogeneousSubmodule_eq_finsupp_supported,
    LinearEquiv.finrank_eq (AddMonoidAlgebra.supportedEquivFinsupp (R := K) (S := K) _),
    Module.finrank_finsupp_self, Fintype.card_ofFinset, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show 3 + d - 1 = d + 2 by omega]
  exact Nat.choose_symm_add

/-- The gradient as a linear map. -/
noncomputable def gradL : 𝒫 →ₗ[K] (Fin 3 → 𝒫) where
  toFun := grad
  map_add' f g := by funext i; simp [grad]
  map_smul' c f := by funext i; simp [grad]

/-- The curl as a linear map. -/
noncomputable def curlL : (Fin 3 → 𝒫) →ₗ[K] (Fin 3 → 𝒫) where
  toFun := curl
  map_add' F G := by
    funext i; fin_cases i <;> simp [curl] <;> ring
  map_smul' c F := by
    funext i; fin_cases i <;> simp [curl, smul_sub]

/-- The homogeneous fields of degree `n` without curl. -/
noncomputable def curlFree (n : ℕ) : Submodule K (Fin 3 → 𝒫) :=
  Submodule.pi Set.univ (fun _ => homogeneousSubmodule (Fin 3) K n) ⊓ LinearMap.ker (curlL (K := K))

variable [CharZero K]

/-- [proved-standard; formal-checked] **The fields without curl are the gradients**: of degree `n`, they are the
image of the homogeneous polynomials of degree `n + 1`. -/
theorem curlFree_eq_range (n : ℕ) :
    curlFree (K := K) n = LinearMap.range (gradL ∘ₗ (homogeneousSubmodule (Fin 3) K (n + 1)).subtype) := by
  ext F
  simp only [curlFree, Submodule.mem_inf, Submodule.mem_pi, Set.mem_univ, true_implies, mem_homogeneousSubmodule,
    LinearMap.mem_ker, LinearMap.mem_range, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
    Subtype.exists, exists_prop]
  constructor
  · rintro ⟨hF, hc⟩
    obtain ⟨f, hf, rfl⟩ := (curl_eq_zero_iff hF).mp hc
    exact ⟨f, hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    exact ⟨fun i => pderiv_isHomogeneous hf i, curl_grad f⟩

/-- [proved-standard; formal-checked] **The curl leaves `C(n + 3, 2)` free**: the gradient is injective on degree
`n + 1`, so the homogeneous fields of degree `n` without curl have the dimension of `P_(n+1)`. -/
theorem finrank_curlFree (n : ℕ) : Module.finrank K (curlFree (K := K) n) = (n + 3).choose 2 := by
  have hinj : Function.Injective (gradL ∘ₗ (homogeneousSubmodule (Fin 3) K (n + 1)).subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    exact Subtype.ext ((grad_eq_zero_iff (K := K) a.2).mp ha)
  rw [curlFree_eq_range, LinearMap.finrank_range_of_inj hinj, finrank_homogeneous]

end Count

/-- `C(m + 1, 2) = m + C(m, 2)`. -/
lemma choose_two_succ (m : ℕ) : (m + 1).choose 2 = m + m.choose 2 := by
  rw [Nat.choose_succ_succ', Nat.choose_one_right]

/-- [proved-standard; formal-checked] **The free count**: unknowns less equations plus the identities among them,
`3C(n+2, 2) − 3C(n+1, 2) + C(n, 2) = C(n+3, 2)`. -/
theorem free_count (n : ℕ) :
    (3 * (n + 2).choose 2 - 3 * (n + 1).choose 2 + n.choose 2 : ℤ) = (n + 3).choose 2 := by
  have h3 : (n + 3).choose 2 = (n + 2) + (n + 2).choose 2 := choose_two_succ (n + 2)
  have h2 : (n + 2).choose 2 = (n + 1) + (n + 1).choose 2 := choose_two_succ (n + 1)
  have h1 : (n + 1).choose 2 = n + n.choose 2 := choose_two_succ n
  rw [h3, h2, h1]
  push_cast
  ring

/-- [proved-standard; formal-checked] **The alternating count of the whole chain is zero**:
`C(n+3, 2) − 3C(n+2, 2) + 3C(n+1, 2) − C(n, 2) = 0`. -/
theorem alternating_count (n : ℕ) :
    ((n + 3).choose 2 - 3 * (n + 2).choose 2 + 3 * (n + 1).choose 2 - n.choose 2 : ℤ) = 0 := by
  have := free_count n
  linear_combination -this

end Holonics.Mathematics.PolynomialDeRham
