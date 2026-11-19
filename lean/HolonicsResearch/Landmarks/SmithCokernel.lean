import HolonicsResearch.Landmarks.IntegralCokernel
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# The integral cokernel ledger: a Smith form reads the cokernel one coordinate at a time

[definition] Formal obligations (#410), the integral half of the cokernel ledger
(atlas `linalg.smith-normal-form`). `Landmarks/IntegralCokernel` states an integral face map's
cokernel as a quotient group and reads a class reachable only in a multiple as nonzero torsion in
it; it reads the `𝔽₂` ledger of `E/2E` whole (§5 there). This module writes the ledger over a
commutative ring `R` (a principal ideal domain is what makes the form exist, Mathlib's
`Submodule.smithNormalForm`): given a Smith normal form of a submodule `N ≤ M`
(Mathlib's `Basis.SmithNormalForm N ι n`: a basis `bM` of `M`, a basis `bN` of `N`, an embedding
`f : Fin n ↪ ι` and diagonal entries `a` with `bN i = a i • bM (f i)`), the cokernel `M ⧸ N` is
read coordinate by coordinate, each coordinate modulo its own invariant.

[proved-derived; formal-checked] What is proved.

1. **The invariants.** `invariant snf j` is `a i` at the coordinate `j = f i` and `0` off the range
   of `f` (`invariant_f`, `invariant_of_notMem`). Over a nontrivial ring the diagonal entries are nonzero
   (`a_ne_zero`), so a coordinate's invariant is zero exactly off the range of `f`
   (`invariant_eq_zero_iff`); with `ι` finite there are `card ι − n` such free coordinates
   (`card_free`).
2. **The ledger.** `ledger snf : M →ₗ[R] Π j, R ⧸ (invariant j)` reads the `j`-th coordinate of a
   vector in the basis `bM` modulo its invariant. Its kernel is `N` (`mem_ker_ledger_iff`, each
   coordinate divisible by its invariant; `ker_ledger`), it is onto for finite `ι`
   (`ledger_surjective`), and so **the cokernel is the product of its coordinates' quotients**,
   `M ⧸ N ≃ₗ[R] Π j, R ⧸ (invariant j)` (`cokernelEquiv`, `cokernelEquiv_mk`).
3. **Reading the ledger.** A vector is reached exactly when each coordinate is divisible by its
   invariant (`reached_iff`), and its multiple `c • y` exactly when each `invariant j` divides
   `c · y_j` (`reached_in_multiple_iff`). The rank of `N` is `n` (`finrank_eq`).
4. **The integer instance.** For `A : ℤᵏ →ₗ ℤᵐ`, `smith A` is Mathlib's Smith form of the image in
   the standard basis. The cokernel is `Π_j ℤ ⧸ (c_j)` (`int_cokernelEquiv`), and as a group
   `Π_j ZMod |c_j|` (`int_cokernelAddEquivZMod`): a free coordinate (`c_j = 0`) contributes `ZMod 0`,
   a copy of `ℤ`, a unit invariant contributes the trivial group, and the torsion is carried by the
   invariants above one in absolute value. The image has rank `n` (`int_finrank_range`) and the
   free coordinates number `m − n` (`int_card_free`). **A face is reachable only in the multiple
   `c` exactly when `c ≠ 0`, every `c_j` divides `c · y_j`, and some `c_j` does not divide `y_j`**
   (`reachableOnlyInMultiple_iff_ledger`, for any Smith form of the image; it joins
   `CokernelCalculus.ReachableOnlyInMultiple` and `IntegralCokernel.reachableOnlyInMultiple_iff`).
5. **A worked instance.** Doubling on `ℤ¹` has the Smith form `(2)` (`doublingSmith`, its invariant
   `doublingSmith_invariant`), and the ledger reads the face `1` as reachable only in the multiple
   `2` (`one_reachableOnlyInMultiple_two`).

The computational object: a ratio carried as an undivided pair with its remainder. Each coordinate
of a face is divided by its invariant, and the remainder is that coordinate's ledger entry; the
face is reached when every remainder vanishes, and the cokernel is the set of remainders.

[established-bounded] Scope. Mathlib's `Basis.SmithNormalForm` carries no divisibility chain: the
entries `a i` are fixed only as a diagonal, so the atlas row's `d₁ ∣ d₂ ∣ ⋯ ∣ d_r` and the
uniqueness of the factors up to units are not stated here, and the invariants are those of the
chosen form. What stands without the chain is all that a reachability read uses: the cokernel's
product decomposition, the rank, the free coordinates and the divisibility tests. The `𝔽₂` ledger
of `E/2E` is `IntegralCokernel.descentFaceF2` with `descent_exact_sequence_F2`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Landmarks.SmithCokernel

open Module
open Holonics.Landmarks.CokernelCalculus

/-! ## 1. The invariants -/

section Ledger

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
  {N : Submodule R M} {ι : Type*} {n : ℕ} (snf : Basis.SmithNormalForm N ι n)

/-- [definition] **The invariant of a coordinate**: the diagonal entry `a i` at `j = f i`, and `0`
at a coordinate off the range of `f`. -/
def invariant (j : ι) : R := by
  classical exact if h : ∃ i, snf.f i = j then snf.a h.choose else 0

/-- [proved-derived; formal-checked] At `f i` the invariant is the diagonal entry `a i`. -/
theorem invariant_f (i : Fin n) : invariant snf (snf.f i) = snf.a i := by
  classical
  have h : ∃ i', snf.f i' = snf.f i := ⟨i, rfl⟩
  simp only [invariant, dif_pos h]
  rw [snf.f.injective h.choose_spec]

/-- [proved-derived; formal-checked] Off the range of `f` the invariant is `0`. -/
theorem invariant_of_notMem {j : ι} (hj : j ∉ Set.range snf.f) : invariant snf j = 0 := by
  classical
  have h : ¬ ∃ i, snf.f i = j := by simpa using hj
  simp only [invariant, dif_neg h]

/-- [proved-derived; formal-checked] Over a nontrivial ring the diagonal entries are nonzero:
`a i = 0` would make the basis vector `bN i` zero. -/
theorem a_ne_zero [Nontrivial R] (i : Fin n) : snf.a i ≠ 0 := by
  intro h
  have hs := snf.snf i
  rw [h, zero_smul] at hs
  exact snf.bN.ne_zero i (Subtype.ext hs)

/-- [proved-derived; formal-checked] **A coordinate's invariant is zero exactly off the range of
`f`**: the free coordinates. -/
theorem invariant_eq_zero_iff [Nontrivial R] (j : ι) :
    invariant snf j = 0 ↔ j ∉ Set.range snf.f := by
  constructor
  · rintro h ⟨i, rfl⟩
    rw [invariant_f] at h
    exact a_ne_zero snf i h
  · exact invariant_of_notMem snf

/-- [proved-derived; formal-checked] **There are `card ι − n` free coordinates.** -/
theorem card_free [Nontrivial R] [Fintype ι] [DecidableEq ι]
    [DecidablePred fun j => invariant snf j = 0] :
    (Finset.univ.filter fun j => invariant snf j = 0).card = Fintype.card ι - n := by
  have hset : (Finset.univ.filter fun j => invariant snf j = 0) =
      Finset.univ \ Finset.univ.map snf.f := by
    ext j
    simp [invariant_eq_zero_iff]
  rw [hset, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_map, Finset.card_univ,
    Finset.card_univ, Fintype.card_fin]

/-! ## 2. The ledger -/

/-- [definition] **The ledger**: the `j`-th coordinate in the basis `bM`, read modulo its
invariant. -/
def ledger : M →ₗ[R] ((j : ι) → R ⧸ Ideal.span {invariant snf j}) :=
  LinearMap.pi fun j => (Ideal.span {invariant snf j}).mkQ ∘ₗ snf.bM.coord j

theorem ledger_apply (x : M) (j : ι) :
    ledger snf x j = Submodule.Quotient.mk (snf.bM.repr x j) := rfl

/-- [proved-derived; formal-checked] **The ledger vanishes exactly when each coordinate is divisible
by its invariant.** -/
theorem mem_ker_ledger_iff (x : M) :
    x ∈ LinearMap.ker (ledger snf) ↔ ∀ j, invariant snf j ∣ snf.bM.repr x j := by
  rw [LinearMap.mem_ker, funext_iff]
  refine forall_congr' fun j => ?_
  rw [ledger_apply, Pi.zero_apply, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton]

/-- [proved-derived; formal-checked] **The ledger's kernel is `N`.** -/
theorem ker_ledger : LinearMap.ker (ledger snf) = N := by
  ext x
  rw [mem_ker_ledger_iff]
  constructor
  · intro h
    rw [← snf.bM.linearCombination_repr x, Finsupp.linearCombination_apply]
    refine Submodule.finsuppSum_mem _ _ _ _ fun j _ => ?_
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      obtain ⟨t, ht⟩ := h (snf.f i)
      rw [invariant_f] at ht
      rw [ht, mul_comm, mul_smul, ← snf.snf i]
      exact N.smul_mem t (snf.bN i).2
    · have h0 := h j
      rw [invariant_of_notMem snf hj, zero_dvd_iff] at h0
      rw [h0, zero_smul]
      exact N.zero_mem
  · intro hx j
    by_cases hj : j ∈ Set.range snf.f
    · obtain ⟨i, rfl⟩ := hj
      rw [invariant_f]
      have he := snf.repr_apply_embedding_eq_repr_smul ⟨x, hx⟩ (i := i)
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul] at he
      exact ⟨_, he⟩
    · rw [snf.repr_eq_zero_of_notMem_range ⟨x, hx⟩ hj]
      exact dvd_zero _

/-- [proved-derived; formal-checked] **The ledger is onto**: every assignment of residues is read
from some vector. -/
theorem ledger_surjective [Finite ι] : Function.Surjective (ledger snf) := by
  intro q
  have hq : ∀ j, ∃ r : R, (Submodule.Quotient.mk r : R ⧸ Ideal.span {invariant snf j}) = q j :=
    fun j => Submodule.Quotient.mk_surjective _ (q j)
  choose r hr using hq
  refine ⟨snf.bM.equivFun.symm r, funext fun j => ?_⟩
  rw [ledger_apply, ← hr j]
  congr 1
  have := congrFun (snf.bM.equivFun.apply_symm_apply r) j
  rwa [Basis.equivFun_apply] at this

/-- [proved-derived; formal-checked] **The cokernel is the product of its coordinates'
quotients**: `M ⧸ N ≃ₗ[R] Π j, R ⧸ (invariant j)`. -/
def cokernelEquiv [Finite ι] : (M ⧸ N) ≃ₗ[R] ((j : ι) → R ⧸ Ideal.span {invariant snf j}) :=
  (Submodule.quotEquivOfEq _ _ (ker_ledger snf).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (ledger_surjective snf))

theorem cokernelEquiv_mk [Finite ι] (x : M) :
    cokernelEquiv snf (Submodule.Quotient.mk x) = ledger snf x := rfl

/-! ## 3. Reading the ledger -/

/-- [proved-derived; formal-checked] **A vector is reached exactly when each coordinate is divisible
by its invariant.** -/
theorem reached_iff (y : M) : y ∈ N ↔ ∀ j, invariant snf j ∣ snf.bM.repr y j := by
  rw [← mem_ker_ledger_iff, ker_ledger]

/-- [proved-derived; formal-checked] **The multiple `c • y` is reached exactly when each invariant
divides `c · y_j`.** -/
theorem reached_in_multiple_iff (c : R) (y : M) :
    c • y ∈ N ↔ ∀ j, invariant snf j ∣ c * snf.bM.repr y j := by
  rw [reached_iff snf]
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul]

/-- [proved-derived; formal-checked] **The rank of `N` is `n`.** -/
theorem finrank_eq [Nontrivial R] (snf : Basis.SmithNormalForm N ι n) : finrank R N = n := by
  rw [finrank_eq_card_basis snf.bN, Fintype.card_fin]

end Ledger

/-! ## 4. The integer instance -/

section Integer

variable {k m : ℕ} (A : (Fin k → ℤ) →ₗ[ℤ] (Fin m → ℤ))

/-- [definition] Mathlib's Smith normal form of the image of `A`, in the standard basis of
`ℤᵐ`. -/
def smith : Σ n : ℕ, Basis.SmithNormalForm (LinearMap.range A) (Fin m) n :=
  Submodule.smithNormalForm (Pi.basisFun ℤ (Fin m)) (LinearMap.range A)

/-- [proved-derived; formal-checked] **The cokernel of `A` is `Π_j ℤ ⧸ (c_j)`.** -/
def int_cokernelEquiv :
    ((Fin m → ℤ) ⧸ LinearMap.range A) ≃ₗ[ℤ]
      ((j : Fin m) → ℤ ⧸ Ideal.span {invariant (smith A).2 j}) :=
  cokernelEquiv (smith A).2

/-- [proved-derived; formal-checked] **As a group the cokernel is `Π_j ZMod |c_j|`**: a free
coordinate gives `ZMod 0 = ℤ`, a unit invariant the trivial group, and an invariant above one its
torsion. -/
def int_cokernelAddEquivZMod :
    ((Fin m → ℤ) ⧸ LinearMap.range A) ≃+ ((j : Fin m) → ZMod (invariant (smith A).2 j).natAbs) :=
  (int_cokernelEquiv A).toAddEquiv.trans
    (AddEquiv.piCongrRight fun _ => (Int.quotientSpanEquivZMod _).toAddEquiv)

/-- [proved-derived; formal-checked] **The image of `A` has rank `n`.** -/
theorem int_finrank_range : finrank ℤ (LinearMap.range A) = (smith A).1 :=
  finrank_eq (smith A).2

/-- [proved-derived; formal-checked] **The free coordinates of the cokernel number `m − n`.** -/
theorem int_card_free [DecidablePred fun j => invariant (smith A).2 j = 0] :
    (Finset.univ.filter fun j => invariant (smith A).2 j = 0).card = m - (smith A).1 := by
  rw [card_free, Fintype.card_fin]

/-- [proved-derived; formal-checked] **A face is reachable only in the multiple `c` exactly when
`c ≠ 0`, every invariant divides `c · y_j`, and some invariant does not divide `y_j`**, read on any
Smith form of the image of `A`. -/
theorem reachableOnlyInMultiple_iff_ledger {ι : Type*} {n : ℕ}
    (snf : Basis.SmithNormalForm (LinearMap.range A) ι n) (y : Fin m → ℤ) (c : ℤ) :
    ReachableOnlyInMultiple (Set.range A) y c ↔
      c ≠ 0 ∧ (∀ j, invariant snf j ∣ c * snf.bM.repr y j) ∧
        ∃ j, ¬ invariant snf j ∣ snf.bM.repr y j := by
  have hcl : ∀ z, z ∈ AddSubgroup.closure (Set.range A) ↔ z ∈ LinearMap.range A := by
    intro z
    have h := IntegralCokernel.closure_range A.toAddMonoidHom
    change z ∈ AddSubgroup.closure (Set.range A.toAddMonoidHom) ↔ _
    rw [h, AddMonoidHom.mem_range, LinearMap.mem_range]
    rfl
  unfold ReachableOnlyInMultiple
  rw [hcl, hcl, reached_iff snf y, not_forall]
  exact and_congr_right fun _ => and_congr_left fun _ => reached_in_multiple_iff snf c y

/-- [proved-derived; formal-checked] The same read on Mathlib's Smith form `smith A`. -/
theorem reachableOnlyInMultiple_iff_smith (y : Fin m → ℤ) (c : ℤ) :
    ReachableOnlyInMultiple (Set.range A) y c ↔
      c ≠ 0 ∧ (∀ j, invariant (smith A).2 j ∣ c * (smith A).2.bM.repr y j) ∧
        ∃ j, ¬ invariant (smith A).2 j ∣ (smith A).2.bM.repr y j :=
  reachableOnlyInMultiple_iff_ledger A (smith A).2 y c

end Integer

/-! ## 5. A worked instance: doubling on `ℤ¹` -/

section Worked

/-- [definition] Doubling on `ℤ¹`. -/
def doubling : (Fin 1 → ℤ) →ₗ[ℤ] (Fin 1 → ℤ) := (2 : ℤ) • LinearMap.id

/-- The generator of the image of doubling. -/
def twoVec : Fin 1 → (Fin 1 → ℤ) := fun _ _ => 2

theorem twoVec_linearIndependent : LinearIndependent ℤ twoVec :=
  linearIndependent_unique_iff.mpr fun h => by simpa [twoVec] using congrFun h 0

theorem range_doubling : LinearMap.range doubling = Submodule.span ℤ (Set.range twoVec) := by
  ext x
  rw [LinearMap.mem_range, show Set.range twoVec = {fun _ => 2} from Set.range_const,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨y 0, funext fun i => ?_⟩
    fin_cases i
    simp [doubling, mul_comm]
  · rintro ⟨t, rfl⟩
    refine ⟨fun _ => t, funext fun i => ?_⟩
    simp [doubling, mul_comm]

/-- [definition] A Smith form of the image of doubling: the standard basis, and the image's basis
`(2)`, with diagonal entry `2`. -/
def doublingSmith : Basis.SmithNormalForm (LinearMap.range doubling) (Fin 1) 1 where
  bM := Pi.basisFun ℤ (Fin 1)
  bN := (Basis.span twoVec_linearIndependent).map (LinearEquiv.ofEq _ _ range_doubling.symm)
  f := Function.Embedding.refl _
  a := fun _ => 2
  snf i := by
    fin_cases i
    ext j
    fin_cases j
    simp [twoVec]

theorem doublingSmith_invariant : invariant doublingSmith 0 = 2 :=
  invariant_f doublingSmith 0

/-- [proved-derived; formal-checked] **The face `1` is reachable only in the multiple `2`** under
doubling, read from the ledger: `2 ∣ 2 · 1` and `2 ∤ 1`. -/
theorem one_reachableOnlyInMultiple_two :
    ReachableOnlyInMultiple (Set.range doubling) (fun _ => 1) 2 := by
  have hinv : ∀ j, invariant doublingSmith j = 2 := fun j => by
    fin_cases j
    exact doublingSmith_invariant
  rw [reachableOnlyInMultiple_iff_ledger doubling doublingSmith]
  refine ⟨two_ne_zero, fun j => ?_, ⟨0, ?_⟩⟩
  · rw [hinv]
    simp [doublingSmith]
  · rw [hinv]
    simp [doublingSmith]

end Worked

section Audit
#print axioms invariant_f
#print axioms invariant_of_notMem
#print axioms invariant_eq_zero_iff
#print axioms card_free
#print axioms mem_ker_ledger_iff
#print axioms ker_ledger
#print axioms ledger_surjective
#print axioms cokernelEquiv
#print axioms reached_iff
#print axioms reached_in_multiple_iff
#print axioms finrank_eq
#print axioms int_cokernelEquiv
#print axioms int_cokernelAddEquivZMod
#print axioms int_finrank_range
#print axioms int_card_free
#print axioms reachableOnlyInMultiple_iff_ledger
#print axioms reachableOnlyInMultiple_iff_smith
#print axioms one_reachableOnlyInMultiple_two
end Audit

end Holonics.Landmarks.SmithCokernel
