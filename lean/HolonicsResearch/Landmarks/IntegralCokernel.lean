import HolonicsResearch.Landmarks.CokernelCalculus
import HolonicsResearch.EllipticCurve.FamilyImage
import Holonics.Compression.Core.FaceMap
import Mathlib.Algebra.Module.ZMod

/-!
# The descent face and the integral cycle face are face maps: kernel, cokernel and the field gap

[definition] Rebuild step 3 (#145). `Compression/Core/FaceMap` states the face map's kernel,
exact sequence and reachability over a **field**. BSD's descent and the integral Hodge conjecture
carry **integral** face maps (ℤ-modules), whose cokernel can hold torsion: a class reachable only
in a multiple (`Landmarks/CokernelCalculus.ReachableOnlyInMultiple`). This module states them as
instances of the face-map law and names the ℤ-module versus field gap exactly.

[proved-derived; formal-checked] What is proved.

1. **The integral face map.** For a ℤ-linear face map `F : X →+ Y`, a face is reached exactly when
   its cokernel class is zero (`integral_reachable_iff_cokernelClass_zero`, the ℤ instance of
   `FaceMap.reachable_iff_cokernelClass_zero`), and **a class is reachable only in the multiple `m`
   exactly when its cokernel class is nonzero `m`-torsion** (`reachableOnlyInMultiple_iff`, which
   has `CokernelCalculus.theMultipleReachableClassIsTorsionInTheCokernel` as its forward half).
2. **The gap.** Over a field, a face is reached exactly when every cocycle vanishes on it
   (`FaceMap.reachable_iff_cocycles_vanish`). Over ℤ this fails: for doubling on ℤ the class of `1`
   is unreached, yet every ℤ- or ℚ-valued cocycle that kills the image kills `1`; an `𝔽₂`-valued
   cocycle detects it (`integer_cocycles_miss_the_torsion_class`). Torsion cokernels need torsion
   coefficients.
3. **Integral Hodge.** The integral cycle face `ℤ^(S) → V` (ℤ-combinations of algebraic cycle
   classes `S`) has image `⟨S⟩`, and its ℚ-linear extension, a field face map of `FaceMap`, has image
   `span_ℚ S` (`range_integralFace`, `range_rationalFace`). **A class reachable only in a multiple
   has a nonzero `m`-torsion integral cokernel class and a zero rational cokernel class**
   (`integral_rational_gap`, with `CokernelCalculus.theMultipleReachableClassIsRationallyReachable`
   as its second half). On a declared Hodge datum the rational face is the datum's own cycle class
   map, so a Kollár class is in the algebraic span (`hodge_kollar_class`,
   `CokernelCalculus.theIntegralHodgeObstructionIsNotAMillenniumObstruction`). Witness: in `ℚ` with
   `S = {2}`, the class `1` (`kollar_witness`).
4. **BSD descent.** On `E_n : y² = x³ − n²x` (`n > 0`) the descent face
   `P ↦ (x, x − n) mod squares` is an additive map into the square-class group
   `(ℚˣ/ℚˣ²)²` (`descentFace`, from `FamilyFace.theFaceIsAHomomorphismOnEveryTwist`). **Its kernel is
   the doubles** (`ker_descentFace`, from `FamilyImage.theTwoDescentIsExactAtEveryModulus` over
   `FamilyKernel.theKernelIsTheDoublesAtEveryModulus`), so `E →[2] E →φ (ℚˣ/ℚˣ²)²` is exact
   (`descent_exact`) and the obstruction `E(ℚ)/2E(ℚ)`, the cokernel of doubling, is read
   faithfully by the descent face (`obstruction_read_faithfully`). A point outside `2E` is reachable
   only in the multiple `2`, so its obstruction class is nonzero `2`-torsion and its face is nonzero
   (`escaping_point`).
5. **The field closes the gap at `𝔽₂`.** The obstruction and the square classes are `𝔽₂`-vector
   spaces, and the descended face is `𝔽₂`-linear (`descentFaceF2`). The field law of `FaceMap`
   applies verbatim: its kernel is zero (nothing the face reads is released,
   `ker_descentFaceF2`), and a square class is realized by a point exactly when every `𝔽₂`-cocycle
   killing the realized classes kills it (`descent_realized_iff_cocycles_vanish`, an instance of
   `FaceMap.reachable_iff_cocycles_vanish`).

[established-bounded; formal-checked] The gap, named: `FaceMap` is over a field. At `ℚ` every
integral torsion class is invisible (the rational bar of `CokernelCalculus`), so descent bounds a
rank and says nothing rational about `Ш`; at `𝔽₂`, after quotienting by the doubles, the field law
holds and reads the obstruction whole. Nothing here concerns the conjectures themselves.

No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Landmarks.IntegralCokernel

open Holonics.EllipticCurve
open Holonics.Landmarks.CokernelCalculus

/-! ## 1. The integral face map -/

section Integral

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- [proved-derived; formal-checked] **A face is reached exactly when its cokernel class is zero**,
over ℤ. -/
theorem integral_reachable_iff_cokernelClass_zero (F : X →+ Y) (y : Y) :
    y ∈ F.range ↔ QuotientAddGroup.mk' F.range y = 0 :=
  (QuotientAddGroup.eq_zero_iff y).symm

theorem closure_range (F : X →+ Y) : AddSubgroup.closure (Set.range F) = F.range := by
  rw [← AddMonoidHom.coe_range, AddSubgroup.closure_eq]

/-- [proved-derived; formal-checked] **A class is reachable only in the multiple `m` exactly when
its cokernel class is nonzero `m`-torsion.** -/
theorem reachableOnlyInMultiple_iff (F : X →+ Y) (y : Y) (m : ℤ) :
    ReachableOnlyInMultiple (Set.range F) y m ↔
      m ≠ 0 ∧ m • QuotientAddGroup.mk' F.range y = 0 ∧ QuotientAddGroup.mk' F.range y ≠ 0 := by
  constructor
  · intro h
    have ht := theMultipleReachableClassIsTorsionInTheCokernel h
    rw [closure_range] at ht
    exact ⟨h.1, ht⟩
  · rintro ⟨hm, htor, hne⟩
    refine ⟨hm, ?_, ?_⟩
    · rw [closure_range, integral_reachable_iff_cokernelClass_zero, map_zsmul]
      exact htor
    · rw [closure_range, integral_reachable_iff_cokernelClass_zero]
      exact hne

/-- [counterexample; formal-checked] **Integer cocycles miss the torsion class.** For doubling on
ℤ, `1` is not reached, yet every ℤ- or ℚ-valued cocycle killing the image vanishes at `1`; an
`𝔽₂`-valued cocycle kills the image and reads `1`. -/
theorem integer_cocycles_miss_the_torsion_class :
    (1 : ℤ) ∉ (AddMonoidHom.mulLeft (2 : ℤ)).range ∧
      (∀ ω : ℤ →+ ℤ, ω.comp (AddMonoidHom.mulLeft 2) = 0 → ω 1 = 0) ∧
      (∀ ω : ℤ →+ ℚ, ω.comp (AddMonoidHom.mulLeft 2) = 0 → ω 1 = 0) ∧
      ∃ ω : ℤ →+ ZMod 2, ω.comp (AddMonoidHom.mulLeft 2) = 0 ∧ ω 1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨k, hk⟩
    simp only [AddMonoidHom.coe_mulLeft] at hk
    omega
  · intro ω h
    have h2 := DFunLike.congr_fun h 1
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_one,
      AddMonoidHom.zero_apply] at h2
    have : ω 2 = 2 * ω 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, map_add]
      ring
    omega
  · intro ω h
    have h2 := DFunLike.congr_fun h 1
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_one,
      AddMonoidHom.zero_apply] at h2
    have : ω 2 = 2 * ω 1 := by
      rw [show (2 : ℤ) = 1 + 1 by norm_num, map_add]
      ring
    rw [this] at h2
    linarith
  · refine ⟨Int.castAddHom (ZMod 2), ?_, ?_⟩
    · ext
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft, mul_one, Int.coe_castAddHom,
        AddMonoidHom.zero_apply]
      decide
    · simp only [Int.coe_castAddHom, Int.cast_one]
      decide

end Integral

/-! ## 2. Integral Hodge: the integral cycle face and its rational extension -/

section Hodge

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

/-- [definition] **The integral cycle face**: ℤ-combinations of the cycle classes `S`. -/
def integralFace (S : Set V) : (S →₀ ℤ) →+ V :=
  (Finsupp.linearCombination ℤ ((↑) : S → V)).toAddMonoidHom

/-- [definition] **The rational cycle face**, a field face map of `FaceMap`. -/
def rationalFace (S : Set V) : (S →₀ ℚ) →ₗ[ℚ] V :=
  Finsupp.linearCombination ℚ ((↑) : S → V)

omit [Module ℚ V] in
theorem range_integralFace (S : Set V) : (integralFace S).range = AddSubgroup.closure S := by
  have h : LinearMap.range (Finsupp.linearCombination ℤ ((↑) : S → V)) = Submodule.span ℤ S := by
    rw [Finsupp.range_linearCombination, Subtype.range_coe]
  ext x
  rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, ← h]
  rfl

theorem range_rationalFace (S : Set V) :
    LinearMap.range (rationalFace S) = Submodule.span ℚ S := by
  rw [rationalFace, Finsupp.range_linearCombination, Subtype.range_coe]

/-- [proved-derived; formal-checked] **The integral–rational gap.** A class reachable only in the
multiple `m` of the cycle classes has a nonzero `m`-torsion integral cokernel class, and a zero
rational cokernel class. -/
theorem integral_rational_gap (S : Set V) (α : V) (m : ℤ)
    (h : ReachableOnlyInMultiple S α m) :
    (m • QuotientAddGroup.mk' (integralFace S).range α = 0 ∧
        QuotientAddGroup.mk' (integralFace S).range α ≠ 0) ∧
      (LinearMap.range (rationalFace S)).mkQ α = 0 := by
  have hS : ReachableOnlyInMultiple (Set.range (integralFace S)) α m := by
    rw [ReachableOnlyInMultiple, closure_range, range_integralFace]
    exact h
  refine ⟨((reachableOnlyInMultiple_iff _ α m).mp hS).2, ?_⟩
  rw [← Holonics.Compression.Core.FaceMap.reachable_iff_cokernelClass_zero, range_rationalFace]
  exact theMultipleReachableClassIsRationallyReachable S α m h.1 h.2.1

open Holonics.Hodge.HodgeConjecture in
/-- [proved-derived; formal-checked] **A Kollár class on a Hodge datum**: reachable only in a
multiple of integral cycle classes, it has a nonzero torsion integral cokernel class, while its
cokernel class for the datum's cycle class map (the field face map) is zero: it is algebraic over
ℚ. -/
theorem hodge_kollar_class (D : Datum) (S : Set D.Cohomology)
    (hS : S ⊆ LinearMap.range D.cycleClass.hom) (α : D.Cohomology) (m : ℤ)
    (h : ReachableOnlyInMultiple S α m) :
    (m • QuotientAddGroup.mk' (integralFace S).range α = 0 ∧
        QuotientAddGroup.mk' (integralFace S).range α ≠ 0) ∧
      (LinearMap.range D.cycleClass.hom).mkQ α = 0 := by
  refine ⟨(integral_rational_gap S α m h).1, ?_⟩
  rw [← Holonics.Compression.Core.FaceMap.reachable_iff_cokernelClass_zero]
  exact theIntegralHodgeObstructionIsNotAMillenniumObstruction D S hS α m h.1 h.2.1

/-- [counterexample; formal-checked] **A Kollár witness in `ℚ`**: with `S = {2}`, the class `1` is
reachable only in the multiple `2`; its integral cokernel class is nonzero and its rational one
is zero. -/
theorem kollar_witness :
    ReachableOnlyInMultiple ({2} : Set ℚ) 1 2 ∧
      QuotientAddGroup.mk' (integralFace ({2} : Set ℚ)).range (1 : ℚ) ≠ 0 ∧
      (LinearMap.range (rationalFace ({2} : Set ℚ))).mkQ (1 : ℚ) = 0 := by
  have hw : ReachableOnlyInMultiple ({2} : Set ℚ) 1 2 := by
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [AddSubgroup.mem_closure_singleton]
      exact ⟨1, by norm_num⟩
    · rw [AddSubgroup.mem_closure_singleton]
      rintro ⟨k, hk⟩
      rw [zsmul_eq_mul] at hk
      have h2 : ((2 * k : ℤ) : ℚ) = 1 := by push_cast; linarith
      have h3 : 2 * k = 1 := by exact_mod_cast h2
      omega
  exact ⟨hw, (integral_rational_gap _ _ _ hw).1.2, (integral_rational_gap _ _ _ hw).2⟩

end Hodge

/-! ## 3. BSD: the descent face is a face map whose kernel is the doubles -/

section Descent

/-- [definition] The square-class group `ℚˣ/ℚˣ²`. -/
abbrev SquareClass : Type := ℚˣ ⧸ (powMonoidHom 2 : ℚˣ →* ℚˣ).range

/-- [proved-derived; formal-checked] `Descent.SqCls` is equality of square classes. -/
theorem sqCls_iff (a b : ℚˣ) :
    Descent.SqCls a b ↔ (QuotientGroup.mk a : SquareClass) = QuotientGroup.mk b := by
  rw [QuotientGroup.eq, MonoidHom.mem_range]
  constructor
  · rintro ⟨c, hc, hab⟩
    refine ⟨(Units.mk0 c hc)⁻¹, ?_⟩
    ext
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
      Units.val_mk0, Units.val_mul]
    rw [hab]
    have hb : (b : ℚ) ≠ 0 := b.ne_zero
    field_simp
  · rintro ⟨u, hu⟩
    refine ⟨(u⁻¹ : ℚˣ), Units.ne_zero _, ?_⟩
    have hu' := congrArg (fun v : ℚˣ => (v : ℚ)) hu
    simp only [powMonoidHom_apply, Units.val_pow_eq_pow_val, Units.val_mul,
      Units.val_inv_eq_inv_val] at hu'
    simp only [Units.val_inv_eq_inv_val]
    have ha : (a : ℚ) ≠ 0 := a.ne_zero
    have hu0 : (u : ℚ) ≠ 0 := u.ne_zero
    rw [inv_pow, hu']
    field_simp

variable {n : ℚ}

theorem slotOne_ne_zero (hn : n ≠ 0) (P : (FamilyFace.E n).Point) : FamilyFace.slotOne n P ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [FamilyFace.slotOne]
  · simp only [FamilyFace.slotOne]
    split_ifs with hx
    · exact neg_ne_zero.mpr (pow_ne_zero 2 hn)
    · exact hx

theorem slotTwo_ne_zero (hn : n ≠ 0) (P : (FamilyFace.E n).Point) : FamilyFace.slotTwo n P ≠ 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · simp [FamilyFace.slotTwo]
  · simp only [FamilyFace.slotTwo]
    split_ifs with hx
    · exact mul_ne_zero two_ne_zero (pow_ne_zero 2 hn)
    · exact sub_ne_zero.mpr hx

/-- [definition] The square class of a nonzero rational. -/
def sqClass (a : ℚ) (ha : a ≠ 0) : SquareClass := QuotientGroup.mk (Units.mk0 a ha)

theorem sqClass_eq_iff {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sqClass a ha = sqClass b hb ↔ Descent.SqCls a b := by
  rw [sqClass, sqClass, ← sqCls_iff]
  rfl

theorem sqClass_mul {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    sqClass (a * b) (mul_ne_zero ha hb) = sqClass a ha * sqClass b hb := by
  rw [sqClass, sqClass, sqClass, ← QuotientGroup.mk_mul]
  congr 1
  ext
  simp

theorem sqClass_one : sqClass 1 one_ne_zero = 1 := by
  rw [sqClass, ← QuotientGroup.mk_one]
  congr 1
  ext
  simp

/-- [definition] **The descent face** `P ↦ (x, x − n) mod squares`, as an additive map into the
square-class group. -/
def descentFace (n : ℚ) (hn : n ≠ 0) :
    (FamilyFace.E n).Point →+ Additive (SquareClass × SquareClass) where
  toFun P := Additive.ofMul
    (sqClass _ (slotOne_ne_zero hn P), sqClass _ (slotTwo_ne_zero hn P))
  map_zero' := by
    rw [← ofMul_one]
    congr 1
    ext
    · change sqClass (FamilyFace.slotOne n 0) _ = 1
      rw [← sqClass_one, sqClass_eq_iff]
      exact ⟨1, one_ne_zero, by simp [FamilyFace.slotOne]⟩
    · change sqClass (FamilyFace.slotTwo n 0) _ = 1
      rw [← sqClass_one, sqClass_eq_iff]
      exact ⟨1, one_ne_zero, by simp [FamilyFace.slotTwo]⟩
  map_add' P Q := by
    obtain ⟨h1, h2⟩ := FamilyFace.theFaceIsAHomomorphismOnEveryTwist hn P Q
    rw [← ofMul_mul]
    congr 1
    ext
    · change sqClass _ _ = sqClass _ _ * sqClass _ _
      rw [← sqClass_mul, sqClass_eq_iff]
      exact h1
    · change sqClass _ _ = sqClass _ _ * sqClass _ _
      rw [← sqClass_mul, sqClass_eq_iff]
      exact h2

theorem descentFace_eq_zero_iff (hn : n ≠ 0) (P : (FamilyFace.E n).Point) :
    descentFace n hn P = 0 ↔
      Descent.SqCls (FamilyFace.slotOne n P) 1 ∧ Descent.SqCls (FamilyFace.slotTwo n P) 1 := by
  change Additive.ofMul _ = Additive.ofMul 1 ↔ _
  rw [EmbeddingLike.apply_eq_iff_eq, Prod.ext_iff]
  simp only [Prod.fst_one, Prod.snd_one]
  rw [← sqClass_one, sqClass_eq_iff, sqClass_eq_iff]

/-- [definition] Doubling on the point group. -/
def doubling (n : ℚ) : (FamilyFace.E n).Point →+ (FamilyFace.E n).Point :=
  zsmulAddGroupHom 2

theorem doubling_apply (P : (FamilyFace.E n).Point) : doubling n P = P + P := by
  simp [doubling, two_zsmul]

theorem slotOneAt_eq (P : (FamilyFace.E n).Point) :
    FamilyKernel.slotOneAt n P = FamilyFace.slotOne n P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

theorem slotTwoAt_eq (P : (FamilyFace.E n).Point) :
    FamilyKernel.slotTwoAt n P = FamilyFace.slotTwo n P := by
  rcases P with _ | ⟨x, y, h⟩ <;> rfl

/-- [proved-derived; formal-checked] **The kernel of the descent face is the doubles**, the
`FamilyImage.theTwoDescentIsExactAtEveryModulus` read as a subgroup equality. -/
theorem ker_descentFace (hn : 0 < n) : (descentFace n hn.ne').ker = (doubling n).range := by
  ext P
  rw [AddMonoidHom.mem_ker, descentFace_eq_zero_iff, AddMonoidHom.mem_range, ← slotOneAt_eq,
    ← slotTwoAt_eq, FamilyImage.theTwoDescentIsExactAtEveryModulus n hn P]
  simp only [doubling_apply]

/-- [proved-derived; formal-checked] **`E →[2] E →φ (ℚˣ/ℚˣ²)²` is exact.** -/
theorem descent_exact (hn : 0 < n) : Function.Exact (doubling n) (descentFace n hn.ne') := by
  intro P
  rw [← AddMonoidHom.mem_ker, ker_descentFace hn, AddMonoidHom.mem_range]
  rfl

/-- [definition] **The obstruction** `E(ℚ)/2E(ℚ)`: the cokernel of doubling. -/
abbrev Obstruction (n : ℚ) : Type := (FamilyFace.E n).Point ⧸ (doubling n).range

/-- [definition] The descent face read on the obstruction. -/
def obstructionFace (hn : 0 < n) : Obstruction n →+ Additive (SquareClass × SquareClass) :=
  QuotientAddGroup.lift (doubling n).range (descentFace n hn.ne') (ker_descentFace hn).ge

/-- [proved-derived; formal-checked] **The descent face reads the obstruction faithfully.** -/
theorem obstruction_read_faithfully (hn : 0 < n) : Function.Injective (obstructionFace hn) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  induction c using QuotientAddGroup.induction_on with
  | H P =>
    rw [obstructionFace, QuotientAddGroup.lift_mk] at hc
    rw [QuotientAddGroup.eq_zero_iff, ← ker_descentFace hn]
    exact hc

/-- [proved-derived; formal-checked] **An escaping point** (not a double) is reachable only in the
multiple `2` of the doubles: its obstruction class is nonzero `2`-torsion
(`CokernelCalculus.theMultipleReachableClassIsTorsionInTheCokernel`), and its face is nonzero. -/
theorem escaping_point (hn : 0 < n) (P : (FamilyFace.E n).Point) (hP : P ∉ (doubling n).range) :
    ReachableOnlyInMultiple (Set.range (doubling n)) P 2 ∧
      (2 : ℤ) • QuotientAddGroup.mk' (doubling n).range P = 0 ∧
      QuotientAddGroup.mk' (doubling n).range P ≠ 0 ∧ descentFace n hn.ne' P ≠ 0 := by
  have hR : ReachableOnlyInMultiple (Set.range (doubling n)) P 2 := by
    refine ⟨by norm_num, ?_, ?_⟩
    · rw [closure_range]
      exact ⟨P, rfl⟩
    · rw [closure_range]
      exact hP
  obtain ⟨-, htor, hne⟩ := (reachableOnlyInMultiple_iff _ P 2).mp hR
  refine ⟨hR, htor, hne, fun h => hP ?_⟩
  rw [← ker_descentFace hn]
  exact h

/-! ## 4. The field closes the gap at `𝔽₂` -/

theorem sqClass_sq (a : SquareClass) : a ^ 2 = 1 := by
  induction a using QuotientGroup.induction_on with
  | H u =>
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨u, rfl⟩

/-- [proved-derived; formal-checked] The square classes are killed by `2`. -/
theorem squareClasses_two_torsion (x : Additive (SquareClass × SquareClass)) : 2 • x = 0 := by
  change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
  congr 1
  ext <;> simp [sqClass_sq]

/-- [definition] The `𝔽₂`-vector space of square-class pairs. -/
abbrev squareClassesF2 : Module (ZMod 2) (Additive (SquareClass × SquareClass)) :=
  AddCommGroup.zmodModule squareClasses_two_torsion

/-- [definition] The `𝔽₂`-vector space of the obstruction: the doubles contain every `2 • P`. -/
abbrev obstructionF2 (n : ℚ) : Module (ZMod 2) (Obstruction n) :=
  QuotientAddGroup.zmodModule (n := 2) fun P => ⟨P, by rw [doubling_apply, two_nsmul]⟩

attribute [local instance] squareClassesF2 obstructionF2

/-- [definition] **The descended face over `𝔽₂`.** -/
def descentFaceF2 (hn : 0 < n) :
    Obstruction n →ₗ[ZMod 2] Additive (SquareClass × SquareClass) :=
  (obstructionFace hn).toZModLinearMap 2

/-- [proved-derived; formal-checked] **Over `𝔽₂` the descended face has zero kernel**: the face
releases nothing of the obstruction. -/
theorem ker_descentFaceF2 (hn : 0 < n) : LinearMap.ker (descentFaceF2 hn) = ⊥ :=
  LinearMap.ker_eq_bot.mpr (obstruction_read_faithfully hn)

/-- [proved-derived; formal-checked] **A square class is realized by a point exactly when every
`𝔽₂`-cocycle killing the realized classes kills it**, the instance of
`FaceMap.reachable_iff_cocycles_vanish` at `K = 𝔽₂`. -/
theorem descent_realized_iff_cocycles_vanish (hn : 0 < n)
    (c : Additive (SquareClass × SquareClass)) :
    c ∈ (descentFace n hn.ne').range ↔
      ∀ ω : Holonics.Objects.Pairing.Coholon (ZMod 2) (Additive (SquareClass × SquareClass)),
        (descentFaceF2 hn).dualMap ω = 0 → ω c = 0 := by
  rw [← Holonics.Compression.Core.FaceMap.reachable_iff_cocycles_vanish]
  constructor
  · rintro ⟨P, rfl⟩
    exact ⟨QuotientAddGroup.mk P, rfl⟩
  · rintro ⟨c', rfl⟩
    induction c' using QuotientAddGroup.induction_on with
    | H P => exact ⟨P, rfl⟩

/-- [proved-derived; formal-checked] **The field face map's exact sequence at `𝔽₂`**
(`FaceMap.exact_sequence`) for the descended face. -/
theorem descent_exact_sequence_F2 (hn : 0 < n) :
    Function.Injective (LinearMap.ker (descentFaceF2 hn)).subtype ∧
      Function.Exact (LinearMap.ker (descentFaceF2 hn)).subtype (descentFaceF2 hn) ∧
      Function.Exact (descentFaceF2 hn) (LinearMap.range (descentFaceF2 hn)).mkQ ∧
      Function.Surjective (LinearMap.range (descentFaceF2 hn)).mkQ :=
  Holonics.Compression.Core.FaceMap.exact_sequence _

section Audit
#print axioms integral_reachable_iff_cokernelClass_zero
#print axioms reachableOnlyInMultiple_iff
#print axioms integer_cocycles_miss_the_torsion_class
#print axioms range_integralFace
#print axioms range_rationalFace
#print axioms integral_rational_gap
#print axioms hodge_kollar_class
#print axioms kollar_witness
#print axioms sqCls_iff
#print axioms descentFace
#print axioms ker_descentFace
#print axioms descent_exact
#print axioms obstruction_read_faithfully
#print axioms escaping_point
#print axioms squareClasses_two_torsion
#print axioms ker_descentFaceF2
#print axioms descent_realized_iff_cocycles_vanish
#print axioms descent_exact_sequence_F2
end Audit

end Descent

end Holonics.Landmarks.IntegralCokernel
