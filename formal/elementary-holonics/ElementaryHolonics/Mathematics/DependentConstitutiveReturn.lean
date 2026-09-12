import Mathlib
import ElementaryHolonics.Computation.HolonicConstitutiveFibre

/-!
# Dependent constitutive returns

An update family is indexed by one source parameter.  Projections are taken
after specializing that same parameter; they are not a union of separately
learned rows.  The final examples record two elementary obstructions to
recovering a joint from its projections.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.DependentConstitutiveReturn

open Soma.Holonics.Computation.HolonicConstitutiveFibre

universe u v w

/-- A family of point laws, with one shared source parameter `θ`. -/
def UpdateFamily (Θ : Type u) (X : Θ → Type v) (Y : Θ → Type w) :=
  ∀ θ, X θ → Y θ

variable {Θ : Type u} {X : Θ → Type v} {A B : Θ → Type w}

/-- The two projections of one dependent update family. -/
def projectPair (u : UpdateFamily Θ X (fun θ => A θ × B θ)) :
    UpdateFamily Θ X A × UpdateFamily Θ X B :=
  (fun θ x => (u θ x).1, fun θ x => (u θ x).2)

theorem projectPair_apply (u : UpdateFamily Θ X (fun θ => A θ × B θ))
    (θ : Θ) (x : X θ) :
    (projectPair u).1 θ x = (u θ x).1 ∧
      (projectPair u).2 θ x = (u θ x).2 := by
  constructor <;> rfl

theorem pair_reconstruct (u : UpdateFamily Θ X (fun θ => A θ × B θ))
    (θ : Θ) (x : X θ) :
    ((projectPair u).1 θ x, (projectPair u).2 θ x) = u θ x := by
  rfl

/-! ## Ordered evaluation at one shared source parameter -/

def liftedWord {Z : Θ → Type v}
    (word : List (∀ θ, Z θ → Z θ)) (θ : Θ) (initial : Z θ) : Z θ :=
  word.foldl (fun state step => step θ state) initial

theorem liftedWord_singleton {Z : Θ → Type v}
    (step : ∀ θ, Z θ → Z θ) (θ : Θ) (initial : Z θ) :
    liftedWord [step] θ initial = step θ initial := by
  rfl

theorem liftedWord_append {Z : Θ → Type v}
    (word : List (∀ θ, Z θ → Z θ)) (step : ∀ θ, Z θ → Z θ)
    (θ : Θ) (initial : Z θ) :
    liftedWord (word ++ [step]) θ initial =
      step θ (liftedWord word θ initial) := by
  simp [liftedWord, List.foldl_append]

theorem ordered_word_evaluation_is_pointwise
    {Z : Θ → Type v} (word : List (∀ θ, Z θ → Z θ))
    (initial : ∀ θ, Z θ) (θ : Θ) :
    (word.foldl (fun family step => fun θ => step θ (family θ)) initial) θ =
      liftedWord word θ (initial θ) := by
  induction word generalizing initial with
  | nil => rfl
  | cons step word ih =>
    simpa only [List.foldl_cons, liftedWord] using
      ih (fun θ => step θ (initial θ))

theorem ordered_word_order_separator :
    liftedWord [fun _ : Unit => fun n : ℕ => n + 1,
      fun _ : Unit => fun n : ℕ => 2 * n] () 1 = 4 ∧
      liftedWord [fun _ : Unit => fun n : ℕ => 2 * n,
        fun _ : Unit => fun n : ℕ => n + 1] () 1 = 3 := by
  norm_num [liftedWord]

section PairedMaterial

universe uI uV uW

variable {I : Type uI} {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [AddCommGroup W]
variable [Module ℚ V] [Module ℚ W]

/- A dependent material return adjoins one paired operand under each `θ` assignment.
   The definition does not union the rows over `θ`; every result remains a
   separate submodule carrying the same parameter into both coordinates. -/
def dependentFormation (x : I → V) (y : I → W)
    (sx : Θ → V) (sy : Θ → W) (θ : Θ) : Submodule ℚ (V × W) :=
  addPairedCurrentSubmodule x y (sx θ) (sy θ)

theorem dependentFormation_contains_original (x : I → V) (y : I → W)
    (sx : Θ → V) (sy : Θ → W) (θ : Θ) :
    pairedCurrentSubmodule x y ≤ dependentFormation x y sx sy θ := by
  exact le_sup_left

theorem dependentFormation_contains_new_pair (x : I → V) (y : I → W)
    (sx : Θ → V) (sy : Θ → W) (θ : Θ) :
    (sx θ, sy θ) ∈ dependentFormation x y sx sy θ := by
  change (sx θ, sy θ) ∈
    pairedCurrentSubmodule x y ⊔ Submodule.span ℚ {(sx θ, sy θ)}
  have hle : Submodule.span ℚ {(sx θ, sy θ)} ≤
      pairedCurrentSubmodule x y ⊔ Submodule.span ℚ {(sx θ, sy θ)} := le_sup_right
  exact hle (Submodule.subset_span (Set.mem_singleton (sx θ, sy θ)))

theorem dependentFormation_point_specialization (x : I → V) (y : I → W)
    (sx : Θ → V) (sy : Θ → W) (θ : Θ) :
    pairedCurrentSubmodule (sumUnitSource x (sx θ)) (sumUnitReturn y (sy θ)) =
      dependentFormation x y sx sy θ := by
  exact pairedCurrentSubmodule_sumUnit_eq_add x y (sx θ) (sy θ)

end PairedMaterial

section ReceiverCoordinates

universe uΘ uV uY

variable {Θ₀ : Type uΘ} {V₀ : Type uV} {Y₀ : Type uY}
variable [AddCommGroup Θ₀] [Module ℚ Θ₀]
variable [AddCommGroup V₀] [Module ℚ V₀]

/- A receiver coordinate packet decodes through one affine map.  Its kernel
   records coordinate aliases; it is not a unique cause decoder. -/
def decodedFace (origin : V₀) (D : Θ₀ →ₗ[ℚ] V₀) (θ : Θ₀) : V₀ :=
  origin + D θ

theorem decodedFace_eq_iff_kernel_difference
    (origin : V₀) (D : Θ₀ →ₗ[ℚ] V₀) (θ₁ θ₂ : Θ₀) :
    decodedFace origin D θ₁ = decodedFace origin D θ₂ ↔
      θ₁ - θ₂ ∈ LinearMap.ker D := by
  constructor
  · intro h
    apply LinearMap.mem_ker.mpr
    rw [map_sub]
    exact sub_eq_zero.mpr (add_left_cancel h)
  · intro h
    have hzero : D θ₁ - D θ₂ = 0 := by
      rw [← map_sub]
      exact LinearMap.mem_ker.mp h
    have hd : D θ₁ = D θ₂ := sub_eq_zero.mp hzero
    simp [decodedFace, hd]

theorem decodedFace_aliases_agree
    (origin : V₀) (D : Θ₀ →ₗ[ℚ] V₀) (θ₁ θ₂ : Θ₀)
    (hθ : θ₁ - θ₂ ∈ LinearMap.ker D) (next : V₀ → Y₀) :
    next (decodedFace origin D θ₁) = next (decodedFace origin D θ₂) := by
  congr 1
  exact (decodedFace_eq_iff_kernel_difference origin D θ₁ θ₂).mpr hθ

end ReceiverCoordinates

/-- The scalar law `x*h = 2` is not affine in the paired `(x,h)` coordinates. -/
theorem scalar_law_midpoint_obstruction :
    ((1 : ℝ) * 2 = 2) ∧ (2 : ℝ) * 1 = 2 ∧
      (3 / 2 : ℝ) * (3 / 2) ≠ 2 := by
  norm_num

def sign (x : ℝ) : Prop := x = 1 ∨ x = -1

def plusRelation (x y : ℝ) : Prop := sign x ∧ y = x
def minusRelation (x y : ℝ) : Prop := sign x ∧ y = -x

def leftMarginal (r : ℝ → ℝ → Prop) (x : ℝ) : Prop := ∃ y, r x y
def rightMarginal (r : ℝ → ℝ → Prop) (y : ℝ) : Prop := ∃ x, r x y

theorem plus_leftMarginal (x : ℝ) :
    leftMarginal plusRelation x ↔ sign x := by
  constructor
  · rintro ⟨y, hx, _⟩
    exact hx
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem minus_leftMarginal (x : ℝ) :
    leftMarginal minusRelation x ↔ sign x := by
  constructor
  · rintro ⟨y, hx, _⟩
    exact hx
  · intro hx
    exact ⟨-x, hx, by ring⟩

theorem plus_rightMarginal (y : ℝ) :
    rightMarginal plusRelation y ↔ sign y := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    rcases hy with rfl | rfl
    · exact ⟨1, Or.inl rfl, rfl⟩
    · exact ⟨-1, Or.inr rfl, rfl⟩

theorem minus_rightMarginal (y : ℝ) :
    rightMarginal minusRelation y ↔ sign y := by
  constructor
  · rintro ⟨x, hx, hxy⟩
    rcases hx with rfl | rfl <;> simp_all [sign]
  · intro hy
    rcases hy with rfl | rfl
    · exact ⟨-1, Or.inr rfl, by norm_num⟩
    · exact ⟨1, Or.inl rfl, by norm_num⟩

theorem equal_marginals_different_joint (x : ℝ) :
    leftMarginal plusRelation x ↔ leftMarginal minusRelation x := by
  rw [plus_leftMarginal, minus_leftMarginal]

theorem equal_right_marginals_different_joint (y : ℝ) :
    rightMarginal plusRelation y ↔ rightMarginal minusRelation y := by
  rw [plus_rightMarginal, minus_rightMarginal]

theorem joint_separator : plusRelation 1 1 ∧ ¬ minusRelation 1 1 := by
  constructor
  · exact ⟨Or.inl rfl, rfl⟩
  · simp [minusRelation, sign]
    norm_num

/-! ## One-row unit-admittance contact -/

def dot (u v : ℝ × ℝ) : ℝ := u.1 * v.1 + u.2 * v.2

def unitContact (u h : ℝ × ℝ) (b : ℝ) : ℝ × ℝ :=
  (h.1 + ((b - dot u h) / dot u u) * u.1,
    h.2 + ((b - dot u h) / dot u u) * u.2)

theorem unitContact_satisfies {u h : ℝ × ℝ} {b : ℝ}
    (hu : dot u u ≠ 0) : dot u (unitContact u h b) = b := by
  simp [unitContact, dot]
  have hu' : u.1 ^ 2 + u.2 ^ 2 ≠ 0 := by
    simpa [dot, pow_two] using hu
  field_simp [hu']
  ring

theorem unitContact_preserves_tangent {u h t : ℝ × ℝ} {b : ℝ}
    (hu : dot u u ≠ 0) (ht : dot t u = 0) :
    dot t (unitContact u h b) = dot t h := by
  simp [unitContact, dot]
  have hu' : u.1 ^ 2 + u.2 ^ 2 ≠ 0 := by
    simpa [dot, pow_two] using hu
  field_simp [hu']
  simp only [dot] at ht
  linear_combination (b - (h.1 * u.1 + h.2 * u.2)) * ht

def sourceDependentContact (a : ℝ) : ℝ × ℝ :=
  unitContact (1, a) (1, 0) 2

theorem sourceDependentContact_values :
    sourceDependentContact 1 = (3 / 2, 1 / 2) ∧
      sourceDependentContact 2 = (6 / 5, 2 / 5) := by
  constructor <;> norm_num [sourceDependentContact, unitContact, dot]

theorem sourceDependentContact_not_affine_graph :
    (sourceDependentContact (3 / 2)).1 ≠
      ((sourceDependentContact 1 + sourceDependentContact 2) / 2 : ℝ × ℝ).1 := by
  norm_num [sourceDependentContact, unitContact, dot]

/-- Agreement at the declared source receiver does not identify the whole generator. -/
theorem one_receiver_does_not_determine_generator :
    sourceDependentContact 1 = (fun _ : ℝ => sourceDependentContact 1) 1 ∧
      sourceDependentContact ≠ (fun _ : ℝ => sourceDependentContact 1) := by
  constructor
  · rfl
  · intro equal
    have at_two := congrFun equal 2
    norm_num [sourceDependentContact, unitContact, dot] at at_two

/-! ## Joined relational returns

The source support of a returned relation is computed from the complete joined
pairs.  Reapplying the relation to that support alone forgets the target-side
constraint, so it can admit a target that the joined return excluded.
-/

section JoinedRelations

variable {X Y Z : Type*}

def relationalPreimage (R : X → Y → Prop) (G : Set Y) : Set X :=
  {x | ∃ y, R x y ∧ y ∈ G}

def joinedRelation (F : Set X) (R : X → Y → Prop) (G : Set Y) : X → Y → Prop :=
  fun x y => x ∈ F ∧ R x y ∧ y ∈ G

def supportedSource (F : Set X) (R : X → Y → Prop) (G : Set Y) : Set X :=
  {x | x ∈ F ∧ ∃ y, R x y ∧ y ∈ G}

theorem supportedSource_eq_inter_relationalPreimage
    (F : Set X) (R : X → Y → Prop) (G : Set Y) :
    supportedSource F R G = F ∩ relationalPreimage R G := by
  ext x
  rfl

theorem joinedRelation_mem_iff
    (F : Set X) (R : X → Y → Prop) (G : Set Y) (x : X) (y : Y) :
    joinedRelation F R G x y ↔ x ∈ F ∧ R x y ∧ y ∈ G := by
  rfl

theorem joinedRelation_source_supported
    (F : Set X) (R : X → Y → Prop) (G : Set Y)
    {x : X} {y : Y} (hxy : joinedRelation F R G x y) :
    x ∈ supportedSource F R G := by
  exact ⟨hxy.1, y, hxy.2.1, hxy.2.2⟩

def serialRelation (R : X → Y → Prop) (S : Y → Z → Prop) : X → Z → Prop :=
  fun x z => ∃ y, R x y ∧ S y z

theorem relationalPreimage_serial
    (R : X → Y → Prop) (S : Y → Z → Prop) (H : Set Z) :
    relationalPreimage (serialRelation R S) H =
      relationalPreimage R (relationalPreimage S H) := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hR, hS⟩, hz⟩
    exact ⟨y, hR, z, hS, hz⟩
  · rintro ⟨y, hR, z, hS, hz⟩
    exact ⟨z, ⟨y, hR, hS⟩, hz⟩

theorem relationalPreimage_serial_joined_middle
    (R : X → Y → Prop) (S : Y → Z → Prop) (M : Set Y) (H : Set Z) :
    relationalPreimage (serialRelation R (joinedRelation M S Set.univ)) H =
      relationalPreimage R (M ∩ relationalPreimage S H) := by
  ext x
  constructor
  · rintro ⟨z, ⟨y, hR, hyM, hS, _, _⟩, hz⟩
    exact ⟨y, hR, hyM, z, hS, hz⟩
  · rintro ⟨y, hR, hyM, z, hS, hz⟩
    exact ⟨z, ⟨y, hR, hyM, hS, Set.mem_univ z⟩, hz⟩

theorem bool_serial_middle_constraint_counterexample :
    let R : Bool → Bool → Prop := fun x y => x = y
    let S : Bool → Unit → Prop := fun _ _ => True
    let M : Set Bool := {false}
    let H : Set Unit := {()}
    true ∈ relationalPreimage (serialRelation R S) H ∧
      true ∉ relationalPreimage (serialRelation R (joinedRelation M S Set.univ)) H := by
  simp [relationalPreimage, serialRelation, joinedRelation]

/- The converse of a relation can be used as a relational constraint; this
   serial law keeps the direction of time in `R` then `S`. -/

def broadReturnRelation (x _y : Bool) : Prop := x = true

def allowedTrue : Set Bool := {true}

theorem supportedSource_reapplication_can_reintroduce_disallowed_target :
    ∃ x y : Bool,
      x ∈ supportedSource allowedTrue broadReturnRelation allowedTrue ∧
      broadReturnRelation x y ∧ y ∉ allowedTrue := by
  refine ⟨true, false, ?_⟩
  simp [supportedSource, broadReturnRelation, allowedTrue]

end JoinedRelations

end Soma.Holonics.Mathematics.DependentConstitutiveReturn
