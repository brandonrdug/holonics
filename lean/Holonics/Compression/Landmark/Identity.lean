import Holonics.Geometry.TwoSidedIdentityAtlas
import Holonics.Mathematics.RatioSeriesTransport
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# The identity atlas: an identity is two constructions with one face

[definition] A receiver reads constructions through a **face map** `F : C → V`. An **identity** is
two constructions with one face, `F c₁ = F c₂`: a pair in the kernel of the face. For polynomial
constructions on a configuration `V ⊆ Kˢ` the face is evaluation on `V`, a ring map, so an
identity is a difference in its kernel, the **identity ideal** of `V`
([identity-atlas plan](https://github.com/brandonrdug/holonics/blob/13f8c734/docs/plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md)).
A landmark search certifies candidate identities on **charts** (parametrizations into `V`); the
coverage lesson is which chart families may certify.

[proved-derived; formal-checked] What is proved.

1. **Two constructions, one face.** An identity is a difference in the kernel of the face
   (`identity_iff_sub_mem_identityIdeal`). The ratio-series block face identifies the distinct
   routes `[1,1,1]` and `[1/2, 3, 2/3]` although their interiors differ
   (`ratio_routes_are_an_identity`, over `Mathematics/RatioSeriesTransport`).
2. **Finiteness of the identities** (Hilbert's basis theorem, imported from Mathlib): the identity
   ideal of any configuration in finitely many variables over a field is finitely generated
   (`identityIdeal_fg`).
3. **The coverage law, for the atlas's polynomial receivers.** A chart family certifies a
   polynomial exactly when the polynomial lies in the identity ideal of the union of its images
   (`certified_eval_iff`). A family certifies exactly the identities of `V` exactly when
   `I(⋃ images) = I(V)` (`certifies_exactly_iff`); for a sound family (landing in `V`) that holds
   exactly when `V` lies in the Zariski closure of the images (`identityIdeal_eq_iff_dense`). This
   is checked per component: missing a point is harmless, missing a component is not. For
   arbitrary (non-polynomial)
   receivers the same question needs pointwise covering (`certification_sound_iff_covers`, proved
   with an indicator receiver), which the identity atlas does not use.
4. **The recorded case.** On the Galilean fibre `C² = 1` of the two-sided angle (`k = 0`, the
   owner `Geometry/TwoSidedIdentityAtlas`), both winding charts are sound. The principal winding
   misses the component `C = −1`, so its image has a strictly larger identity ideal: it certifies
   `C − 1`, which is not an identity (`principal_winding_invents_an_identity`, derived from the
   owner's `galileanPrincipalChartIsNotTheFibre`; `principal_image_ideal_strictly_larger`). The
   two-winding family covers the fibre (`two_windings_cover`), its image ideal is the fibre's
   (`two_windings_image_ideal`), and it certifies exactly the fibre's identities
   (`two_windings_certify_exactly`). In the ideal:
   `C² − 1` is an identity and `C − 1` is not (`galilean_identity_ideal`).

[counterexample; formal-checked] **Coverage is sufficient, not necessary, for polynomial
receivers.** The chart of the punctured plane misses the origin, yet its image ideal is the
plane's, so it certifies exactly the plane's identities (`punctured_plane_certifies_exactly`).
Likewise a polynomial in one variable certified on the natural numbers vanishes on all of `ℚ`
(`polynomial_density_suffices`). For polynomial receivers a Zariski-dense chart suffices, which is
the identity atlas's coverage/density certificate (I1).

[open] Owed in #62, not proved here.
- **Gröbner completion and the kernel equality.** Buchberger's algorithm halts on a supplied finite
  presentation (Dickson's lemma) and certifies a Gröbner basis *of the ideal supplied*; an
  all-degree claim additionally owes `J = ker(face)` (elimination with saturation, or a certified
  Hilbert bound). Neither Buchberger's termination nor that equality is formalized.
- **Richardson undecidability.** Identity of general expressions in `exp`, `sin`, `|·|`, `π` is
  undecidable; the holonomic (D-finite) class is where equality is certified by an annihilator
  and initial data. The Rust consumer (`holonics::compression::landmark::identity`) searches
  polynomial identities on one-parameter rational charts only; a holonomic search is owed in #62
  with this item.
- **The chart's density and the dimension certificate.** The Rust consumer covers a declared
  irreducible curve by one nonconstant chart landing in it (an infinite subset of an irreducible
  curve is Zariski dense in it) and certifies each component's declared dimension by a nonzero
  generator in every single coordinate (a point) or every pair of coordinates (a curve). Both are
  standard and neither is stated here.

No `axiom`, no `sorry`.
-/

namespace Holonics.Compression.Landmark.Identity

open Holonics.IdentityAtlas

/-! ## 1. Two constructions with one face -/

section Face

variable {C V : Type*}

/-- [definition] Two constructions form an identity for the receiver face `F` when they have one
face. -/
def IsIdentity (F : C → V) (c₁ c₂ : C) : Prop := F c₁ = F c₂

/-- [proved-derived; formal-checked] **The ratio-series block face identifies two routes** whose
interiors differ: `compile [1,1,1] = compile [1/2, 3, 2/3]`, yet their first partial sums are
distinct. An identity is two constructions, not one. -/
theorem ratio_routes_are_an_identity :
    IsIdentity Holonics.Mathematics.RatioSeriesTransport.compile [1, 1, 1]
        [(1 : ℚ) / 2, 3, (2 : ℚ) / 3] ∧
      ([1, 1, 1] : List ℚ) ≠ [(1 : ℚ) / 2, 3, (2 : ℚ) / 3] ∧
      (Holonics.Mathematics.RatioSeriesTransport.step 1 (1, 0)).2 ≠
        (Holonics.Mathematics.RatioSeriesTransport.step ((1 : ℚ) / 2) (1, 0)).2 :=
  ⟨Holonics.Mathematics.RatioSeriesTransport.distinct_routes_same_block, by norm_num,
    Holonics.Mathematics.RatioSeriesTransport.equal_block_different_interior⟩

end Face

section Polynomial

variable {σ K : Type*} [Field K]

/-- [definition] The evaluation face of polynomial constructions on a configuration `V`. -/
noncomputable def face (V : Set (σ → K)) : MvPolynomial σ K →+* (V → K) :=
  RingHom.pi fun x : V => MvPolynomial.eval (x : σ → K)

/-- [definition] The identity ideal of `V`: the kernel of its face. -/
noncomputable def identityIdeal (V : Set (σ → K)) : Ideal (MvPolynomial σ K) :=
  RingHom.ker (face V)

theorem face_apply (V : Set (σ → K)) (p : MvPolynomial σ K) (x : V) :
    face V p x = MvPolynomial.eval (x : σ → K) p := rfl

/-- [proved-derived; formal-checked] **An identity is a difference in the kernel of the face.** -/
theorem identity_iff_sub_mem_identityIdeal (V : Set (σ → K)) (p q : MvPolynomial σ K) :
    IsIdentity (face V) p q ↔ p - q ∈ identityIdeal V :=
  (RingHom.sub_mem_ker_iff (face V)).symm

/-- [proved-derived; formal-checked] Membership in the identity ideal is vanishing on `V`. -/
theorem mem_identityIdeal_iff (V : Set (σ → K)) (p : MvPolynomial σ K) :
    p ∈ identityIdeal V ↔ ∀ x ∈ V, MvPolynomial.eval x p = 0 := by
  rw [identityIdeal, RingHom.mem_ker]
  constructor
  · intro h x hx
    exact congrFun h ⟨x, hx⟩
  · intro h
    funext x
    exact h x x.2

/-- [proved-standard; formal-checked] **The identities are finitely generated** (Hilbert's basis
theorem, from Mathlib): in finitely many variables over a field, every configuration's identity
ideal has a finite generating family. -/
theorem identityIdeal_fg [Finite σ] (V : Set (σ → K)) : (identityIdeal V).FG :=
  IsNoetherian.noetherian _

end Polynomial

/-! ## 2. The coverage law -/

section Coverage

variable {X R ι : Type*} [Zero R] {P : ι → Type*}

/-- [definition] A receiver `f` vanishes on the configuration `V`: it reads an identity there. -/
def VanishesOn (V : Set X) (f : X → R) : Prop := ∀ x ∈ V, f x = 0

/-- [definition] A chart family `χ` certifies the receiver `f` when `f` vanishes on every chart. -/
def Certified (χ : ∀ i, P i → X) (f : X → R) : Prop := ∀ i p, f (χ i p) = 0

/-- [proved-derived; formal-checked] A sound chart family certifies every true identity. -/
theorem certified_of_vanishes {V : Set X} {χ : ∀ i, P i → X} (hsound : ∀ i p, χ i p ∈ V)
    {f : X → R} (hf : VanishesOn V f) : Certified χ f :=
  fun i p => hf _ (hsound i p)

/-- [proved-derived; formal-checked] A covering chart family certifies only true identities. -/
theorem vanishes_of_certified {V : Set X} {χ : ∀ i, P i → X}
    (hcover : ∀ x ∈ V, ∃ i p, χ i p = x) {f : X → R} (hf : Certified χ f) : VanishesOn V f := by
  intro x hx
  obtain ⟨i, p, rfl⟩ := hcover x hx
  exact hf i p

/-- [proved-derived; formal-checked] **Arbitrary receivers need pointwise covering.** A chart family
certifies only true identities for every receiver `X → R` whatever exactly when it covers the
configuration; the proof uses the indicator of the images, which is no polynomial. The identity
atlas certifies polynomial receivers, whose law is `certifies_exactly_iff`. -/
theorem certification_sound_iff_covers [One R] [NeZero (1 : R)] (V : Set X)
    (χ : ∀ i, P i → X) :
    (∀ f : X → R, Certified χ f → VanishesOn V f) ↔ ∀ x ∈ V, ∃ i p, χ i p = x := by
  classical
  constructor
  · intro h x hx
    by_contra hnot
    let f : X → R := fun y => if ∃ i p, χ i p = y then 0 else 1
    have hcert : Certified χ f := by
      intro i p
      simp only [f]
      rw [if_pos ⟨i, p, rfl⟩]
    have := h f hcert x hx
    simp only [f, if_neg hnot] at this
    exact one_ne_zero this
  · intro hcover f hf
    exact vanishes_of_certified hcover hf

end Coverage


/-! ## 3. The coverage law for polynomial receivers -/

section PolynomialCoverage

variable {σ K ι : Type*} [Field K] {P : ι → Type*}

/-- [definition] The Zariski closure of a configuration: the common zeros of its identities. -/
def zariskiClosure (S : Set (σ → K)) : Set (σ → K) :=
  {x | ∀ p ∈ identityIdeal S, MvPolynomial.eval x p = 0}

theorem identityIdeal_antitone {S T : Set (σ → K)} (h : S ⊆ T) :
    identityIdeal T ≤ identityIdeal S := by
  intro p hp
  rw [mem_identityIdeal_iff] at hp ⊢
  exact fun x hx => hp x (h hx)

/-- [proved-derived; formal-checked] **A chart family certifies a polynomial exactly when it lies
in the identity ideal of the union of the images.** -/
theorem certified_eval_iff (χ : ∀ i, P i → σ → K) (p : MvPolynomial σ K) :
    Certified χ (fun x => MvPolynomial.eval x p) ↔ p ∈ identityIdeal (⋃ i, Set.range (χ i)) := by
  rw [mem_identityIdeal_iff]
  constructor
  · intro h x hx
    obtain ⟨i, ⟨q, rfl⟩⟩ := Set.mem_iUnion.mp hx
    exact h i q
  · intro h i q
    exact h _ (Set.mem_iUnion.mpr ⟨i, q, rfl⟩)

/-- [proved-derived; formal-checked] **The coverage law.** A chart family certifies exactly the
identities of `V` exactly when its images have the identity ideal of `V`. -/
theorem certifies_exactly_iff {V : Set (σ → K)} {χ : ∀ i, P i → σ → K} :
    (∀ p, Certified χ (fun x => MvPolynomial.eval x p) ↔ p ∈ identityIdeal V) ↔
      identityIdeal (⋃ i, Set.range (χ i)) = identityIdeal V := by
  simp only [certified_eval_iff]
  constructor
  · intro h
    ext p
    exact h p
  · intro h p
    rw [h]

/-- [proved-derived; formal-checked] **Density.** For a sound family, the image ideal is the
ideal of `V` exactly when `V` lies in the Zariski closure of the images. -/
theorem identityIdeal_eq_iff_dense {V : Set (σ → K)} {χ : ∀ i, P i → σ → K}
    (hsound : ∀ i q, χ i q ∈ V) :
    identityIdeal (⋃ i, Set.range (χ i)) = identityIdeal V ↔
      V ⊆ zariskiClosure (⋃ i, Set.range (χ i)) := by
  have hsub : (⋃ i, Set.range (χ i)) ⊆ V := by
    intro x hx
    obtain ⟨i, ⟨q, rfl⟩⟩ := Set.mem_iUnion.mp hx
    exact hsound i q
  constructor
  · intro h x hx p hp
    rw [h, mem_identityIdeal_iff] at hp
    exact hp x hx
  · intro h
    apply le_antisymm
    · intro p hp
      rw [mem_identityIdeal_iff]
      exact fun x hx => h hx p hp
    · exact identityIdeal_antitone hsub

end PolynomialCoverage

/-! ## 4. The recorded case: one winding invents `C − 1`, two windings refuse it -/

section Galilean

/-- [definition] The Galilean fibre of the two-sided circle: `C² + 0·S² = 1`, in `(C, S)`. -/
def galileanFibre : Set (Fin 2 → ℚ) := {x | x 0 ^ 2 = 1}

/-- [definition] The winding chart of the two-sided angle at `k = 0`: `t ↦ (C_e(t), S_e(t))`. -/
def windingChart (e : ℚ) (t : ℚ) : Fin 2 → ℚ := ![twoSidedCos e t 0, twoSidedSin e t 0]

/-- [definition] The principal chart family: the single winding `e = 1`. -/
def principalFamily : Unit → ℚ → Fin 2 → ℚ := fun _ => windingChart 1

/-- [definition] The two-winding family: `e = 1` and the half-turn `e = −1 = e^{iπ}`. -/
def twoWindingFamily : Bool → ℚ → Fin 2 → ℚ := fun b => windingChart (if b then 1 else -1)

/-- [definition] The receiver `C − 1`. -/
def cMinusOne (x : Fin 2 → ℚ) : ℚ := x 0 - 1

theorem windingChart_apply (e t : ℚ) :
    windingChart e t 0 = e ∧ windingChart e t 1 = 2 * e * t := by
  simp [windingChart, twoSidedCos, twoSidedSin]
  ring

/-- [proved-derived; formal-checked] Every winding chart with `e² = 1` lands in the fibre
(`twoSidedPythagoras` at `k = 0`). -/
theorem windingChart_sound (e : ℚ) (he : e ^ 2 = 1) (t : ℚ) : windingChart e t ∈ galileanFibre := by
  have h := twoSidedPythagoras e t (0 : ℚ) he (by norm_num)
  simp only [galileanFibre, Set.mem_ofPred_eq, windingChart]
  simpa using h

/-- [counterexample; formal-checked] **One winding invents an identity**, read from the owner's
falsifier `IdentityAtlas.galileanPrincipalChartIsNotTheFibre`: the principal chart is sound and
certifies `C − 1` (its cosine is `1`), yet the half-turn winding's point lies on the fibre with
`C − 1 ≠ 0`. -/
theorem principal_winding_invents_an_identity :
    (∀ i t, principalFamily i t ∈ galileanFibre) ∧ Certified principalFamily cMinusOne ∧
      ¬ VanishesOn galileanFibre cMinusOne := by
  refine ⟨fun _ t => windingChart_sound 1 (by norm_num) t, ?_, ?_⟩
  · intro _ t
    simp [cMinusOne, principalFamily, windingChart, (galileanPrincipalChartIsNotTheFibre t).1]
  · intro h
    obtain ⟨-, -, hon, hne⟩ := galileanPrincipalChartIsNotTheFibre 0
    apply hne
    have := h (windingChart (-1) 0) (by
      simp only [galileanFibre, Set.mem_ofPred_eq, windingChart]
      simpa using hon)
    simpa [cMinusOne, windingChart] using this

/-- [proved-derived; formal-checked] **Two windings cover the fibre.** `(C, S)` with `C² = 1` is the
chart point `e = C`, `t = S·C/2`. -/
theorem two_windings_cover : ∀ x ∈ galileanFibre, ∃ b t, twoWindingFamily b t = x := by
  intro x hx
  simp only [galileanFibre, Set.mem_ofPred_eq] at hx
  have hC : x 0 = 1 ∨ x 0 = -1 := by
    have : (x 0 - 1) * (x 0 + 1) = 0 := by linear_combination hx
    rcases mul_eq_zero.mp this with h | h
    · left; linarith
    · right; linarith
  rcases hC with h | h
  · refine ⟨true, x 1 / 2, ?_⟩
    funext j
    fin_cases j
    · simp [twoWindingFamily, (windingChart_apply 1 _).1, h]
    · simp [twoWindingFamily, (windingChart_apply 1 _).2]
      ring
  · refine ⟨false, -(x 1) / 2, ?_⟩
    funext j
    fin_cases j
    · simp [twoWindingFamily, (windingChart_apply (-1) _).1, h]
    · simp [twoWindingFamily, (windingChart_apply (-1) _).2]
      ring

/-- [proved-derived; formal-checked] **The two-winding family certifies exactly the fibre's
identities**, for every receiver, and so refuses `C − 1`. -/
theorem two_windings_certify_exactly :
    (∀ f : (Fin 2 → ℚ) → ℚ, Certified twoWindingFamily f ↔ VanishesOn galileanFibre f) ∧
      ¬ Certified twoWindingFamily cMinusOne := by
  have hsound : ∀ b t, twoWindingFamily b t ∈ galileanFibre := by
    intro b t
    cases b <;> exact windingChart_sound _ (by norm_num) t
  refine ⟨fun f => ⟨vanishes_of_certified two_windings_cover, certified_of_vanishes hsound⟩, ?_⟩
  intro h
  have := h false 0
  simp [cMinusOne, twoWindingFamily, (windingChart_apply (-1) 0).1] at this
  norm_num at this

/-- [proved-derived; formal-checked] **In the identity ideal:** `C² − 1` is an identity of the
Galilean fibre and `C − 1` is not. -/
theorem galilean_identity_ideal :
    (MvPolynomial.X 0 ^ 2 - 1 : MvPolynomial (Fin 2) ℚ) ∈ identityIdeal galileanFibre ∧
      (MvPolynomial.X 0 - 1 : MvPolynomial (Fin 2) ℚ) ∉ identityIdeal galileanFibre := by
  constructor
  · rw [mem_identityIdeal_iff]
    intro x hx
    simp only [galileanFibre, Set.mem_ofPred_eq] at hx
    simp [hx]
  · rw [mem_identityIdeal_iff]
    intro h
    have := h ![-1, 0] (by simp [galileanFibre])
    simp at this
    norm_num at this

end Galilean

/-- [counterexample; formal-checked] **The principal image misses a component, so its identity
ideal is strictly larger**: `C − 1` lies in it and not in the fibre's ideal. -/
theorem principal_image_ideal_strictly_larger :
    identityIdeal galileanFibre < identityIdeal (⋃ i, Set.range (principalFamily i)) := by
  have hsub : (⋃ i, Set.range (principalFamily i)) ⊆ galileanFibre := by
    intro x hx
    obtain ⟨i, ⟨t, rfl⟩⟩ := Set.mem_iUnion.mp hx
    exact principal_winding_invents_an_identity.1 i t
  refine lt_of_le_of_ne (identityIdeal_antitone hsub) fun h => ?_
  apply galilean_identity_ideal.2
  rw [h, ← certified_eval_iff]
  intro i t
  have := principal_winding_invents_an_identity.2.1 i t
  simpa [cMinusOne] using this

/-- [proved-derived; formal-checked] **The two-winding image has the fibre's identity ideal**, so
by the coverage law it certifies exactly the fibre's polynomial identities. -/
theorem two_windings_image_ideal :
    identityIdeal (⋃ b, Set.range (twoWindingFamily b)) = identityIdeal galileanFibre := by
  have hsound : ∀ b t, twoWindingFamily b t ∈ galileanFibre := by
    intro b t
    cases b <;> exact windingChart_sound _ (by norm_num) t
  rw [identityIdeal_eq_iff_dense hsound]
  intro x hx p hp
  rw [mem_identityIdeal_iff] at hp
  obtain ⟨b, t, rfl⟩ := two_windings_cover x hx
  exact hp _ (Set.mem_iUnion.mpr ⟨b, t, rfl⟩)

/-! ## 5. The limit: density suffices for polynomial receivers -/

/-- [definition] The chart of the punctured plane: every nonzero point, nothing at the origin. -/
def puncturedChart : Unit → {x : Fin 2 → ℚ // x ≠ 0} → Fin 2 → ℚ := fun _ x => x.1

/-- [counterexample; formal-checked] **Missing a point is harmless.** The punctured chart does not
cover the plane, yet its image has the plane's identity ideal (zero), so it certifies exactly the
plane's polynomial identities: a polynomial vanishing off the origin times `X₀` vanishes
everywhere. -/
theorem punctured_plane_certifies_exactly :
    (0 : Fin 2 → ℚ) ∉ ⋃ i, Set.range (puncturedChart i) ∧
      identityIdeal (⋃ i, Set.range (puncturedChart i)) =
        identityIdeal (Set.univ : Set (Fin 2 → ℚ)) := by
  constructor
  · intro h
    obtain ⟨_, ⟨x, hx⟩⟩ := Set.mem_iUnion.mp h
    exact x.2 hx
  · apply le_antisymm
    · intro p hp
      rw [mem_identityIdeal_iff] at hp ⊢
      have hprod : p * MvPolynomial.X 0 = 0 := by
        apply MvPolynomial.funext
        intro x
        rw [map_mul, MvPolynomial.eval_X, map_zero]
        by_cases hx : x = 0
        · simp [hx]
        · rw [hp x (Set.mem_iUnion.mpr ⟨(), ⟨x, hx⟩, rfl⟩), zero_mul]
      have hp0 : p = 0 := (mul_eq_zero.mp hprod).resolve_right (MvPolynomial.X_ne_zero _)
      intro x _
      simp [hp0]
    · exact identityIdeal_antitone (Set.subset_univ _)

/-- [counterexample; formal-checked] **Coverage is not necessary for polynomial receivers.** A
polynomial certified on the naturals vanishes on all of `ℚ`, which the naturals do not cover. -/
theorem polynomial_density_suffices (p : Polynomial ℚ) (h : ∀ n : ℕ, p.eval (n : ℚ) = 0) :
    ∀ x : ℚ, p.eval x = 0 := by
  have hp : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℚ)) Nat.cast_injective
    intro n
    exact h n
  intro x
  simp [hp]

section Audit
#print axioms identity_iff_sub_mem_identityIdeal
#print axioms identityIdeal_fg
#print axioms certification_sound_iff_covers
#print axioms certified_eval_iff
#print axioms certifies_exactly_iff
#print axioms identityIdeal_eq_iff_dense
#print axioms principal_image_ideal_strictly_larger
#print axioms two_windings_image_ideal
#print axioms punctured_plane_certifies_exactly
#print axioms principal_winding_invents_an_identity
#print axioms two_windings_certify_exactly
#print axioms galilean_identity_ideal
#print axioms polynomial_density_suffices
end Audit

end Holonics.Compression.Landmark.Identity
