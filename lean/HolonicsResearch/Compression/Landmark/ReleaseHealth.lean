import Mathlib

/-!
# A mixture face's variation: the family-to-class map is L1 nonexpansive, and posterior widths bound its face

[proved-standard] The source is #410's box "Release distribution and health" (L1 nonexpansiveness of the
family-to-class map, bounded by summed posterior interval widths; Rust `receiver::population::health`, retired on
September 28 with U3, history `1bdacc8f`), part done by `Compression/Landmark/Context/Population.certified_inverseCDF_class`.
The law is kept in `docs/RECEIVER_HOLARCHY.md#width-and-release` ("A mixture face's variation") and the atlas row
`receiver.population-receiving-face-health`: `A_fc = P_f(c)`, `Σ_c A_fc = 1`, `A_fc ≥ 0` give `‖A‖₁ = 1` and
`‖A(w − v)‖₁ ≤ ‖w − v‖₁ ≤ Σ_f (upper_f − lower_f)`.

The model. Families `ι` and classes `C` are finite; a family-to-class map `A` gives each family a face of the
classes, nonnegative and summing to one (`IsClassMap`); a posterior `w` over the families mixes to the receiving face
`(A w)_c = Σ_f w_f A_fc` (`mix`). Values lie in any linearly ordered field (`ℚ` for the receiver's exact faces).

What is proved.

1. **The map is L1 nonexpansive** (`l1_mix_le`, `mix_nonexpansive`): `‖A x‖₁ ≤ ‖x‖₁` for every `x`, so the faces of
   two posteriors differ in L1 by at most the posteriors' own L1 distance; the bound is attained at a point mass
   (`l1_mix_single`), so the map's L1 operator norm is one.
2. **Posterior widths bound the variation** (`l1_sub_le_widths`, `mix_variation_le_widths`): two posteriors inside the
   intervals `[lower_f, upper_f]` have mixture faces within `Σ_f (upper_f − lower_f)` in L1. Normalization is not
   needed.
3. **The class enclosure** (`mix_mem_enclosure`, `enclosure_widths_sum`): a posterior inside the intervals has class
   mass `(A w)_c ∈ [Σ_f lower_f A_fc, Σ_f upper_f A_fc]`, and these enclosures' widths sum over the classes to
   `Σ_f (upper_f − lower_f)`.
4. **An enclosure that covers the simplex certifies no draw** (`covering_enclosure_holds_every_draw`): on two or more
   classes, a class enclosure holding every point of the simplex has every lower bound at most `0`, so no draw
   `≥ 0` meets the certificate's condition `draw < Σ_(j ≤ i) lower_j` of
   `Population.certified_inverseCDF_class`: every key is held.

Limits. The enclosure of the posterior itself (its intervals) is a hypothesis: this file does not bound the Bayesian
update or a field solver, as the atlas row says. "Truthful health" in #410's box is not defined by its sources: the
guide names F5's numerical health (radius, robust count, operator bound, contraction) as a missing term, and the full
release distribution and the producing-key relation are not stated here.

The computational object is the helical pair interaction read as a receiver's population: each family is a
navigator whose face of the classes is its pairing with the receiver, the mixture is the population's one receiving
face, and the L1 bound says the pairing cannot amplify a difference of posteriors. Of the winding guide's six general
objects this touches the faces and placement (the families' faces, the mixture face and its enclosure); the helix,
the pair, the cell holonomy, the tube and the tower thread stay attached through the families' own owners.

Consumers: the atlas row `receiver.population-receiving-face-health`; the guide's "Width and release";
`Population.certified_inverseCDF_class`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.ReleaseHealth

open Finset

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {ι C : Type*} [Fintype ι] [Fintype C]

/-- [definition] A family-to-class map: each family's face of the classes is nonnegative and sums to one. -/
structure IsClassMap (A : ι → C → K) : Prop where
  nonneg : ∀ f c, 0 ≤ A f c
  sum_one : ∀ f, ∑ c, A f c = 1

/-- [definition] The mixture face of a posterior `w`: `(A w)_c = Σ_f w_f A_fc`. -/
def mix (A : ι → C → K) (w : ι → K) (c : C) : K := ∑ f, w f * A f c

/-- [definition] The L1 size `Σ_i |x_i|`. -/
def l1 {α : Type*} [Fintype α] (x : α → K) : K := ∑ i, |x i|

omit [LinearOrder K] [IsStrictOrderedRing K] [Fintype C] in
/-- [proved-standard; formal-checked] The mixture is linear: the difference of two faces is the face of the
difference. -/
theorem mix_sub (A : ι → C → K) (w v : ι → K) (c : C) : mix A w c - mix A v c = mix A (w - v) c := by
  simp only [mix, ← sum_sub_distrib, Pi.sub_apply, sub_mul]

/-- [proved-standard; formal-checked] **The family-to-class map is L1 nonexpansive**: `‖A x‖₁ ≤ ‖x‖₁`. -/
theorem l1_mix_le {A : ι → C → K} (hA : IsClassMap A) (x : ι → K) : l1 (mix A x) ≤ l1 x := by
  unfold l1 mix
  calc ∑ c, |∑ f, x f * A f c| ≤ ∑ c, ∑ f, |x f| * A f c := by
        refine sum_le_sum fun c _ => (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        refine sum_congr rfl fun f _ => ?_
        rw [abs_mul, abs_of_nonneg (hA.nonneg f c)]
    _ = ∑ f, |x f| * ∑ c, A f c := by
        rw [sum_comm]
        exact sum_congr rfl fun f _ => (mul_sum _ _ _).symm
    _ = ∑ f, |x f| := by simp [hA.sum_one]

/-- [proved-standard; formal-checked] **The bound is attained at a point mass**: the face of the family `f` alone
has L1 size one, the size of the point mass, so the map's L1 operator norm is one. -/
theorem l1_mix_single [DecidableEq ι] {A : ι → C → K} (hA : IsClassMap A) (f : ι) :
    l1 (mix A (Pi.single f 1)) = 1 ∧ l1 (Pi.single f (1 : K)) = 1 := by
  constructor
  · unfold l1 mix
    have : ∀ c, ∑ g, (Pi.single f (1 : K) : ι → K) g * A g c = A f c := by
      intro c
      rw [sum_eq_single f]
      · simp
      · intro g _ hg; simp [hg]
      · simp
    simp_rw [this, abs_of_nonneg (hA.nonneg f _), hA.sum_one]
  · unfold l1
    rw [sum_eq_single f]
    · simp
    · intro g _ hg; simp [hg]
    · simp

/-- [proved-standard; formal-checked] **Two posteriors' faces differ by at most the posteriors' own distance**, in
L1. -/
theorem mix_nonexpansive {A : ι → C → K} (hA : IsClassMap A) (w v : ι → K) :
    l1 (fun c => mix A w c - mix A v c) ≤ l1 (fun f => w f - v f) := by
  have h := l1_mix_le hA (w - v)
  simp only [mix_sub]
  exact h

/-- [proved-standard; formal-checked] Two posteriors inside the intervals `[lower_f, upper_f]` lie within the summed
widths of each other, in L1. -/
theorem l1_sub_le_widths {lower upper w v : ι → K} (hw : ∀ f, lower f ≤ w f ∧ w f ≤ upper f)
    (hv : ∀ f, lower f ≤ v f ∧ v f ≤ upper f) :
    l1 (fun f => w f - v f) ≤ ∑ f, (upper f - lower f) := by
  refine sum_le_sum fun f _ => abs_sub_le_iff.mpr ⟨?_, ?_⟩
  · linarith [(hw f).2, (hv f).1]
  · linarith [(hv f).2, (hw f).1]

/-- [proved-standard; formal-checked] **Posterior widths bound a mixture face's variation**: two posteriors inside the
intervals `[lower_f, upper_f]` have receiving faces within `Σ_f (upper_f − lower_f)` in L1. -/
theorem mix_variation_le_widths {A : ι → C → K} (hA : IsClassMap A) {lower upper w v : ι → K}
    (hw : ∀ f, lower f ≤ w f ∧ w f ≤ upper f) (hv : ∀ f, lower f ≤ v f ∧ v f ≤ upper f) :
    l1 (fun c => mix A w c - mix A v c) ≤ ∑ f, (upper f - lower f) :=
  (mix_nonexpansive hA w v).trans (l1_sub_le_widths hw hv)

/-- [proved-standard; formal-checked] **The class enclosure**: a posterior inside the intervals has each class mass
inside `[Σ_f lower_f A_fc, Σ_f upper_f A_fc]`. -/
theorem mix_mem_enclosure {A : ι → C → K} (hA : IsClassMap A) {lower upper w : ι → K}
    (hw : ∀ f, lower f ≤ w f ∧ w f ≤ upper f) (c : C) :
    ∑ f, lower f * A f c ≤ mix A w c ∧ mix A w c ≤ ∑ f, upper f * A f c :=
  ⟨sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hw f).1 (hA.nonneg f c),
    sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hw f).2 (hA.nonneg f c)⟩

omit [IsStrictOrderedRing K] in
/-- [proved-standard; formal-checked] The class enclosures' widths sum over the classes to the posterior's summed
widths. -/
theorem enclosure_widths_sum {A : ι → C → K} (hA : IsClassMap A) (lower upper : ι → K) :
    ∑ c, (∑ f, upper f * A f c - ∑ f, lower f * A f c) = ∑ f, (upper f - lower f) := by
  simp_rw [← sum_sub_distrib, ← sub_mul]
  rw [sum_comm]
  refine sum_congr rfl fun f _ => ?_
  rw [← mul_sum, hA.sum_one, mul_one]

/-- [proved-standard; formal-checked] **An enclosure that covers the simplex certifies no draw**: on two or more
classes, if the class enclosure `[lower_j, upper_j]` holds every point of the simplex, every lower bound is at most
`0`, so no draw `≥ 0` meets the certificate's condition `draw < Σ_(j ≤ i) lower_j`
(`Population.certified_inverseCDF_class`): every key is held. -/
theorem covering_enclosure_holds_every_draw {n : ℕ} (hn : 2 ≤ n) (lower upper : Fin n → K)
    (hcover : ∀ q : Fin n → K, (∀ j, 0 ≤ q j) → ∑ j, q j = 1 → ∀ j, lower j ≤ q j ∧ q j ≤ upper j)
    {draw : K} (hd : 0 ≤ draw) (i : Fin n) :
    ¬ draw < ∑ j ∈ univ.filter (fun j : Fin n => j.val ≤ i.val), lower j := by
  have hlow : ∀ j : Fin n, lower j ≤ 0 := by
    intro j
    obtain ⟨k, hk⟩ : ∃ k : Fin n, k ≠ j := by
      by_cases h0 : j.val = 0
      · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
      · exact ⟨⟨0, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
    have hq := hcover (Pi.single k 1) (fun j => by by_cases h : j = k <;> simp [h])
      (by simp) j
    simpa [Pi.single_apply, hk.symm] using hq.1
  rw [not_lt]
  exact (sum_nonpos fun j _ => hlow j).trans hd

end Holonics.Compression.Landmark.ReleaseHealth
