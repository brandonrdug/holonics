import Holonics.Aeon.Production.PathReversal
import Holonics.Physics.Information.ClockJoin

/-!
# Kolmogorov's criterion: a chain is reversible exactly when every cycle's ratio product is one

`Aeon/Production/PathReversal` proves the forward direction of Kolmogorov's criterion in the real
chart: under detailed balance every positive cycle reads zero affinity
(`detailedBalance_cycle_affinity_zero`). The Rust owner
`holonics::aeon::MarkovChain::reversible_law` claims the converse and computes with it: the
reversible law is read along a spanning tree of the support from one state,
`π(y)/π(x) = P(x→y)/P(y→x)`, and every passage off the tree closes a fundamental cycle whose ratio
product must be one (atlas `aeon.kolmogorov-converse`). #410 owes the Lean statement.
`Physics/Information/ClockJoin` already owns its law: a rate cochain on a connected parametric
complex is exact exactly when it is silent on every cycle (`join_iff_silent`). This file reads the
chain's ratios as such a cochain.

[definition] **The support complex** of a chain `P` (`supportComplex`) has the states as occurrences
and an oriented edge for every positive transition `x → y`, with no two-cell; its aeons are the
paths the chain can run, each step taken along or against its transition. **The ratio form**
(`ratioForm`) carries each edge's exact ratio `P(x→y)/P(y→x)` in the multiplicative chart
`Additive Kˣ`, the carrier `ClockJoin.triangleRates` uses, so a cycle reads the undivided product of
its ratios and no logarithm is taken. **The reversible law** (`reversibleLaw`) of a choice of aeons
`path v` from one state `base` is the product of the ratios along `path v`: the Rust owner's weight
before it is normalized to total mass one.

[proved-standard; formal-checked] What is proved, over any ordered field `K`, for `P ≥ 0` with
symmetric support (`P x y > 0 ⇒ P y x > 0`) and every state reached from `base` by an aeon of the
support complex. Finiteness of the states is not used.

1. **The read law is positive** (`reading_pos`, `reversibleLaw_pos`): every ratio is positive, so
   the product along any word is.
2. **Detailed balance makes the ratio form exact** (`ratioForm_eq_exactForm`): with a positive law
   `π` in detailed balance, the ratio of each edge is `π y / π x`, the exact form of `π` in the
   multiplicative chart. So **every cycle's ratio product is one**
   (`cycle_ratio_one_of_detailedBalance`, ClockJoin's `join_silent_on_cycles`), and the law read
   along the tree is `π` up to its value at `base`, `reversibleLaw v = π v / π base`
   (`reversibleLaw_eq`): the reversible law is unique up to scale.
3. **The converse** (`detailedBalance_of_cycles`): if every cycle of the support complex reads ratio
   product one, the law read along the chosen aeons is in detailed balance with `P`. ClockJoin's
   `join_of_silent_on_cycles` makes the ratio form the exact form of the read law; on a positive
   edge that is `P(x→y)/P(y→x) = π y / π x`, and off the support both flows are zero.
4. **Kolmogorov's criterion** (`kolmogorov_iff`): a positive law in detailed balance exists exactly
   when every cycle's ratio product is one.

The affinity `log(P(x→y)/P(y→x))` of `PathReversal` is the logarithm of the ratio form, so the
forward direction proved there is the real-chart reading of item 2; the converse is stated in the
ratio chart only.

[counterexample; formal-checked] **The biased rotation has no reversible law.** Its cycle
`0 → 1 → 2 → 0` reads ratio product `2 · 2 · 2 = 8` (`rotation_cycle_ratio`), so no positive law of
any kind is in detailed balance with it (`rotation_no_reversible_law`); `PathReversal` shows only
that the uniform law is not.

The computational object is the helical pair interaction: each transition and its reverse are a pair
contact whose ratio `P(x→y)/P(y→x)` is the contact's slip, a cycle's ratio product is the holonomy
of the slips around it, and the reversible law is the potential that a spanning tree of contacts
reads when every holonomy is trivial. Of the winding guide's six general objects this touches the
pair (each transition's ratio) and the cell holonomy (each cycle's product); the helix, faces and
placement, the tube and the tower thread stay attached.

Consumers: the atlas rows `aeon.kolmogorov-converse` and `aeon.production-state-heat`, the Rust
owner `holonics::aeon::MarkovChain::reversible_law`, and #410.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Aeon.Production.Kolmogorov

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Aeon.Production.PathReversal
open Holonics.Physics.Information

variable {S K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : S → S → K}

/-! ## 1. The support complex, its ratio form and the law read along a tree -/

/-- [definition] **The support complex** of a chain: an oriented edge for every positive
transition, and no two-cell. -/
def supportComplex (P : S → S → K) : ParametricComplex S {e : S × S // 0 < P e.1 e.2} Empty where
  src e := e.1.1
  tgt e := e.1.2
  base f := f.elim
  boundary f := f.elim

/-- [definition] **The ratio form**: each positive transition carries its exact ratio
`P(x→y)/P(y→x)` in the multiplicative chart. -/
def ratioForm (hsupp : ∀ x y, 0 < P x y → 0 < P y x) :
    {e : S × S // 0 < P e.1 e.2} → Additive Kˣ := fun e =>
  Additive.ofMul (Units.mk0 (P e.1.1 e.1.2 / P e.1.2 e.1.1)
    (div_ne_zero e.2.ne' (hsupp _ _ e.2).ne'))

/-- [proved-standard; formal-checked] **The ratio product along any word is positive.** -/
theorem reading_pos (hsupp : ∀ x y, 0 < P x y → 0 < P y x)
    (w : List ({e : S × S // 0 < P e.1 e.2} × Bool)) :
    0 < ((Additive.toMul (wordReading (ratioForm hsupp) w) : Kˣ) : K) := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [wordReading_cons, toMul_add, Units.val_mul]
    refine mul_pos ?_ ih
    obtain ⟨⟨⟨x, y⟩, hxy⟩, b⟩ := s
    have hr : 0 < P x y / P y x := div_pos hxy (hsupp x y hxy)
    cases b
    · have h := inv_pos.mpr hr
      simpa [stepReading, ratioForm, toMul_neg, toMul_ofMul] using h
    · simpa [stepReading, ratioForm, toMul_ofMul] using hr

/-- [definition] **The reversible law read along a tree**: the ratio product along the chosen aeon
from `base` to each state. -/
def reversibleLaw (hsupp : ∀ x y, 0 < P x y → 0 < P y x) {base : S}
    (path : ∀ v, Aeon (supportComplex P) base v) (v : S) : K :=
  ((Additive.toMul (wordReading (ratioForm hsupp) (path v).steps) : Kˣ) : K)

/-- [proved-standard; formal-checked] The read law is positive. -/
theorem reversibleLaw_pos (hsupp : ∀ x y, 0 < P x y → 0 < P y x) {base : S}
    (path : ∀ v, Aeon (supportComplex P) base v) (v : S) : 0 < reversibleLaw hsupp path v :=
  reading_pos hsupp _

/-! ## 2. Detailed balance makes the ratio form exact -/

/-- [definition] A positive law in the multiplicative chart. -/
def lawForm {π : S → K} (hπ : ∀ x, 0 < π x) : S → Additive Kˣ := fun v =>
  Additive.ofMul (Units.mk0 (π v) (hπ v).ne')

/-- [proved-standard; formal-checked] **Detailed balance makes the ratio form exact**: each edge's
ratio is `π y / π x`, the exact form of the law in the multiplicative chart. -/
theorem ratioForm_eq_exactForm (hsupp : ∀ x y, 0 < P x y → 0 < P y x) {π : S → K}
    (hπ : ∀ x, 0 < π x) (hdb : DetailedBalance π P) :
    ratioForm hsupp = exactForm (supportComplex P) (lawForm hπ) := by
  funext e
  obtain ⟨⟨x, y⟩, hxy⟩ := e
  have hyx := hsupp x y hxy
  have h := hdb x y
  unfold flow at h
  apply Additive.toMul.injective
  apply Units.ext
  simp only [exactForm, ratioForm, lawForm, supportComplex, toMul_sub, toMul_ofMul, Units.val_mk0,
    Units.val_div_eq_div_val]
  rw [div_eq_div_iff hyx.ne' (hπ x).ne']
  linarith

/-- [proved-standard; formal-checked] **Kolmogorov's criterion, the forward direction, in the ratio
chart**: under detailed balance with a positive law every cycle's ratio product is one. -/
theorem cycle_ratio_one_of_detailedBalance (hsupp : ∀ x y, 0 < P x y → 0 < P y x) {π : S → K}
    (hπ : ∀ x, 0 < π x) (hdb : DetailedBalance π P) {u : S} (γ : Aeon (supportComplex P) u u) :
    Additive.toMul (wordReading (ratioForm hsupp) γ.steps) = 1 :=
  toMul_eq_one.mpr (ClockJoin.join_silent_on_cycles (ratioForm_eq_exactForm hsupp hπ hdb) γ)

/-- [proved-standard; formal-checked] **The reversible law is unique up to scale**: a positive law
in detailed balance is the law read along the tree, scaled by its value at `base`. -/
theorem reversibleLaw_eq (hsupp : ∀ x y, 0 < P x y → 0 < P y x) {π : S → K}
    (hπ : ∀ x, 0 < π x) (hdb : DetailedBalance π P) {base : S}
    (path : ∀ v, Aeon (supportComplex P) base v) (v : S) :
    reversibleLaw hsupp path v = π v / π base := by
  unfold reversibleLaw
  rw [ratioForm_eq_exactForm hsupp hπ hdb, wordReading_exactForm _ (path v).chained, toMul_sub]
  simp [lawForm, toMul_ofMul]

/-! ## 3. The converse -/

/-- [proved-standard; formal-checked] **Kolmogorov's criterion, the converse**: if every cycle of
the support complex reads ratio product one, the law read along the chosen aeons is in detailed
balance. -/
theorem detailedBalance_of_cycles (hnn : ∀ x y, 0 ≤ P x y)
    (hsupp : ∀ x y, 0 < P x y → 0 < P y x) {base : S} (path : ∀ v, Aeon (supportComplex P) base v)
    (hcyc : ∀ (u : S) (γ : Aeon (supportComplex P) u u),
      Additive.toMul (wordReading (ratioForm hsupp) γ.steps) = 1) :
    DetailedBalance (reversibleLaw hsupp path) P := by
  have hjoin : ratioForm hsupp =
      exactForm (supportComplex P) (fun v => wordReading (ratioForm hsupp) (path v).steps) :=
    ClockJoin.join_of_silent_on_cycles (ratioForm hsupp) base path
      fun u γ => toMul_eq_one.mp (hcyc u γ)
  intro x y
  unfold flow
  by_cases hxy : 0 < P x y
  · have hyx := hsupp x y hxy
    have he : ratioForm hsupp ⟨(x, y), hxy⟩ =
        exactForm (supportComplex P) (fun v => wordReading (ratioForm hsupp) (path v).steps)
          ⟨(x, y), hxy⟩ :=
      congrFun hjoin _
    have hm : P x y / P y x = reversibleLaw hsupp path y / reversibleLaw hsupp path x := by
      have h1 : ((Additive.toMul (ratioForm hsupp ⟨(x, y), hxy⟩) : Kˣ) : K) = P x y / P y x := rfl
      rw [← h1, he]
      simp only [exactForm, supportComplex, toMul_sub, Units.val_div_eq_div_val, reversibleLaw]
    rw [div_eq_div_iff hyx.ne' (reversibleLaw_pos hsupp path x).ne'] at hm
    linarith
  · have hxy0 : P x y = 0 := le_antisymm (not_lt.mp hxy) (hnn x y)
    have hyx0 : P y x = 0 := le_antisymm (not_lt.mp fun h => hxy (hsupp y x h)) (hnn y x)
    rw [hxy0, hyx0, mul_zero, mul_zero]

/-- [proved-standard; formal-checked] **Kolmogorov's criterion**: on a connected support, a
positive law in detailed balance exists exactly when every cycle's ratio product is one. -/
theorem kolmogorov_iff (hnn : ∀ x y, 0 ≤ P x y) (hsupp : ∀ x y, 0 < P x y → 0 < P y x)
    {base : S} (path : ∀ v, Aeon (supportComplex P) base v) :
    (∃ π : S → K, (∀ x, 0 < π x) ∧ DetailedBalance π P) ↔
      ∀ (u : S) (γ : Aeon (supportComplex P) u u),
        Additive.toMul (wordReading (ratioForm hsupp) γ.steps) = 1 :=
  ⟨fun ⟨_, hπ, hdb⟩ _ γ => cycle_ratio_one_of_detailedBalance hsupp hπ hdb γ,
    fun h => ⟨reversibleLaw hsupp path, reversibleLaw_pos hsupp path,
      detailedBalance_of_cycles hnn hsupp path h⟩⟩

/-! ## 4. The biased rotation has no reversible law -/

/-- [definition] The cycle `0 → 1 → 2 → 0` of the biased rotation, along its forward
transitions. -/
def rotationLoop : Aeon (supportComplex Rotation.P) 0 0 :=
  ⟨[(⟨(0, 1), by norm_num [Rotation.P]⟩, true), (⟨(1, 2), by norm_num [Rotation.P]⟩, true),
      (⟨(2, 0), by norm_num [Rotation.P]⟩, true)], by
    simp [ParametricComplex.Chained, ParametricComplex.start, ParametricComplex.finish,
      supportComplex]⟩

/-- [counterexample; formal-checked] **The rotation's cycle reads ratio product `8`**: each forward
step has ratio `(2/3)/(1/3) = 2`. -/
theorem rotation_cycle_ratio :
    ((Additive.toMul (wordReading (ratioForm Rotation.admissible.support) rotationLoop.steps) :
      ℚˣ) : ℚ) = 8 := by
  simp [rotationLoop, wordReading, stepReading, ratioForm, toMul_ofMul, Rotation.P] <;> norm_num

/-- [counterexample; formal-checked] **The biased rotation has no reversible law**: no positive
law is in detailed balance with it. -/
theorem rotation_no_reversible_law :
    ¬ ∃ π : Fin 3 → ℚ, (∀ x, 0 < π x) ∧ DetailedBalance π Rotation.P := by
  rintro ⟨π, hπ, hdb⟩
  have h8 := rotation_cycle_ratio
  rw [cycle_ratio_one_of_detailedBalance Rotation.admissible.support hπ hdb rotationLoop] at h8
  norm_num at h8

end Holonics.Aeon.Production.Kolmogorov
