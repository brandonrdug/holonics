import ElementaryHolonics.Millennium.CokernelCalculus

/-!
# SelmerCalculus: the reopening rule keyed to the receiver family

The fourth and last slot of the standing demand.  `CokernelCalculus` showed that the
descent obstruction and the integral Hodge obstruction are one species — torsion in a
cokernel — and that neither can witness a rational statement.  What it did **not**
supply is the rule by which a class is readmitted: the **local conditions**.

That rule is a receiver family.  Given a global group `A`, a realizer map `φ : G → A`,
and for each receiver `i` a restriction `rᵢ : A → Tᵢ` together with the subgroup `Lᵢ`
of what that receiver admits, the **Selmer group** is everything admitted *everywhere*:

```text
Sel  =  ⋂ᵢ rᵢ⁻¹(Lᵢ)
```

and the obstruction `Sel / im φ` is exactly the population **no receiver can see**.

* **`theImageSitsInsideTheSelmerGroup`** — realized classes are locally admitted
  everywhere.  The easy direction, and the reason `Sel` is a bound.
* **`theSelmerGroupBoundsTheRealizedClasses`** — so any bound on `Sel` bounds the
  realized population.
* **`theReceiverFamilyCanBeBlind`** — but not conversely: there is a family whose
  Selmer group strictly exceeds the image, and that gap is the obstruction.  A
  carrying exterior is not an adjudicating one.
* **`theObstructionVanishesExactlyWhenEveryLocalClassIsGlobal`** — the obstruction is
  trivial precisely when local admission everywhere implies global realization.

**Boundary, stated rather than hidden.**  This file supplies the *calculus*, not the
arithmetic instances.  The Birch–Swinnerton-Dyer receiver family is the places of `ℚ`
with `Lᵥ` the image of the local descent, giving `Sel₂` and `Ш[2]`; that requires
`ℚ_v`-points of the descent torsors and is **not constructed here**.  The tree's
unconditional descent bounds `E(ℚ)/2E(ℚ)` — the image — directly and globally, which
is sharper per curve than a Selmer bound and yields **no** `Ш` information; the two are
different readings and this file is what distinguishes them.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.SelmerCalculus

open Soma.Holonics.Millennium

variable {G A : Type*} [AddCommGroup G] [AddCommGroup A]
variable {ι : Type*} {T : ι → Type*} [∀ i, AddCommGroup (T i)]

/-! ## 1. The Selmer group of a receiver family -/

/-- **The Selmer group**: the classes every receiver admits. -/
def selmer (r : ∀ i, A →+ T i) (L : ∀ i, AddSubgroup (T i)) : AddSubgroup A :=
  ⨅ i, (L i).comap (r i)

@[simp]
lemma mem_selmer {r : ∀ i, A →+ T i} {L : ∀ i, AddSubgroup (T i)} {α : A} :
    α ∈ selmer r L ↔ ∀ i, r i α ∈ L i := by
  unfold selmer
  simp [AddSubgroup.mem_iInf]

/-- **THE IMAGE SITS INSIDE THE SELMER GROUP**: a realized class is admitted by every
receiver, provided each receiver admits the realized classes it sees. -/
theorem theImageSitsInsideTheSelmerGroup (φ : G →+ A) (r : ∀ i, A →+ T i)
    (L : ∀ i, AddSubgroup (T i)) (hloc : ∀ i g, r i (φ g) ∈ L i) :
    φ.range ≤ selmer r L := by
  rintro α ⟨g, rfl⟩
  rw [mem_selmer]
  exact fun i => hloc i g

/-- **THE SELMER GROUP BOUNDS THE REALIZED CLASSES**: any bound on the locally
admitted population bounds the globally realized one. -/
theorem theSelmerGroupBoundsTheRealizedClasses (φ : G →+ A) (r : ∀ i, A →+ T i)
    (L : ∀ i, AddSubgroup (T i)) (hloc : ∀ i g, r i (φ g) ∈ L i)
    {α : A} (hα : α ∈ φ.range) : α ∈ selmer r L :=
  theImageSitsInsideTheSelmerGroup φ r L hloc hα

/-! ## 2. The obstruction is the receivers' blind spot -/

/-- **THE OBSTRUCTION VANISHES EXACTLY WHEN LOCAL ADMISSION IS GLOBAL REALIZATION**. -/
theorem theObstructionVanishesExactlyWhenEveryLocalClassIsGlobal (φ : G →+ A)
    (r : ∀ i, A →+ T i) (L : ∀ i, AddSubgroup (T i)) :
    selmer r L ≤ φ.range ↔ ∀ α : A, (∀ i, r i α ∈ L i) → α ∈ φ.range := by
  constructor
  · intro h α hα
    exact h (mem_selmer.mpr hα)
  · intro h α hα
    exact h α (mem_selmer.mp hα)

/-- **THE RECEIVER FAMILY CAN BE BLIND**: there is a realizer map and a receiver
family whose Selmer group strictly exceeds the image.  Local admission everywhere does
not imply global realization, and that gap is the obstruction — a carrying exterior is
not an adjudicating one. -/
theorem theReceiverFamilyCanBeBlind :
    ∃ (G A : Type) (_ : AddCommGroup G) (_ : AddCommGroup A) (ι : Type)
      (T : ι → Type) (_ : ∀ i, AddCommGroup (T i)) (φ : G →+ A)
      (r : ∀ i, A →+ T i) (L : ∀ i, AddSubgroup (T i)),
      (∀ i g, r i (φ g) ∈ L i) ∧ ¬ (selmer r L ≤ φ.range) := by
  refine ⟨PUnit, ZMod 2, inferInstance, inferInstance, PUnit, fun _ => PUnit,
    inferInstance, 0, fun _ => 0, fun _ => ⊤, fun i g => trivial, ?_⟩
  intro hle
  have h1 : (1 : ZMod 2) ∈ selmer (fun _ : PUnit => (0 : ZMod 2 →+ PUnit))
      (fun _ => ⊤) := by
    rw [mem_selmer]
    exact fun _ => trivial
  have h2 := hle h1
  obtain ⟨g, hg⟩ := h2
  have : (0 : ZMod 2) = 1 := by simpa using hg
  exact absurd this (by decide)


/-! ## 3. The four slots, in one statement -/

open Soma.Holonics.Millennium.CokernelCalculus

/-- **THE FOUR SLOTS OF THE DEMAND, STATED TOGETHER**.  For a realizer map into a
`ℚ`-vector space carrying a receiver family:

1. **supported realizer population** — the image of `φ`;
2. **certified remainder** — a class reachable only in a nonzero multiple is torsion
   in the cokernel, hence an *integral* obstruction;
3. **the bar on it** — and therefore invisible over `ℚ`: it lies in the rational span,
   so it can never witness a rational statement;
4. **reopening rule keyed to the receiver family** — the realized classes are admitted
   by every receiver, so the Selmer group bounds them, while the converse can fail and
   that failure is the obstruction.

This is the same four-part structure the corpus demands, now with each part a theorem
rather than a description, and it is the structure both the descent and the cycle-class
map instantiate. -/
theorem theFourSlotsOfTheDemand {V : Type*} [AddCommGroup V] [Module ℚ V]
    (φ : G →+ V) (r : ∀ i, V →+ T i) (L : ∀ i, AddSubgroup (T i))
    (hloc : ∀ i g, r i (φ g) ∈ L i)
    (S : Set V) (α : V) (m : ℤ) (hm : m ≠ 0)
    (hmul : m • α ∈ AddSubgroup.closure S) (hout : α ∉ AddSubgroup.closure S) :
    -- 2. the remainder is torsion in the cokernel, and nonzero there
    (m • (QuotientAddGroup.mk' (AddSubgroup.closure S) α) = 0 ∧
      (QuotientAddGroup.mk' (AddSubgroup.closure S) α) ≠ 0) ∧
    -- 3. and invisible over `ℚ`
    α ∈ Submodule.span ℚ S ∧
    -- 4. while the realized classes are admitted everywhere
    φ.range ≤ selmer r L :=
  ⟨theMultipleReachableClassIsTorsionInTheCokernel ⟨hm, hmul, hout⟩,
    theMultipleReachableClassIsRationallyReachable S α m hm hmul,
    theImageSitsInsideTheSelmerGroup φ r L hloc⟩

end Soma.Holonics.Millennium.SelmerCalculus
