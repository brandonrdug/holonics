# lean_owners_audit

Testimony of one Opus 5 audit sub-agent, 2026-09-03, read-only over the repository and the conversation logs; integrated by the primary session in `../2026-09-03_SKE_AUDIT_THE_COORDINATE_GRAIN_THE_HOST_READOUT_AND_THE_COMPRESSION_LAW_WERE_INJECTIONS_AND_THE_CANON_ALREADY_OWNS_THE_ANSWERS.md`. Every claim below is testimony until cited there.

I'll start by reading the blueprint and locating the Lean files.
# Audit of the Lean formalizations behind SKE

**Scope.** `soma/formal/elementary-holonics/ElementaryHolonics/` (1,091 `.lean` files), read-only, no `lake` run. Every derivation I give below is a hand proof from the quoted text and is marked as such; nothing here has been kernel-checked in this session. Blueprint read in full including §0b.

---

## 1. The owners, verbatim

### 1.1 `Site`, `Carrier`, the state, the ecology

`/home/b/Workspaces/holonics/soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicNeuralEcology.lean:29-37`

```lean
/-- A finite chart of local holonic current and constitutive response.  `localCurrent` may depend
on the complete contemporary state, so fixed and input-conditioned incidence share one type. -/
structure FiniteLocalCurrentEcology
    (Site : Type uS) (Carrier : Type uC) (Morphology : Type uM)
    (Generator : Type uG) (Receiver : Type uR) (Face : Type uF)
    [Fintype Site] [AddCommMonoid Carrier] where
  localCurrent : Morphology → Generator → (Site → Carrier) → Site → Site → Carrier
  reaction : Morphology → Generator → Site → Carrier → Carrier
  observe : Receiver → (Site → Carrier) → Face
```

`aggregateCurrent`, `step`, `inferWord` — same file, `:47-49`, `:52-55`, `:64-66`:

```lean
/-- All caused currents entering one addressed site, before local reaction. -/
def aggregateCurrent (morphology : Morphology) (generator : Generator)
    (state : Site → Carrier) (target : Site) : Carrier :=
  ∑ source : Site, N.localCurrent morphology generator state target source

/-- One complete native transport through fixed contemporary morphology. -/
def step (morphology : Morphology) (generator : Generator)
    (state : Site → Carrier) : Site → Carrier :=
  fun target ↦ N.reaction morphology generator target
    (N.aggregateCurrent morphology generator state target)

/-- Ordered inference through one rested morphology. -/
def inferWord (morphology : Morphology) (word : List Generator)
    (state : Site → Carrier) : Site → Carrier :=
  transportWord (N.step morphology) word state
```

`observe` is not a definition — it is the third **field** of the structure (`:37`), an arbitrary `Receiver → (Site → Carrier) → Face`.

**Is `Site` a free type parameter? Yes, and it is constrained by exactly one class.** `HolonicExcitationFoundedQuotient.lean:38-41`:

```lean
variable {Site : Type uS} {Carrier : Type uC} {Morphology : Type uM}
  {Generator : Type uG} {Receiver : Type uR} {Face : Type uF}
  [Fintype Site] [AddCommMonoid Carrier]
  (N : FiniteLocalCurrentEcology Site Carrier Morphology Generator Receiver Face)
```

`[Fintype Site]` and nothing else — no `DecidableEq` (the file opens `open scoped Classical`, `:30`), no order, no algebra. Line `:213` even carries `omit [Fintype Site] in` before `withdraw_empty`. So a coordinate, a population, a head, a layer, a cross-layer carrier are all equally admissible instantiations *of the type*. (For contrast, elsewhere in the tree `Site` **is** given structure: `[LinearOrder Site]` at `Computation/HolonicFermiHubbard.lean:87`, `[AddCommGroup Site]` at `Computation/HolonicArchitectureCharts.lean:223`. Neither is in the SKE line.)

The state is literally the function type `Site → Carrier`; the only algebra assumed of `Carrier` is `AddCommMonoid` — enough for `0` (used by `withdraw`) and `∑` (used by `aggregateCurrent`), nothing more.

### 1.2 `signature`, `withdraw`, `IsCone`, `LoadBearing`

`/home/b/…/Computation/HolonicExcitationFoundedQuotient.lean:45-48`

```lean
/-- The complete receiver face of one presented state after one ordered history at one rest. -/
def signature (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) (history : List Generator) : Face :=
  N.observe receiver (N.inferWord morphology history state)
```

`:209-211`

```lean
/-- Withdraw a population of sites from a presented state: the intervention. -/
def withdraw (population : Set Site) (state : Site → Carrier) : Site → Carrier :=
  fun site => if site ∈ population then 0 else state site
```

`:218-224` — **the load-bearing definition of the whole campaign**

```lean
/-- A cone at one receiver and history: withdrawing any population disjoint from it leaves the
face unchanged.  Soundness of the cone is exactly the outside-unchanged law. -/
def IsCone (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) (cone : Set Site) : Prop :=
  ∀ population : Set Site, Disjoint population cone →
    signature N morphology (withdraw population state) receiver history =
      signature N morphology state receiver history
```

`:236-240`

```lean
/-- A site is load-bearing when its own withdrawal changes the face. -/
def LoadBearing (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) (site : Site) : Prop :=
  signature N morphology (withdraw {site} state) receiver history ≠
    signature N morphology state receiver history
```

Note the asymmetry that decides everything below: `IsCone` quantifies universally over **arbitrary populations**; `LoadBearing` is defined on a **singleton** only.

### 1.3 `DeclaredFamily`, `Exposure`, `Identified`, `familyCompression`, `extent`, `insufficiency`

`:129-134`, `:143-151`, `:166-178`, `:254-264`

```lean
/-- A declared family: the occurrences presented, the receivers reading them, and the ordered
histories they are driven through.  An application declares it; nothing here selects answers. -/
structure DeclaredFamily (Occurrence : Type uO) where
  present : Occurrence → (Site → Carrier)
  receivers : Set Receiver
  histories : Set (List Generator)

/-- The declared receiver/history pairs the family exposes its occurrences to. -/
def Exposure : Type _ :=
  { pair : Receiver × List Generator // pair.1 ∈ family.receivers ∧ pair.2 ∈ family.histories }

/-- Two occurrences are identified when every declared exposure returns equal faces. -/
def Identified (morphology : Morphology) (left right : Occurrence) : Prop :=
  ∀ exposure : family.Exposure,
    signature N morphology (family.present left) exposure.1.1 exposure.1.2 =
      signature N morphology (family.present right) exposure.1.1 exposure.1.2
```

```lean
def familyCompression (morphology : Morphology) :
    Soma.Holonics.Compression family.Exposure Occurrence (family.Class N morphology) Face where
  quotient := Quotient.mk (family.familySetoid N morphology)
  receiver := fun exposure occurrence =>
    signature N morphology (family.present occurrence) exposure.1.1 exposure.1.2
  factor := fun exposure =>
    Quotient.lift
      (fun occurrence =>
        signature N morphology (family.present occurrence) exposure.1.1 exposure.1.2)
      (fun _ _ h => h exposure)
  exact := by
    intro exposure occurrence
    rfl
```

```lean
/-- The extent of a family's lift: the union of the cones the family excited. -/
def DeclaredFamily.extent (family : …) (cone : Occurrence → family.Exposure → Set Site) : Set Site :=
  ⋃ occurrence, ⋃ exposure, cone occurrence exposure

/-- The insufficiency of a family's lift: what no declared exposure made load-bearing. -/
def DeclaredFamily.insufficiency (family : …) (cone : Occurrence → family.Exposure → Set Site) : Set Site :=
  (family.extent cone)ᶜ
```

`extent`/`insufficiency` take the cone assignment as an **argument**. They assert nothing about it. A cone family that is nowhere `IsCone` produces an `extent` and an `insufficiency` just as well.

---

## 2. Cones: what is provable, what the card proved

### 2.a A superset of an `IsCone` cone **is** a cone. Unions of sound cones are sound.

**Refuted as an open question; the property holds trivially.** Not stated in the file, but a two-line consequence of `:220-224`:

```lean
theorem isCone_mono {cone cone' : Set Site} (sub : cone ⊆ cone')
    (h : IsCone N morphology state receiver history cone) :
    IsCone N morphology state receiver history cone' :=
  fun population disjoint => h population (disjoint.mono_right sub)
```

(Hand proof, not kernel-checked. `Disjoint population cone'` plus `cone ≤ cone'` gives `Disjoint population cone` by `Disjoint.mono_right`; then apply `h`.) The file already proves the degenerate maximal case, `:226-234`:

```lean
/-- The complete site population is always a cone. -/
theorem isCone_univ (morphology : Morphology) (state : Site → Carrier) (receiver : Receiver)
    (history : List Generator) :
    IsCone N morphology state receiver history Set.univ := by
  intro population disjoint
  have empty : population = ∅ := by
    rw [Set.disjoint_univ] at disjoint
    exact disjoint
  rw [empty, withdraw_empty]
```

Consequences:
- `{C : IsCone …}` is an **up-set**, hence closed under arbitrary unions — including unions across *different* occurrences and *different* exposures, since a cone for exposure `e₁` stays a cone for `e₁` when enlarged by anything at all.
- It is **not** closed under intersection: `Disjoint P (C₁ ∩ C₂)` does not give `Disjoint P C₁`. So a *least* cone need not exist, and the blueprint's "smallest suffix of that order" (§SKE2, blueprint line 199) presupposes a minimum the definition does not guarantee. The SKE2 record is correct where the blueprint is loose: *"the cone is minimal along the contribution order, not the least cone"* (`research/records/2026-09-03_SKE2_…md:135`).

**Therefore the card's union refutation cannot be a refutation of union-closure.** Run the modus tollens. Let `U = C₁ ∪ C₂`, and let `P ⊆ Uᶜ` be the population that changed exposure 1's face. Since `C₁ ⊆ U`, `Disjoint P C₁`. If `IsCone … C₁` held, `IsCone` instantiated at `P` would force the face to be unchanged. It changed. **So `C₁` was never an `IsCone` cone.** The card refuted the *individual measured cones*, not the union operation.

This is exactly what the measurement says, and the research record already carries the correct diagnosis — while the blueprint does not. `research/records/2026-09-03_SKE3_…md:65-71`:

> [counterexample; measured] The class cones reported above as unions of the members' cones over every exposure are not cones. On the card, withdrawing the complement of class 0's union (961,417 sites, a subset of each exposure's own complement) changed two of its three faces (`**` for `7` under the empty history, `7` for `5` under `The second operand is `) … A cone verified by withdrawing its whole complement is one sufficient population; `IsCone` is universal over sub-populations, and unions of such cones do not inherit it.

The record's last clause is one step off: unions of *`IsCone` cones* **do** inherit it. What fails to be union-closed is the weaker measured property (§2.b). The two named faces identify precisely which cones fell: `cone(7+5=, empty)` = 29,588 sites and `cone(7+5=, "The second operand is ")` = 162,238 sites (`…SKE3…md:44`) are each **directly refuted as `IsCone` cones by the campaign's own measurement**.

### 2.b What the card verification establishes: `LoadBearing` membership vs. the `IsCone` universal

The card procedure (blueprint `:196-201`) closes each cone by two readings. Formally they are:

1. **Complement sufficiency** — `signature N m (withdraw coneᶜ state) r h = signature N m state r h`. This is *one instance* of `IsCone`, at `population := coneᶜ` (`Disjoint coneᶜ cone` holds). Plus the 21–22 monotone probes, each another such instance at a nested suffix-complement.
2. **Cone necessity** — `signature N m (withdraw cone state) r h ≠ signature N m state r h`. **This proposition has no owner in the Lean tree.** `LoadBearing` (`:237-240`) is defined only on `{site}`; there is no set-valued generalization anywhere in the file or elsewhere (`grep` over the tree returns `LoadBearing` only at `HolonicExcitationFoundedQuotient.lean:237,244,247` and, unrelatedly, `Computation/NativeTransportScaffold.lean:238` `scaffoldInitiallyLoadBearing` over `Probe`s, and `Millennium/SignChange.lean:674`).

**Precisely:**

| finite measurement | Lean proposition it establishes |
|---|---|
| withdraw one site, face changes | `LoadBearing N m s r h site` |
| withdraw one site, face unchanged | `¬ LoadBearing …` (no upper bound on any cone) |
| withdraw populations `P₁ … P_k`, each disjoint from `C`, all unchanged | `k` instances of `IsCone`'s universal |
| withdraw `C` itself, face changes | nothing named in the tree |

The only bridge the file offers runs **from** `IsCone`, never toward it — `:242-252`:

```lean
/-- Every cone contains every load-bearing site: a cone that omitted one would have to leave the
face unchanged under that site's withdrawal. -/
theorem loadBearing_mem_of_isCone (morphology : Morphology) (state : Site → Carrier)
    (receiver : Receiver) (history : List Generator) {cone : Set Site}
    (isCone : IsCone N morphology state receiver history cone) {site : Site}
    (bearing : LoadBearing N morphology state receiver history site) :
    site ∈ cone := by
  by_contra outside
  apply bearing
  apply isCone
  exact Set.disjoint_singleton_left.mpr outside
```

This is **necessary-condition only**: it licenses `{load-bearing sites} ⊆ C` as a *lower bound* on any true cone. It never certifies a candidate as a cone. And on the resident operator its lower bound is empty in the relevant sense — SKE2 measured that no single population's withdrawal changes the face (`…SKE2…md:18-20`: *"face unchanged for all 54 populations tried … The load is joint: no single population carries the face"*). Absence of load-bearing singletons emphatically does **not** make `∅` a cone, because `IsCone` quantifies over multi-element populations.

**Counting the gap.** `IsCone` for `cone(7+5=, empty)` quantifies over every subset of a 1,565,804-site complement: `2^1,565,804` instances. The card discharged 22. There is no clause anywhere in the ecology from which the remaining ones follow, because there is no structure to interpolate with: `localCurrent` takes the **complete** contemporary state (`HolonicNeuralEcology.lean:35`, docstring `:29-30` *"`localCurrent` may depend on the complete contemporary state"*), `reaction` is an arbitrary `Carrier → Carrier` (`:36`), and `observe` reads the whole state (`:37`). Withdrawal is therefore not additive, not monotone, and not even continuous in the withdrawn set. **The card's 22 confirmations carry zero implication toward the 23rd.**

### 2.c At the flux-group grain: what remains unverified, and what would discharge `IsCone`

**Still unverified: the same universal, only over a smaller lattice.** Under a grouping `group : Site → FluxGroup` with `G` groups (blueprint §0b names populations, heads, layers, cross-layer carriers; the resident numbers are 719 coefficient populations / 665 configured / 344 cross-sections), the intervention lattice shrinks from `2^1,595,392` to `2^G`. For `G` in the hundreds this is still astronomically past exhaustion. The verification defect is **not** repaired by the grain change; it is repaired only where it makes the refuting witness *inexpressible*.

That last point is the substantive one. There are exactly two readings of §0b, and neither is what the blueprint claims:

- **(i) Group-saturated cones over the same `Site` type.** Keep `Site` = coordinates, require `cone = group ⁻¹' S`. Then `IsCone` is *unchanged*, its `∀ population : Set Site` still ranges over all 2^1.6M populations, and the SKE3 refuting population of 961,417 sites is still an admissible witness. The refutation survives verbatim.
- **(ii) A genuinely coarser ecology, `Site := FluxGroup`.** Then `aggregateCurrent` sums over groups (`HolonicNeuralEcology.lean:47-49`), i.e. it is a *different dynamical object*. To claim it returns the resident operator's faces you owe a `ClassicalConfiguration` (`HolonicNeuralEcology.lean:81-90`) with `observeExact` and `generatorExact` — an exactness obligation nobody has discharged and which the blueprint does not mention. Under this reading `IsCone`'s universal is restricted to group-aligned withdrawals, so the refutation becomes unstatable rather than answered.

**What obligation would discharge `IsCone` without exhaustive withdrawal.** Nothing in the tree provides one. The shape required is a **locality/zero-support law added to the ecology**, roughly:

- `reactionZero : ∀ m g t, reaction m g t 0 = 0` (zero-preservation), and
- a read-set for `observe` plus an in-neighbourhood for `localCurrent`, i.e. `localCurrent m g` depends on `state` only through its restriction to a declared `inNeighbourhood target`,

from which the backward closure of the receiver's read-set over `|history|` steps is provably an `IsCone` cone, by induction on the word, with **no withdrawals at all**. That is the causal-reachability cone. It is precisely what `FiniteLocalCurrentEcology` was designed to *exclude* — its architecture-neutrality is bought by making `localCurrent` state-global. The one place in the tree where such a law would even be derivable is the linear chart `Computation/HolonicOrientedSiteTransport.lean:98-107` (`pairCurrent port state target source = state source * localTransport port target source`, `reaction _ _ _ current := current`); no support theorem is stated there either.

### 2.c′ `LocalCausalConeCultivation` — hypothesis-carrying, not sound-by-construction, and not the same proposition

`/home/b/…/Computation/NativeMorphologyVariant.lean:105-126`

```lean
/-- One returned local morphology change with source-detached remount, ablation, and restoration.

`localFace` is the native anatomical face at one site.  `outsideUnchanged` prevents a local return
from silently rewriting inactive morphology.  The conduct receiver may still be global; locality
is exactly the supplied causal cone, not a promise of constant work.
-/
structure LocalCausalConeCultivation
    (Site Morphology LocalFace Difference Delta Probe Face RestIdentity Occurrence : Type*) where
  passage :
    Soma.Holonics.Computation.HolonicIntelligence.CultivationPassage
      Morphology Difference Delta Probe Face RestIdentity Occurrence
  causalCone : Delta → Set Site
  probeSite : Probe → Site
  localFace : Morphology → Site → LocalFace
  outsideUnchanged : ∀ site,
    site ∉ causalCone (passage.causalAdjoint passage.returnedDifference) →
      localFace passage.successor site = localFace passage.predecessor site
  outsideConductUnchanged : ∀ probe,
    probeSite probe ∉ causalCone (passage.causalAdjoint passage.returnedDifference) →
      passage.conduct passage.successor probe = passage.conduct passage.predecessor probe
  restore : Morphology → Morphology
  restorationExact : restore passage.predecessor = passage.successor
```

**Answer: neither a reachability cone nor an effective one — it is a declared cone plus a supplied proof obligation.** `outsideUnchanged` is a *field*, not a theorem. `everyOutsideSiteUnchanged` (`:134-139`) is literally the field re-exported; `changedProbe_meets_causalCone` (`:159-165`) is the contrapositive of `outsideConductUnchanged` at the single `witnessProbe`. In the tree's only instance, `twoSiteLocalCultivation` (`:428-456`), the cone is *declared* `causalCone _ := {0}` and the obligation is discharged by `simp` on an explicit two-site successor. There is no minimality clause: `causalCone _ := Set.univ` satisfies `outsideUnchanged` and `outsideConductUnchanged` vacuously — the same degeneracy `isCone_univ` exhibits for `IsCone`.

**And it is a different proposition from `IsCone`.** The blueprint §1 (line 88-90) says: *"Outside the cone the withdrawal leaves the face unchanged; that is the `outsideUnchanged` law of `LocalCausalConeCultivation` read at the dismantling boundary."* The Lean does not support this identification on three counts:

1. **What varies.** `outsideUnchanged` compares `localFace passage.successor site` against `localFace passage.predecessor site` — the support of a *returned morphology difference*. `IsCone` compares the signature of `withdraw population state` against that of `state` — an *intervention on the presented carrier*. `CultivationPassage.withdraw : Difference → Morphology → Morphology` (`Computation/HolonicIntelligenceLifecycle.lean:198`) withdraws a morphology delta; `HolonicExcitationFoundedQuotient.withdraw : Set Site → (Site → Carrier) → …` (`:210`) zeroes carriers. They are unrelated functions with a shared name.
2. **Quantification.** `outsideUnchanged` is per-*site* and per-*probe*; `IsCone` is per-*population*. This is exactly the joint-load gap SKE2 measured.
3. **Linkage.** There is no import, instance, theorem, or definitional path from `LocalCausalConeCultivation` to `IsCone`. `HolonicExcitationFoundedQuotient.lean` imports `NativeMorphologyVariant` (line 2) only to reach `FaithfulLocalSectionLift` (`:300`, `:322`). `LocalCausalConeCultivation` is never mentioned in the SKE file.

---

## 3. Compression in the formal tree

### 3.1 `Soma.Holonics.Compression`

`/home/b/…/Foundation/Receiver.lean:86-94` (namespace `Soma.Holonics`, `:11`)

```lean
/--
A compression is exact for its declared receiver family when every receiver
factors through the quotient map.
-/
structure Compression (ι : Type*) (X : Type u) (Q : Type v) (Y : Type w) where
  quotient : X → Q
  receiver : ι → X → Y
  factor : ι → Q → Y
  exact : ∀ i x, factor i (quotient x) = receiver i x
```

**This object has no compression content.** It has no size comparison, no injectivity failure, no remainder, no cost. The identity (`Q := X`, `quotient := id`, `factor := receiver`) inhabits it for any receiver family. It is a *receiver-exact factorization*, nothing more.

Beware a name collision: `Millennium/PhysicalRealization.lean:228-232` defines a second, opposite-polarity `Compression` — a *witness of collapse*:

```lean
/-- A non-injective realization passage is compression, with the collapsed fibre exhibited. -/
structure Compression (P : RealizationPassage A B) where
  left : Source
  right : Source
  distinct : left ≠ right
  sameTarget : P.span.chart left = P.span.chart right
```

paired at `:222-226` with the sharpest formal rebase in the tree:

```lean
/-- A rebase owes a passage back and both literal identity compositions. -/
structure Rebase (P : RealizationPassage A B) where
  inverse : RealizationPassage.{uG, uR, uB, uA, uF, uOcc} B A
  forwardIdentity : ∀ source, inverse.span.chart (P.span.chart source) = source
  backwardIdentity : ∀ target, P.span.chart (inverse.span.chart target) = target
```

### 3.2 `ReceiverHistoryCompression`, `CompleteReceiverHistoryQuotient`, `preimageFibre`

`Millennium/LineageCompression.lean:35-47`

```lean
structure ReceiverHistoryCompression
    (Generator : Type u) (Receiver : Type v)
    (Source : Type w) (Quotient : Type x) (Face : Type y) where
  /-- Exact factorization at the present receiver cut. -/
  present : Compression Receiver Source Quotient Face
  /-- The admitted source transport generators. -/
  sourceTransport : Generator → Source → Source
  /-- Their proposed transports on the quotient. -/
  quotientTransport : Generator → Quotient → Quotient
  /-- The quotient commutes with every generator. -/
  generatorExact : ∀ generator source,
    present.quotient (sourceTransport generator source) =
      quotientTransport generator (present.quotient source)
```

`:55-57`: `def preimageFibre (quotient : Quotient) : Type _ := { source : Source // C.present.quotient source = quotient }`.

`Millennium/ReceiverHistory.lean:22-33`

```lean
structure CompleteReceiverHistoryQuotient
    (Generator : Type u) (Receiver : Type v)
    (Source : Type w) (Quotient : Type x) (Face : Type y)
    extends ReceiverHistoryCompression Generator Receiver Source Quotient Face where
  complete : ∀ {left right : Source},
    (∀ receiver word,
      toReceiverHistoryCompression.present.receiver receiver
          (transportWord toReceiverHistoryCompression.sourceTransport word left) =
        toReceiverHistoryCompression.present.receiver receiver
          (transportWord toReceiverHistoryCompression.sourceTransport word right)) →
    toReceiverHistoryCompression.present.quotient left =
      toReceiverHistoryCompression.present.quotient right
```

with `causalSignature` (`:42-44`), `quotientEq_iff_causalSignatureEq` (`:47-49`), `quotientNe_returnsSeparatingReceiverHistory` (`:60-63`).

Its docstring, `LineageCompression.lean:33`, is worth quoting because it names the thing SKE would need and disclaims having it:

> The quotient is not called a decoder: its full inverse image is retained as the reconstruction fibre below. **A codec compression additionally owes an exterior presentation and decoder cost.**

No such structure is defined anywhere in the tree.

### 3.3 `FaithfulLocalSectionLift` — and a serious gap

`Computation/NativeMorphologyVariant.lean:24-42`

```lean
structure FaithfulLocalSectionLift
    (Source Code Native Generator Receiver Face : Type*) [AddCommGroup Native] where
  foreign :
    Soma.Holonics.Computation.HolonicIntelligence.ExactForeignWeightPassage Source Code Native
  history :
    Soma.Holonics.Millennium.LineageCompression.ReceiverHistoryCompression
      Generator Receiver Source Native Face
  quotientIsStored : ∀ source,
    history.present.quotient source = foreign.storedValue (foreign.encode source)
  sourceIncidence : Source → Source → Prop
  nativeIncidence : Native → Native → Prop
  incidenceExact : ∀ left right,
    sourceIncidence left right ↔
      nativeIncidence (history.present.quotient left) (history.present.quotient right)
```

**The identity inhabits this type.** Take `Source = Code = Native`, `encode = sourceValue = storedValue = id`, `residual = 0`, `quotient = id`, `factor = receiver = observe`, `sourceTransport = quotientTransport = step`, `sourceIncidence = nativeIncidence`. Every field and law is `rfl` or trivial. (Hand construction from the quoted fields; not kernel-checked.)

Consequently the docstring at `HolonicExcitationFoundedQuotient.lean:291-293` —

```lean
/-- A Soulkiller return: a dismantling return whose productive lane is a faithful local section
lift.  A manifestation — a copied realization with no lift — has no productive lane of this type
and does not inhabit it. -/
structure ExcitationFoundedReturn
    (Source : Type uSource) (Code : Type uCode) (Native : Type uNative)
    (ColdWitness : Type uCold) (Insufficiency : Type uInsufficiency)
    [AddCommGroup Native] where
  returned :
    Soma.Holonics.Computation.HolonicIntelligence.DismantlingReturn
      (Soma.Holonics.Computation.NativeMorphologyVariant.FaithfulLocalSectionLift
        Source Code Native Generator Receiver Face)
      ColdWitness Insufficiency
```

— **is not proved and is false as written.** A copied realization is its own faithful local section lift. The blueprint's SKE0 pass criterion *"a manifestation without that lane does not inhabit it"* (line 164-165) is discharged by no theorem in the file. There is no non-triviality obligation anywhere: nothing requires `Code` to be smaller than `Source`, nothing bounds `residual`, nothing forbids `quotient = id`.

A second gap in the same structure: `ExcitationFoundedReturn`'s only shared parameters with the ambient section are `Generator`, `Receiver`, `Face`. **`N`, `family`, `morphology`, `Site`, `Carrier`, `IsCone`, `extent`, `insufficiency` do not appear.** `DismantlingReturn` itself is a bare triple with no laws (`Computation/HolonicIntelligenceLifecycle.lean:66-72`):

```lean
/-- The physically split return of one foreign-realization dismantling boundary. -/
structure DismantlingReturn
    (Productive : Type uProductive) (ColdWitness : Type uCold)
    (Insufficiency : Type uInsufficiency) where
  productive : Productive
  coldWitness : ColdWitness
  insufficiency : Insufficiency
```

So the blueprint's *"a `DismantlingReturn` type whose productive lane is a `FaithfulLocalSectionLift` **on the family**"* (line 163) is half-built: the lane's *type* is constrained, its relation to the family is not expressible in the type as written.

### 3.4 Is the SKE3 `familyCompression` a `Compression`?

**Yes, literally** — it is declared as `Soma.Holonics.Compression family.Exposure Occurrence (family.Class N morphology) Face` (`:167`). And that is the whole content: an exactness receipt saying the class face is well-defined.

Three things it is not:

1. **It compresses the occurrence population, not the operator.** `X := Occurrence`, `Q := Class`. The body being quotiented is the five presented problems, not the 1,595,392-site operator.
2. **Under SKE3's own full exposure family it is the identity.** `…SKE3…md:91-92`: *"the classes are singletons under the full exposure family."* Five occurrences, five classes. `quotient` is a bijection. Nothing is compressed at all.
3. **It carries no remainder, no trichotomy class, and no loss accounting**, because `Compression` has no field for any of these.

### 3.5 Rebase / condensation / remainder / locking / reach

| §0b term | Formal owner |
|---|---|
| **rebase (zero remainder)** | Present, several times, always as an isomorphism: `Foundation/Holon.lean:61` `structure Rebase` (four `Equiv` fields + three naturality laws); `Algorithm/Rebase.lean:15` `def rebase … (e : S ≃ S')` with module doc *"A noninvertible map is deliberately not called a rebase here"*; `Millennium/PhysicalRealization.lean:222` (two-sided inverse); `Computation/HolonicRecurrentEcology.lean:285-300` `OperationRebase` (four `Equiv`s + `natural`). Zero-remainder holds **by being an equivalence**, never via a `remainder = 0` field. `Millennium/Polarity.lean:161` states the doctrine in prose: *"It is a rebase with zero remainder, not a compression."* |
| **condensation (certified remainder, invertible up to it)** | **No such object.** Nearest are `Foundation/Receiver.lean:181` `structure ReceiverCondensation` — a *witness that two entering faces collapsed* (`left`, `right`, `distinctEntering`, `sameReturned`), i.e. an exhibition of loss with no remainder and no invertibility; and `Millennium/NavierStokesClockedExtensionTower.lean:214` `def condense`, whose docstring says *"This intentionally forgets the intermediate state."* There is **no structure carrying (a) a remainder and (b) an invertibility-up-to-it clause**. |
| **certified remainder** | The remainder *term* exists: `Computation/ExactForeignWeight.lean:17-25` `ExactForeignWeightPassage.residual : Source → Native` with `reconstructs : ∀ source, sourceValue source = storedValue (encode source) + residual source`; and `Millennium/Paying.lean:49` `CompressedPositivity.remainder : AddSubgroup V` with `orthogonal` and `definite`. **Nothing certifies either.** `ExactForeignWeightPassage` has no bound, norm, or smallness condition on `residual`: any `encode`/`storedValue` whatsoever becomes "exact" by *defining* `residual := sourceValue - storedValue ∘ encode`. The blueprint's certified remainder — "the terminal census of width and octave under the restriction" (§0b line 71-72) — has **no formal counterpart**. The phrase "certified remainder" occurs once in the tree, as prose, in an unrelated Selmer context (`Millennium/SelmerCalculus.lean:121`). |
| **quotient (collapsed population exhibited)** | Present: `Compression` + `preimageFibre` + `Millennium/PhysicalRealization.lean:228` `Compression` (the collapse witness) + `Foundation/Receiver.lean:104` `ReceiverInsufficiency`. |
| **the trichotomy as a formal object** | **ABSENT.** There is no `Trichotomy` type, no discriminated union over {rebase, condensation, quotient}, and no obligation anywhere that a return *state which one it is*. The word appears only in unrelated theorem names (`Millennium/AngleExcess.lean:269` `theTrichotomyIsFiveThreeAndUnbounded`; `Millennium/Paying.lean:243` the radical trichotomy; `Mathematics/CopsonDeBruijnOrbitLimit.lean:486`) and in `lt_trichotomy` proof calls. |
| **locking** (retained standing stops growing per added exposure) | **ABSENT.** No declaration or docstring in 1,091 files matches "locking", "marginal standing", "retained standing", or a saturating-growth notion. The `lock` hits are Parametron *phase* locking (`Millennium/HolonicParametron.lean`, `Computation/SituatedMachineLearning.lean:11,116,124`); the `saturat*` hits are lattice/Selmer saturation (`Foundation/LatticeTransport.lean:87-146`). |
| **reach** (how far a body reproduces the operator per retained octet) | **ABSENT.** `reach` exists only as Navier–Stokes frequency propagation (`Millennium/NavierStokesFrequencyReach.lean:75` `def reach (N : ℕ) : ℕ → Set SpatialFrequency`). No codec, no octet accounting, no "coverage per retained octet." `octet` appears once, as a number-theoretic eighth (`Millennium/Coupling.lean:171`). |

The one place the tree does formalize *hidden* loss is `Computation/SituatedMachineLearning.lean:26-…` (`SituatedLearningReturn`, `ReturnDescendsThroughLoss`, `equalLoss_differentReturn_obstructsDescent`, `scalarLossDoesNotDetermineCultivation`) — a proof that a scalar loss face does not determine the morphology return. That is a refutation pattern, not a compression grade.

---

## 4. Grain and group characteristics

**No Lean owner states cones, currents, or signatures over groups/populations of sites.**

- Every `Set Site` in the SKE line is an *arbitrary* subset: `withdraw` (`:210`), `IsCone`'s `cone` and `population` (`:220-224`), `causalCone : Delta → Set Site` (`NativeMorphologyVariant.lean:116`), `extent`/`insufficiency` (`:255-264`). Not one carries a grouping map, a partition, a `Setoid Site`, or a saturation condition.
- `aggregateCurrent` sums over the **entire** `Fintype Site` (`HolonicNeuralEcology.lean:49`), never a subgroup.
- There is no `Setoid Site`, no `Quotient` of `Site`, no `Site → Group` anywhere in the tree. The setoids that exist are on the *state* (`allHistorySetoid` on `Site → Carrier`, `:66`), the *occurrence* (`familySetoid`, `:154`), or the *source* (`Millennium/HolonicGranularBoundaryRadiation.lean:257` `signatureSetoid`).

**The tree's only formal notion of "grain" is receiver-side, not intervention-side.** `Millennium/HolonicGranularBoundaryRadiation.lean:245-302`:

```lean
/-- A receiver grain is only a family of observable future consequences over one source
population.  `Index` may contain a receiver and an ordered generator word, but this definition
does not privilege that presentation. -/
structure CausalGrain (Source Index Face : Type*) where
  signature : Source → Index → Face

/-- A passage to a coarser grain exists only when equality of every fine consequence forces
equality of every coarse consequence.  This is the factorization law which an authored tokenizer
or renderer would owe and cannot obtain from matching spellings alone. -/
structure Passage
    (fine : CausalGrain Source FineIndex FineFace)
    (coarse : CausalGrain Source CoarseIndex CoarseFace) where
  respects : ∀ {left right},
    fine.signature left = fine.signature right →
      coarse.signature left = coarse.signature right
```

`CausalGrain.Passage` coarsens the **index of observation**. §0b's move coarsens the **lattice of intervention**. There is no owner for the latter, and `Passage` cannot be repurposed: its `respects` law is about signature equality, not about withdrawal.

**Closest existing group-characteristic-of-flux owner** — `Computation/HolonicCausalTailLens.lean:29-45`:

```lean
/-- Exterior depth and nonnegative-energy receiver over one finite addressed pair population. -/
structure CausalTailLens (Site : Type uS) (Current : Type uC) (Depth : Type uD)
    [Fintype Site] [Fintype Depth] [DecidableEq Depth] [Zero Current] where
  depth : Site → Site → Depth
  energy : Current → NNReal
  energy_zero : energy 0 = 0

/-- Sum exactly those pair-energy faces at the receiver-declared depth. -/
def project (lens : CausalTailLens Site Current Depth)
    (currents : AddressedPairSection Site Current) : Depth → NNReal :=
  fun depth ↦ ∑ target : Site, ∑ source : Site,
    if lens.depth target source = depth then lens.energy (currents target source) else 0
```

This *is* a grouping of the flux (site-pairs partitioned by a declared `depth`, a nonnegative characteristic summed per group), with `mass`/`tailEnergy`/`tailRadius`/`tailSurface` functionals over it (`Mathematics/CopsonDeBruijnFiniteTail.lean:29-48`; `mass finite := ∑ n, finite n`). But its own module doc, `:10-11`, says: *"The scalar receiver never becomes native morphology or a transport governor."* It groups **pairs by depth**, not sites by population/head/layer, and it has no connection to `withdraw`, `IsCone`, or `DeclaredFamily`.

**Census-like characteristics (octave, width, mass, dilation, enclosure).** In Lean these words are entirely number-theoretic or PDE-analytic and never touch `Site`: `octave` only at `Millennium/LandmarksAndModuli.lean:120` (Bertrand's postulate) and the Mertens files; `mass` in the RH/Copson tail functionals; `dilation` in modular/power-series/Navier–Stokes scaling; `enclosure` in interval arithmetic. `Computation/HolonicArchitectureCharts.lean:56` carries an explicit denial: `/-- Normalization is over the admitted contact population, not over an authored global width. -/`.

Outside Lean, §0b's phrase *"read through what the passage census already returns (the widest octave and enclosure width of a carrier, its bound octave, its mass and dilation)"* (blueprint line 45-47) does not describe the live census either. `crates/holonic-engine/src/resident_section.rs:479-496` `struct TransferCensus` carries only octets, launches, synchronizations, allocations, resident octets, and `section_read_outs`. `widest_octave` / `bound_octave` / `enclosure_width` appear **only under `archive/retired-phoenix-rust/`**. That vocabulary is not standing apparatus.

**Is "coordinate" formally the wrong instantiation?** **No.** Nothing in the Lean makes coordinates illegitimate. The grain is a modelling choice at the realization boundary, subject only to `[Fintype Site]`. What *is* formally consequential is the direction of the change: **coarsening restricts the admissible withdrawals, so group-grain `IsCone` is strictly weaker than coordinate-grain `IsCone`.** Every coordinate cone that is `IsCone` remains sound at any grain; a group cone that is `IsCone` at group grain says nothing about non-group-aligned withdrawals. §0b's re-founding therefore weakens the claim rather than strengthening the verification.

---

## 5. HNA0 — does `HolonicRecurrentEcology` require an exact trace or per-operation observation?

**No. Neither.** `Computation/HolonicRecurrentEcology.lean:28-38`

```lean
/-- One exact operation on one contemporary ecology. -/
structure OperationStep
    (Ecology : Type uEcology) (Occurrence : Type uOccurrence)
    (Emission : Type uEmission) (Trace : Type uTrace) where
  operate : Ecology → Occurrence → Emission × Trace × Ecology
  predecessor : Ecology
  occurrence : Occurrence
  emission : Emission
  trace : Trace
  successor : Ecology
  exact : operate predecessor occurrence = (emission, trace, successor)
```

`:71-82`

```lean
/-- A complete recurrence driven by one operation owner. -/
structure Recurrence
    {Ecology : Type uEcology} {Occurrence : Type uOccurrence}
    {Emission : Type uEmission} {Trace : Type uTrace}
    (operate : Ecology → Occurrence → Emission × Trace × Ecology) where
  state : ℕ → Ecology
  occurrence : ℕ → Occurrence
  emission : ℕ → Emission
  trace : ℕ → Trace
  exact : ∀ time,
    operate (state time) (occurrence time) =
      (emission time, trace time, state (time + 1))
```

`:101-104`

```lean
/-- The next operation consumes exactly the preceding successor ecology. -/
theorem successor_joins_next_predecessor (recurrence : Recurrence operate) (time : ℕ) :
    (recurrence.stepAt time).successor =
      (recurrence.stepAt (time + 1)).predecessor := rfl
```

The joining theorem is `rfl` — it is definitional in `stepAt`'s construction from `Recurrence.state : ℕ → Ecology`. **The only law in the primitive is that `operate`'s three outputs are the ones recorded.** `Trace` is a bare type parameter; nothing forbids `Trace := Unit`. `exact` is an equation, not a measurement obligation: it says the record agrees with the function, not that anything was read out to a host.

`FiniteRecurrentOperation` (`:197-205`) adds only two fields, `present` and `advanceMorphology`. Its `operate` (`:217-241`) builds the trace as a record of *closures*:

```lean
  let trace : FiniteOperationTrace Site Carrier Generator Receiver Occurrence := {
    …
    localCurrent := fun target source =>
      neural.localCurrent ecology.morphology generator presented target source
    aggregateCurrent := neural.aggregateCurrent ecology.morphology generator presented
    reacted := reacted
  }
  …
  (neural.observe receiver reacted, trace, successor)
```

Constructing that record forces no evaluation. And observation happens **exactly once per operation**, at `neural.observe receiver reacted` — the terminal face. So HNA0 is, if anything, evidence *for* §0b's SKE4 apparatus obligation ("one readout at the terminal face"): the formal owner never asked for per-sub-operation readout. The 1,275-readouts-per-cycle session that §0b indicts (blueprint lines 56-65) is an injection with no formal warrant, correctly identified.

---

## 6. Every theorem of `HolonicExcitationFoundedQuotient.lean`

| Line | Declaration | What it licenses | What it does **not** license about a card measurement |
|---|---|---|---|
| `:50` | `signature_nil : signature N m s r [] = N.observe r s` (`rfl`) | Empty history reads the presented state directly. | Nothing measured. |
| `:55` | `signature_step : signature N m (N.step m g s) r h = signature N m s r (h ++ [g])` | Driving then reading equals reading at the extended history — the associativity that makes the quotient well-defined. | Says nothing about withdrawal. |
| `:110` | `nativeEq_iff_signatureEq` — `quotient left = quotient right ↔ causalSignature left = causalSignature right`, inherited from `CompleteReceiverHistoryQuotient.quotientEq_iff_causalSignatureEq` | The relevance law: native identity **is** equality of the complete causal signature over **all** receivers and **all** words. | It is a statement about the **all-history** quotient, not the declared family. A card measurement over three fixed words (`…SKE3…md:31-32`) can never instantiate it. `…SKE3…md:89-90` says so: *"the all-history quotient of SKE0 is not computed."* SKE3's actual owner is `Identified` (`:148`) and `separatingExposure_reopens` (`:188`). |
| `:118` | `nativeNe_returnsSeparatingHistory` — unequal native states yield an explicit separating `(receiver, history)` | Non-identity is always witnessable. | Existence of a separator, not a procedure for finding one; and again over all histories, not the declared three. |
| `:181` | `identified_faces_eq (h : Identified …) (exposure) : … = …` (`h exposure`) | Trivial projection of the definition. | Nothing. It is `Identified`'s eliminator. |
| `:188` | `separatingExposure_reopens` — one separating declared exposure gives `¬ Identified left right` | **This is the theorem SKE3's card deed actually discharges.** `The second operand is ` returning `5` against `6` refutes the empty-history identification. Sound and fully licensed by one measurement. | It gives non-identity only. Positive identification (`Identified`) requires *every* exposure, which is finite here and so *is* measurable — but only relative to the declared family. |
| `:198` | `identified_of_nativeEq` — the family quotient is coarser than the all-history quotient | Any family class is a union of native classes. | The converse is false and unclaimed: measured class equality is not native equality. |
| `:214` | `withdraw_empty : withdraw ∅ state = state` | The null-withdrawal control's premise. | The card's null-withdrawal receipt (`…SKE3…md:39`) verifies the *apparatus*, not this theorem, which is `rfl`-adjacent. |
| `:227` | `isCone_univ : IsCone … Set.univ` | The whole site population is always a cone. | **Exhibits the degeneracy.** `IsCone` alone certifies nothing about locality; the interesting content is entirely in minimality, which the tree does not define. |
| `:244` | `loadBearing_mem_of_isCone` — `IsCone C → LoadBearing site → site ∈ C` | A **necessary condition**: every true cone contains every singleton-load-bearing site. Usable as a *lower bound* certificate given single-site withdrawal measurements. | **Does not go the other way.** It never certifies a candidate as `IsCone`. On the resident operator its lower bound is vacuous, because SKE2 found no single-population load (`…SKE2…md:18-20`). |
| `:268` | `DeclaredFamily.withdraw_insufficiency_unchanged` — *given* `sound : ∀ occurrence exposure, IsCone …`, withdrawing anything inside the insufficiency leaves every declared face unchanged | The "you can only lift what you infer" law, correctly proved. | **Its hypothesis `sound` is exactly the thing the card cannot supply.** It is a conditional whose antecedent is unverified — and, at SKE3's measured cones, *refuted*. Applied to SKE3's numbers, the theorem's conclusion is the very statement the card falsified. It licenses nothing about the 279,132-site insufficiency reported at `…SKE3…md:55`. |
| `:312` | `productive_everyGeneratorWordExact` | The productive lane's quotient commutes with every generator word. | Inherited from `ReceiverHistoryCompression`; holds for the identity lift too (§3.3). |
| `:320` | `admitted_replaceColdWitness` (`rfl`) | Cold ancestry cannot change productive admission. | A projection fact about a 3-tuple. |
| `:347-386` | **Control** — `signature_false = 3`, `signature_true = 3`, `site0_bearing_under_false`, `site1_inert_under_false`, `site1_bearing_under_true`, `site0_inert_under_true`, `cone_false : IsCone ecology () presented () [false] {0}`, `cone_true : IsCone ecology () presented () [true] {1}` | **The only non-degenerate `IsCone` proofs in the entire tree.** They establish that a magnitude ranking of the presented state does not determine the cone. Both are discharged by `simp`/`decide` over a two-site model — i.e. by *exhausting* `Set (Fin 2)`. | The Lean control uses **one** state (`presented : Fin 2 → ℤ := fun _ => 3`) under **two different histories**. The blueprint's SKE0 pass criterion says *"a control exhibits two occurrences with equal magnitude and different cones"* (line 162). The Lean docstring at `:371-373` is accurate — *"The same presented magnitudes have different cones under different histories"* — the blueprint's paraphrase is not. |

No `sorry` in the file. `#print axioms` at `:392-395` covers `nativeEq_iff_signatureEq`, `loadBearing_mem_of_isCone`, `withdraw_insufficiency_unchanged`, `Control.cone_false`. Imported by the umbrella at `ElementaryHolonics.lean:38`.

---

## 7. Where blueprint §0b claims what the Lean does not support

**(1) The grain is not what decides union-composition.** §0b, line 90-91: *"On the resident operator a site is a flux group … never a coordinate, **so cones compose under union** and a family's extent is a union of groups."* And SKE4's pass criterion, line 268: *"the class cones and the family cone are group cones **that compose**."*

The "so" is unsupported. `IsCone` is monotone-upward at **every** grain (§2.a), coordinates included — union-composition was never in doubt for genuine cones. What does not compose, at every grain including groups, is the card's actual property: *"the smallest suffix of that order whose complement, withdrawn as one population, leaves the receiver face unchanged"* (blueprint line 199-201). Call it complement-sufficiency. It is monotone in neither direction: `C ⊆ C'` compares `withdraw Cᶜ` against `withdraw C'ᶜ`, two unrelated interventions on a nonlinear operator. **The sentence is therefore either trivially true and grain-independent (if "cone" means `IsCone`) or false and grain-independent (if "cone" means what the card measured).** Re-grained, the same procedure will produce the same defect; it will simply be harder to find a witness because the search space is smaller.

**(2) SKE2's cones were not merely "withdrawn as cones under §0b" — they were measured false.** Blueprint line 214-220 grades SKE2 PASSED and says *"its cones are withdrawn as cones under §0b … The instrument and the controls stand; the coordinate grain does not."* The SKE3 measurement (`…SKE3…md:66-69`) refutes `IsCone` for at least two named exposure cones directly (§2.a). The failure is attributable to the *verification method* — one complement plus 22 nested probes standing in for a universal over 2^1.5M populations — which the grain change does not touch. The SKE2 record itself states the limit correctly (`…SKE2…md:122-125`); the blueprint's §0b re-attribution to the grain does not match its own receipts.

**(3) "Compression is the trichotomy" has no formal object.** §0b line 67-70. There is no `Trichotomy` type, no discriminated return, no obligation that a return state its class (§3.5). The pass criteria at lines 126-127 and 268-269 ("the return states its trichotomy class"; "carries the certified remainder that bounds its flux profile") name obligations the tree cannot express, let alone check. `ExactForeignWeightPassage.residual` is an unbounded bookkeeping term, not a certificate.

**(4) Locking and reach are not formal objects.** §0b line 72-76 and SKE5's pass criteria (lines 285-292) require "locking" and "reach" receipts. **Absent** from the tree entirely (§3.5). They can be *measured* — they cannot yet be *stated*.

**(5) The `outsideUnchanged` identification is wrong.** §1, line 88-90 (§2.c′): `LocalCausalConeCultivation.outsideUnchanged` is a supplied field about the support of a **morphology difference**, per-site, with a `withdraw` of a different type. It is not the outside-unchanged law of `IsCone` "read at the dismantling boundary"; there is no path between the two in the Lean.

**(6) The manifestation exclusion is not proved.** §1, line 96-100 and the SKE0 pass criterion: *"a manifestation without that lane does not inhabit it."* The identity inhabits `FaithfulLocalSectionLift` (§3.3). The type refuses nothing.

**(7) The productive lane is not tied to the family.** §1 line 96, SKE0 pass line 163: *"a `FaithfulLocalSectionLift` **on the family**."* `ExcitationFoundedReturn` (`:294-302`) shares only `Generator`, `Receiver`, `Face` with the family section; `DeclaredFamily`, `IsCone`, `extent`, and `insufficiency` do not occur in it, and `DismantlingReturn` is a lawless triple.

**(8) The census the group grain is to be read through does not exist.** §0b line 45-47 (§4): neither in Lean nor in the live `TransferCensus`; the vocabulary is in retired Rust.

---

## 8. The one change that would make `IsCone` dischargeable

Stated because the tree's own idiom already contains it. Everywhere else, obligations are quantified over a **declared** finite family — `declaredProbes` in `NativeTransportScaffold.lean:237-252`, `family.receivers`/`family.histories` in `DeclaredFamily`, `∀ receiver word` inside a `Compression`'s exactness. `IsCone` is the sole place the SKE line quantifies over an unbounded lattice, and it is the sole place the campaign is stuck.

Two consistent exits, both expressible in the existing owners:

- **Declared-population cone.** Replace `∀ population : Set Site` with `∀ population ∈ declaredWithdrawals`, a field of the family. Then the card discharges the obligation exactly, the grade is honest, and `extent`/`insufficiency` inherit a bounded meaning. Unions still compose (monotonicity holds verbatim). This matches how every other obligation in the tree is written.
- **Structural cone.** Add locality to `FiniteLocalCurrentEcology` — `reaction m g t 0 = 0`, a read-set for `observe`, an in-neighbourhood for `localCurrent` — and derive `IsCone` for the backward closure by induction on the history, with no withdrawals at all. This buys the universal, at the cost of the architecture-neutrality that `localCurrent`'s whole-state argument was built to protect (`HolonicNeuralEcology.lean:29-30`).

What cannot be done is what the campaign has been doing: measure a bounded number of sufficient withdrawals and grade a universal.


