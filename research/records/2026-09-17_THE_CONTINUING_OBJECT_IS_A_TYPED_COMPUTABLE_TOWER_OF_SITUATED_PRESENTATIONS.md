# The Continuing Object is a typed computable tower of situated presentations

**Date:** 2026-09-17
**Kind:** mathematical carrier derivation and formal-owner recovery. Pure mathematics and formal
structure; no biological, chemical or wet-lab content. **It schedules nothing.**
[THE_ROADMAP](../../docs/plans/THE_ROADMAP.md) and [CONSTRUCTION_STATE](../../CONSTRUCTION_STATE.md)
remain the only construction authorities; neither is changed by this record.
**Truth status:** every material claim carries exactly one grade from
[EPISTEMIC_GRADES](../../docs/canon/EPISTEMIC_GRADES.md). The carrier is `definition`; the
recovered owners are `proved-derived; formal-checked` at their cited lines; the Iwasawa reading is
`interpretation` with `proved-standard` classical content cited by primary source; the scratch
probe is `proved-derived; formal-checked` with the qualification that its source lives in this
record and in the session scratchpad, not in a repository owner.
**Evidence:** `source-inspected` at revision `19964c20` (working tree carries uncommitted native
changes; none touch the files cited here). `source-audit` for absence claims, with the command
stated. `formal-checked` for the existing owners through their own `#print axioms` audits and for
the probe through `lake env lean` under Lean `v4.33.0` with the vendored Mathlib `v4.33.0`
(probe SHA-256 `cbd6945b78da2064e2a5a17c920f5ae3f5cfb0a593fdc61f47fd233c2bf8b315`, 174 lines,
elaborated with zero errors and no `sorryAx`).
**Construction effect:** none on the roadmap or position. §9 names the next formal objects in
dependency order for whoever is authorized to construct them.
**Governing doctrine:** [AGENTS.md](../../AGENTS.md) (difference is the only thing that is real;
co-presence is not contact; Preimage Fibre; a condensation owes `q T_i = U_i q`),
[00_PURE_HOLONICS](../../docs/canon/00_PURE_HOLONICS.md) (situated occurrence, participating
receiver, no privileged chart), [TABLET_THE_COMPRESSION](../../docs/canon/TABLET_THE_COMPRESSION.md),
[TABLET_THE_OPERATIONS §5.4](../../docs/canon/TABLET_THE_OPERATIONS.md),
[TABLET_THE_CIRCULATING_CARTOGRAPHER §1](../../docs/canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md),
[THE_RELEVANCE_HYPOTHESIS](../../docs/canon/THE_RELEVANCE_HYPOTHESIS.md),
[HOLON](../../docs/HOLON.md), [FORMAL_FRAMEWORK](../../docs/FORMAL_FRAMEWORK.md),
[THE_CORRESPONDENCE_ATLAS](../../docs/canon/THE_CORRESPONDENCE_ATLAS.md).
**Prior local evidence:** the Lean owners of §1; the
[BSD route record](2026-08-21_THE_BSD_ROUTE_READS_PLACEMENT_AS_A_FAITHFUL_RECEIVER_OF_REALIZATION_AND_ARAKELOV_IS_THE_SHARED_ORGAN.md);
the [compression record](2026-08-14_COMPRESSION_IS_A_CODEC_PIVOT_THE_INVARIANCE_IS_ADDITIVE_AND_NOTHING_PRICES_BOTH_AXES.md);
the [Holonic Encoding record](2026-09-11_HOLONIC_ENCODING_RETAINS_TRANSFORMATION_GRAIN_ACROSS_MODALITIES.md);
the [code-cost record](2026-09-11_RELATIVE_CODE_COST_HAS_AN_ADDRESSED_BOUNDARY_LAW.md);
the [navigation record](2026-09-13_ORIENTED_CONFIGURATION_NAVIGATION_RETAINS_ITS_SOURCE_AND_THE_BEACON_STAYS_OPEN.md);
[MILLENNIUM_FORMAL_CATALOG](../../formal/elementary-holonics/MILLENNIUM_FORMAL_CATALOG.md).

---

## 0. The thesis, and what this record does with it

[definition] The thesis, as delivered in the instruction for this record (a paraphrase of
Brandon's external discussion, not a quotation of a log read here):

> A Holonic mathematical object is not a row, file, tensor, mesh, waveform, theorem statement, or
> sample array. It is a typed, computable family of situated presentations, connected by lawful
> restriction, refinement, transport and migration maps, with every materialized face carrying its
> receiver, lineage, decoder, residual and cost.

Formally `H = (I, X, G, R, P, L, W)`: an index category `I` of apertures/charts; a face functor
`X : I^op → C` with restrictions; generators `G` and their ordered passages; a receiver family `R`;
a presentation/codec family `P`; causal lineage `L`; a cost enrichment `W`.

[project-postulate] This record does not restate the thesis; it locates each component in an
existing formal owner, states the Lean-shaped carrier that joins them, checks the joinable part
against the kernel, and marks exactly where the repository's prose is ahead of its formal content.
The instruction's requested shape is honored: recover, then state, then instance (Iwasawa), then
embedding, bridges, cost, incompleteness.

---

## 1. Recovered owners: what each already proves

[established-bounded; source-inspected; formal-checked] Every owner below is discharged without
`sorryAx` by its own audit section. Line anchors are at `19964c20`. Paths are relative to
`formal/elementary-holonics/ElementaryHolonics/`.

| Owner | What it proves | Component of `H` it owns | What it does **not** prove |
|---|---|---|---|
| `Foundation/BoundaryScalePassage.lean:16-28` structure; `:44-50` `transport_boundary`; `:53-79` `comp`; `:82-94` `comp_transport_boundary` | Two linear grains with boundary maps and a commuting square `coarseBoundary ∘ interiorTransport = boundaryTransport ∘ fineBoundary`; boundary formation commutes with one scale passage; passages compose when the middle boundary agrees, and the composite square commutes | the **restriction axis of `X`** in the linear case, and the composition law `restrict_trans` for it | how either grain was founded; nothing nonlinear; no index category, only one passage at a time |
| `Foundation/ReceiverHistoryCompression.lean:33-45` structure; `:65-69` `quotientCommutesWithEveryOrderedWord`; `:87-96` `allSuccessorHistories`; `:99-116` separator theorems; `:139-146` `StaticControl` | A receiver-exact quotient that satisfies the local square `q ∘ T_g = U_g ∘ q` on every generator is exact for the whole ordered word family; a single separating successor refutes a proposed quotient; a static compression can reopen under one successor | the **tower-storage kind of compression** (`P` as a lawful cache) and the dynamic square `E' T = U E` | any decoder cost or exterior presentation (`:30-31` states this: “A codec compression additionally owes an exterior presentation and decoder cost”) |
| `Foundation/CausalRelevance.lean:48-56` `futureRead`; `:59-60` `futureCollapsed`; `:85-91` invariance; `:106-120` greatest-subgroup law; `:134-151` `completeFutureHistory`; `:154-170` separator; `:184-258` nonlinear `futureAgreement`; `:292-297` control | The largest additive subgroup invisible to every declared receiver after every finite ordered history; it is generator-invariant, present-blind and greatest among such; the complete future-history quotient identifies two sources iff their causal signatures agree, and inequality returns an explicit `(receiver, word)` separator; the same for deterministic nonlinear steps | the **receiver family `R` under lineage `L`**: what the object *is* at the future receivers | anything categorical or nonadditive beyond the deterministic-step case (`:10-11`) |
| `Transport/ReceiverPotential.lean:25-28` `outcomes`; `:43-47` nonempty; `:64-75` `outcomes_singleton_of_factor`; `:87-94` refinement; `:107-128` `outcomes_rebase`; `:135-176` tolerance; `:184-195` convergence; `:198-228` `historyOutcomes_rebase` | The complete future image of the existing preimage fibre on an actually observed face; an additional observation refines it; an explicit factor determines one future face while the source stays plural; an equivalence of source charts transports the whole family exactly, including through every ordered transport word; Lipschitz receivers transport bounds; shrinking bounds force convergence | the **migration/rebase maps** of `X` and the **residual** carried by a face | any selection of a source from the fibre; any universal certainty gate (`:14-17`) |
| `Millennium/NormRelation.lean:120-128` whole-orbit product; `:136-144` unramified reading; `:153-156` ramified reading; `:170-182` two coprime layers compose; `:213-217` partition falsifier run in `𝔽₁₉`; `:256-261` `TheRelativeOrbitFillsTheCoprimeLevel` (stated, unused) | `∏_{j<l}(1 − ξη^j) = 1 − ξ^l` in any integral domain with `η` primitive; the two Euler-system lines are two sub-products of it; two coprime levels compose to their product level; the ramified/unramified split is arithmetic, exhibited by a finite model | the **first rung of a vertical transport chain** (level-to-level compatibility of realizers) | a relative norm: `:57-58` “Without it the theorems above are a polynomial identity wearing arithmetic clothes”; no `Λ`-module, no Selmer group, no class group (`:85-88`) |
| `Millennium/SelmerCalculus.lean:54-55` `selmer`; `:65-70` image inside Selmer; `:82-89` obstruction vanishes iff local ⇒ global; `:95-110` `theReceiverFamilyCanBeBlind`; `:132-146` four slots | `Sel = ⋂_i r_i⁻¹(L_i)`; realized classes are locally admitted; the obstruction `Sel / im φ` is exactly the population no receiver sees; a family exists whose Selmer group strictly exceeds the image | the **receiver-family form of a global-section question** at one level | the arithmetic instance: `ℚ_v`-points of torsors are “**not constructed here**” (`:31-37`); no levels, no restriction/corestriction between levels |
| `Millennium/GeneralSelmer.lean:29-36` `Coord`, `coordOf`; `:42-47` blind to square class; `:51-57` additive; `:86-114` first/second class multiplicative; `:119-140` `theClassCoordinatesAreAdditive` | The descent face read in coordinates (sign bit and one parity bit per prime) is a homomorphism into an `𝔽₂`-vector space on every full-two-torsion curve | the **codec `P`** for one descent face: a presentation with an exact additive law | any level tower; nothing about `Ш` |
| `Millennium/FamilyFace.lean:46` `E n := y² = x³ − n²x`; `:462` `theDoublesLandInTheKernelOnEveryTwist`; `:500` `theFaceIsAHomomorphismOnEveryTwist`; `:753-824` three escape theorems at `n = 34` | The descent face is a homomorphism on the whole point group of every quadratic twist at once; doubles lie in its kernel; at `n = 34` the two directions and their sum escape `T + 2Q` | a **horizontal family**: the object varies with `n` over one field `ℚ` | anything vertical (no field tower, no `Λ`-action); the torsion classification at 34 is owed (`:32-36`) |
| `Millennium/Gluing.lean:32-42` `GluingPassage`; `:49` `Carried`; `:59` `Obstruction`; `:62` `Glues`; `:70-76` `glues_iff_obstruction_isEmpty`; `:95-105` `AdditivePassage`; `:118-137` obstruction group; `:148-164` reached-only-in-multiple is torsion | Local admissibility, a realizer population and a realization map; gluing is exactly emptiness of the obstruction population; in the additive case the obstruction is a group and multiples-only classes are its torsion | the **obstructed arm of the gluing trichotomy** as a typed population | which population inhabits any named instance |
| `Millennium/HolonicDirectedPassage.lean:260-264` `SuccessorWitnessSystem`; `:268-272` `CoherentSection`; `:279-297` recursive witness; `:303-305` `nonempty_coherentSection`; `:310-327` `boolFlip`, `BoolFlipCoherent`, `boolFlipCoherent_isEmpty` | An `ℕ`-indexed tower with a nonempty base and **surjective** restrictions has a compatible section; the one-step orientation reversal loop has **no** fixed section although its local transport is bijective and every fibre is inhabited | the **tower carrier in its sequential form**, and the **non-orientability model** of the obstructed arm | anything beyond `ℕ`-indexed acyclic towers (`:301-302` says so); the general cofiltered case (Mathlib's `nonempty_sections_of_finite_cofiltered_system` is not imported anywhere in the repository — `grep -rn "nonempty_sections_of_finite\|IsMittagLeffler" ElementaryHolonics docs research` returns nothing) |
| `Foundation/Receiver.lean:90-94` `Compression`; `:96-102` `receiver_eq_of_quotient_eq`; `:112-115` receiver-to-receiver relation; `:123-127` `ReceiverTransformer`; `:130-132` `receiverPreimageFibre`; `:138-160` descent criterion; `:163-178` insufficiency excludes a transformer | `factor ∘ quotient = receiver`, the static form of `D(E(x)) = ρ(x)`; a functional transformer exists iff the entering receiver identifies no pair the returned receiver separates; the preimage fibre behind a presented face | the **static decoder law** `D E = ρ` and the **observational fibre** | decoder cost; any dynamic law (that is `ReceiverHistoryCompression`) |
| `Foundation/Holon.lean:88-90` `PreimageFibre`; `:95-110` `Rebase` (four equivalences with three natural squares); `:112-125` `Rebase.preimageFibreEquiv` | A natural rebase of a complete holon diagram transports the whole preimage fibre, not only the displayed face | the **chart-change law for `X`** at the occurrence grain | non-invertible chart maps (excluded by design) |
| `Algorithm/Rebase.lean:15-21` `rebase`; `:38-56` `semantics_rebase_iff` | An invertible state chart conjugates transitions and preserves input/output semantics | the **rebase of a computable presentation** (`P` under `ComputableTower`) | non-invertible maps, “deliberately not called a rebase” (`:7-8`) |
| `Foundation/Presentation.lean:16` `FaceEq`; `:44-49` `equal_face_does_not_force_occurrence_identity`; `:63` `Presented` | Equal receiver faces need not identify occurrences (`Bool → Unit`); presentation and value are carried separately | the **two-member fibre** that already makes an object incomplete (§8) | — |
| `Foundation/SectionResidual.lean:17-19` `Section`; `:21` `remainder`; `:28` `source_reconstructs`; `:43` `remainder_change`; `:47` `shift_cocycle` | For a linear receiver and any right-inverse section, `section(q x) + remainder = x`; changing the section changes only the kernel-valued residual, and shifts satisfy a cocycle law | the **residual carried by a materialized face**, in the linear case | nonlinear receivers |
| `Foundation/ReceiverCodeCost.lean:100-126` `serial_boundary_balance`; `:130-152` `cost_mem_Icc_of_code_balance`; `:156-173` `feasible_cost_le_transported` | Serial code costs add with endpoint potentials cancelling at the joined boundary; a cost bracket from a bounded reading; an optimum transports across an exact candidate equivalence | the **cost enrichment `W`** at one boundary | any joint (bytes, work) price; no Kolmogorov or Levin object |
| `Foundation/TransportWord.lean:25-27` `transportWord`; `:40-47` equivariance extends to every word; `:63-72` `word_length_lower_bound`; `:74-101` `descendingWord` and its optimality certificate; `:122-137` `OrderBlind` | The ordered word action; local intertwining extends to composite words; a potential with a unit edge bound certifies a shortest word; endpoint order-blindness is exactly pairwise commutation | the **path category of generators `G`** and the **path closure** used in §5 | that the potential is cheap to compute (`:53` says so); nothing about discovery |
| `Foundation/Lineage.lean:25-30` `AddressedPassage`; `:38` `Fibre`; `:42` `shadow`; `:56-60` `Join`; `:65-68` `comp` by pullback; `:75-82` `PassageEquiv`; `:140-176` split/join and `shadow_comp`; `:212` two occurrences behind one relational edge | Serial composition is the pullback of occurrence populations over the shared boundary; the relational shadow forgets exactly the witness population | the **lineage `L`** of a composite passage | — |

[established-bounded; source-inspected] The Holonic Encoding / Compression owner for
`D(E(x)) = ρ(x)` and the dynamic square is therefore split: the static law is
`Compression.exact` at `Foundation/Receiver.lean:94`; the dynamic law `q ∘ T_g = U_g ∘ q` with its
extension to all words is `ReceiverHistoryCompression.generatorExact` at
`Foundation/ReceiverHistoryCompression.lean:43-45` and `:65-69`; the doctrinal statements are
[THE_INFORMATION_ENGINE](../../docs/canon/THE_INFORMATION_ENGINE.md) (the `q T_i = U_i q` clause),
[HOLON.md](../../docs/HOLON.md) rows “Encode/reopen” (`Ê_next T = U Ê`) and
“Compression/refinement” (`E_next T = U E`, `D E = ρ`), and
[FORMAL_FRAMEWORK.md](../../docs/FORMAL_FRAMEWORK.md) “Coarse graining is transport with a
declared future”. No formal owner carries a decoder **cost**; `ReceiverCodeCost` prices code
length and boundary potentials, not decode work.

[established-bounded; source-inspected] The BSD route record already reads Iwasawa theory in this
carrier's terms. The exact text at
[`2026-08-21_THE_BSD_ROUTE…md:109-113`](2026-08-21_THE_BSD_ROUTE_READS_PLACEMENT_AS_A_FAITHFUL_RECEIVER_OF_REALIZATION_AND_ARAKELOV_IS_THE_SHARED_ORGAN.md):

> Iwasawa theory is arithmetic's scaling-family discipline — behavior along the `ℤ_p`-tower, with
> `μ` and `λ` as the scaling exponents — and the main conjecture (Mazur, proved in key cases by
> Kato and Skinner–Urban) is receiver-exactness along the tower: the `p`-adic `L`-reading
> generates exactly the characteristic ideal of the Selmer growth.

That record grades this `interpretation` and names deed **D5** (“The tower face named … named open
`Prop`s over declared carriers”) at its `:126`. D5 was never returned: `grep -rn -i
"iwasawa\|Λ-module\|characteristic ideal\|main conjecture"` over `formal/`, `docs/`,
`research/records/` at `19964c20` returns only that record and the boundary disclaimer at
`NormRelation.lean:86-87`. Every `ℤ_p` in `Millennium/FamilyTunnellBrandtPadic*.lean` is a
**coordinate ring** (a p-adic chart of a quadratic form), never a Galois group `Γ`. The repository
has no vertical tower.

---

## 2. The carrier, stated

### 2.1 The mathematical core

[definition] Let `I` be a category of apertures (charts, levels, cuts). The **face functor** is
`X : I^op → C`; an arrow `f : i → j` in `I` (chart `i` is coarser than, or contained in, chart `j`)
gives the restriction `X(f) : X(j) → X(i)`. When `I` is cofiltered the pair `(I, X)` is a
**pro-object** of `C`, and its limit `lim X` — when `C` has it — is the type of **compatible
sections**: families `(x_i)_i` with `X(f)(x_j) = x_i` for every `f`. The object of the thesis is the
pro-object, **not** its limit: the limit is one receiver face of it, and can be empty, a point, or
plural while the pro-object remains fully meaningful.

[definition] The remaining components are enrichments of this core: `G` is a path category on the
generator graph (its morphisms are the ordered words of `TransportWord.lean:25`); `R` is a family
of receivers `ρ_r : X(i) → Y_r` indexed with their charts; `P` is a family of presentations with
declared decoders (`Compression` at `Receiver.lean:90`); `L` is lineage, realized as the pullback
occurrence population of `Lineage.lean:65`; `W` is a cost enrichment, i.e. each passage carries a
cost in an ordered monoid so that `G` becomes a cost-enriched (Lawvere-style) category, with
`ReceiverCodeCost.serial_boundary_balance` as the one-boundary additivity law.

[definition] The **locality axis** (sheaf-like) is a second index structure: a site of covers on
each chart, with the gluing condition “agree on overlaps ⇒ glue uniquely”. It is distinct from the
**refinement axis** (the preorder of levels). A tower may satisfy neither, one, or both. The
sequential carrier below formalizes only the refinement axis; the locality axis is named as a next
object in §9 and is not claimed.

### 2.2 The Lean-shaped carrier, checked

[proved-derived; formal-checked] The following file was elaborated in this session with
`lake env lean` from `formal/elementary-holonics` (Lean `v4.33.0`, vendored Mathlib `v4.33.0`,
imports resolved against the built library). Zero errors, zero warnings after the final pass. The
`#print axioms` receipts are: `Tower.gluingResult_total` — `propext, Classical.choice, Quot.sound`;
`padicTower_plural` — `propext, Classical.choice, Quot.sound`; `shiftTower_obstructed` —
`propext, Quot.sound`; `theOrderFaceDoesNotDetermineTheModule` — `propext, Classical.choice,
Quot.sound`. No `sorryAx`. **The file is not a repository owner**; depositing it is object 1 of §9.

```lean
import ElementaryHolonics.Foundation.Receiver
import ElementaryHolonics.Millennium.HolonicDirectedPassage
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms

/-! Scratch probe for the Continuing Object record (2026-09-17). Not a repository owner. -/

namespace Soma.Holonics.ContinuingObjectProbe

universe u v

/-- A tower: faces over a preordered index with lawful restriction. -/
structure Tower (Index : Type u) [Preorder Index] where
  Face : Index → Type v
  restrict : ∀ {i j : Index}, i ≤ j → Face j → Face i
  restrict_refl : ∀ (i : Index) (x : Face i), restrict (le_refl i) x = x
  restrict_trans : ∀ {i j k : Index} (hij : i ≤ j) (hjk : j ≤ k) (x : Face k),
    restrict hij (restrict hjk x) = restrict (le_trans hij hjk) x

namespace Tower

variable {Index : Type u} [Preorder Index] (T : Tower.{u, v} Index)

/-- A compatible section: one witness at every index, agreeing under restriction. -/
structure CompatibleSection where
  witness : ∀ i, T.Face i
  compatible : ∀ {i j : Index} (h : i ≤ j), T.restrict h (witness j) = witness i

/-- The observation fibre: sections that restrict to an actually materialized face. -/
def ObservationFibre (i : Index) (face : T.Face i) : Type _ :=
  { s : T.CompatibleSection // s.witness i = face }

/-- The gluing trichotomy. -/
inductive GluingResult : Prop
  | unique (h : Nonempty T.CompatibleSection) (hs : Subsingleton T.CompatibleSection)
  | plural (h : Nonempty T.CompatibleSection) (hp : ¬ Subsingleton T.CompatibleSection)
  | obstructed (h : IsEmpty T.CompatibleSection)

/-- Every tower lands in one arm. -/
theorem gluingResult_total : T.GluingResult := by
  classical
  by_cases h : Nonempty T.CompatibleSection
  · by_cases hs : Subsingleton T.CompatibleSection
    · exact .unique h hs
    · exact .plural h hs
  · exact .obstructed (not_nonempty_iff.mp h)

/-- A materialized face carries its chart and the lineage of sections behind it. -/
structure MaterializedFace where
  chart : Index
  face : T.Face chart
  lineage : T.ObservationFibre chart face

end Tower

/-- Computable tower: a state, a materialization per chart, compatibility, and a cost. -/
structure ComputableTower (Index : Type u) [Preorder Index] extends Tower.{u, v} Index where
  State : Type u
  materialize : State → ∀ i, Face i
  materialize_compatible : ∀ (s : State) {i j : Index} (h : i ≤ j),
    restrict h (materialize s j) = materialize s i
  cost : State → Index → ℕ

/-- A computable tower supplies a compatible section for every state. -/
def ComputableTower.section {Index : Type u} [Preorder Index]
    (C : ComputableTower.{u, v} Index) (s : C.State) : C.toTower.CompatibleSection where
  witness := C.materialize s
  compatible := fun h => C.materialize_compatible s h

/-! ## The canonical toy instance: `ℤ/p^n` with the p-adic integers as global sections. -/

section Padic

variable (p : ℕ) [Fact p.Prime]

/-- The `ℤ/p^n` tower under the cast maps. -/
def padicTower : Tower.{0, 0} ℕ where
  Face := fun n => ZMod (p ^ n)
  restrict := fun {m n} h x => ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m)) x
  restrict_refl := by
    intro n x
    simp
  restrict_trans := by
    intro i j k hij hjk x
    show ZMod.castHom (pow_dvd_pow p hij) (ZMod (p ^ i))
        (ZMod.castHom (pow_dvd_pow p hjk) (ZMod (p ^ j)) x) =
      ZMod.castHom (pow_dvd_pow p (le_trans hij hjk)) (ZMod (p ^ i)) x
    rw [← RingHom.comp_apply, ZMod.castHom_comp]

omit [Fact p.Prime] in
/-- Every restriction is surjective: the fibre over every face is inhabited. -/
theorem padicTower_restrict_surjective {m n : ℕ} (h : m ≤ n) :
    Function.Surjective (fun x : ZMod (p ^ n) => (padicTower p).restrict h x) :=
  ZMod.ringHom_surjective _

/-- Every p-adic integer is a compatible section. -/
noncomputable def padicSection (a : ℤ_[p]) : (padicTower p).CompatibleSection where
  witness := fun n => PadicInt.toZModPow n a
  compatible := by
    intro m n h
    have := congrArg (fun f => f a) (PadicInt.zmod_cast_comp_toZModPow (p := p) m n h)
    simpa [padicTower] using this

/-- The tower is plural: `0` and `1` are distinct compatible sections. -/
theorem padicTower_plural : ¬ Subsingleton (padicTower p).CompatibleSection := by
  intro hsub
  have h := Subsingleton.elim (padicSection p 0) (padicSection p 1)
  have h1 : PadicInt.toZModPow (p := p) 1 0 = PadicInt.toZModPow (p := p) 1 1 :=
    congrArg (fun s : (padicTower p).CompatibleSection => s.witness 1) h
  rw [map_zero, map_one] at h1
  have : Nontrivial (ZMod (p ^ 1)) :=
    ZMod.nontrivial_iff.mpr (by simpa using (Fact.out : p.Prime).ne_one)
  exact zero_ne_one h1

theorem padicTower_gluing : (padicTower p).GluingResult :=
  .plural ⟨padicSection p 0⟩ (padicTower_plural p)

end Padic

/-! ## An obstructed tower with every fibre inhabited and no loop (Mittag-Leffler failure). -/

/-- Faces `ℕ` at every depth; restriction adds the depth difference. -/
def shiftTower : Tower.{0, 0} ℕ where
  Face := fun _ => ℕ
  restrict := fun {m n} _ x => x + (n - m)
  restrict_refl := by intro n x; simp
  restrict_trans := by
    intro i j k hij hjk x
    show x + (k - j) + (j - i) = x + (k - i)
    omega

theorem shiftTower_face_nonempty (n : ℕ) : Nonempty (shiftTower.Face n) := ⟨(0 : ℕ)⟩

/-- Read a shift-tower face as the natural number it is. -/
abbrev shiftFaceNat (n : ℕ) (x : shiftTower.Face n) : ℕ := x

/-- No compatible section: the base witness would exceed every natural number. -/
theorem shiftTower_obstructed : IsEmpty shiftTower.CompatibleSection := by
  constructor
  intro s
  have key : ∀ n : ℕ, shiftFaceNat n (s.witness n) + n = shiftFaceNat 0 (s.witness 0) := by
    intro n
    have h := s.compatible (Nat.zero_le n)
    change shiftFaceNat n (s.witness n) + (n - 0) = shiftFaceNat 0 (s.witness 0) at h
    simpa using h
  have := key (shiftFaceNat 0 (s.witness 0) + 1)
  omega

theorem shiftTower_gluing : shiftTower.GluingResult := .obstructed shiftTower_obstructed

/-! ## The loop obstruction is already an owner. -/

example : IsEmpty Soma.Holonics.Millennium.HolonicDirectedPassage.BoolFlipCoherent :=
  Soma.Holonics.Millennium.HolonicDirectedPassage.boolFlipCoherent_isEmpty

/-! ## A codimension-one face need not determine the module: the ℤ-toy of the characteristic
ideal. `ℤ/4` and `ℤ/2 ⊕ ℤ/2` have the same order face and are not isomorphic. -/

theorem theOrderFaceDoesNotDetermineTheModule :
    Nat.card (ZMod 4) = Nat.card (ZMod 2 × ZMod 2) ∧
      IsEmpty (ZMod 4 ≃+ ZMod 2 × ZMod 2) := by
  refine ⟨by simp, ⟨fun e => ?_⟩⟩
  have hz : ∀ x : ZMod 2 × ZMod 2, (2 : ℕ) • x = 0 := by decide
  have h : e ((2 : ℕ) • (1 : ZMod 4)) = e 0 := by
    rw [map_nsmul, hz, map_zero]
  have h' : (2 : ℕ) • (1 : ZMod 4) = 0 := e.injective h
  exact absurd h' (by decide)

end Soma.Holonics.ContinuingObjectProbe

#print axioms Soma.Holonics.ContinuingObjectProbe.Tower.gluingResult_total
#print axioms Soma.Holonics.ContinuingObjectProbe.padicTower_plural
#print axioms Soma.Holonics.ContinuingObjectProbe.shiftTower_obstructed
#print axioms Soma.Holonics.ContinuingObjectProbe.theOrderFaceDoesNotDetermineTheModule
```

### 2.3 What is provable now, and what needs new formalization

[proved-derived; formal-checked] Provable now, and proved above or in the owners:

- The trichotomy `unique | plural | obstructed` is total (`gluingResult_total`). It is a
  classical case split, and that is the point: the object's content is *which arm and why*, not
  the existence of a global choice.
- The **plural arm**: `padicTower` — faces `ℤ/p^n`, restrictions the reductions, every restriction
  surjective (`padicTower_restrict_surjective`), compatible sections supplied by every `a ∈ ℤ_p`
  through `PadicInt.toZModPow` and `PadicInt.zmod_cast_comp_toZModPow`, and at least two of them
  (`padicTower_plural`). This is the canonical `A_n = ℤ/p^nℤ` instance requested; its exact fibre
  splitting is the kernel `p^n ℤ_p` of `PadicInt.toZModPow n` (`Mathlib/NumberTheory/Padics/
  RingHoms.lean:459` `ker_toZModPow`), and its global-section object is `ℤ_p` itself
  (`PadicInt.lift` and `lift_spec`, `RingHoms.lean:658-684`, the universal property of the limit).
- The **obstructed arm without any loop**: `shiftTower` — every fibre inhabited, restriction
  injective but not surjective, no compatible section. This is the Mittag-Leffler failure in its
  smallest form; it shows that obstruction does not require holonomy.
- The **obstructed arm with a loop**: `boolFlipCoherent_isEmpty` at
  `HolonicDirectedPassage.lean:327-330` — bijective local transport, inhabited fibres, no fixed
  section around the reversal loop. This is the exact non-orientability model: local orientations
  exist, transport around the loop returns the reversed one, and the theorem **returns the
  obstruction** instead of forcing a choice.
- The **existence theorem for the sequential surjective case**:
  `SuccessorWitnessSystem.nonempty_coherentSection` at `HolonicDirectedPassage.lean:303-305`.
- The **order-face counterexample** `theOrderFaceDoesNotDetermineTheModule`: the `ℤ`-toy of §3.3.

[open] Needs new formalization (dependency order in §9):

- `Tower` over a general small category `I` rather than a preorder, with the pro-object reading;
  the general finite-fibre existence theorem is already in Mathlib
  (`CategoryTheory.Functor.nonempty_sections_of_finite_cofiltered_system`,
  `Mathlib/CategoryTheory/CofilteredSystem.lean:79`, and `…_inverse_system` at `:111`, with
  `IsMittagLeffler` at `:137`) but is imported by nothing in this repository.
- The locality axis (site, covers, overlap agreement) and its interaction with refinement.
- `ObservationFibre` as the Preimage Fibre of the restriction-to-a-chart receiver, joined to
  `Holon.PreimageFibre` (`Holon.lean:88`) so that the two notions are one owner.
- `ComputableTower.cost` as a genuine enrichment: the present `ℕ` is a placeholder; `W` should be
  the ordered monoid of `ReceiverCodeCost` receipts (bytes, work) with `serial_boundary_balance` as
  its additivity.
- A `Migration` map between towers with different index categories (the operator's “migration”),
  i.e. a functor `I' → I` with a natural transformation of face functors; `Holon.Rebase` is its
  invertible special case at one chart.

[interpretation] A tower with no global compatible section is not a defective object. The
non-orientable case is the clean model: the local data is complete and lawful; the failure is a
theorem about the index geometry (the loop) or the restriction maps (non-surjectivity), and the
theorem is returned as the object's content. `GluingPassage.Obstruction` at `Gluing.lean:59` is
exactly the population the obstructed arm returns. The falsifier is an instance in which the
repository silently selects a section where the trichotomy would return `obstructed`.

---

## 3. The Iwasawa instance

All classical statements in this section are `proved-standard`, cited to Washington, *Introduction
to Cyclotomic Fields* (2nd ed., GTM 83, 1997), chapters 7 (the Iwasawa algebra) and 13
(`ℤ_p`-extensions, the structure theorem, Iwasawa's growth theorem); Mazur–Wiles, *Class fields of
abelian extensions of ℚ*, Invent. Math. 76 (1984); Rubin's appendix to Lang, *Cyclotomic Fields I
and II* (GTM 121, 1990); Kato, *p-adic Hodge theory and values of zeta functions of modular forms*,
Astérisque 295 (2004); Skinner–Urban, *The Iwasawa main conjectures for GL₂*, Invent. Math. 195
(2014); Mazur, *Rational points of abelian varieties with values in towers of number fields*,
Invent. Math. 18 (1972); Ferrero–Washington, Ann. of Math. 109 (1979). None is reproved here; none
is formalized in this repository or in Mathlib beyond the pieces named in §3.7.

### 3.1 The vertical tower is a `Tower`

[proved-standard] Let `K` be a number field, `p` an odd prime, `K_∞/K` a `ℤ_p`-extension:
`Γ = Gal(K_∞/K) ≅ ℤ_p`, with the unique subfields `K_0 = K ⊂ K_1 ⊂ … ⊂ K_n ⊂ …`,
`Gal(K_n/K) = Γ/Γ^{p^n} ≅ ℤ/p^n`. The **Iwasawa algebra** is
`Λ = ℤ_p[[Γ]] = lim_n ℤ_p[Γ/Γ^{p^n}]`, and for a topological generator `γ` the map `T ↦ γ − 1`
gives `Λ ≅ ℤ_p[[T]]` (Washington, ch. 7). Writing `ω_n = (1+T)^{p^n} − 1`, the level-`n`
group ring is `Λ/(ω_n) ≅ ℤ_p[Γ/Γ^{p^n}]`.

[definition] As an instance of §2.2: `Index = ℕ`, `Face n = ℤ_p[Γ/Γ^{p^n}] = Λ/(ω_n)`, restriction
= the projection `Λ/(ω_m) → Λ/(ω_n)` for `n ≤ m` (surjective), and `lim = Λ`. This is the
**level direction**. `Λ` is in fact a two-parameter limit, `Λ = lim_{n,m} (ℤ/p^m)[Γ/Γ^{p^n}]`,
with a second, **coefficient direction** `m` (the `p`-adic filtration). The probe's `padicTower`
is that coefficient direction at level `n = 0`: `(ℤ/p^m)[Γ/Γ^{1}] = ℤ/p^m`, with limit
`ℤ_p = Λ/(T)`, the residue of `Λ` at the trivial character. (It is **not** the `ω_n`-face:
`ω_n = (1+T)^{p^n} − 1 ∈ (T)`, so `Λ/(T, ω_n) = ℤ_p` for every `n`.) The probe is therefore the
trivial-character shadow of the Iwasawa tower along its coefficient axis; the level axis is the
one that carries the `Γ`-action and is the subject of the rest of this section.

[proved-standard] For a `Λ`-module `M` the **level-`n` face** is `M/ω_n M` (or the `Γ^{p^n}`-
coinvariants). For the arithmetic modules of interest the actual level objects (class groups
`A_n`, Selmer groups `Sel(E/K_n)`) and the faces `X_∞/ω_n X_∞` agree up to a **bounded defect**:
Mazur's control theorem (Mazur 1972; for good ordinary reduction) states that the restriction
`Sel_{p^∞}(E/K_n) → Sel_{p^∞}(E/K_∞)^{Γ^{p^n}}` has finite kernel and cokernel bounded
independently of `n`. In the carrier: the restriction axis holds **up to a certified residual**,
which is the `SectionResidual` pattern rather than exact compatibility.

### 3.2 The characteristic ideal is a codimension-one receiver face

[proved-standard] Structure theorem (Serre; Washington ch. 13): for a finitely generated
`Λ`-module `M` there is a `Λ`-homomorphism with finite kernel and cokernel (a
**pseudo-isomorphism**, `M ∼ M'`)

```text
M  ∼  Λ^r  ⊕  ⊕_i Λ/(p^{μ_i})  ⊕  ⊕_j Λ/(f_j^{m_j}),
```

with `f_j` distinguished polynomials (Weierstrass preparation in `ℤ_p[[T]]`). For torsion `M`
(`r = 0`) the **characteristic ideal** is `char_Λ(M) = (p^{Σμ_i} ∏_j f_j^{m_j})`, `μ = Σ μ_i`,
`λ = Σ_j m_j deg f_j`.

[interpretation] `char_Λ(M)` is a **receiver**: a map from `Λ`-modules to principal ideals of a
two-dimensional regular local ring, blind to everything of codimension `≥ 2` (finite modules are
**pseudo-null**, and pseudo-null modules have characteristic ideal `Λ`). It is the codimension-one
face of `M`. The receiver's preimage fibre is plural, and the following are its exact witnesses:

[counterexample] (a) `Λ/(T²)` and `Λ/(T) ⊕ Λ/(T)` both have `char = (T²)`; they are not isomorphic
(the annihilators are `(T²)` and `(T)`), and they are not pseudo-isomorphic either: the
elementary divisors `(T²)` versus `(T), (T)` differ, and the structure theorem's decomposition is
unique up to pseudo-isomorphism.
(b) `Λ/(T)` and `Λ/(T) ⊕ Λ/(p, T)` both have `char = (T)`; the second has a nonzero finite
submodule and the first does not; they are pseudo-isomorphic and not isomorphic.
(c) `Λ/(p, T)` itself is finite, nonzero, and has `char = Λ`: the receiver returns the unit face.
The `ℤ`-toy of (a) — same cardinality face, non-isomorphic modules — is
`theOrderFaceDoesNotDetermineTheModule` (§2.2, kernel-checked). So: **`char_Λ` does not determine
`M`**; a `CharacteristicFace` owner must carry this counterexample beside its definition.

[proved-standard] Iwasawa's growth theorem: if `p^{e_n}` is the exact power of `p` dividing the
class number of `K_n`, then for `n` large `e_n = μ p^n + λ n + ν` with `μ, λ ≥ 0` and `ν` integers
determined by `X_∞ = lim A_n` (Washington ch. 13). `μ` and `λ` are the **scaling exponents** of
the tower in exactly the BSD record's sense. They are growth invariants of a codimension-one face;
they are **not** an entropy (no measure, no receiver-relative code length, no `H_R(μ_B)` in the
sense of the code-cost record is involved), and calling them one would violate
[the code-cost record's](2026-09-11_RELATIVE_CODE_COST_HAS_AN_ADDRESSED_BOUNDARY_LAW.md) definition
of entropy as belonging to a receiver and a declared measure.

### 3.3 The main conjecture is receiver-exactness, not source identity

[proved-standard] The **main conjecture** in its classical (cyclotomic, abelian over `ℚ`) form —
Mazur–Wiles 1984, with Rubin's Euler-system proof in Lang's GTM 121 — states, for the relevant
eigenspaces, `char_Λ(X_∞) = (L_p)`, where `X_∞` is the Galois group of the maximal abelian
pro-`p` extension unramified outside `p` (or the projective limit of `p`-class groups) and `L_p`
is the Kubota–Leopoldt `p`-adic `L`-function as a power series. For elliptic curves with good
ordinary reduction at `p`, `char_Λ(Sel_{p^∞}(E/ℚ_∞)^∨) = (L_p(E))` is Kato's divisibility
(`⊇`, Astérisque 295, 2004) together with Skinner–Urban's (`⊆`, Invent. Math. 2014) under their
stated hypotheses (`p ≥ 3`, good ordinary reduction, irreducible residual representation, and a
ramification condition on an auxiliary prime). Those hypotheses are part of the claim and are not
removed here (`conditional` for any instance outside them).

[interpretation] In the carrier: the left side is an **arithmetic/Galois/cohomological
population** (a `Λ`-module built from Selmer or class groups along the tower); the right side is
an **analytic interpolation object** (a power series whose specializations at characters of `Γ`
are special values). The main conjecture asserts they **agree at one declared receiver**
(`char_Λ`), a codimension-one face. It does **not** assert that `X_∞` and `Λ/(L_p)` are the same
module (§3.2(a)–(c) show that the receiver cannot see that), and it does not identify their
sources. This is precisely the `Compression.exact` shape: a shared receiver face, with the
preimage fibre plural on both sides. The BSD record's phrase “receiver-exactness along the tower”
is exact at this receiver and should not be read at any finer one.

### 3.4 The two axes are independent

[definition] **Horizontal** (a family): a base `B` and an object `E_b` over each `b ∈ B`, all over
one field. `FamilyFace.lean:46` is exactly this — `E n := y² = x³ − n²x` over `ℚ`, `n` the
parameter; its theorems (`:462`, `:500`) are statements uniform in `n`. Changing `n` changes the
**object**; the arithmetic environment (`ℚ`, its places) is fixed. Nothing acts by `Γ`.
**Vertical** (a tower): one object `E` and a refining family of environments `K_0 ⊂ K_1 ⊂ …`;
the object is fixed; the level index carries a `Γ`-action and produces a `Λ`-module. `FamilyFace`
is horizontal; the repository has no vertical tower (§1, source-audit). A quadratic-twist family
`{E_n}` is not a `ℤ_p`-extension, and a theorem uniform in the twist parameter says nothing about
`μ` or `λ`. The two axes compose into a two-parameter object (twists of `E` over each `K_n`), and
that composition is where Iwasawa theory of families (Hida/Coleman variation) lives; it is named
here and not claimed.

### 3.5 Where the analogy must stop

[proved-standard] Ferrero–Washington: `μ = 0` for the cyclotomic `ℤ_p`-extension of an abelian
number field. The `μ`-invariant of an elliptic curve's Selmer group is conjectured zero in the
good ordinary case and is **not** known in general; `μ` can be positive for non-cyclotomic
`ℤ_p`-extensions (Iwasawa's own examples).

[proved-standard] The zeros of `L_p` are `p`-adic; the Riemann hypothesis concerns complex zeros
of `ζ(s)`. Cyclotomic Iwasawa theory proves nothing about the location of complex zeros, and no
main conjecture implies RH. The BSD record's Arakelov/heat-kernel bridge (`§3b`) is a separate
`interpretation` with its own falsifiers; this record does not strengthen it.

[open] The following are not supplied by the analogy and must be constructed if the Iwasawa
instance is to enter the library: the relative-norm step at `NormRelation.lean:256-261`; Galois
cohomology and local conditions at each level (Mathlib has neither Selmer groups of elliptic
curves nor Galois cohomology); the `Λ`-module structure theorem (not in Mathlib; Weierstrass
preparation for power series over a complete local ring **is** — `Mathlib/RingTheory/PowerSeries/
WeierstrassPreparation.lean`); `p`-adic `L`-functions (not in Mathlib).

### 3.6 The concrete construction path

[definition] In dependency order, each step naming its existing owner and its missing piece:

1. **Abstract compatible tower** — deposit §2.2's `Tower`, `CompatibleSection`,
   `ObservationFibre`, `GluingResult`, `MaterializedFace`, `ComputableTower`; join
   `SuccessorWitnessSystem` (`HolonicDirectedPassage.lean:260`) as the `ℕ`-indexed surjective
   case and `GluingPassage` (`Gluing.lean:32`) as the obstructed arm's population.
2. **Canonical toy** — deposit `padicTower`, `padicSection`, `padicTower_plural`; add the exact
   fibre splitting as a theorem: the fibre of `restrict (n ≤ n+1)` over each face is a coset of
   `ker (ZMod.castHom …)` of cardinality `p` (Mathlib: `ZMod.castHom_surjective` at
   `Mathlib/Data/ZMod/Basic.lean:362`, `PadicInt.ker_toZModPow` at `RingHoms.lean:459`).
3. **Cyclotomic norms** — discharge `TheRelativeOrbitFillsTheCoprimeLevel`
   (`NormRelation.lean:256-261`). The file itself locates the gap at `:60-70`:
   `IsCyclotomicExtension.autEquivPow` (`Mathlib/NumberTheory/Cyclotomic/Gal.lean:77`) needs
   `Irreducible (cyclotomic l K)` over `K = ℚ(ζ_m)`, and Mathlib discharges irreducibility only
   over `ℚ` (`cyclotomic.irreducible_rat`, `Mathlib/RingTheory/Polynomial/Cyclotomic/Roots.lean:190`).
   The missing object is that one irreducibility (linear disjointness of `ℚ(ζ_m)` and `ℚ(ζ_l)`
   for coprime `m, l`). With it, `theHigherUnitDescendsThroughTheEulerFactor` becomes a relative
   norm and the tower's first restriction map is arithmetic.
4. **Levelwise Selmer with restriction/corestriction** — index `SelmerCalculus.selmer`
   (`SelmerCalculus.lean:54`) by level `n` and supply `res_n : Sel(K_n) → Sel(K_{n+1})` and
   `cor_n` in the opposite direction with `cor ∘ res = [K_{n+1} : K_n]`; this needs actual Galois
   cohomology (absent from Mathlib) or an explicit descent-coordinate model extending
   `GeneralSelmer.coordOf` (`GeneralSelmer.lean:35`) to `K_n`. The direct limit of the `res_n`
   is the `Λ`-module's Pontryagin dual's source.
5. **The Iwasawa action** — `T = γ − 1` on `lim`; `Λ ≅ ℤ_p[[T]]` via Mathlib `PowerSeries` and
   `WeierstrassPreparation`; `ω_n`, the level faces `M/ω_n M`, and the control-theorem residual as
   a `SectionResidual`-shaped statement with a bounded kernel/cokernel field.
6. **`CharacteristicFace`** — define `char_Λ` for finitely generated torsion `Λ`-modules
   **conditionally** on the structure theorem (state the theorem as a `Prop`, as `NormRelation`
   does for its orbit step) and deposit §3.2's counterexamples (a)–(c) as theorems that do not
   depend on it: `Λ/(T²) ≄ Λ/(T) ⊕ Λ/(T)` is provable now from annihilators; `Λ/(p,T)` finite is
   provable now.
7. **The main conjecture as an exact open boundary** — a `Prop` over declared carriers
   (`X_∞ : Λ-module`, `L_p : Λ`, `char_Λ X_∞ = (L_p)`), which is D5 of the BSD record, with its
   hypotheses (§3.3) as explicit fields and no theorem asserting it.

---

## 4. The embedding object: placement in a receiver atlas

### 4.1 Embedding is not projection into one `ℝ^n`

[project-postulate] “Embedding” means **placement in a receiver atlas**: a family of local charts
with transition maps on overlaps, each chart a receiver of the exact object, none of them the
object. This is standing doctrine, not a new rule:
[00_PURE_HOLONICS](../../docs/canon/00_PURE_HOLONICS.md) item 7 (“No privileged chart … A chart
earns use by the passages it makes exact or efficient”); [HNN_FORMULA](../../docs/HNN_FORMULA.md)
“One object, its charts and its recursive geometry” (“An embedding into a displayed 3D scene is a
receiver of these relations”); [TABLET_THE_CHART §10](../../docs/canon/TABLET_THE_CHART.md)
(“A coordinate system is a receiver, and the Jacobian is the transport”, quoting
`crates/relational-geometry/src/model.rs:38`: “The chart is not an ambient coordinate system … A
receiver can compare it with another chart only through declared frame relations”);
[04_GEOMETRY_NAVIGATION_AND_WEAVE](../../docs/canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md)
“Charts are instruments of motion” (GPS: “no single coordinate face is the terrain”).

[definition] Lean-shaped (type sketch; **not elaborated** in this session):

```lean
structure LocalChart (X : Type u) where
  Region     : Set X                       -- where this chart reads
  Coordinate : Type v                      -- the face type of this receiver
  place      : Region → Coordinate         -- the receiver on its domain
  fibre      : Coordinate → Set X          -- the retained preimage, never dropped
  fibre_exact : ∀ x : Region, x.1 ∈ fibre (place x)
  metric     : Option (Capability Coordinate)   -- present only when constituted (§8)

structure Transition {X} (A B : LocalChart X) where
  overlap : Set X                                 -- A.Region ∩ B.Region
  map     : ∀ x ∈ overlap, B.Coordinate           -- computed from A's face and the fibre
  natural : ∀ x (h : x ∈ overlap), map x h = B.place ⟨x, _⟩

structure ReceiverAtlas (X : Type u) where
  Chart       : Type w
  chart       : Chart → LocalChart X
  transition  : ∀ a b, Option (Transition (chart a) (chart b))   -- None = undiscovered
  cost        : Chart → Chart → Option ℕ                          -- of the transition, if known
```

[established-bounded; source-inspected] Each of the following is one chart of this atlas, and the
repository already owns the receiver for it: a 3D display (`relational-geometry::LocalChart`, an
exact `BigRational` frame); an auditory response (the acoustic receivers of the Holonic Encoding
record and `HolonicRecurrentEcology.FirstArrival` at `HNN_FORMULA.md` “first-arrival
populations”); a proof-state graph (`Lean` itself, kept exterior by AGENTS.md); a `p`-adic
coordinate (`Foundation/PrimeValuationRadixAtlas.lean:1-20`: “A numeral is a receiver face of a
finite causal population. Changing the radix changes that face, but it does not authorize rounding
the population”); a spectral embedding (the RH/zeta owners and `ReceiverCodeCost.perronTransition`
at `:28`). The exact object stays behind all of them.

### 4.2 The transition and migration owners already present

[proved-derived; formal-checked] The existing rebase machinery **is** the transition law at the
occurrence grain and at the algorithm grain:

- `Holon.Rebase` (`Holon.lean:95-110`): an equivalence of complete diagrams — occurrences,
  sources, targets, faces — with three natural squares; `Rebase.preimageFibreEquiv` (`:112-125`)
  transports the whole preimage fibre. A transition that moved only the displayed face would not
  be a `Rebase`.
- `ReceiverPotential.outcomes_rebase` (`:115-127`) and `historyOutcomes_rebase` (`:211-228`):
  recharting observation, future receiver **and** every generator transports the compatible
  future family exactly, through every ordered history.
- `SituatedAlgorithm.rebase` / `semantics_rebase_iff` (`Algorithm/Rebase.lean:15-56`): an
  invertible state chart conjugates the computation and preserves its semantics — the
  `ComputableTower` transition.
- `HolonicConstitutiveRechart.PhaseGauge` (`Computation/HolonicConstitutiveRechart.lean:25-28`):
  a fixed-node phase rechart with held fields travelling together.

[open] None of these is a **non-invertible** chart map. The atlas needs one: a transition defined
only on the overlap, with a residual (§7 (b)) where the source chart forgot a distinction the
target chart reads. `ReceiverTransformer` (`Receiver.lean:123-127`) is the functional case on the
presented range; `ReceiverInsufficiency` (`:163-168`) is the witness that no such transition
exists. The typed `Transition` above must carry `Option` at exactly that point.

### 4.3 The navigation law and the path closure

[project-postulate] AGENTS.md's September 13 correction: “a scalar priority queue or scan over
candidates is not the general Holonics navigation law … Preserve the source and relevant
sign/phase, branch, momentum and preimage information before any magnitude or extremum receiver.”
The [navigation record](2026-09-13_ORIENTED_CONFIGURATION_NAVIGATION_RETAINS_ITS_SOURCE_AND_THE_BEACON_STAYS_OPEN.md)
demoted `group_navigation` (Dijkstra on a static finite group) to example support for exactly this
reason.

[definition] In the atlas the navigation object is the **generator network**
`G = (Chart, gen : Chart → Chart → Set Passage, admissible, compose, cost, residual, discovered,
failed, cache)`. Every pairwise route lives in the **path closure** of `G` — the free category on
the generator graph modulo the declared composition rules — realized as ordered words
(`transportWord`, `TransportWord.lean:25`). What is **stored** is `|gen|` local generators plus a
cache of composite routes, not `O(n²)` pairwise edges; what is **available** is every pairwise
traversal, because `generatorEquivarianceExtendsToEveryTransportWord` (`:40-47`) pays the whole
word family by the local law. A cached composite is lawful only while its constituent passages
remain admissible: the cache is a **quotient of the route family**, and by
`ReceiverHistoryCompression.separatingSuccessorReopensTheProposedQuotient` (`:109-116`) one newly
discovered passage that separates two cached routes reopens the cache.

[proved-derived; formal-checked] The optimality certificate is already formal:
`descendingWord_is_optimal` (`TransportWord.lean:100-116`) proves that a potential with a unit
edge bound and a strictly descending policy returns a shortest word to the declared goal. It is a
**certificate, not a search**, and `:53` says so (“not an assumption that computing the potential
is cheap”).

[interpretation] The operator's framing — a distribution-network / active-cartography problem on
an **undiscovered** map, where optimal paths change during discovery — is the
[circulating cartographer tablet §1](../../docs/canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md):
“passage → difference → return → changed morphology → changed continuation … An obstruction is
part of the map, not a failed attempt to manufacture a forced continuation.” In the carrier:
`discovered` and `failed` are fields of `G`, not side effects; a `failed` passage is a returned
obstruction (`GluingPassage.Obstruction`) with its own lineage; the potential of
`descendingWord_is_optimal` is **not** available on an undiscovered map, so the certified-optimal
regime is the *closed* special case and the general law is a lineage-carrying discovery whose
routes are provisional quotients. The first derivation target is a theorem of the form: *adding
one admissible generator to `G` changes the optimal word between two charts only if the new
generator lies on some shortest word* (monotonicity of discovery), with the failing case being a
newly discovered **failure** (which can lengthen routes). The falsifier is a network in which a
cached composite remains cheapest after one of its constituents is marked failed.

---

## 5. Bridges as first-class objects

[project-postulate] AGENTS.md: “Co-presence is not contact. Contact has a declared interaction;
equal receiver output is not source equality.” “Everything is connectable” is true only as a typed
discipline, in which the **kind** of connection is data and the weakest kinds carry no map.

[definition] The bridge kinds, in strictly increasing strength, each with what it owes:

| kind | data owed | what it does not assert |
|---|---|---|
| `coPresence` | one aperture in which both occur | any map, any equality |
| `numericalResemblance` | two receivers into a common numeric face, a tolerance, the aperture | that the receivers read the same structure |
| `sharedReceiverFace` | one receiver `ρ` with `ρ(a) = ρ(b)` (`Compression.exact` shape) | source identity (`equal_face_does_not_force_occurrence_identity`) |
| `map` | `f : A → B`, its domain, its residual | preservation of any structure |
| `structurePreservingMap` | `f` plus the preserved diagram (e.g. the commuting square of `BoundaryScalePassage.boundary_natural`) | invertibility |
| `equivalence` | `A ≃ B` with natural squares (`Holon.Rebase`, `PassageEquiv`) | naturality in a parameter |
| `naturalFamily` | an indexed family of maps commuting with restriction (`ReceiverHistoryCompression.generatorExact` over all generators; a natural transformation of face functors) | that the family is exhaustive |
| `speculativeAnalogy` | candidate map, required hypotheses, supporting receivers, counterexamples | any of the above |

[definition] Lean-shaped (type sketch; **not elaborated**):

```lean
inductive EpistemicGrade
  | definition | projectPostulate | provedStandard | provedDerived | establishedBounded
  | conditional | interpretation | conjecture | counterexample | open_ | historical

inductive BridgeKind
  | coPresence | numericalResemblance | sharedReceiverFace | map
  | structurePreservingMap | equivalence | naturalFamily | speculativeAnalogy

structure Bridge (A : Type u) (B : Type v) where
  kind         : BridgeKind
  Domain       : Set A                          -- where the bridge is defined at all
  map          : Option (Domain → B)            -- None for coPresence / numericalResemblance
  Preserved    : Type w                         -- the diagram/structure claimed preserved
  preserves    : Preserved → Prop
  residual     : A → Prop                       -- where the bridge is known to fail
  sourceStatus : EpistemicGrade                 -- exactly one, per EPISTEMIC_GRADES.md

structure ProposedBridge (A : Type u) (B : Type v) where
  candidate          : Bridge A B
  requiredHypotheses : List Prop
  supportingReceivers: List (Σ F : Type w, (A → F) × (B → F))
  counterexamples    : List (A × B)
  falsifier          : Prop                      -- the test that can fire (EPISTEMIC_GRADES)
```

[established-bounded; source-inspected] `sourceStatus` is bound to
[EPISTEMIC_GRADES](../../docs/canon/EPISTEMIC_GRADES.md): an `interpretation` **must** carry
“explicit maps, limits, preserved diagram, first derivation target, and a falsifier that can fire;
never an identity without proof”, which is exactly `ProposedBridge`; a `proved-derived` bridge must
be a `structurePreservingMap` or stronger with its diagram discharged. The
[correspondence atlas](../../docs/canon/THE_CORRESPONDENCE_ATLAS.md) card form
(`SOURCE ESTABLISHES / LAB CLAIM / RELATION / NON-EQUIVALENCE / TESTABLE CONSEQUENCE`) with
`RELATION ∈ {EXACT, DIRECT CORRESPONDENCE, STRUCTURAL, OPEN, CONTRADICTION}` is the prose form of
the same discipline; `NON-EQUIVALENCE` is `residual`, `TESTABLE CONSEQUENCE` is `falsifier`.

[established-bounded; source-inspected] Existing formal bridges, typed: `Compression`
(`Receiver.lean:90`) is `sharedReceiverFace` promoted to `naturalFamily` by
`ReceiverHistoryCompression`; `BoundaryScalePassage` is `structurePreservingMap`;
`Holon.Rebase`, `PassageEquiv`, `SituatedAlgorithm.rebase` are `equivalence`;
`ReceiverTransformer` is `map` on the presented domain; `ReceiverInsufficiency` is the
`counterexamples` field of a refused bridge. The Iwasawa reading of §3 is a `ProposedBridge` of
kind `structurePreservingMap` whose `Preserved` is the trichotomy and the char-ideal receiver, with
`requiredHypotheses` = §3.6 steps 3–5 and `counterexamples` = §3.2 (a)–(c) against any stronger
kind.

---

## 6. Compression and cost

[definition] Three kinds of compression of one continuing object, distinguished by what is
stored and what is owed:

| kind | stores | owes | owner |
|---|---|---|---|
| **extensional samples** | materialized faces `x_i ∈ X(i)` at chosen charts | the fibre behind each face; no law | `MaterializedFace` with `lineage`; `Presented` (`Presentation.lean:63`) |
| **intensional generator** | a state and a materialization law (`ComputableTower`) | decoder work per face; the generator's domain and residual | `ofEvolution_receive_eq_encoded` (`Holon.lean:75`); the compression tablet §4 (`π` as a compact generator, `conditional`) |
| **tower storage** | a quotient `q` with `q ∘ T_g = U_g ∘ q` for every admitted generator | exactness for the declared future receiver family; a reopening on any separator | `ReceiverHistoryCompression` (`:33-45`, `:87-96`, `:109-116`) |

[definition] The objective for a presentation `P` at receiver family `q`:

```text
C(P; q) = α·bytes(P) + β·decodeWork(P; q) + γ·updateWork(P) + δ·certificateWork(P; q) + η·residual(P; q).
```

`bytes` is code length under the declared codec (`ReceiverCodeCost.perron_edge_code_balance`,
`:45-54`, is one exact code-length law); `decodeWork` is the cost of materializing a requested face;
`updateWork` the cost of incorporating an admitted difference (the roadmap's fourth responsibility);
`certificateWork` the cost of the receipt that `P` is exact for `q` (the separating-word search of
`receiver_exact_compression.rs`, per the compression tablet §2); `residual` the retained
receiver-relative remainder (`SectionResidual.remainder`, `ReceiverPotential.bounded_outcomes_transport`).

[proved-standard] Kolmogorov complexity `K` is uncomputable, and (Chaitin 1974) no sound effective
theory proves `K(x) > c` beyond a constant `c`. Levin's `Kt(x) = min_p {|p| + log₂ t(p)}` is
computable, with an additive invariance theorem, but `log t` is a **declaration** (the
[compression record §5](2026-08-14_COMPRESSION_IS_A_CODEC_PIVOT_THE_INVARIANCE_IS_ADDITIVE_AND_NOTHING_PRICES_BOTH_AXES.md)
and the tablet §5 say so). Therefore:

[project-postulate] The target is never one minimal encoding. It is the **receiver-relative Pareto
frontier** of presentations in the five coordinates above, at the declared `q`, with the weights
`α…η` explicit receiver declarations exactly as Levin's `log t` is one. A claim “this is the
compressed form of `H`” owes the point on the frontier and the `q` it is exact for. The existing
`feasible_cost_le_transported` (`ReceiverCodeCost.lean:156-173`) is the law that a frontier point
survives an exact rebase of the candidate set; it does not select the point.

[proved-standard] A finite prefix `a_0, …, a_N` does not determine a generating law: for any
proposed `a_{N+1}` there is a polynomial of degree at most `N+1` through all `N+2` values
(Lagrange), so the fibre of laws over the prefix is infinite, and every finite prefix is
consistent with every continuation. [THE_INFORMATION_ENGINE](../../docs/canon/THE_INFORMATION_ENGINE.md)
§3 carries the converse `counterexample` (an infinite family with a finite generator).

[project-postulate] Hence a **discovered recurrence** becomes a lawful cache of the prefix only
when it carries: its coefficients; its initial conditions; its domain (which indices, which chart);
its evidence (the prefix, as extensional samples, with lineage); its residual or counterexample
(the first index at which it fails, if known); and the later-term cost (decode work per term). The
`NavigatorInference` owner (`Foundation/NavigatorInference.lean:7-15`) prices exactly this
description/likelihood trade and “supplies no new optimizer”; the tablet's refusal
(“**A compression ratio quoted without its decoder is convicted**”) is the same law at the prose
grain. A recurrence without those fields is a `numericalResemblance` bridge to the prefix, not a
`naturalFamily`.

---

## 7. Four kinds of incompleteness

[project-postulate] The repository's standing claim is that a Preimage Fibre “retains compatible
causes and future conduct from limited observations, possibly implicitly; no perfect inverse,
singleton cause or archive of every raw state is required” (AGENTS.md; TABLET_THE_OPERATIONS §5.4;
TABLET_THE_COMPRESSION §1). That claim is correct and is also too coarse to be a single theorem:
it is four theorems with different owners and different failure modes. (The phrase “intrinsic
incompleteness” does not occur in `docs/` or `research/records/` at `19964c20`; the coarseness is
in usage — one word, “plural”, doing the work of four — not in a single overclaiming sentence.)

### (a) Observational incompleteness — the strongest defensible universal claim

[definition] `Fib_ρ(y) = { x : ρ(x) = y }` — the preimage fibre of one receiver at one presented
face. Owners: `receiverPreimageFibre` (`Receiver.lean:130-132`, domain `Set.range ρ`, so an
unpresented face owes nothing), `Holon.PreimageFibre` (`Holon.lean:88-90`), `PreimageFibre` in
TABLET_THE_OPERATIONS §5.4 (`PF(D_K, R; [y]) = (q_R^* ∘ D_K)^{-1}([y])`).

[proved-derived; formal-checked] The universal statement is exactly: *a receiver face is not the
occurrence* — `equal_face_does_not_force_occurrence_identity` (`Presentation.lean:44-49`). Nothing
stronger is universal. In particular:

[proved-derived; formal-checked] **A fibre with exactly two members is already incomplete.** The
witness is `FaceEq (fun _ : Bool ↦ ()) false true ∧ false ≠ true`: `Fib(()) = Bool`, two members,
and the receiver cannot separate them. Holonic incompleteness does **not** require infinitely
many causal factors. The fibre may be **finite** (`Bool` above), **infinite** (`shiftTower`'s
faces, or the polynomial fibre over a prefix in §6), **implicit** (`SectionResidual`: a particular
solution plus a kernel, `source_reconstructs` at `:28`, with no enumeration), or **empty**
(`ReceiverPotential.lean:96-98`: “Empty source/target fibres remain empty in the same identity”;
THE_RELEVANCE_HYPOTHESIS: “An admissible target whose fibre is still empty or unknown retains
that existence question”). Any prose that says “infinitely many” where it means “more than one”
is an overclaim relative to this owner.

### (b) Representational incompleteness — four sub-cases with four owners

[proved-derived; formal-checked]

| sub-case | statement | owner |
|---|---|---|
| exactly recoverable through a generator | `factor ∘ quotient = receiver`; `section(q x) + remainder = x` | `Compression.exact` (`Receiver.lean:94`); `source_reconstructs` (`SectionResidual.lean:28`) |
| recoverable under assumptions | an explicit factor determines one future face while the source stays plural | `outcomes_singleton_of_factor` (`ReceiverPotential.lean:64-75`) |
| bounded by a residual | Lipschitz transport of a whole-fibre bound; any two compatible faces within `2·tolerance` | `bounded_outcomes_transport` (`:135-147`), `compatible_outcomes_pairwise_bound` (`:163-176`) |
| destroyed by a lossy codec | a returned distinction inside one entering fibre excludes every functional transformer | `ReceiverInsufficiency`, `ReceiverTransformer.excludesInsufficiency` (`Receiver.lean:163-178`) |

The four are not one claim: the first is an equality, the second a conditional, the third an
inequality, the fourth a refutation.

### (c) Consequential non-exhaustion

[proved-derived; formal-checked] A finitely specified object can be inexhaustible in
consequences without any fibre being large: `allSuccessorHistories`
(`ReceiverHistoryCompression.lean:87-96`) is exact for the infinite word family
`Receiver × List Generator` and is paid for by one local law; the docstring states the principle
(“the infinite word family is paid for by the local generator commuting law, not by enumerating
successor histories”). `CausalRelevance.futureCollapsed` (`:59-60`) is the corresponding kernel:
the largest subgroup invisible after **every** finite history.

[proved-standard] The external form is Chaitin's incompleteness (compression tablet §7): a sound
effective theory proves only finitely many statements `K(x) > c`. This is a limit on **what a
finite specification can certify about its own consequences**, distinct from (a) and (b).

### (d) Failure of a global section

[proved-derived; formal-checked] Local data complete and lawful, no compatible global section:
`shiftTower_obstructed` (no loop; Mittag-Leffler failure), `boolFlipCoherent_isEmpty`
(`HolonicDirectedPassage.lean:327-330`; loop holonomy), `GluingPassage.Obstruction`
(`Gluing.lean:59`) as the returned population, and `SelmerCalculus.theReceiverFamilyCanBeBlind`
(`:95-110`) as the receiver-family form (locally admitted everywhere, globally unrealized). This
kind has nothing to do with observation: every fibre may be fully known.

[project-postulate] A claim of “incompleteness” about a Holonic object must name which of (a)–(d)
it asserts and supply that owner's witness. “Intrinsic incompleteness” with no kind named is
refused.

### The `Capability` type, and the over-claim it replaces

[established-bounded; source-inspected] The repository's canon **already** refuses the claim that
geometry confers every structure: [TABLET_THE_MANIFOLD §16](../../docs/canon/TABLET_THE_MANIFOLD.md)
“Every geometry is a reduction of the structure group” (`GL(n)` no structure; `GL⁺(n)` an
orientation; `O(n)` a metric — “lengths and angles are fixed”; `U(n)` a complex structure;
`Sp(2n)` a phase area; `SL(n)` a volume), and [HOLON.md](../../docs/HOLON.md) “A gradient, metric,
mass, distribution, tensor rank or reversible decoder is additional mathematical structure.
Requiring every Holon to contain all of them confuses the general object with a physical chart.”
The over-claim, where it occurs, is in exterior discussion and in loose usage, not in a canon
clause found at `19964c20`. The correction is therefore a **formalization of standing doctrine**:

[definition] Angles need a metric or conformal structure (`O(n)` or `CO(n)` reduction); calculus
needs a smooth structure or a discrete-differential structure (a cochain complex with `d`, as
`GradedCausalComplex` supplies `∂² = 0`); analytic continuation needs analytic data (a germ and a
path; `08_CORE_MATHEMATICAL_INSTRUMENTS` “Analytic continuation transports those fibers; monodromy
records loop return”); fractal dimension needs an identified scaling family (HNN_FORMULA: “fractal
dimension and effective receiver rank are separate quantities”; and §3.2: `μ, λ` are one such
family's exponents, not a dimension). A structure is **constituted** by a witness, and operations
become available when the witness does:

```lean
structure Capability (Carrier : Type u) where
  Parameters : Type v                          -- e.g. a metric tensor, a complex structure J
  admits     : Parameters → Prop               -- the law the parameters must satisfy (J² = −I)
  Operation  : Type w                          -- what becomes available (angle, d, continuation)
  operations : ∀ p, admits p → Operation
  laws       : ∀ p (h : admits p), Prop        -- the identities the operations then obey
```

A `LocalChart` (§4.1) carries `metric : Option (Capability Coordinate)`; a chart with `None` has
placement and incidence and **no angles**. Asking a `Capability`-less chart for an angle is a type
error, not a zero. (Type sketch; not elaborated.)

---

## 8. Where the repository's prose is ahead of its formal content

[established-bounded; source-inspected] Each row names the prose, the formal content actually
present, and the gap. None is a retraction; each is a scope correction.

| prose | formal content | gap |
|---|---|---|
| BSD record `:109-116`: “the main conjecture … is receiver-exactness along the tower: the `p`-adic `L`-reading generates exactly the characteristic ideal of the Selmer growth”; deed D5 at `:126` | nothing vertical exists (source-audit §1); `NormRelation` explicitly stops short of a relative norm (`:57-58`) | “Selmer growth” names a `Λ`-module and its growth exponents in one phrase; the receiver is `char_Λ` and it is blind in codimension `≥ 2` (§3.2). D5 is unreturned. The reading is correctly graded `interpretation` there; this record supplies its `ProposedBridge` fields. |
| `MILLENNIUM_FORMAL_CATALOG.md:317`: “general finite cofiltered systems reuse Mathlib's existing section theorem” | no repository file imports `nonempty_sections_of_finite_cofiltered_system` or `IsMittagLeffler` (source-audit §2.3) | “reuse” is prospective; the sequential theorem at `HolonicDirectedPassage.lean:303` is the only tower existence theorem in the library. |
| `HOLON.md` rows “Encode/reopen” and “Compression/refinement” list `Ê_next T = U Ê`, `D E = ρ` with existing owners “Kernel-mode factorization, receiver descent and boundary memory” | the static law is `Compression.exact`; the dynamic law is `ReceiverHistoryCompression.generatorExact`; **no owner carries decoder cost or an exterior presentation** — `ReceiverHistoryCompression.lean:30-31` says so | the table row reads as if decoder and residual were formal at the same grade as the square; the residual is formal only linearly (`SectionResidual`) and the cost only as code length (`ReceiverCodeCost`). |
| the Preimage Fibre clauses (AGENTS.md; tablets) use “plural”, “implicit”, “no singleton cause” as one claim | four distinct owners with four distinct failure modes (§7) | one word carries four theorems; a consumer cannot tell whether a stated incompleteness is (a), (b), (c) or (d). |
| `TABLET_THE_COMPRESSION` §1 (retained verbatim as origin): “compression is gauge-fixing the flat directions and keeping the curvature” | `ReceiverHistoryCompression` and `CausalRelevance.futureCollapsed` (the collapsed kernel is the “flat directions” only in the additive case) | the geometric phrasing is `interpretation` and is marked as Brandon's origin hypothesis; its formal content is the additive kernel, and nothing curved. |
| `docs/canon/04_GEOMETRY_NAVIGATION_AND_WEAVE.md` “Charts are instruments of motion … Transition maps and their lineage are part of the journey” | every formal chart map is invertible (`Holon.Rebase`, `SituatedAlgorithm.rebase`, `outcomes_rebase`) | the atlas of §4 needs non-invertible transitions with residuals; none is formal. |
| `FamilyFace.lean:5-9` docstring: “the descent face is a homomorphism on every twist at once” | true, on the horizontal family | no reader should take “every twist at once” as any statement along a field tower; the axes are independent (§3.4). |

---

## 9. Next formal objects, in dependency order

[definition] Each item names its prerequisites, its owner-to-be, and what discharges it.

1. **`Tower`, `CompatibleSection`, `ObservationFibre`, `GluingResult`, `MaterializedFace`,
   `ComputableTower`** — deposit §2.2 as `Foundation/ContinuingTower.lean`; join
   `SuccessorWitnessSystem` (as the `ℕ`-indexed surjective instance with
   `nonempty_coherentSection` giving the `unique | plural` arms) and `GluingPassage.Obstruction`
   (as the obstructed arm's population). Prerequisites: none beyond `Receiver.lean` and
   `HolonicDirectedPassage.lean`.
2. **`padicTower` and its exact fibre splitting** — deposit with a theorem that each restriction
   fibre is a `p`-element coset of `ker (ZMod.castHom …)`, and that `ℤ_p ≃ CompatibleSection`
   (both directions: `padicSection` and `PadicInt.lift`). Prerequisite: 1.
3. **`ObservationFibre = PreimageFibre`** — an `Equiv` between `Tower.ObservationFibre i face` and
   `Holon.PreimageFibre` of the holon whose receiver is “restrict to chart `i`”. Prerequisite: 1.
4. **`Migration`** — a functor of index categories with a natural transformation of face functors;
   `Holon.Rebase` and `outcomes_rebase` as its invertible instances; a `Transition` with `Option`
   and a residual as its non-invertible instance. Prerequisites: 1, 3.
5. **Cost enrichment** — replace `cost : State → Index → ℕ` by an ordered-monoid enrichment with
   `ReceiverCodeCost.serial_boundary_balance` as additivity and a `ParetoPoint` structure
   carrying the five coordinates of §6. Prerequisites: 1; `ReceiverCodeCost.lean`.
6. **`Capability`** and `LocalChart`/`ReceiverAtlas`/`GeneratorNetwork` (§4, §7) — type
   definitions first, then the discovery-monotonicity theorem of §4.3 as the first derivation
   target. Prerequisites: 1, 4, 5.
7. **`Bridge` / `ProposedBridge` / `EpistemicGrade`** (§5) — with the existing owners typed as
   instances; no theorem beyond well-typedness is owed at first. Prerequisites: none formal;
   doctrinal binding to EPISTEMIC_GRADES.
8. **`TheRelativeOrbitFillsTheCoprimeLevel` discharged** — `Irreducible (cyclotomic l ℚ(ζ_m))`
   for coprime `m, l`, then `autEquivPow` at that base. Prerequisite: Mathlib work; independent
   of 1–7.
9. **Levelwise Selmer with `res`/`cor`** — prerequisite 8 for the cyclotomic case, and a Galois-
   cohomology or explicit-coordinate model (§3.6 step 4).
10. **The Iwasawa action and `CharacteristicFace`** — `Λ ≅ ℤ_p[[T]]` via Mathlib `PowerSeries`
    and `WeierstrassPreparation`; `ω_n`; `M/ω_n M` as the level face; the structure theorem as a
    named `Prop`; counterexamples (a)–(c) of §3.2 as unconditional theorems. Prerequisites: 1, 2.
11. **The main conjecture as an open `Prop`** — the BSD record's D5, over the carriers of 10, with
    its hypotheses as fields. Prerequisites: 9, 10.

---

## 10. Boundaries

No claim of movement on the Birch–Swinnerton-Dyer conjecture, any Iwasawa main conjecture, or the
Riemann hypothesis. Every classical statement is imported with its primary source and none is
reproved. The scratch probe is kernel-checked and is **not** a repository owner until deposited
under §9 item 1; its receipts are reproducible by writing the quoted file into the scratchpad and
running `lake env lean` from `formal/elementary-holonics`. The `LocalChart`, `Transition`,
`ReceiverAtlas`, `Bridge`, `ProposedBridge`, `EpistemicGrade` and `Capability` declarations are
type sketches marked as not elaborated. Absence claims are measured by the stated `grep`
apertures over `formal/elementary-holonics/ElementaryHolonics`, `docs/` and `research/records/`
at `19964c20`, excluding `.lake/`. The roadmap and construction state are unchanged, and nothing
here is committed.
