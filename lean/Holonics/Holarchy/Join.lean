import Holonics.Holon.Law
import Holonics.Foundation.ContinuingTower
import Holonics.Objects.Pairing
import Holonics.Aeon.Clock.Lock
import Mathlib.NumberTheory.Real.Irrational

/-!
# Holarchy.Join: `interconnect` returns a Holarchy or a typed gluing defect

[definition] Object 11 of `docs/ELEMENTARY_OBJECTS.md`. A **constituent** (`Constituent`) is a
port Holon together with what the Holon object carries beyond its interconnection and element
relations: its cell complex and oriented interior chain, the unit of each external port, the face
of its complex each external port sits on, its navigators (each with an initial configuration,
whole windings and open phase, and a clock rate: `NavigatorClock`) and the navigator driving each
pump (active port). A **join declaration** (`JoinDeclaration A B`) is typed by the two constituents
and holds only the gluing: the shared-port join law `f_B = −F f_A`, `e_B = E e_A`, the glued
complex with a cellular embedding of each constituent's own complex (`CellEmbedding`: cell to cell
with a unit gauge, grade by grade), and the joint clock rate. A **Holarchy** is what `interconnect`
returns: the declaration of two retained constituents together with the proof that it glues.
Every check reads the constituents' own data, in this order, and a failed check returns a typed
`GluingDefect`:

1. **Ports.** Each shared port carries the same unit in both constituents (`unitMismatch`), and the
   join cancels the interface power, `EᵀF = 1` (`uncancelledPower`).
2. **Cells.** Each embedding commutes with both boundaries (`nonCommutingCells`) and is injective on
   cells of every grade (`degenerateCells`), and the two images cover the glued complex
   (`uncoveredCells`). Each shared port's two faces are identified in the glued complex
   (`unidentifiedSharedFace`); the two images meet only there, on no region and on no other face
   (`strayOverlap`); and each shared face enters the two constituents' oriented boundaries with
   opposite signs, so it is interior to the whole (`sharedFaceUncancelled`).
3. **Pumps.** Every pump's rate, read from its navigator, is a whole multiple of the joint clock
   rate (`incompatibleClocks`).

The whole (`Holarchy.wholeConstituent`) is again a constituent: its port Holon is the port join,
its complex the glued one, its units and port faces those of the unshared ports, its navigators the
two families side by side (provenance by `Sum`), its pumps namespaced likewise. Its parametric
orientation is the lift of the joint clock torus of its navigators (`Holarchy.parametric`,
`Aeon/Clock/Winding.clockLift`), which carries its aeons. Namespace `Holonics.HolarchyCore`.

[proved-derived; formal-checked]

* **The port join.** The interface power is `⟨e, (1 − EᵀF) f⟩` (`interfacePower_eq`), so it
  cancels for every shared bond exactly when `EᵀF = 1` (`interfacePower_cancels_iff`). Under
  that law the gain link is a Dirac relation (`gainLink_isDirac`), so the joined whole is a port
  Holon (`joinHolon`); at `F = E = 1` it is `Holon/Law.PortHolon.interconnect` (`joinHolon_one`).
* **One sign law for ports and faces.** Read on its face, a shared port's flow is the constituent's
  own flux through that face (`faceFlow`). The face-read flows of a shared port satisfy the
  identity join `f_B = −f_A` for every current exactly when the shared face cancels
  (`faceFlows_join_iff`); so in a Holarchy the port join at `F = E = 1` and the face cancellation
  are one law (`Holarchy.sharedPort_face_join`), and the shared face is silent in the whole's
  boundary (`Holarchy.sharedFace_silent`).
* **The whole's balance is the sum of the constituents'.** Every admitted point of a Holarchy's
  whole restricts to admitted points of both constituents through one shared bond, and their
  external powers, shared ports included, sum to the whole's (`Holarchy.power_balance`); storage
  rate, dissipation and active power add (`Holarchy.balance_is_sum`).
* **Cells.** A commuting embedding carries a child's own boundary flux to the glued complex
  (`CellEmbedding.flux_pullback`), its transpose carries exact currents to exact currents
  (`CellEmbedding.restrict_exact`), and the whole's flux is the sum of the constituents' own
  (`Holarchy.whole_flux`). An embedding never has a zero column (`CellEmbedding.m₂_ne_zero`): the
  degenerate zero map of the earlier draft is not a cellular embedding.
* **Pumps.** A pump on the joint clock closes at every joint aeon (`OnJointClock.closes`,
  `Aeon/Clock/Lock.jointReading_isCycle_iff`), and two pumps on one joint clock lock at their
  Farey address (`OnJointClock.lock`, `Aeon/Clock/Lock.lock_at_address`), with the pair contact's
  no-slip reading.
* **`interconnect`.** It returns a Holarchy exactly when the declaration glues the two actual
  constituents (`interconnect_ok_iff`), retaining the declaration (`interconnect_ok_retains`);
  every returned defect refutes the gluing (`GluingDefect.not_glues`). The whole's pumps and
  navigators are the constituents' (`Holarchy.wholeConstituent_pumpRate`).
* **Gluing is unique, plural or obstructed** on the shared bonds realizing one whole bond:
  obstructed exactly when the whole refuses the bond (`interface_obstructed_iff`), plural exactly
  when two shared bonds realize it (`interface_plural_iff`).

[counterexample; formal-checked] Each defect is reached by a declaration that passes every earlier
check (`unitMismatch_witness`, `uncancelledPower_witness`, `nonCommutingCells_witness`,
`degenerateCells_witness`, `uncoveredCells_witness`, `unidentifiedSharedFace_witness`,
`strayOverlap_witness`, `sharedFaceUncancelled_witness`, `incompatibleClocks_witness`); two
constituents sharing a face glue (`base_glues`), and so do two pumped constituents on a common
joint clock (`pumped_glues`), whose pumps lock at `1/2` (`pumped_pumps_lock`). Rates `1` and `√2`
close at no joint aeon (`incommensurate_rates_never_close`). The interface fibre is plural for two
passive coholons (`plural_interface_witness`), obstructed for a wire driven into a passive coholon
(`obstructed_interface_witness`) and unique for two wires in series (`unique_interface_witness`).

[open] The constituent family is binary; a recursively generated family is the iterate (the whole
is again a constituent), not a separate object here. The restriction facet `π` of the Holon object
(scale restrictions) is not carried by `PortHolon` and is not joined here; the child restriction is
the transposed cellular embedding. The port–face law is the identity join; a transformer join
(`F ≠ 1`) is an element on the shared face, whose constitutive law is not formalized.
-/

noncomputable section

namespace Holonics.HolarchyCore

open Matrix
open Holonics.HolonCore
open Holonics.Foundation.ContinuingTower
/-! ## 1. The port join law and the interface power -/

section PortLaw

variable {𝕜 : Type*} [Field 𝕜] {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- [definition] The shared bond seen by the right constituent when the left carries `q`:
`f_B = −F f_A`, `e_B = E e_A`. -/
def joinBond (F E : Matrix τ τ 𝕜) (q : Bond 𝕜 τ) : Bond 𝕜 τ := (-(F *ᵥ q.1), E *ᵥ q.2)

omit [DecidableEq τ] in
/-- [definition] `joinBond` as a linear map. -/
def joinBondLin (F E : Matrix τ τ 𝕜) : Bond 𝕜 τ →ₗ[𝕜] Bond 𝕜 τ :=
  (-Matrix.mulVecLin F).prodMap (Matrix.mulVecLin E)

omit [DecidableEq τ] in
@[simp] theorem joinBondLin_apply (F E : Matrix τ τ 𝕜) (q : Bond 𝕜 τ) :
    joinBondLin F E q = joinBond F E q := rfl

/-- [definition] **The interface power**: the power delivered into the left constituent at the
shared ports plus the power delivered into the right one. -/
def interfacePower (F E : Matrix τ τ 𝕜) (q : Bond 𝕜 τ) : 𝕜 := power q + power (joinBond F E q)

omit [DecidableEq τ] in
theorem mulVec_dot_mulVec (E F : Matrix τ τ 𝕜) (e f : τ → 𝕜) :
    (E *ᵥ e) ⬝ᵥ (F *ᵥ f) = e ⬝ᵥ ((Eᵀ * F) *ᵥ f) := by
  rw [← mulVec_mulVec, dotProduct_comm, transpose_dot]

/-- [proved-derived; formal-checked] The interface power is `⟨e, (1 − EᵀF) f⟩`. -/
theorem interfacePower_eq (F E : Matrix τ τ 𝕜) (q : Bond 𝕜 τ) :
    interfacePower F E q = q.2 ⬝ᵥ ((1 - Eᵀ * F) *ᵥ q.1) := by
  simp only [interfacePower, joinBond, power, dotProduct_neg, mulVec_dot_mulVec, sub_mulVec,
    one_mulVec, dotProduct_sub]
  ring

theorem eq_of_dotProduct_single {u v : τ → 𝕜}
    (h : ∀ j, u ⬝ᵥ Pi.single j 1 = v ⬝ᵥ Pi.single j 1) : u = v := by
  funext j
  simpa [dotProduct_single_one] using h j

/-- [proved-derived; formal-checked] **The join cancels the interface power exactly when
`EᵀF = 1`.** The equal-effort, opposite-flow join `F = E = 1` is one instance; a transformer
`E = F⁻ᵀ` is another. -/
theorem interfacePower_cancels_iff (F E : Matrix τ τ 𝕜) :
    (∀ q, interfacePower F E q = 0) ↔ Eᵀ * F = 1 := by
  constructor
  · intro h
    have hM : (1 - Eᵀ * F) = 0 := by
      ext i j
      have := h (Pi.single j 1, Pi.single i 1)
      rw [interfacePower_eq, mulVec_single_one, single_one_dotProduct] at this
      simpa using this
    exact (sub_eq_zero.mp hM).symm
  · intro h q
    rw [interfacePower_eq, h, sub_self, zero_mulVec, dotProduct_zero]

/-- [proved-derived; formal-checked] An uncancelled join exhibits a shared bond whose interface
power is not zero. -/
theorem exists_interfacePower_ne_zero {F E : Matrix τ τ 𝕜}
    (h : Eᵀ * F ≠ 1) : ∃ q, interfacePower F E q ≠ 0 := by
  by_contra hall
  push Not at hall
  exact h ((interfacePower_cancels_iff F E).mp hall)

/-- [definition] **The gain link**: the graph of `joinBond`, the relation the join imposes on the
two copies of the shared bond. -/
def gainLink (F E : Matrix τ τ 𝕜) : Submodule 𝕜 (Bond 𝕜 τ × Bond 𝕜 τ) :=
  LinearMap.graph (joinBondLin F E)

omit [DecidableEq τ] in
theorem mem_gainLink {F E : Matrix τ τ 𝕜} {x : Bond 𝕜 τ × Bond 𝕜 τ} :
    x ∈ gainLink F E ↔ x.2 = joinBond F E x.1 := LinearMap.mem_graph_iff _ _

/-- [proved-derived; formal-checked] The equal-effort, opposite-flow join is the Dirac link of
`Holon/Dirac`. -/
theorem gainLink_one : gainLink (1 : Matrix τ τ 𝕜) 1 = link 𝕜 τ := by
  ext x
  rw [mem_gainLink]
  simp only [joinBond, one_mulVec, Prod.ext_iff]
  rfl

/-- [proved-derived; formal-checked] **The gain link is a Dirac relation when the join cancels
the interface power.** Isotropy is `EᵀF = 1`; co-isotropy uses `F Eᵀ = 1`, the same law read
from the other side. -/
theorem gainLink_isDirac {F E : Matrix τ τ 𝕜} (h : Eᵀ * F = 1) :
    IsDirac (prodForm (bondForm 𝕜 τ) (bondForm 𝕜 τ)) (gainLink F E) := by
  have hFE : F * Eᵀ = 1 := mul_eq_one_comm.mp h
  have hEF : E * Fᵀ = 1 := by
    have := congrArg Matrix.transpose hFE
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at this
  apply isDirac_of
  · intro x hx y hy
    rw [mem_gainLink] at hx hy
    rw [prodForm_apply, hx, hy]
    simp only [joinBond, bondForm_apply, dotProduct_neg, mulVec_dot_mulVec, h, one_mulVec]
    ring
  · intro y hy
    rw [mem_gainLink]
    have hflow : ∀ f : τ → 𝕜, y.1.2 ⬝ᵥ f = (Fᵀ *ᵥ y.2.2) ⬝ᵥ f := by
      intro f
      have := hy ((f, 0), joinBond F E (f, 0)) (mem_gainLink.mpr rfl)
      simp only [prodForm_apply, bondForm_apply, joinBond, mulVec_zero, zero_dotProduct,
        zero_add, dotProduct_neg] at this
      rw [dotProduct_comm (Fᵀ *ᵥ y.2.2), transpose_dot]
      linear_combination this
    have heff : ∀ e : τ → 𝕜, y.1.1 ⬝ᵥ e = (-(Eᵀ *ᵥ y.2.1)) ⬝ᵥ e := by
      intro e
      have := hy ((0, e), joinBond F E (0, e)) (mem_gainLink.mpr rfl)
      simp only [prodForm_apply, bondForm_apply, joinBond, mulVec_zero, neg_zero,
        dotProduct_zero, add_zero] at this
      rw [neg_dotProduct, dotProduct_comm (Eᵀ *ᵥ y.2.1), transpose_dot, dotProduct_comm y.1.1,
        dotProduct_comm y.2.1]
      linear_combination this
    have h1 : y.1.2 = Fᵀ *ᵥ y.2.2 := eq_of_dotProduct_single fun j => hflow _
    have h2 : y.1.1 = -(Eᵀ *ᵥ y.2.1) := eq_of_dotProduct_single fun j => heff _
    refine Prod.ext ?_ ?_
    · simp only [joinBond, h2, mulVec_neg, neg_neg, mulVec_mulVec, hFE, one_mulVec]
    · simp only [joinBond, h1, mulVec_mulVec, hEF, one_mulVec]

end PortLaw

/-! ## 2. The joined whole of two port Holons -/

section Whole

variable {𝕜 : Type*} [Field 𝕜]
variable {σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ]
  [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ]

/-- [definition] The whole's interconnection structure: both constituents' structures side by
side, joined through the gain link at the shared ports, with the ports merged kind by kind. -/
def joinD (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA) (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB)
    (F E : Matrix τ τ 𝕜) :
    Submodule 𝕜 (Bond 𝕜 (Ports (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB))) :=
  (compose (pairedD (A.D.map (bondReindex (𝕜 := 𝕜) splitA).toLinearMap)
      (B.D.map (bondReindex (𝕜 := 𝕜) splitB).toLinearMap)) (gainLink F E)).map
    (bondReindex (𝕜 := 𝕜) mergeKinds).toLinearMap

/-- [proved-derived; formal-checked] **The joined whole is Dirac** when the join cancels the
interface power. -/
theorem joinD_isDirac (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA) (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB)
    {F E : Matrix τ τ 𝕜} (h : Eᵀ * F = 1) :
    IsDirac (bondForm 𝕜 (Ports (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB))) (joinD A B F E) :=
  (compose_isDirac bondForm_symm
    (fun x y => by rw [prodForm_apply, prodForm_apply, bondForm_symm x.1, bondForm_symm x.2])
    bondForm_separating
    (fun x h => by
      have h1 := bondForm_separating x.1 fun y => by simpa using h (y, 0)
      have h2 := bondForm_separating x.2 fun y => by simpa using h (0, y)
      exact Prod.ext h1 h2)
    (pairedD_isDirac (A.dirac.reindex splitA) (B.dirac.reindex splitB))
    (gainLink_isDirac h)).reindex mergeKinds

/-- [definition] **The joined whole** of two port Holons at their shared ports `τ`, under a
join law that cancels the interface power: block storage and resistance, and the composed
interconnection. -/
def joinHolon (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA) (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB)
    (F E : Matrix τ τ 𝕜) (h : Eᵀ * F = 1) :
    PortHolon 𝕜 (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB) where
  D := joinD A B F E
  dirac := joinD_isDirac A B h
  Q := Matrix.fromBlocks A.Q 0 0 B.Q
  Q_symm := by rw [Matrix.fromBlocks_transpose, A.Q_symm, B.Q_symm]; simp
  R := Matrix.fromBlocks A.R 0 0 B.R

/-- [proved-derived; formal-checked] At the equal-effort, opposite-flow join the whole is
`Holon/Law.PortHolon.interconnect`. -/
theorem joinHolon_one (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA) (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB)
    (h : (1 : Matrix τ τ 𝕜)ᵀ * 1 = 1) : joinHolon A B 1 1 h = A.interconnect B := by
  have hD : joinD A B (1 : Matrix τ τ 𝕜) 1 = (A.interconnect B).D := by
    rw [joinD, gainLink_one]; rfl
  unfold joinHolon
  rw [PortHolon.mk.injEq]
  exact ⟨hD, rfl, rfl⟩

omit [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA] [Fintype σB] [Fintype ρB] [Fintype πB]
  [Fintype αB] [Fintype τ] [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ] in
theorem bondReindex_symm_apply {ι ι' : Type*} (e : ι ≃ ι') (b : Bond 𝕜 ι') :
    (bondReindex (𝕜 := 𝕜) e).symm b = (b.1 ∘ e, b.2 ∘ e) := by
  ext i <;> simp [bondReindex]

omit [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ] in
/-- [proved-derived; formal-checked] Membership in the whole: some shared bond `q` makes the
left side admitted with `q` and the right side admitted with `joinBond F E q`. -/
theorem mem_joinD (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA) (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB)
    (F E : Matrix τ τ 𝕜) (b : Bond 𝕜 (Ports (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB))) :
    b ∈ joinD A B F E ↔ ∃ q : Bond 𝕜 τ,
      (bondReindex splitA).symm (partA ((bondReindex mergeKinds).symm b) q) ∈ A.D ∧
      (bondReindex splitB).symm
        (partB ((bondReindex mergeKinds).symm b) (joinBond F E q)) ∈ B.D := by
  rw [joinD, Submodule.mem_map_equiv, mem_compose]
  constructor
  · rintro ⟨⟨q₁, q₂⟩, hL, hA, hB⟩
    rw [mem_gainLink] at hL
    simp only at hL
    refine ⟨q₁, ?_, ?_⟩
    · exact (Submodule.mem_map_equiv _).mp hA
    · rw [← hL]; exact (Submodule.mem_map_equiv _).mp hB
  · rintro ⟨q, hA, hB⟩
    exact ⟨(q, joinBond F E q), mem_gainLink.mpr rfl, (Submodule.mem_map_equiv _).mpr hA,
      (Submodule.mem_map_equiv _).mpr hB⟩

omit [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA] [Fintype σB] [Fintype ρB] [Fintype πB]
  [Fintype αB] [Fintype τ] [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ] in
/-- [proved-derived; formal-checked] The left constituent's part of an assembled whole bond is the
assembled bond of its own kinds, with the shared bond on its shared ports. -/
theorem leftPart_assemble (fS eS : σA ⊕ σB → 𝕜) (fR eR : ρA ⊕ ρB → 𝕜) (fP eP : πA ⊕ πB → 𝕜)
    (fA eA : αA ⊕ αB → 𝕜) (q : Bond 𝕜 τ) :
    (bondReindex splitA).symm
        (partA ((bondReindex mergeKinds).symm (assemble fS eS fR eR fP eP fA eA)) q) =
      assemble (σ := σA) (ρ := ρA) (π := πA ⊕ τ) (α := αA)
        (fS ∘ Sum.inl) (eS ∘ Sum.inl) (fR ∘ Sum.inl) (eR ∘ Sum.inl)
        (Sum.elim (fP ∘ Sum.inl) q.1) (Sum.elim (eP ∘ Sum.inl) q.2)
        (fA ∘ Sum.inl) (eA ∘ Sum.inl) := by
  simp only [bondReindex_symm_apply]
  ext i <;> rcases i with s | r | (p | t) | a <;> rfl

omit [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA] [Fintype σB] [Fintype ρB] [Fintype πB]
  [Fintype αB] [Fintype τ] [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ] in
/-- [proved-derived; formal-checked] The right constituent's part, symmetrically. -/
theorem rightPart_assemble (fS eS : σA ⊕ σB → 𝕜) (fR eR : ρA ⊕ ρB → 𝕜) (fP eP : πA ⊕ πB → 𝕜)
    (fA eA : αA ⊕ αB → 𝕜) (q : Bond 𝕜 τ) :
    (bondReindex splitB).symm
        (partB ((bondReindex mergeKinds).symm (assemble fS eS fR eR fP eP fA eA)) q) =
      assemble (σ := σB) (ρ := ρB) (π := τ ⊕ πB) (α := αB)
        (fS ∘ Sum.inr) (eS ∘ Sum.inr) (fR ∘ Sum.inr) (eR ∘ Sum.inr)
        (Sum.elim q.1 (fP ∘ Sum.inr)) (Sum.elim q.2 (eP ∘ Sum.inr))
        (fA ∘ Sum.inr) (eA ∘ Sum.inr) := by
  simp only [bondReindex_symm_apply]
  ext i <;> rcases i with s | r | (t | p) | a <;> rfl

omit [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ] in
theorem sum_elim_dotProduct {ι κ : Type*} [Fintype ι] [Fintype κ] (a c : ι → 𝕜) (b d : κ → 𝕜) :
    Sum.elim a b ⬝ᵥ Sum.elim c d = a ⬝ᵥ c + b ⬝ᵥ d := by
  simp [dotProduct, Fintype.sum_sum_type]

omit [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ] in
theorem dotProduct_sum_type {ι κ : Type*} [Fintype ι] [Fintype κ] (u v : ι ⊕ κ → 𝕜) :
    u ⬝ᵥ v = (u ∘ Sum.inl) ⬝ᵥ (v ∘ Sum.inl) + (u ∘ Sum.inr) ⬝ᵥ (v ∘ Sum.inr) := by
  simp [dotProduct, Fintype.sum_sum_type]

end Whole

/-! ## 3. Gluing is unique, plural or obstructed: the interface fibre -/

section InterfaceGluing

variable {𝕜 : Type*} [Field 𝕜] {α β τ : Type*} [Fintype α] [Fintype β] [Fintype τ]

/-- [definition] **The interface fibre** over a whole bond `b`: every shared bond that realizes
`b`, i.e. makes the left side admitted with it and the right side admitted with its join. -/
def interfaceFibre (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))) (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β)))
    (F E : Matrix τ τ 𝕜) (b : Bond 𝕜 (α ⊕ β)) : Set (Bond 𝕜 τ) :=
  {q | partA b q ∈ DA ∧ partB b (joinBond F E q) ∈ DB}

omit [Fintype α] [Fintype β] in
/-- [proved-derived; formal-checked] A whole bond is admitted exactly when its interface fibre is
inhabited. -/
theorem mem_join_iff_interfaceFibre_nonempty (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ)))
    (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))) (F E : Matrix τ τ 𝕜) (b : Bond 𝕜 (α ⊕ β)) :
    b ∈ compose (pairedD DA DB) (gainLink F E) ↔ (interfaceFibre DA DB F E b).Nonempty := by
  rw [mem_compose]
  constructor
  · rintro ⟨⟨q₁, q₂⟩, hL, hA, hB⟩
    rw [mem_gainLink] at hL
    simp only at hL
    exact ⟨q₁, hA, by rw [← hL]; exact hB⟩
  · rintro ⟨q, hA, hB⟩
    exact ⟨(q, joinBond F E q), mem_gainLink.mpr rfl, hA, hB⟩

/-- [definition] The interface fibre presented as a one-chart continuing tower, so that the
gluing classification of `Foundation/ContinuingTower` applies to it unchanged. -/
def interfaceTower (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ))) (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β)))
    (F E : Matrix τ τ 𝕜) (b : Bond 𝕜 (α ⊕ β)) : Tower PUnit.{1} where
  Face _ := interfaceFibre DA DB F E b
  restrict _ x := x
  restrict_refl _ _ := rfl
  restrict_trans _ _ _ := rfl

/-- [proved-derived; formal-checked] The tower's continuing objects are exactly the fibre's shared
bonds. -/
def interfaceSectionEquiv (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ)))
    (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))) (F E : Matrix τ τ 𝕜) (b : Bond 𝕜 (α ⊕ β)) :
    (interfaceTower DA DB F E b).CompatibleSection ≃ interfaceFibre DA DB F E b where
  toFun s := s.witness PUnit.unit
  invFun q := ⟨fun _ => q, fun _ => rfl⟩
  left_inv s := Tower.CompatibleSection.ext fun i => by cases i; rfl
  right_inv _ := rfl

omit [Fintype α] [Fintype β] in
/-- [proved-derived; formal-checked] **Obstructed exactly when the whole refuses the bond.** -/
theorem interface_obstructed_iff (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ)))
    (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))) (F E : Matrix τ τ 𝕜) (b : Bond 𝕜 (α ⊕ β)) :
    IsEmpty (interfaceTower DA DB F E b).CompatibleSection ↔
      b ∉ compose (pairedD DA DB) (gainLink F E) := by
  rw [mem_join_iff_interfaceFibre_nonempty, (interfaceSectionEquiv DA DB F E b).isEmpty_congr,
    Set.not_nonempty_iff_eq_empty, ← Set.isEmpty_coe_sort, Set.isEmpty_coe_sort]

omit [Fintype α] [Fintype β] in
/-- [proved-derived; formal-checked] **Plural exactly when two shared bonds realize the bond.** -/
theorem interface_plural_iff (DA : Submodule 𝕜 (Bond 𝕜 (α ⊕ τ)))
    (DB : Submodule 𝕜 (Bond 𝕜 (τ ⊕ β))) (F E : Matrix τ τ 𝕜) (b : Bond 𝕜 (α ⊕ β)) :
    ¬ Subsingleton (interfaceTower DA DB F E b).CompatibleSection ↔
      ∃ q ∈ interfaceFibre DA DB F E b, ∃ q' ∈ interfaceFibre DA DB F E b, q ≠ q' := by
  rw [(interfaceSectionEquiv DA DB F E b).subsingleton_congr, Set.subsingleton_coe]
  simp only [Set.Subsingleton, not_forall, exists_prop]

end InterfaceGluing

/-! ## 4. The cellular facet: complexes and cellular embeddings -/

section Cells

variable {𝕜 : Type*} [Field 𝕜]

/-- [definition] Three consecutive grades of a finite cell complex as incidence matrices,
`d₁ : C₁ → C₀`, `d₂ : C₂ → C₁`, with `d₁ d₂ = 0`. The entries may be connection-valued. -/
structure CellComplex (𝕜 : Type*) [Field 𝕜] where
  /-- Vertices. -/
  C₀ : Type
  /-- Faces (the cells that carry currents and interfaces). -/
  C₁ : Type
  /-- Regions (the cells that carry interiors). -/
  C₂ : Type
  [fintype₀ : Fintype C₀]
  [fintype₁ : Fintype C₁]
  [fintype₂ : Fintype C₂]
  [decEq₀ : DecidableEq C₀]
  [decEq₁ : DecidableEq C₁]
  [decEq₂ : DecidableEq C₂]
  /-- The boundary of a face. -/
  d₁ : Matrix C₀ C₁ 𝕜
  /-- The boundary of a region. -/
  d₂ : Matrix C₁ C₂ 𝕜
  /-- The boundary of a boundary is zero. -/
  dd : d₁ * d₂ = 0

attribute [instance] CellComplex.fintype₀ CellComplex.fintype₁ CellComplex.fintype₂
  CellComplex.decEq₀ CellComplex.decEq₁ CellComplex.decEq₂

/-- [definition] **A cellular embedding** of a constituent's complex into the glued complex: every
cell of each grade goes to one cell of that grade, carrying a unit gauge (an orientation sign, or
the value of an oriented connection transport). -/
structure CellEmbedding (K K' : CellComplex 𝕜) where
  c₀ : K.C₀ → K'.C₀
  c₁ : K.C₁ → K'.C₁
  c₂ : K.C₂ → K'.C₂
  s₀ : K.C₀ → 𝕜ˣ
  s₁ : K.C₁ → 𝕜ˣ
  s₂ : K.C₂ → 𝕜ˣ

namespace CellEmbedding

variable {K K' : CellComplex 𝕜} (f : CellEmbedding K K')

/-- [definition] The matrix of grade 0: column `i` carries the gauge `s₀ i` at row `c₀ i`. -/
def m₀ : Matrix K'.C₀ K.C₀ 𝕜 := fun i' i => if f.c₀ i = i' then (f.s₀ i : 𝕜) else 0

/-- [definition] The matrix of grade 1. -/
def m₁ : Matrix K'.C₁ K.C₁ 𝕜 := fun i' i => if f.c₁ i = i' then (f.s₁ i : 𝕜) else 0

/-- [definition] The matrix of grade 2. -/
def m₂ : Matrix K'.C₂ K.C₂ 𝕜 := fun i' i => if f.c₂ i = i' then (f.s₂ i : 𝕜) else 0

/-- [definition] The embedding commutes with both boundaries. -/
def Commutes : Prop := K'.d₁ * f.m₁ = f.m₀ * K.d₁ ∧ K'.d₂ * f.m₂ = f.m₁ * K.d₂

/-- [definition] The embedding is injective on the cells of every grade. -/
def Injective : Prop :=
  Function.Injective f.c₀ ∧ Function.Injective f.c₁ ∧ Function.Injective f.c₂

/-- [proved-derived; formal-checked] The child restriction of a glued current reads it on the
image face, through the gauge: `(m₁ᵀ j) e = s₁ e · j (c₁ e)`. -/
theorem m₁_transpose_mulVec_apply (j : K'.C₁ → 𝕜) (e : K.C₁) :
    (f.m₁ᵀ *ᵥ j) e = (f.s₁ e : 𝕜) * j (f.c₁ e) := by
  simp only [mulVec, dotProduct, transpose_apply, m₁, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp

/-- [proved-derived; formal-checked] On an embedded face the pushed chain is the gauged value:
`(m₁ v) (c₁ e) = s₁ e · v e`. -/
theorem m₁_mulVec_apply_image (hinj : Function.Injective f.c₁) (v : K.C₁ → 𝕜) (e : K.C₁) :
    (f.m₁ *ᵥ v) (f.c₁ e) = (f.s₁ e : 𝕜) * v e := by
  simp only [mulVec, dotProduct, m₁, hinj.eq_iff, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

/-- [proved-derived; formal-checked] **An embedding is never the zero map**: on a complex with a
region, its matrix of regions has a unit entry. -/
theorem m₂_ne_zero [Nonempty K.C₂] : f.m₂ ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty K.C₂›
  have := congrFun (congrFun h (f.c₂ i)) i
  simp [m₂] at this

/-- [proved-derived; formal-checked] **The child's own flux is the whole's flux through its image.**
Under a commuting embedding, the flux of a glued current `j` through the image of a child region
equals the child's own flux of the restricted current `m₁ᵀ j`
(`Objects/Pairing.coordinate_stokes`). -/
theorem flux_pullback {f : CellEmbedding K K'} (hf : f.Commutes) (j : K'.C₁ → 𝕜) (c : K.C₂ → 𝕜) :
    j ⬝ᵥ (K'.d₂ *ᵥ (f.m₂ *ᵥ c)) = (f.m₁ᵀ *ᵥ j) ⬝ᵥ (K.d₂ *ᵥ c) := by
  rw [mulVec_mulVec, hf.2, ← mulVec_mulVec, Objects.Pairing.coordinate_stokes]

/-- [proved-derived; formal-checked] **The child restriction carries exact currents to exact
currents**: `m₁ᵀ (d₁ᵀ φ) = d₁ᵀ (m₀ᵀ φ)`, the transpose of the first square. -/
theorem restrict_exact {f : CellEmbedding K K'} (hf : f.Commutes) (φ : K'.C₀ → 𝕜) :
    f.m₁ᵀ *ᵥ (K'.d₁ᵀ *ᵥ φ) = K.d₁ᵀ *ᵥ (f.m₀ᵀ *ᵥ φ) := by
  rw [mulVec_mulVec, mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hf.1]

end CellEmbedding

/-- [proved-derived; formal-checked] **An exact current has no net flux through any region's
boundary** (`d₁ d₂ = 0`, Stokes). -/
theorem CellComplex.exact_flux_zero (K : CellComplex 𝕜) (φ : K.C₀ → 𝕜) (c : K.C₂ → 𝕜) :
    (K.d₁ᵀ *ᵥ φ) ⬝ᵥ (K.d₂ *ᵥ c) = 0 := by
  rw [Objects.Pairing.coordinate_stokes, mulVec_mulVec, K.dd, zero_mulVec, dotProduct_zero]

end Cells

/-! ## 5. Navigators and the joint clock -/

section Clocks

/-- [definition] **A navigator's clock**: its initial configuration, whole windings and open phase
in turns (the key), and its rate in turns per turn of the Holarchy's parameter. Exact rationals. -/
structure NavigatorClock where
  windings : ℤ
  phase : ℚ
  phase_nonneg : 0 ≤ phase
  phase_lt_one : phase < 1
  rate : ℚ

/-- [definition] A rate runs **on the joint clock** when it is a whole multiple of the joint rate. -/
def OnJointClock (jointRate rate : ℚ) : Prop := ∃ k : ℕ, rate = k * jointRate

open Holonics.Aeon.Clock.Lock in
/-- [proved-derived; formal-checked] **A pump on the joint clock closes at every joint aeon**: the
aeon of `m` joint ticks reads a whole number of the pump's turns
(`Aeon/Clock/Lock.jointReading_isCycle_iff`). -/
theorem OnJointClock.closes {ω r : ℚ} (h : OnJointClock ω r) (hω : ω ≠ 0) (m : ℤ) :
    IsCycle (jointReading (r / ω) m) := by
  obtain ⟨k, rfl⟩ := h
  rw [jointReading_isCycle_iff]
  refine ⟨m * k, ?_⟩
  push_cast
  field_simp

open Holonics.Aeon.Clock.Lock in
/-- [proved-derived; formal-checked] **Two pumps on one joint clock lock at their Farey address**:
with rates `k ω` and `k' ω`, `k' > 0`, every aeon of `k' m` ticks of the second is a cycle of the
pair (`Aeon/Clock/Lock.lock_at_address`, with its no-slip reading). -/
theorem OnJointClock.lock {ω r r' : ℚ} (h : OnJointClock ω r) (h' : OnJointClock ω r')
    (hω : ω ≠ 0) : ∃ k k' : ℕ, r = k * ω ∧ r' = k' * ω ∧
      (0 < k' → ∀ m : ℤ, IsCycle (jointReading (r / r') (k' * m))) := by
  obtain ⟨k, rfl⟩ := h
  obtain ⟨k', rfl⟩ := h'
  refine ⟨k, k', rfl, rfl, fun hk' m => ?_⟩
  have hratio : (k : ℚ) * ω / (k' * ω) = ((k : ℤ) : ℚ) / k' := by
    have : (k' : ℚ) ≠ 0 := by exact_mod_cast hk'.ne'
    field_simp
    push_cast
    ring
  rw [hratio]
  exact (lock_at_address k k' hk' m).2.1

open Holonics.Aeon.Clock.Lock in
/-- [counterexample; formal-checked] **Incommensurate rates close at no joint aeon.** Rates `1`
and `√2` have no aeon of nonzero ticks that is a cycle of the pair
(`Aeon/Clock/Lock.no_cycle_of_irrational`); no exact joint clock carries them. -/
theorem incommensurate_rates_never_close {k : ℤ} (hk : k ≠ 0) :
    ¬ IsCycle (jointReading (Real.sqrt 2) k) :=
  no_cycle_of_irrational irrational_sqrt_two hk

end Clocks

/-! ## 6. Constituents, the declared gluing, the Holarchy and `interconnect` -/

section Join

variable {𝕜 : Type*} [Field 𝕜] {U : Type*}

/-- [definition] **A constituent**: a port Holon with its cell complex and oriented interior chain,
the unit of each external port, the face each external port sits on, its navigators with their
clocks, and the navigator driving each pump (active port). -/
structure Constituent (𝕜 U σ ρ π α : Type*) [Field 𝕜] [Fintype σ] [Fintype ρ] [Fintype π]
    [Fintype α] where
  /-- The port Holon: interconnection and element relations. -/
  holon : PortHolon 𝕜 σ ρ π α
  /-- Its cell complex. -/
  complex : CellComplex 𝕜
  /-- Its oriented interior chain. -/
  interior : complex.C₂ → 𝕜
  /-- The unit of each external port. -/
  unit : π → U
  /-- The face each external port sits on. -/
  portFace : π → complex.C₁
  /-- Its navigators. -/
  Nav : Type
  [navDecEq : DecidableEq Nav]
  /-- Each navigator's clock. -/
  navigator : Nav → NavigatorClock
  /-- The navigator driving each pump. -/
  pumpNavigator : α → Nav

attribute [instance] Constituent.navDecEq

/-- [definition] A pump's rate, read from its navigator. -/
def Constituent.pumpRate {σ ρ π α : Type*} [Fintype σ] [Fintype ρ] [Fintype π] [Fintype α]
    (A : Constituent 𝕜 U σ ρ π α) (a : α) : ℚ :=
  (A.navigator (A.pumpNavigator a)).rate

/-- [definition] Which constituent. -/
inductive Side where
  | left
  | right
  deriving DecidableEq

variable {σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ] [DecidableEq τ]

/-- [definition] **The declared gluing** of two constituents, typed by them: the shared-port join
law, the glued complex with a cellular embedding of each constituent's own complex, and the joint
clock rate. The shared ports are the `inr` ports of the left constituent and the `inl` ports of the
right one. -/
structure JoinDeclaration (A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA)
    (B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB) where
  flowGain : Matrix τ τ 𝕜
  effortGain : Matrix τ τ 𝕜
  glued : CellComplex 𝕜
  leftCells : CellEmbedding A.complex glued
  rightCells : CellEmbedding B.complex glued
  jointRate : ℚ

namespace JoinDeclaration

variable {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA} {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB}
variable (d : JoinDeclaration A B)

/-- [definition] Each shared port carries one unit in both constituents. -/
def UnitsAgree (_ : JoinDeclaration A B) : Prop := ∀ t, A.unit (.inr t) = B.unit (.inl t)

/-- [definition] The join cancels the interface power. -/
def PowerCancels : Prop := d.effortGainᵀ * d.flowGain = 1

/-- [definition] The embedding of one side commutes with the boundaries. -/
def CellsCommute : Side → Prop
  | .left => d.leftCells.Commutes
  | .right => d.rightCells.Commutes

/-- [definition] The embedding of one side is injective on cells. -/
def CellsInjective : Side → Prop
  | .left => d.leftCells.Injective
  | .right => d.rightCells.Injective

/-- [definition] Every glued cell of every grade is the image of a constituent's cell. -/
def Covers : Prop :=
  (∀ v, (∃ i, d.leftCells.c₀ i = v) ∨ ∃ i, d.rightCells.c₀ i = v) ∧
    (∀ e, (∃ i, d.leftCells.c₁ i = e) ∨ ∃ i, d.rightCells.c₁ i = e) ∧
    (∀ r, (∃ i, d.leftCells.c₂ i = r) ∨ ∃ i, d.rightCells.c₂ i = r)

/-- [definition] The shared port `t` sits on one glued face from both sides. -/
def SharedFaceIdentified (t : τ) : Prop :=
  d.leftCells.c₁ (A.portFace (.inr t)) = d.rightCells.c₁ (B.portFace (.inl t))

/-- [definition] The two images share no region, and share a face only at a shared port. -/
def OverlapsOnlyShared : Prop :=
  (∀ i j, d.leftCells.c₂ i ≠ d.rightCells.c₂ j) ∧
    ∀ i j, d.leftCells.c₁ i = d.rightCells.c₁ j →
      ∃ t, i = A.portFace (.inr t) ∧ j = B.portFace (.inl t)

/-- [definition] The glued boundary coefficient of the shared face of port `t`: each constituent's
oriented boundary at its face, carried by its gauge. -/
def sharedFaceBoundary (t : τ) : 𝕜 :=
  (d.leftCells.s₁ (A.portFace (.inr t)) : 𝕜) *
      (A.complex.d₂ *ᵥ A.interior) (A.portFace (.inr t)) +
    (d.rightCells.s₁ (B.portFace (.inl t)) : 𝕜) *
      (B.complex.d₂ *ᵥ B.interior) (B.portFace (.inl t))

/-- [definition] The shared face enters the two boundaries with opposite signs. -/
def SharedFaceCancels (t : τ) : Prop := d.sharedFaceBoundary t = 0

/-- [definition] Every pump of both constituents runs on the joint clock. -/
def PumpsOnClock : Prop :=
  ∀ p : αA ⊕ αB, OnJointClock d.jointRate (Sum.elim A.pumpRate B.pumpRate p)

/-- [definition] **The declaration glues the two constituents.** -/
def Glues : Prop :=
  d.UnitsAgree ∧ d.PowerCancels ∧ (∀ side, d.CellsCommute side) ∧
    (∀ side, d.CellsInjective side) ∧ d.Covers ∧ (∀ t, d.SharedFaceIdentified t) ∧
    d.OverlapsOnlyShared ∧ (∀ t, d.SharedFaceCancels t) ∧ d.PumpsOnClock

/-- [definition] **A shared port's flow read on its face** from the left constituent: the
constituent's own flux of the restricted current through that face. -/
def faceFlowLeft (t : τ) (j : d.glued.C₁ → 𝕜) : 𝕜 :=
  (d.leftCells.m₁ᵀ *ᵥ j) (A.portFace (.inr t)) *
    (A.complex.d₂ *ᵥ A.interior) (A.portFace (.inr t))

/-- [definition] The same from the right constituent. -/
def faceFlowRight (t : τ) (j : d.glued.C₁ → 𝕜) : 𝕜 :=
  (d.rightCells.m₁ᵀ *ᵥ j) (B.portFace (.inl t)) *
    (B.complex.d₂ *ᵥ B.interior) (B.portFace (.inl t))

omit [DecidableEq τ] in
/-- [proved-derived; formal-checked] **One sign law for ports and faces.** At an identified shared
face, the face-read flows of the shared port satisfy the identity join `f_B = −f_A` for every glued
current exactly when the shared face cancels. -/
theorem faceFlows_join_iff (t : τ) (hid : d.SharedFaceIdentified t) :
    (∀ j, d.faceFlowRight t j = -d.faceFlowLeft t j) ↔ d.SharedFaceCancels t := by
  have hsum : ∀ j, d.faceFlowRight t j + d.faceFlowLeft t j =
      j (d.leftCells.c₁ (A.portFace (.inr t))) * d.sharedFaceBoundary t := by
    intro j
    simp only [faceFlowLeft, faceFlowRight, sharedFaceBoundary,
      CellEmbedding.m₁_transpose_mulVec_apply]
    rw [← hid]
    ring
  constructor
  · intro h
    have := hsum (Pi.single (d.leftCells.c₁ (A.portFace (.inr t))) 1)
    rw [h, neg_add_cancel, Pi.single_eq_same, one_mul] at this
    exact this.symm
  · intro h j
    have := hsum j
    rw [show d.sharedFaceBoundary t = 0 from h, mul_zero] at this
    linear_combination this

end JoinDeclaration

/-- [definition] **The typed gluing defect.** Each constructor carries the failed check and its
witness, read from the two constituents. -/
inductive GluingDefect {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA}
    {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB} (d : JoinDeclaration A B) : Type _ where
  /-- A shared port whose two sides carry different units. -/
  | unitMismatch (port : τ) (mismatch : A.unit (.inr port) ≠ B.unit (.inl port))
  /-- A shared bond whose interface power the declared join does not cancel. -/
  | uncancelledPower (bond : Bond 𝕜 τ)
      (power_ne : interfacePower d.flowGain d.effortGain bond ≠ 0)
  /-- A constituent whose embedding does not commute with the boundaries. -/
  | nonCommutingCells (side : Side) (defect : ¬ d.CellsCommute side)
  /-- A constituent whose embedding merges cells. -/
  | degenerateCells (side : Side) (defect : ¬ d.CellsInjective side)
  /-- A glued cell that belongs to neither constituent. -/
  | uncoveredCells (defect : ¬ d.Covers)
  /-- A shared port whose two faces are not identified. -/
  | unidentifiedSharedFace (port : τ) (defect : ¬ d.SharedFaceIdentified port)
  /-- The two images meet on a region or on a face that no shared port declares. -/
  | strayOverlap (defect : ¬ d.OverlapsOnlyShared)
  /-- A shared face that enters both boundaries with one sign, so it is not interior to the whole. -/
  | sharedFaceUncancelled (port : τ) (defect : ¬ d.SharedFaceCancels port)
  /-- A pump whose rate is not a whole multiple of the joint clock rate. -/
  | incompatibleClocks (pump : αA ⊕ αB)
      (off : ¬ OnJointClock d.jointRate (Sum.elim A.pumpRate B.pumpRate pump))

/-- [proved-derived; formal-checked] **Every defect refutes the gluing.** -/
theorem GluingDefect.not_glues {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA}
    {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB} {d : JoinDeclaration A B} (e : GluingDefect d) :
    ¬ d.Glues := by
  rintro ⟨hu, hp, hc, hi, hcov, hid, hov, hcan, hk⟩
  cases e with
  | unitMismatch port mismatch => exact mismatch (hu port)
  | uncancelledPower bond power_ne =>
      exact power_ne ((interfacePower_cancels_iff _ _).mpr hp bond)
  | nonCommutingCells side defect => exact defect (hc side)
  | degenerateCells side defect => exact defect (hi side)
  | uncoveredCells defect => exact defect hcov
  | unidentifiedSharedFace port defect => exact defect (hid port)
  | strayOverlap defect => exact defect hov
  | sharedFaceUncancelled port defect => exact defect (hcan port)
  | incompatibleClocks pump off => exact off (hk pump)

/-- [definition] **A Holarchy** of two retained constituents: the declared gluing, typed by them,
and the proof that it glues. The joined whole is `Holarchy.wholeConstituent`; the incidence is the
glued complex with each constituent's embedding; the child restrictions are the transposed
embeddings. -/
structure Holarchy (A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA)
    (B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB) where
  /-- The typed gluing. -/
  decl : JoinDeclaration A B
  /-- It glues. -/
  glues : decl.Glues

namespace Holarchy

variable {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA} {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB}
  (h : Holarchy A B)

/-- [definition] **The joined port Holon.** -/
def whole [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
    [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] :
    PortHolon 𝕜 (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB) :=
  joinHolon A.holon B.holon h.decl.flowGain h.decl.effortGain h.glues.2.1

/-- [definition] The whole's interior on the glued complex: both constituents' interiors carried
by their embeddings. -/
def wholeInterior : h.decl.glued.C₂ → 𝕜 :=
  h.decl.leftCells.m₂ *ᵥ A.interior + h.decl.rightCells.m₂ *ᵥ B.interior

/-- [definition] **The joined whole, again a constituent**: the port join, the glued complex and
interior, the unshared ports with their units and faces, the two navigator families side by side
and the pumps namespaced by `Sum`. -/
def wholeConstituent [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
    [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] :
    Constituent 𝕜 U (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB) where
  holon := h.whole
  complex := h.decl.glued
  interior := h.wholeInterior
  unit := Sum.elim (A.unit ∘ Sum.inl) (B.unit ∘ Sum.inr)
  portFace := Sum.elim (h.decl.leftCells.c₁ ∘ A.portFace ∘ Sum.inl)
    (h.decl.rightCells.c₁ ∘ B.portFace ∘ Sum.inr)
  Nav := A.Nav ⊕ B.Nav
  navigator := Sum.elim A.navigator B.navigator
  pumpNavigator := Sum.map A.pumpNavigator B.pumpNavigator

/-- [proved-derived; formal-checked] **The whole's pumps are the constituents' pumps**, on their
own navigators: provenance is kept by `Sum`, and every pump of the whole runs on the joint clock. -/
theorem wholeConstituent_pumpRate [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA]
    [DecidableEq αA] [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB]
    (p : αA ⊕ αB) :
    h.wholeConstituent.pumpRate p = Sum.elim A.pumpRate B.pumpRate p ∧
      OnJointClock h.decl.jointRate (h.wholeConstituent.pumpRate p) := by
  have hp : h.wholeConstituent.pumpRate p = Sum.elim A.pumpRate B.pumpRate p := by
    rcases p with a | a <;> rfl
  exact ⟨hp, hp ▸ h.glues.2.2.2.2.2.2.2.2 p⟩

/-- [definition] **The Holarchy's parametric orientation**: the lift of the joint clock torus of
its navigators, whose aeons are the Holarchy's aeons (`Aeon/Clock/Winding.clockLift`). -/
def parametric :=
  Holonics.Aeon.Clock.Winding.clockLift (A.Nav ⊕ B.Nav)

/-- [proved-derived; formal-checked] **The whole's flux is the sum of the constituents' own
fluxes**, each computed in its own complex from the restricted current, and it is the divergence
paired with the whole's interior (Stokes on the glued complex). -/
theorem whole_flux (j : h.decl.glued.C₁ → 𝕜) :
    j ⬝ᵥ (h.decl.glued.d₂ *ᵥ h.wholeInterior) =
        (h.decl.leftCells.m₁ᵀ *ᵥ j) ⬝ᵥ (A.complex.d₂ *ᵥ A.interior) +
          (h.decl.rightCells.m₁ᵀ *ᵥ j) ⬝ᵥ (B.complex.d₂ *ᵥ B.interior) ∧
      j ⬝ᵥ (h.decl.glued.d₂ *ᵥ h.wholeInterior) =
        (h.decl.glued.d₂ᵀ *ᵥ j) ⬝ᵥ h.wholeInterior := by
  refine ⟨?_, (Objects.Pairing.coordinate_stokes _ _ _).symm⟩
  have hL := CellEmbedding.flux_pullback (f := h.decl.leftCells) (h.glues.2.2.1 .left) j A.interior
  have hR := CellEmbedding.flux_pullback (f := h.decl.rightCells) (h.glues.2.2.1 .right) j
    B.interior
  rw [wholeInterior, mulVec_add, dotProduct_add, hL, hR]

/-- [proved-derived; formal-checked] **A shared face is silent in the whole's boundary**: the two
constituents' boundaries meet there with opposite signs, so the glued boundary of the whole's
interior vanishes on it. -/
theorem sharedFace_silent (t : τ) :
    (h.decl.glued.d₂ *ᵥ h.wholeInterior) (h.decl.leftCells.c₁ (A.portFace (.inr t))) = 0 := by
  obtain ⟨-, -, hc, hi, -, hid, -, hcan, -⟩ := h.glues
  have hL : h.decl.glued.d₂ *ᵥ (h.decl.leftCells.m₂ *ᵥ A.interior) =
      h.decl.leftCells.m₁ *ᵥ (A.complex.d₂ *ᵥ A.interior) := by
    rw [mulVec_mulVec, (hc .left).2, ← mulVec_mulVec]
  have hR : h.decl.glued.d₂ *ᵥ (h.decl.rightCells.m₂ *ᵥ B.interior) =
      h.decl.rightCells.m₁ *ᵥ (B.complex.d₂ *ᵥ B.interior) := by
    rw [mulVec_mulVec, (hc .right).2, ← mulVec_mulVec]
  rw [wholeInterior, mulVec_add, Pi.add_apply, hL, hR,
    CellEmbedding.m₁_mulVec_apply_image _ (hi .left).2.1, hid t,
    CellEmbedding.m₁_mulVec_apply_image _ (hi .right).2.1]
  exact hcan t

/-- [proved-derived; formal-checked] **In a Holarchy the port join and the face cancellation are one
sign law.** Read on its face, every shared port's flow satisfies the identity join `f_B = −f_A` for
every glued current; at `F = E = 1` that is the flow of `joinBond`. -/
theorem sharedPort_face_join (t : τ) (j : h.decl.glued.C₁ → 𝕜) :
    h.decl.faceFlowRight t j = -h.decl.faceFlowLeft t j ∧
      (joinBond (1 : Matrix τ τ 𝕜) 1 (Pi.single t (h.decl.faceFlowLeft t j), 0)).1 t =
        h.decl.faceFlowRight t j := by
  have hj := ((h.decl.faceFlows_join_iff t (h.glues.2.2.2.2.2.1 t)).mpr
    (h.glues.2.2.2.2.2.2.2.1 t)) j
  refine ⟨hj, ?_⟩
  rw [hj]
  simp [joinBond]

variable [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB]

/-- [proved-derived; formal-checked] **The whole's power balance is the sum of the constituents'
external powers.** Every admitted point of the whole restricts, through one shared bond `q`, to an
admitted point of each actual constituent, whose external ports are its own together with the
shared ones; the two constituents' external powers sum to the whole's: the shared terms are the
interface power, which the join cancels. -/
theorem power_balance {x v : σA ⊕ σB → 𝕜} {fR : ρA ⊕ ρB → 𝕜} {fP eP : πA ⊕ πB → 𝕜}
    {fA eA : αA ⊕ αB → 𝕜} (hadm : h.whole.Admits h.whole.Q x v fR fP eP fA eA) :
    ∃ q : Bond 𝕜 τ,
      A.holon.Admits A.holon.Q (x ∘ Sum.inl) (v ∘ Sum.inl) (fR ∘ Sum.inl)
        (Sum.elim (fP ∘ Sum.inl) q.1) (Sum.elim (eP ∘ Sum.inl) q.2)
        (fA ∘ Sum.inl) (eA ∘ Sum.inl) ∧
      B.holon.Admits B.holon.Q (x ∘ Sum.inr) (v ∘ Sum.inr) (fR ∘ Sum.inr)
        (Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).1 (fP ∘ Sum.inr))
        (Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).2 (eP ∘ Sum.inr))
        (fA ∘ Sum.inr) (eA ∘ Sum.inr) ∧
      Sum.elim (eP ∘ Sum.inl) q.2 ⬝ᵥ Sum.elim (fP ∘ Sum.inl) q.1 +
          Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).2 (eP ∘ Sum.inr) ⬝ᵥ
            Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).1 (fP ∘ Sum.inr) =
        eP ⬝ᵥ fP := by
  obtain ⟨q, hA, hB⟩ := (mem_joinD A.holon B.holon _ _ _).mp hadm
  rw [leftPart_assemble] at hA
  rw [rightPart_assemble] at hB
  refine ⟨q, ?_, ?_, ?_⟩
  · unfold PortHolon.Admits
    convert hA using 2
    all_goals
      funext i
      simp only [whole, joinHolon, Function.comp_apply, Pi.neg_apply, Matrix.fromBlocks_mulVec,
        Sum.elim_inl, zero_mulVec, add_zero]
  · unfold PortHolon.Admits
    convert hB using 2
    all_goals
      funext i
      simp only [whole, joinHolon, Function.comp_apply, Pi.neg_apply, Matrix.fromBlocks_mulVec,
        Sum.elim_inr, zero_mulVec, zero_add]
  · have hq := (interfacePower_cancels_iff h.decl.flowGain h.decl.effortGain).mpr h.glues.2.1 q
    rw [sum_elim_dotProduct, sum_elim_dotProduct, dotProduct_sum_type eP fP]
    unfold interfacePower power at hq
    linear_combination hq

/-- [proved-derived; formal-checked] **The whole's balance is the sum of the two constituents'
balances.** The whole's storage rate is the sum of the constituents' storage rates, and each of
those is its own dissipation, external power (shared ports included) and active power; the shared
parts cancel in the sum. -/
theorem balance_is_sum [CharZero 𝕜] {x v : σA ⊕ σB → 𝕜} {fR : ρA ⊕ ρB → 𝕜}
    {fP eP : πA ⊕ πB → 𝕜} {fA eA : αA ⊕ αB → 𝕜}
    (hadm : h.whole.Admits h.whole.Q x v fR fP eP fA eA) :
    ∃ q : Bond 𝕜 τ,
      (A.holon.Q *ᵥ (x ∘ Sum.inl)) ⬝ᵥ (v ∘ Sum.inl) =
          -((fR ∘ Sum.inl) ⬝ᵥ (A.holon.R *ᵥ (fR ∘ Sum.inl))) +
            Sum.elim (eP ∘ Sum.inl) q.2 ⬝ᵥ Sum.elim (fP ∘ Sum.inl) q.1 +
            (eA ∘ Sum.inl) ⬝ᵥ (fA ∘ Sum.inl) ∧
      (B.holon.Q *ᵥ (x ∘ Sum.inr)) ⬝ᵥ (v ∘ Sum.inr) =
          -((fR ∘ Sum.inr) ⬝ᵥ (B.holon.R *ᵥ (fR ∘ Sum.inr))) +
            Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).2 (eP ∘ Sum.inr) ⬝ᵥ
              Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).1 (fP ∘ Sum.inr) +
            (eA ∘ Sum.inr) ⬝ᵥ (fA ∘ Sum.inr) ∧
      (h.whole.Q *ᵥ x) ⬝ᵥ v =
          (A.holon.Q *ᵥ (x ∘ Sum.inl)) ⬝ᵥ (v ∘ Sum.inl) +
            (B.holon.Q *ᵥ (x ∘ Sum.inr)) ⬝ᵥ (v ∘ Sum.inr) ∧
      fR ⬝ᵥ (h.whole.R *ᵥ fR) =
          (fR ∘ Sum.inl) ⬝ᵥ (A.holon.R *ᵥ (fR ∘ Sum.inl)) +
            (fR ∘ Sum.inr) ⬝ᵥ (B.holon.R *ᵥ (fR ∘ Sum.inr)) ∧
      eA ⬝ᵥ fA = (eA ∘ Sum.inl) ⬝ᵥ (fA ∘ Sum.inl) + (eA ∘ Sum.inr) ⬝ᵥ (fA ∘ Sum.inr) ∧
      Sum.elim (eP ∘ Sum.inl) q.2 ⬝ᵥ Sum.elim (fP ∘ Sum.inl) q.1 +
          Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).2 (eP ∘ Sum.inr) ⬝ᵥ
            Sum.elim (joinBond h.decl.flowGain h.decl.effortGain q).1 (fP ∘ Sum.inr) =
        eP ⬝ᵥ fP := by
  obtain ⟨q, hA, hB, hext⟩ := h.power_balance hadm
  refine ⟨q, A.holon.power_balance hA, B.holon.power_balance hB, ?_, ?_,
    dotProduct_sum_type _ _, hext⟩
  · rw [dotProduct_sum_type]
    simp [whole, joinHolon, Matrix.fromBlocks_mulVec]
  · rw [dotProduct_sum_type]
    simp [whole, joinHolon, Matrix.fromBlocks_mulVec]

end Holarchy

open Classical in
/-- [definition] **`interconnect`**: check the constituents' units, the interface power, both
cellular embeddings (commuting, injective, covering), the identification of every shared face,
the overlap, the cancellation of every shared face, and the pumps' joint clock; return the
Holarchy, or the first failed check as a typed defect. -/
def interconnect (A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA) (B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB)
    (d : JoinDeclaration A B) : Except (GluingDefect d) (Holarchy A B) :=
  if hu : d.UnitsAgree then
    if hp : d.PowerCancels then
      if hc : ∀ side, d.CellsCommute side then
        if hi : ∀ side, d.CellsInjective side then
          if hcov : d.Covers then
            if hid : ∀ t, d.SharedFaceIdentified t then
              if hov : d.OverlapsOnlyShared then
                if hcan : ∀ t, d.SharedFaceCancels t then
                  if hk : d.PumpsOnClock then .ok ⟨d, hu, hp, hc, hi, hcov, hid, hov, hcan, hk⟩
                  else .error (.incompatibleClocks (not_forall.mp hk).choose
                    (not_forall.mp hk).choose_spec)
                else .error (.sharedFaceUncancelled (not_forall.mp hcan).choose
                  (not_forall.mp hcan).choose_spec)
              else .error (.strayOverlap hov)
            else .error (.unidentifiedSharedFace (not_forall.mp hid).choose
              (not_forall.mp hid).choose_spec)
          else .error (.uncoveredCells hcov)
        else .error (.degenerateCells (not_forall.mp hi).choose (not_forall.mp hi).choose_spec)
      else .error (.nonCommutingCells (not_forall.mp hc).choose (not_forall.mp hc).choose_spec)
    else .error (.uncancelledPower (exists_interfacePower_ne_zero hp).choose
      (exists_interfacePower_ne_zero hp).choose_spec)
  else .error (.unitMismatch (not_forall.mp hu).choose (not_forall.mp hu).choose_spec)

variable {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA} {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB}

/-- [proved-derived; formal-checked] A declaration that glues the two constituents returns their
Holarchy. -/
theorem interconnect_of_glues {d : JoinDeclaration A B} (hg : d.Glues) :
    interconnect A B d = .ok ⟨d, hg⟩ := by
  obtain ⟨hu, hp, hc, hi, hcov, hid, hov, hcan, hk⟩ := hg
  unfold interconnect
  rw [dif_pos hu, dif_pos hp, dif_pos hc, dif_pos hi, dif_pos hcov, dif_pos hid, dif_pos hov,
    dif_pos hcan, dif_pos hk]

/-- [proved-derived; formal-checked] **`interconnect` returns a Holarchy exactly when the
declaration glues the two actual constituents**: their units, their complexes and interiors under
the declared embeddings, their port faces, and their pumps' navigators. -/
theorem interconnect_ok_iff (d : JoinDeclaration A B) :
    (∃ h, interconnect A B d = .ok h) ↔ d.Glues := by
  constructor
  · rintro ⟨h, hh⟩
    unfold interconnect at hh
    split_ifs at hh with hu hp hc hi hcov hid hov hcan hk
    exact ⟨hu, hp, hc, hi, hcov, hid, hov, hcan, hk⟩
  · intro hg
    exact ⟨_, interconnect_of_glues hg⟩

/-- [proved-derived; formal-checked] **The returned Holarchy retains the declared gluing** of the
two constituents it is typed by. -/
theorem interconnect_ok_retains {d : JoinDeclaration A B} {h : Holarchy A B}
    (hh : interconnect A B d = .ok h) : h.decl = d := by
  have hg := (interconnect_ok_iff d).mp ⟨h, hh⟩
  rw [interconnect_of_glues hg] at hh
  cases hh
  rfl

/-- [proved-derived; formal-checked] **A declaration that does not glue returns a defect.** -/
theorem interconnect_error_of_not_glues {d : JoinDeclaration A B} (hg : ¬ d.Glues) :
    ∃ e, interconnect A B d = .error e := by
  cases hh : interconnect A B d with
  | error e => exact ⟨e, rfl⟩
  | ok h => exact absurd ((interconnect_ok_iff d).mp ⟨h, hh⟩) hg

end Join

/-! ## 7. Witnesses -/

section Witnesses

theorem mem_passiveCoholon_iff {τ : Type*} [Fintype τ] {b : Bond ℚ τ} :
    b ∈ passiveCoholon ℚ τ ↔ b.1 = 0 := Iff.rfl

theorem mem_kirchhoff_iff {ι ν : Type*} [Fintype ι] [Fintype ν] {d : Matrix ι ν ℚ}
    {b : Bond ℚ ι} : b ∈ kirchhoff d ↔ dᵀ *ᵥ b.1 = 0 ∧ ∃ φ, d *ᵥ φ = b.2 := Iff.rfl

/-- [definition] A port Holon on one shared port only, reading it as a passive coholon. -/
def coholonLeft : PortHolon ℚ Empty Empty (Empty ⊕ Unit) Empty where
  D := passiveCoholon ℚ _
  dirac := passiveCoholon_isDirac
  Q := 0
  Q_symm := by simp
  R := 0

/-- [definition] Its mirror on the right. -/
def coholonRight : PortHolon ℚ Empty Empty (Unit ⊕ Empty) Empty where
  D := passiveCoholon ℚ _
  dirac := passiveCoholon_isDirac
  Q := 0
  Q_symm := by simp
  R := 0

/-- [definition] One face bounding one region with coefficient `1`, no vertices. -/
abbrev faceComplex : CellComplex ℚ where
  C₀ := Empty
  C₁ := Unit
  C₂ := Unit
  d₁ := 0
  d₂ := fun _ _ => 1
  dd := by ext i; exact i.elim

/-- [definition] One face bounding two regions, with coefficient `a` in the first (`false`) and `b`
in the second (`true`). -/
abbrev sharedComplex (a b : ℚ) : CellComplex ℚ where
  C₀ := Empty
  C₁ := Unit
  C₂ := Bool
  d₁ := 0
  d₂ := fun _ r => if r then b else a
  dd := by ext i; exact i.elim

/-- [definition] A navigator at rest in its initial configuration, turning at rate `r`. -/
abbrev navAt (r : ℚ) : NavigatorClock := ⟨0, 0, le_rfl, zero_lt_one, r⟩

/-- [definition] The left constituent: a passive coholon on one shared port, sitting on the one face
of `faceComplex`, with the unit `u` and no navigator. -/
abbrev leftConstituent (u : Bool) : Constituent ℚ Bool Empty Empty (Empty ⊕ Unit) Empty where
  holon := coholonLeft
  complex := faceComplex
  interior := fun _ => 1
  unit := fun _ => u
  portFace := fun _ => ()
  Nav := Empty
  navigator := fun x => x.elim
  pumpNavigator := fun x => x.elim

/-- [definition] Its mirror on the right. -/
abbrev rightConstituent (u : Bool) : Constituent ℚ Bool Empty Empty (Unit ⊕ Empty) Empty where
  holon := coholonRight
  complex := faceComplex
  interior := fun _ => 1
  unit := fun _ => u
  portFace := fun _ => ()
  Nav := Empty
  navigator := fun x => x.elim
  pumpNavigator := fun x => x.elim

/-- [definition] The embedding of `faceComplex` sending its face to `e`, with gauge `s`, and its
region to `r`. -/
abbrev faceEmbedding (K' : CellComplex ℚ) (e : K'.C₁) (r : K'.C₂) (s : ℚˣ) :
    CellEmbedding faceComplex K' :=
  ⟨fun x => Empty.elim x, fun _ => e, fun _ => r, fun x => Empty.elim x, fun _ => s, fun _ => 1⟩

/-- [definition] **Two constituents sharing their face**: the identity join, the face glued once,
the left region `false` with coefficient `1`, the right region `true` with the face reversed. -/
abbrev sharedDecl (uL uR : Bool) (F : Matrix Unit Unit ℚ) (a b : ℚ) (s : ℚˣ) :
    JoinDeclaration (leftConstituent uL) (rightConstituent uR) where
  flowGain := F
  effortGain := 1
  glued := sharedComplex a b
  leftCells := faceEmbedding (sharedComplex a b) () false 1
  rightCells := faceEmbedding (sharedComplex a b) () true s
  jointRate := 1

theorem faceEmbedding_commutes_shared {a b : ℚ} (r : Bool) (s : ℚˣ)
    (h : (if r then b else a) = (s : ℚ)) :
    (faceEmbedding (sharedComplex a b) () r s).Commutes := by
  refine ⟨by ext i; exact i.elim, ?_⟩
  ext i j
  rw [Matrix.mul_apply, Matrix.mul_apply]
  cases r <;>
    simp [CellEmbedding.m₁, CellEmbedding.m₂, sharedComplex, faceComplex] at h ⊢ <;> exact h

theorem faceEmbedding_injective (K' : CellComplex ℚ) (e : K'.C₁) (r : K'.C₂) (s : ℚˣ) :
    (faceEmbedding K' e r s).Injective :=
  ⟨fun x => Empty.elim x, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

theorem sharedDecl_units (u : Bool) (F : Matrix Unit Unit ℚ) (a b : ℚ) (s : ℚˣ) :
    (sharedDecl u u F a b s).UnitsAgree := fun _ => rfl

theorem sharedDecl_covers (uL uR : Bool) (F : Matrix Unit Unit ℚ) (a b : ℚ) (s : ℚˣ) :
    (sharedDecl uL uR F a b s).Covers :=
  ⟨fun v => Empty.elim v, fun _ => Or.inl ⟨(), rfl⟩,
    fun r => by cases r; exacts [Or.inl ⟨(), rfl⟩, Or.inr ⟨(), rfl⟩]⟩

theorem sharedDecl_overlap (uL uR : Bool) (F : Matrix Unit Unit ℚ) (a b : ℚ) (s : ℚˣ) :
    (sharedDecl uL uR F a b s).OverlapsOnlyShared :=
  ⟨fun _ _ h => Bool.false_ne_true h, fun _ _ _ => ⟨(), rfl, rfl⟩⟩

theorem sharedDecl_boundary (uL uR : Bool) (F : Matrix Unit Unit ℚ) (a b : ℚ) (s : ℚˣ) :
    (sharedDecl uL uR F a b s).sharedFaceBoundary () = 1 + (s : ℚ) := by
  simp [JoinDeclaration.sharedFaceBoundary, leftConstituent,
    rightConstituent, faceComplex, Matrix.mulVec, dotProduct]

theorem sharedDecl_pumps (uL uR : Bool) (F : Matrix Unit Unit ℚ) (a b : ℚ) (s : ℚˣ) :
    (sharedDecl uL uR F a b s).PumpsOnClock := by
  rintro (p | p) <;> exact p.elim

/-- [definition] The base declaration: units agree, the identity join, the right face reversed. -/
abbrev baseDecl : JoinDeclaration (leftConstituent true) (rightConstituent true) :=
  sharedDecl true true 1 1 (-1) (-1)

/-- [established-bounded; formal-checked] **Two constituents sharing a face glue**, and the shared
face is silent in the whole. -/
theorem base_glues : baseDecl.Glues :=
  ⟨sharedDecl_units _ _ _ _ _, by simp [JoinDeclaration.PowerCancels],
    fun side => by
      cases side
      · exact faceEmbedding_commutes_shared false 1 (by simp)
      · exact faceEmbedding_commutes_shared true (-1) (by simp),
    fun side => by cases side <;> exact faceEmbedding_injective _ _ _ _,
    sharedDecl_covers _ _ _ _ _ _, fun _ => rfl, sharedDecl_overlap _ _ _ _ _ _,
    fun _ => by
      show (sharedDecl true true 1 1 (-1) (-1)).sharedFaceBoundary () = 0
      rw [sharedDecl_boundary]; simp,
    sharedDecl_pumps _ _ _ _ _ _⟩

/-- [established-bounded; formal-checked] So `interconnect` returns their Holarchy. -/
theorem base_interconnect :
    ∃ h, interconnect (leftConstituent true) (rightConstituent true) baseDecl = .ok h :=
  (interconnect_ok_iff _).mpr base_glues

/-- [counterexample; formal-checked] **A unit mismatch is returned as such**: the right
constituent carries its shared port in another unit. -/
theorem unitMismatch_witness :
    ∃ t ht, interconnect (leftConstituent true) (rightConstituent false)
      (sharedDecl true false 1 1 (-1) (-1)) = .error (.unitMismatch t ht) := by
  have hu : ¬ (sharedDecl true false 1 1 (-1) (-1)).UnitsAgree := fun h => by
    simpa [leftConstituent, rightConstituent] using h ()
  unfold interconnect
  rw [dif_neg hu]
  exact ⟨_, _, rfl⟩

/-- [proved-derived; formal-checked] With both flows oriented the same way the join doubles the
interface power instead of cancelling it: `2 ⟨e, f⟩`. -/
theorem interfacePower_same_orientation {τ : Type*} [Fintype τ] [DecidableEq τ]
    (q : Bond ℚ τ) : interfacePower (-1 : Matrix τ τ ℚ) 1 q = 2 * power q := by
  simp only [interfacePower, joinBond, power, Matrix.neg_mulVec, one_mulVec, neg_neg]
  ring

/-- [counterexample; formal-checked] **An uncancelled join is returned as such**: both flows are
oriented the same way (`F = −1`). -/
theorem uncancelledPower_witness :
    ∃ q hq, interconnect (leftConstituent true) (rightConstituent true)
      (sharedDecl true true (-1) 1 (-1) (-1)) = .error (.uncancelledPower q hq) := by
  have hp : ¬ (sharedDecl true true (-1) 1 (-1) (-1)).PowerCancels := fun h => by
    have := congrFun (congrFun h ()) ()
    simp at this
    norm_num at this
  unfold interconnect
  rw [dif_pos (sharedDecl_units _ _ _ _ _), dif_neg hp]
  exact ⟨_, _, rfl⟩

/-- [counterexample; formal-checked] **A non-commuting embedding is returned as such**: the glued
complex gives the right region the coefficient `+1` while the right face is embedded reversed, so
the right square reads `1` against `−1`. -/
theorem nonCommutingCells_witness :
    ∃ side hs, interconnect (leftConstituent true) (rightConstituent true)
      (sharedDecl true true 1 1 1 (-1)) = .error (.nonCommutingCells side hs) := by
  have hp : (sharedDecl true true 1 1 1 (-1)).PowerCancels := by
    simp [JoinDeclaration.PowerCancels]
  have hc : ¬ ∀ side, (sharedDecl true true 1 1 1 (-1)).CellsCommute side := fun h => by
    have := congrFun (congrFun (h .right).2 ()) ()
    rw [Matrix.mul_apply, Matrix.mul_apply] at this
    simp [CellEmbedding.m₁, CellEmbedding.m₂, sharedDecl, faceEmbedding,
      sharedComplex, faceComplex, rightConstituent, 
      ] at this
    norm_num at this
  unfold interconnect
  rw [dif_pos (sharedDecl_units _ _ _ _ _), dif_pos hp, dif_neg hc]
  exact ⟨_, _, rfl⟩

/-- [definition] Two regions both bounded by one face with coefficient `1`. -/
abbrev twoRegionComplex : CellComplex ℚ where
  C₀ := Empty
  C₁ := Unit
  C₂ := Bool
  d₁ := 0
  d₂ := fun _ _ => 1
  dd := by ext i; exact i.elim

/-- [definition] A left constituent whose complex has two regions on its one face. -/
abbrev splitLeftConstituent : Constituent ℚ Bool Empty Empty (Empty ⊕ Unit) Empty where
  holon := coholonLeft
  complex := twoRegionComplex
  interior := fun r => if r then 1 else 0
  unit := fun _ => true
  portFace := fun _ => ()
  Nav := Empty
  navigator := fun x => x.elim
  pumpNavigator := fun x => x.elim

/-- [definition] Its two regions are merged into one glued region. -/
abbrev mergeDecl : JoinDeclaration splitLeftConstituent (rightConstituent true) where
  flowGain := 1
  effortGain := 1
  glued := sharedComplex 1 (-1)
  leftCells := ⟨fun x => Empty.elim x, fun _ => (), fun _ => false, fun x => Empty.elim x,
    fun _ => 1, fun _ => 1⟩
  rightCells := faceEmbedding (sharedComplex 1 (-1)) () true (-1)
  jointRate := 1

/-- [counterexample; formal-checked] **A degenerate embedding is returned as such**: it commutes
with the boundaries, but it merges two regions of the left constituent. -/
theorem degenerateCells_witness :
    ∃ side hs, interconnect splitLeftConstituent (rightConstituent true) mergeDecl =
      .error (.degenerateCells side hs) := by
  have hu : mergeDecl.UnitsAgree := fun _ => rfl
  have hp : mergeDecl.PowerCancels := by simp [JoinDeclaration.PowerCancels]
  have hc : ∀ side, mergeDecl.CellsCommute side := by
    intro side
    cases side
    · refine ⟨by ext i; exact i.elim, ?_⟩
      ext i j
      rw [Matrix.mul_apply, Matrix.mul_apply]
      simp [CellEmbedding.m₁, CellEmbedding.m₂, mergeDecl, sharedComplex,
        twoRegionComplex, splitLeftConstituent]
    · exact faceEmbedding_commutes_shared true (-1) (by simp)
  have hi : ¬ ∀ side, mergeDecl.CellsInjective side := fun h => by
    have := (h .left).2.2 (a₁ := false) (a₂ := true) rfl
    exact Bool.false_ne_true this
  unfold interconnect
  rw [dif_pos hu, dif_pos hp, dif_pos hc, dif_neg hi]
  exact ⟨_, _, rfl⟩

/-- [definition] One face bounding two regions and a third region the constituents leave out. -/
abbrev coverComplex : CellComplex ℚ where
  C₀ := Empty
  C₁ := Unit
  C₂ := Option Bool
  d₁ := 0
  d₂ := fun _ r => match r with
    | some true => -1
    | some false => 1
    | none => 0
  dd := by ext i; exact i.elim

/-- [definition] The two constituents embedded in it. -/
abbrev coverDecl : JoinDeclaration (leftConstituent true) (rightConstituent true) where
  flowGain := 1
  effortGain := 1
  glued := coverComplex
  leftCells := faceEmbedding coverComplex () (some false) 1
  rightCells := faceEmbedding coverComplex () (some true) (-1)
  jointRate := 1

/-- [counterexample; formal-checked] **A glued cell of neither constituent is returned as such.** -/
theorem uncoveredCells_witness :
    ∃ hs, interconnect (leftConstituent true) (rightConstituent true) coverDecl =
      .error (.uncoveredCells hs) := by
  have hu : coverDecl.UnitsAgree := fun _ => rfl
  have hp : coverDecl.PowerCancels := by simp [JoinDeclaration.PowerCancels]
  have hc : ∀ side, coverDecl.CellsCommute side := by
    intro side
    cases side <;> refine ⟨by ext i; exact i.elim, ?_⟩ <;> ext i j <;>
      rw [Matrix.mul_apply, Matrix.mul_apply] <;>
      simp [CellEmbedding.m₁, CellEmbedding.m₂, coverDecl, faceEmbedding,
        coverComplex, faceComplex, 
        ]
  have hi : ∀ side, coverDecl.CellsInjective side := by
    intro side; cases side <;> exact faceEmbedding_injective _ _ _ _
  have hcov : ¬ coverDecl.Covers := fun h => by
    rcases h.2.2 none with ⟨_, h⟩ | ⟨_, h⟩ <;> simp [coverDecl, faceEmbedding] at h
  unfold interconnect
  rw [dif_pos hu, dif_pos hp, dif_pos hc, dif_pos hi, dif_neg hcov]
  exact ⟨_, rfl⟩

/-- [definition] Two faces and two regions: the left region is bounded by face `false`, the right
region by face `true` reversed. -/
abbrev splitComplex : CellComplex ℚ where
  C₀ := Empty
  C₁ := Bool
  C₂ := Bool
  d₁ := 0
  d₂ := fun e r => if e = r then (if r then -1 else 1) else 0
  dd := by ext i; exact i.elim

/-- [definition] The two constituents' shared port lands on two different glued faces. -/
abbrev splitDecl : JoinDeclaration (leftConstituent true) (rightConstituent true) where
  flowGain := 1
  effortGain := 1
  glued := splitComplex
  leftCells := faceEmbedding splitComplex false false 1
  rightCells := faceEmbedding splitComplex true true (-1)
  jointRate := 1

/-- [counterexample; formal-checked] **An unidentified shared face is returned as such**: the shared
port sits on face `false` from the left and on face `true` from the right. -/
theorem unidentifiedSharedFace_witness :
    ∃ t ht, interconnect (leftConstituent true) (rightConstituent true) splitDecl =
      .error (.unidentifiedSharedFace t ht) := by
  have hu : splitDecl.UnitsAgree := fun _ => rfl
  have hp : splitDecl.PowerCancels := by simp [JoinDeclaration.PowerCancels]
  have hc : ∀ side, splitDecl.CellsCommute side := by
    intro side
    cases side <;> refine ⟨by ext i; exact i.elim, ?_⟩ <;> ext i j <;> cases i <;>
      rw [Matrix.mul_apply, Matrix.mul_apply] <;>
      simp [CellEmbedding.m₁, CellEmbedding.m₂, splitDecl, faceEmbedding,
        splitComplex, faceComplex]
  have hi : ∀ side, splitDecl.CellsInjective side := by
    intro side; cases side <;> exact faceEmbedding_injective _ _ _ _
  have hcov : splitDecl.Covers :=
    ⟨fun v => Empty.elim v, fun e => by cases e; exacts [Or.inl ⟨(), rfl⟩, Or.inr ⟨(), rfl⟩],
      fun r => by cases r; exacts [Or.inl ⟨(), rfl⟩, Or.inr ⟨(), rfl⟩]⟩
  have hid : ¬ ∀ t, splitDecl.SharedFaceIdentified t := fun h => by
    have := h ()
    simp [JoinDeclaration.SharedFaceIdentified, splitDecl, faceEmbedding] at this
  unfold interconnect
  rw [dif_pos hu, dif_pos hp, dif_pos hc, dif_pos hi, dif_pos hcov, dif_neg hid]
  exact ⟨_, _, rfl⟩

/-- [definition] Both constituents' regions land on the one region of `faceComplex`. -/
abbrev overlapDecl : JoinDeclaration (leftConstituent true) (rightConstituent true) where
  flowGain := 1
  effortGain := 1
  glued := faceComplex
  leftCells := faceEmbedding faceComplex () () 1
  rightCells := faceEmbedding faceComplex () () 1
  jointRate := 1

/-- [counterexample; formal-checked] **A stray overlap is returned as such**: the two constituents'
regions are glued onto one region. -/
theorem strayOverlap_witness :
    ∃ hs, interconnect (leftConstituent true) (rightConstituent true) overlapDecl =
      .error (.strayOverlap hs) := by
  have hu : overlapDecl.UnitsAgree := fun _ => rfl
  have hp : overlapDecl.PowerCancels := by simp [JoinDeclaration.PowerCancels]
  have hc : ∀ side, overlapDecl.CellsCommute side := by
    intro side
    cases side <;> refine ⟨by ext i; exact i.elim, ?_⟩ <;> ext i j <;>
      rw [Matrix.mul_apply, Matrix.mul_apply] <;>
      simp [CellEmbedding.m₁, CellEmbedding.m₂, overlapDecl, faceEmbedding,
        faceComplex]
  have hi : ∀ side, overlapDecl.CellsInjective side := by
    intro side; cases side <;> exact faceEmbedding_injective _ _ _ _
  have hcov : overlapDecl.Covers :=
    ⟨fun v => Empty.elim v, fun _ => Or.inl ⟨(), rfl⟩, fun _ => Or.inl ⟨(), rfl⟩⟩
  have hid : ∀ t, overlapDecl.SharedFaceIdentified t := fun _ => rfl
  have hov : ¬ overlapDecl.OverlapsOnlyShared := fun h => h.1 () () rfl
  unfold interconnect
  rw [dif_pos hu, dif_pos hp, dif_pos hc, dif_pos hi, dif_pos hcov, dif_pos hid, dif_neg hov]
  exact ⟨_, rfl⟩

/-- [counterexample; formal-checked] **An uncancelled shared face is returned as such**: the right
face is embedded with the left one's orientation, so the shared face bounds the whole with
coefficient `2`, and the face-read port flows do not obey the identity join. -/
theorem sharedFaceUncancelled_witness :
    ∃ t ht, interconnect (leftConstituent true) (rightConstituent true)
      (sharedDecl true true 1 1 1 1) = .error (.sharedFaceUncancelled t ht) := by
  have hp : (sharedDecl true true 1 1 1 1).PowerCancels := by
    simp [JoinDeclaration.PowerCancels]
  have hc : ∀ side, (sharedDecl true true 1 1 1 1).CellsCommute side := by
    intro side
    cases side
    · exact faceEmbedding_commutes_shared false 1 (by simp)
    · exact faceEmbedding_commutes_shared true 1 (by simp)
  have hi : ∀ side, (sharedDecl true true 1 1 1 1).CellsInjective side := by
    intro side; cases side <;> exact faceEmbedding_injective _ _ _ _
  have hcan : ¬ ∀ t, (sharedDecl true true 1 1 1 1).SharedFaceCancels t := fun h => by
    have := h ()
    rw [JoinDeclaration.SharedFaceCancels, sharedDecl_boundary] at this
    norm_num at this
  unfold interconnect
  rw [dif_pos (sharedDecl_units _ _ _ _ _), dif_pos hp, dif_pos hc, dif_pos hi,
    dif_pos (sharedDecl_covers _ _ _ _ _ _),
    dif_pos (show ∀ t, (sharedDecl true true 1 1 1 1).SharedFaceIdentified t from fun _ => rfl),
    dif_pos (sharedDecl_overlap _ _ _ _ _ _), dif_neg hcan]
  exact ⟨_, _, rfl⟩

/-! ### Pumps on a joint clock -/

/-- [definition] A passive coholon on one shared port with one pump. -/
def pumpedHolonLeft : PortHolon ℚ Empty Empty (Empty ⊕ Unit) Unit where
  D := passiveCoholon ℚ _
  dirac := passiveCoholon_isDirac
  Q := 0
  Q_symm := by simp
  R := 0

/-- [definition] Its mirror on the right. -/
def pumpedHolonRight : PortHolon ℚ Empty Empty (Unit ⊕ Empty) Unit where
  D := passiveCoholon ℚ _
  dirac := passiveCoholon_isDirac
  Q := 0
  Q_symm := by simp
  R := 0

/-- [definition] The left constituent with one pump driven by one navigator of rate `r`. -/
abbrev pumpedLeft (r : ℚ) : Constituent ℚ Bool Empty Empty (Empty ⊕ Unit) Unit where
  holon := pumpedHolonLeft
  complex := faceComplex
  interior := fun _ => 1
  unit := fun _ => true
  portFace := fun _ => ()
  Nav := Unit
  navigator := fun _ => navAt r
  pumpNavigator := fun _ => ()

/-- [definition] Its mirror on the right. -/
abbrev pumpedRight (r : ℚ) : Constituent ℚ Bool Empty Empty (Unit ⊕ Empty) Unit where
  holon := pumpedHolonRight
  complex := faceComplex
  interior := fun _ => 1
  unit := fun _ => true
  portFace := fun _ => ()
  Nav := Unit
  navigator := fun _ => navAt r
  pumpNavigator := fun _ => ()

/-- [definition] The pumped constituents with pump rates `1` and `2`, sharing their face, on the
joint clock of rate `ω`. -/
abbrev pumpedDecl (ω : ℚ) : JoinDeclaration (pumpedLeft 1) (pumpedRight 2) where
  flowGain := 1
  effortGain := 1
  glued := sharedComplex 1 (-1)
  leftCells := faceEmbedding (sharedComplex 1 (-1)) () false 1
  rightCells := faceEmbedding (sharedComplex 1 (-1)) () true (-1)
  jointRate := ω

theorem pumpedDecl_cells (ω : ℚ) :
    (pumpedDecl ω).UnitsAgree ∧ (pumpedDecl ω).PowerCancels ∧
      (∀ side, (pumpedDecl ω).CellsCommute side) ∧ (∀ side, (pumpedDecl ω).CellsInjective side) ∧
      (pumpedDecl ω).Covers ∧ (∀ t, (pumpedDecl ω).SharedFaceIdentified t) ∧
      (pumpedDecl ω).OverlapsOnlyShared ∧ (∀ t, (pumpedDecl ω).SharedFaceCancels t) := by
  refine ⟨fun _ => rfl, by simp [JoinDeclaration.PowerCancels], fun side => ?_,
    fun side => by cases side <;> exact faceEmbedding_injective _ _ _ _,
    ⟨fun v => Empty.elim v, fun _ => Or.inl ⟨(), rfl⟩,
      fun r => by cases r; exacts [Or.inl ⟨(), rfl⟩, Or.inr ⟨(), rfl⟩]⟩, fun _ => rfl,
    ⟨fun _ _ h => Bool.false_ne_true h, fun _ _ _ => ⟨(), rfl, rfl⟩⟩, fun _ => ?_⟩
  · cases side
    · exact faceEmbedding_commutes_shared false 1 (by simp)
    · exact faceEmbedding_commutes_shared true (-1) (by simp)
  · simp [JoinDeclaration.SharedFaceCancels, JoinDeclaration.sharedFaceBoundary, 
      pumpedLeft, pumpedRight, faceComplex, Matrix.mulVec, dotProduct]

/-- [established-bounded; formal-checked] **Pumps join under a compatible joint clock**: rates `1`
and `2` on the joint clock of rate `1` glue. -/
theorem pumped_glues : (pumpedDecl 1).Glues := by
  obtain ⟨hu, hp, hc, hi, hcov, hid, hov, hcan⟩ := pumpedDecl_cells 1
  refine ⟨hu, hp, hc, hi, hcov, hid, hov, hcan, ?_⟩
  rintro (p | p)
  · exact ⟨1, by simp [Constituent.pumpRate, pumpedLeft, navAt]⟩
  · exact ⟨2, by simp [Constituent.pumpRate, pumpedRight, navAt]⟩

open Holonics.Aeon.Clock.Lock in
/-- [established-bounded; formal-checked] **Their pumps lock at `1/2`**: every aeon of `2m` ticks
of the second pump is a cycle of the pair. -/
theorem pumped_pumps_lock (m : ℤ) :
    IsCycle (jointReading ((pumpedLeft 1).pumpRate () / (pumpedRight 2).pumpRate ()) (2 * m)) := by
  obtain ⟨k, k', hk, hk', hlock⟩ := OnJointClock.lock (pumped_glues.2.2.2.2.2.2.2.2 (.inl ()))
    (pumped_glues.2.2.2.2.2.2.2.2 (.inr ())) (by simp)
  simp only [Sum.elim_inl, Sum.elim_inr, mul_one] at hk hk' hlock
  have hk'2 : k' = 2 := by
    have : ((2 : ℕ) : ℚ) = k' := by
      simpa [Constituent.pumpRate, pumpedRight, navAt] using hk'
    exact_mod_cast this.symm
  subst hk'2
  exact_mod_cast hlock (by norm_num) m

/-- [counterexample; formal-checked] **An incompatible joint clock is returned as such**: on the
joint clock of rate `2`, the pump of rate `1` is no whole multiple. -/
theorem incompatibleClocks_witness :
    ∃ p hp, interconnect (pumpedLeft 1) (pumpedRight 2) (pumpedDecl 2) =
      .error (.incompatibleClocks p hp) := by
  obtain ⟨hu, hp, hc, hi, hcov, hid, hov, hcan⟩ := pumpedDecl_cells 2
  have hk : ¬ (pumpedDecl 2).PumpsOnClock := fun h => by
    obtain ⟨k, hk⟩ := h (.inl ())
    simp only [Sum.elim_inl, Constituent.pumpRate, pumpedLeft, navAt] at hk
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · have : (1 : ℚ) = 2 * (2 * j) := by push_cast at hk; linarith
      have h' : (1 : ℤ) = 2 * (2 * j) := by exact_mod_cast this
      omega
    · have : (1 : ℚ) = 2 * (2 * j + 1) := by push_cast at hk; linarith
      have h' : (1 : ℤ) = 2 * (2 * j + 1) := by exact_mod_cast this
      omega
  unfold interconnect
  rw [dif_pos hu, dif_pos hp, dif_pos hc, dif_pos hi, dif_pos hcov, dif_pos hid, dif_pos hov,
    dif_pos hcan, dif_neg hk]
  exact ⟨_, _, rfl⟩

/-! ### The three arms of the interface gluing -/

/-- [established-bounded; formal-checked] **Plural.** Two passive coholons joined at one port with
no external ports: the shared flow is forced to zero and the shared effort is free, so the empty
whole bond is realized by every effort. -/
theorem plural_interface_witness :
    Nonempty (interfaceTower (passiveCoholon ℚ (Empty ⊕ Unit)) (passiveCoholon ℚ (Unit ⊕ Empty)) 1 1
      (0 : Bond ℚ (Empty ⊕ Empty))).CompatibleSection ∧
    ¬ Subsingleton (interfaceTower (passiveCoholon ℚ (Empty ⊕ Unit))
      (passiveCoholon ℚ (Unit ⊕ Empty)) 1 1 (0 : Bond ℚ (Empty ⊕ Empty))).CompatibleSection := by
  have hmem : ∀ c : Unit → ℚ, ((0, c) : Bond ℚ Unit) ∈ interfaceFibre (passiveCoholon ℚ (Empty ⊕ Unit))
      (passiveCoholon ℚ (Unit ⊕ Empty)) 1 1 (0 : Bond ℚ (Empty ⊕ Empty)) := by
    intro c
    refine ⟨?_, ?_⟩
    · rw [mem_passiveCoholon_iff]; funext i; rcases i with e | u
      · exact e.elim
      · rfl
    · rw [mem_passiveCoholon_iff]; funext i; rcases i with u | e
      · simp [partB, joinBond]
      · exact e.elim
  have hplural : ¬ Subsingleton (interfaceTower (passiveCoholon ℚ (Empty ⊕ Unit))
      (passiveCoholon ℚ (Unit ⊕ Empty)) 1 1 (0 : Bond ℚ (Empty ⊕ Empty))).CompatibleSection := by
    rw [interface_plural_iff]
    refine ⟨(0, 0), hmem 0, (0, fun _ => 1), hmem _, fun h => ?_⟩
    have := congrFun (congrArg Prod.snd h) ()
    simp at this
  exact ⟨⟨(interfaceSectionEquiv _ _ _ _ _).symm ⟨_, hmem 0⟩⟩, hplural⟩

/-- [definition] A wire: two ports on one node (KCL `f₁ + f₂ = 0`, KVL `e₁ = e₂`). -/
def wire : Matrix (Unit ⊕ Unit) Unit ℚ := fun _ _ => 1

theorem mem_wire_iff {b : Bond ℚ (Unit ⊕ Unit)} :
    b ∈ kirchhoff wire ↔ b.1 (.inl ()) + b.1 (.inr ()) = 0 ∧ b.2 (.inl ()) = b.2 (.inr ()) := by
  rw [mem_kirchhoff_iff]
  constructor
  · rintro ⟨hkcl, φ, hφ⟩
    refine ⟨?_, ?_⟩
    · have := congrFun hkcl ()
      simpa [wire, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using this
    · rw [← hφ]; simp [wire, Matrix.mulVec, dotProduct]
  · rintro ⟨hkcl, hkvl⟩
    refine ⟨?_, fun _ => b.2 (.inl ()), ?_⟩
    · funext u; simpa [wire, Matrix.mulVec, dotProduct, Fintype.sum_sum_type] using hkcl
    · funext i; rcases i with u | u <;> cases u <;> simp [wire, Matrix.mulVec, dotProduct, hkvl]

/-- [established-bounded; formal-checked] **Obstructed.** A wire whose external port is driven by
the flow `1`, joined to a passive coholon: the wire needs shared flow `−1`, the coholon admits
only `0`, so no shared bond realizes the whole bond. -/
theorem obstructed_interface_witness :
    IsEmpty (interfaceTower (kirchhoff wire) (passiveCoholon ℚ (Unit ⊕ Empty)) 1 1
      ((fun _ => 1, 0) : Bond ℚ (Unit ⊕ Empty))).CompatibleSection := by
  rw [(interfaceSectionEquiv _ _ _ _ _).isEmpty_congr]
  refine ⟨fun ⟨q, hA, hB⟩ => ?_⟩
  rw [mem_wire_iff] at hA
  rw [mem_passiveCoholon_iff] at hB
  have h1 := hA.1
  have h2 := congrFun hB (.inl ())
  simp [partA, partB, joinBond] at h1 h2
  rw [h2] at h1
  norm_num at h1

/-- [established-bounded; formal-checked] **Unique.** Two wires in series, driven by the flow `1`
in and `−1` out at zero effort: the shared bond is forced to flow `−1` at effort `0`. -/
theorem unique_interface_witness :
    Nonempty (interfaceTower (kirchhoff wire) (kirchhoff wire) 1 1
      ((Sum.elim (fun _ => 1) (fun _ => -1), 0) : Bond ℚ (Unit ⊕ Unit))).CompatibleSection ∧
    Subsingleton (interfaceTower (kirchhoff wire) (kirchhoff wire) 1 1
      ((Sum.elim (fun _ => 1) (fun _ => -1), 0) : Bond ℚ (Unit ⊕ Unit))).CompatibleSection := by
  set b : Bond ℚ (Unit ⊕ Unit) := (Sum.elim (fun _ => 1) (fun _ => -1), 0) with hb
  have hforced : ∀ q ∈ interfaceFibre (kirchhoff wire) (kirchhoff wire) 1 1 b,
      q = ((fun _ => -1), 0) := by
    rintro q ⟨hA, _⟩
    rw [mem_wire_iff] at hA
    obtain ⟨h1, h2⟩ := hA
    simp [partA, hb] at h1 h2
    refine Prod.ext (funext fun u => ?_) (funext fun u => ?_)
    · cases u; linarith
    · cases u; simpa using h2.symm
  have hmem : ((fun _ => -1), 0) ∈ interfaceFibre (kirchhoff wire) (kirchhoff wire) 1 1 b := by
    refine ⟨?_, ?_⟩
    · rw [mem_wire_iff]; simp [partA, hb]
    · rw [mem_wire_iff]; simp [partB, joinBond, hb]
  have hsub : Subsingleton (interfaceTower (kirchhoff wire) (kirchhoff wire) 1 1 b).CompatibleSection := by
    rw [(interfaceSectionEquiv _ _ _ _ _).subsingleton_congr]
    refine ⟨fun x y => Subtype.ext ?_⟩
    rw [hforced x.1 x.2, hforced y.1 y.2]
  exact ⟨⟨(interfaceSectionEquiv _ _ _ _ _).symm ⟨_, hmem⟩⟩, hsub⟩

end Witnesses

end Holonics.HolarchyCore
