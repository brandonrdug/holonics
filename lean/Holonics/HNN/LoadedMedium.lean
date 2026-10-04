import Holonics.HNN.RingLoci
import Holonics.HNN.LoadedRing

/-!
# HNN.LoadedMedium: the loaded ring block joined to the medium

[definition] #62 (owed by `HNN/LoadedRing`, `HNN/LocusMap`, `HNN/FactoredMedium` and
`HNN/RingLoci`: the loaded ring block on `Word.Medium`, so that the tick's class reads the pump's
phase). Every ring carries a resonator on its element port (`hnn::ring::ResonatorOperands`): the
element's output `e` drives it, and it returns the ring's next storage
(`hnn::word`, "The loaded field balance"):

```text
ring block  (x, (u, w)),   x = (s, arrivals) ∈ BlockM(g),   e = s-part of the element edge's image
r = 2C w + h e − h K_j u ,   ω = M_j⁻¹ r ,   (u, w) ↦ (u + hω, 2ω − w) ,   s′ = e − (2/Y) ω
j = t mod P at the field's absolute tick t                        (ResonatorOperands::phase_at)
```

* **The blocks** (`LoadedM`) are the word's blocks with the resonator's state `(u, w) ∈ V g × V g`
  at a ring and nothing at a contact (`ResState`).
* **The operator** at the absolute tick `t` (`loadedOp`) is the medium's block operator on the
  blocks' medium part (`liftOp`), with the element edge `g → g` loaded: its storage part is
  replaced by the resonator's return `s′` and its resonator part is the resonator's tick
  (`diagOp`, `loadCorr`). On the edge `g → g` it is `HNN/LoadedRing.loadedEdge` with
  `rest = T_(g,g) − store ∘ elem` (`loadedOp_self`), so its resonator closes its balance
  (`loadedOp_self_balance`).
* **An unloaded ring** is a ring whose resonator operands are zero: `ω = 0`, `s′ = e`. Releasing a
  resonator zeroes its operands, which unloads its ring.
* **The class** is the absolute tick: the word on a carry runs `k ↦ op(τ + k)`
  (`TickStanding.wordOp`), so each ring's pump phase `(τ + k) mod P_g` continues across receptions
  (`HNN/LoadedRing.resonance_shift`).
* **The constitution** (`LoadedAt`) is `HNN/RingLoci.RingsAt` with the resonator operands per ring.
  **The loci** (`LLocus`) are `RingLoci.RLocus` and `Resonator(g)`, read on the element edge
  `g → g` alone. The opening, the reading and the deposit act on the medium part as in `RingLoci`
  (`loadedOpen`, `liftRecv`, `projData`); a resonator moves by its own law from the data on its
  edge (`resData`).

[proved-derived; formal-checked] What is proved.

1. **The loaded operator is sparse** (`loadedOp_sparse`), and on the element edge it is the loaded
   edge of `HNN/LoadedRing` (`loadedOp_self`) whose resonator part closes the exact balance
   (`loadedOp_self_balance`).
2. **The locus map's laws hold** (`loadedLaw_lawful`) for every factor, ring-locus and resonator
   law, and **the quiet laws** (`loadedLaw_quiet`) for laws that keep a locus on empty data, so
   the standing law holds at the pump's phase (`loadedStanding`) and released loci stay released
   (`loaded_released_stays_released`).
3. **The Rust's rule keeps the retained loci** (`retained_rust_loaded`) at `e_last = 2|B|`: the
   medium's loci by the medium's rule (the ring loci by `RingLoci.retained_rust_ring`), and a
   resonator by `element(g)` (`Diamond::retains(Resonator(g))`, `HNN/LoadedRing.resonatorRule_iff`),
   since its only reading edge is `g → g`. Hence **the Rust's collapse is sufficient for every
   per-locus law** (`loaded_collapse_sufficient`), at every pump phase, and on the ring loci of
   `HNN/RingLoci` (`loaded_ring_rust_collapse_sufficient`).

[open; source-inspected at `5b7712fd`] Here a resonator's law reads only its own operands and
the data on its edge. The Rust's resonator steps read beyond it: whether the reach passes its ring
decides whether its moves are held out of the joint certified step (`hnn::constitution`, the held
parts of `Locus::Resonator`), and otherwise they share that step, whose span factor `F(s)` reads
every resonator not certified passive (`HNN/FactoredMedium`, module header [open]). The joint step
on retained loci, with the carried statistics in the locus's state, is owed in #62. The executed
split and chart of the lattice word are `HNN/Ring`'s and `HNN/LatticeWord`'s; the resonator's held
momentum across a deposit is `HNN/HeldCommits` and the reception carry's `cross`, a parameter
here.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LoadedMedium

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open Holonics.HNN.TickFamily Holonics.HNN.TickStanding
open Holonics.HNN.Word Holonics.HNN.TickBlocks Holonics.HNN.LocusMap
open Holonics.HNN.MediumStanding Holonics.HNN.FactoredMedium Holonics.HNN.RingLoci
open Holonics.HNN.LoadedRing Holonics.HNN.Ring

universe u

/-! ## 1. The loaded blocks and the loaded operator -/

section Blocks

variable {Ring Contact : Type u} [DecidableEq Ring] [DecidableEq Contact]
variable {endRing : Contact × Bool → Ring}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]

variable (V) in
/-- [definition] **The resonator's state at a block**: `(u, w) ∈ V g × V g` at ring `g`, nothing
at a contact. -/
def ResState : Ring ⊕ Contact → Type u
  | .inl g => V g × V g
  | .inr _ => PUnit

instance instAddCommGroupResState (b : Ring ⊕ Contact) :
    AddCommGroup (ResState (Contact := Contact) V b) :=
  match b with
  | .inl g => inferInstanceAs (AddCommGroup (V g × V g))
  | .inr _ => inferInstanceAs (AddCommGroup PUnit)

instance instModuleResState (b : Ring ⊕ Contact) : Module ℝ (ResState (Contact := Contact) V b) :=
  match b with
  | .inl g => inferInstanceAs (Module ℝ (V g × V g))
  | .inr _ => inferInstanceAs (Module ℝ PUnit)

variable (endRing V Ch) in
/-- [definition] **The loaded blocks**: the word's block and the resonator's state. -/
abbrev LoadedM (b : Ring ⊕ Contact) : Type u := BlockM endRing V Ch b × ResState V b

/-- [definition] **The resonator operands of a ring** (`ResonatorOperands`): the pump's period `P`,
`C`, `D`, the stiffness `K_j` and the executed solve `M_j⁻¹` at each phase `j`, and the port
admittance `Y`. Zero operands unload the ring. -/
structure ResOp (W : Type u) [NormedAddCommGroup W] [InnerProductSpace ℝ W] : Type u where
  P : ℕ
  C : W →L[ℝ] W
  D : W →L[ℝ] W
  Kp : ℕ → W →L[ℝ] W
  Minvp : ℕ → W →L[ℝ] W
  Y : ℝ

/-- [definition] The released resonator: zero operands. -/
def ResOp.zero (W : Type u) [NormedAddCommGroup W] [InnerProductSpace ℝ W] : ResOp W :=
  ⟨1, 0, 0, fun _ => 0, fun _ => 0, 0⟩

/-- [definition] **The medium's operator on the loaded blocks**: the block operator on the medium
part, zero into the resonator part. -/
def liftOp (T : BlockOp ℝ (BlockM endRing V Ch)) : BlockOp ℝ (LoadedM endRing V Ch) :=
  fun y z => (LinearMap.inl ℝ _ _).comp ((T y z).comp (LinearMap.fst ℝ _ _))

/-- [definition] **A diagonal correction**: `D b` on the edge `b → b`, zero elsewhere. -/
def diagOp {B : Type*} [DecidableEq B] {M : B → Type*} [∀ b, AddCommGroup (M b)]
    [∀ b, Module ℝ (M b)] (D : (b : B) → M b →ₗ[ℝ] M b) : BlockOp ℝ M :=
  fun y z => if h : z = y then h ▸ D z else 0

theorem diagOp_self {B : Type*} [DecidableEq B] {M : B → Type*} [∀ b, AddCommGroup (M b)]
    [∀ b, Module ℝ (M b)] (D : (b : B) → M b →ₗ[ℝ] M b) (b : B) : diagOp D b b = D b := by
  simp [diagOp]

theorem diagOp_ne {B : Type*} [DecidableEq B] {M : B → Type*} [∀ b, AddCommGroup (M b)]
    [∀ b, Module ℝ (M b)] (D : (b : B) → M b →ₗ[ℝ] M b) {y z : B} (h : z ≠ y) :
    diagOp D y z = 0 := by
  simp only [diagOp, dif_neg h]

/-- [definition] The element's output at ring `g`: the storage part of the element edge's image. -/
def elemMap (T : BlockOp ℝ (BlockM endRing V Ch)) (g : Ring) :
    BlockM endRing V Ch (.inl g) →ₗ[ℝ] V g :=
  (LinearMap.fst ℝ (V g) (Port endRing g → V g)).comp (T (.inl g) (.inl g))

/-- [definition] The ring's storage written into its block: `s ↦ (s, 0)`. -/
def storeMap (g : Ring) : V g →ₗ[ℝ] BlockM endRing V Ch (.inl g) :=
  LinearMap.inl ℝ (V g) (Port endRing g → V g)

/-- [definition] **The resonator's tick on the ring block** at the field's tick `t`:
`(x, p) ↦ stepMap C K_j M_j⁻¹ Y h (p, e)` with `e` the element's output and `j = t mod P`. -/
def resStep (T : BlockOp ℝ (BlockM endRing V Ch)) (g : Ring) (o : ResOp (V g)) (h : ℝ) (t : ℕ) :
    LoadedM endRing V Ch (.inl g) →ₗ[ℝ] (V g × V g) × V g :=
  (stepMap o.C (stiffAt o.Kp o.P t) (o.Minvp (phaseAt o.P t)) o.Y h : (V g × V g) × V g →L[ℝ] _)
    |>.toLinearMap.comp
      ((LinearMap.snd ℝ (BlockM endRing V Ch (.inl g))
          (ResState (Contact := Contact) V (.inl g))).prod
        ((elemMap T g).comp (LinearMap.fst ℝ (BlockM endRing V Ch (.inl g))
          (ResState (Contact := Contact) V (.inl g)))))

/-- [definition] **The load's correction at a ring**: the storage part becomes `s′ − e + e = s′`
and the resonator part its tick. Zero at a contact. -/
def loadCorr (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (g : Ring) → ResOp (V g)) (h : ℝ)
    (t : ℕ) : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b →ₗ[ℝ] LoadedM endRing V Ch b
  | .inl g =>
    ((storeMap g).comp ((LinearMap.snd ℝ (V g × V g) (V g)).comp (resStep T g (res g) h t) -
        (elemMap T g).comp (LinearMap.fst ℝ (BlockM endRing V Ch (.inl g))
          (ResState (Contact := Contact) V (.inl g))))).prod
      ((LinearMap.fst ℝ (V g × V g) (V g)).comp (resStep T g (res g) h t))
  | .inr _ => 0

/-- [definition] **The loaded operator** at the field's tick `t`: the medium's block operator with
every ring's element edge loaded by its resonator at the phase `t mod P_g`. -/
def loadedOp (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (g : Ring) → ResOp (V g)) (h : ℝ)
    (t : ℕ) : BlockOp ℝ (LoadedM endRing V Ch) :=
  fun y z => liftOp T y z + diagOp (loadCorr T res h t) y z

/-- [proved-derived; formal-checked] **The loaded operator is sparse** on any graph with
self-edges on which the medium's operator is sparse. -/
theorem loadedOp_sparse [Fintype Ring] [Fintype Contact]
    {adj : Ring ⊕ Contact → Ring ⊕ Contact → Prop} (hrefl : ∀ b, adj b b)
    {T : BlockOp ℝ (BlockM endRing V Ch)} (hT : Sparse adj T)
    (res : (g : Ring) → ResOp (V g)) (h : ℝ) (t : ℕ) : Sparse adj (loadedOp T res h t) := by
  intro y z hzy
  have hne : z ≠ y := fun he => hzy (he ▸ hrefl z)
  simp only [loadedOp, liftOp, hT y z hzy, LinearMap.zero_comp, LinearMap.comp_zero,
    diagOp_ne _ hne, add_zero]

/-- [proved-derived; formal-checked] **On the element edge the loaded operator is the loaded edge**
of `HNN/LoadedRing` at the phase `t mod P_g`, with drive `e` the element's output, the storage
written back by `store`, and `rest = T_(g,g) − store ∘ elem`. -/
theorem loadedOp_self (T : BlockOp ℝ (BlockM endRing V Ch)) (res : (g : Ring) → ResOp (V g))
    (h : ℝ) (t : ℕ) (g : Ring) (x : BlockM endRing V Ch (.inl g)) (p : V g × V g) :
    (loadedOp T res h t (.inl g) (.inl g) (x, p) : BlockM endRing V Ch (.inl g) × (V g × V g)) =
      loadedEdge (T (.inl g) (.inl g) - (storeMap g).comp (elemMap T g)) (elemMap T g)
        (storeMap g) (res g).C (stiffAt (res g).Kp (res g).P t)
        ((res g).Minvp (phaseAt (res g).P t)) (res g).Y h (x, p) := by
  rw [loadedEdge_apply, loadedOp, LinearMap.add_apply, diagOp_self]
  refine Prod.ext ?_ ?_
  · show T (.inl g) (.inl g) x + storeMap g ((stepMap (res g).C (stiffAt (res g).Kp (res g).P t)
        ((res g).Minvp (phaseAt (res g).P t)) (res g).Y h (p, elemMap T g x)).2 - elemMap T g x) = _
    rw [map_sub, LinearMap.sub_apply, LinearMap.comp_apply]
    abel_nf
  · show (0 : V g × V g) + (stepMap (res g).C (stiffAt (res g).Kp (res g).P t)
        ((res g).Minvp (phaseAt (res g).P t)) (res g).Y h (p, elemMap T g x)).1 = _
    exact zero_add _

/-- [proved-derived; formal-checked] **The loaded edge's resonator closes its balance**
(`HNN/LoadedRing.loadedEdge_balance`): at a right inverse of `M_j`, its energy at the phase's
stiffness after the tick, less the energy at the previous stiffness `K`, is the pump's, the port's
and the dissipation's terms, with drive the element's output. -/
theorem loadedOp_self_balance (T : BlockOp ℝ (BlockM endRing V Ch))
    (res : (g : Ring) → ResOp (V g)) (h : ℝ) (t : ℕ) (g : Ring) (K : V g →L[ℝ] V g)
    (hC : ∀ x y, inner ℝ ((res g).C x) y = inner ℝ x ((res g).C y))
    (hK' : ∀ x y, inner ℝ (stiffAt (res g).Kp (res g).P t x) y =
      inner ℝ x (stiffAt (res g).Kp (res g).P t y))
    (hY : (res g).Y ≠ 0)
    (hM : ∀ v, ringOperator (res g).C (res g).D (stiffAt (res g).Kp (res g).P t) (res g).Y h
      ((res g).Minvp (phaseAt (res g).P t) v) = v)
    (x : BlockM endRing V Ch (.inl g)) (p : V g × V g) :
    contactEnergy (res g).C (stiffAt (res g).Kp (res g).P t)
        (loadedOp T res h t (.inl g) (.inl g) (x, p) :
          BlockM endRing V Ch (.inl g) × (V g × V g)).2.1
        (loadedOp T res h t (.inl g) (.inl g) (x, p) :
          BlockM endRing V Ch (.inl g) × (V g × V g)).2.2 - contactEnergy (res g).C K p.1 p.2 =
      (1 / 2 : ℝ) * inner ℝ p.1 ((stiffAt (res g).Kp (res g).P t - K) p.1) +
        h * (res g).Y / 4 * (‖elemMap T g x‖ ^ 2 - ‖(stepMap (res g).C
          (stiffAt (res g).Kp (res g).P t) ((res g).Minvp (phaseAt (res g).P t)) (res g).Y h
            (p, elemMap T g x)).2‖ ^ 2) -
        h * inner ℝ ((res g).Minvp (phaseAt (res g).P t) (ringRight (res g).C
            (stiffAt (res g).Kp (res g).P t) h p.1 p.2 (elemMap T g x)))
          ((res g).D ((res g).Minvp (phaseAt (res g).P t) (ringRight (res g).C
            (stiffAt (res g).Kp (res g).P t) h p.1 p.2 (elemMap T g x)))) := by
  rw [loadedOp_self]
  exact loadedEdge_balance _ _ _ _ _ _ _ _ hC hK' hY hM x p

end Blocks

/-! ## 2. The law with the loaded blocks -/

section Law

variable {Ring Contact : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact]
variable {endRing : Contact × Bool → Ring}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]
variable {Con Loc : Type*} {Ref : Ring ⊕ Contact → Type*} {Cls Λ Mo Cell Crib : Type*}

variable (V Con) in
/-- [definition] **The loaded constitution**: the medium's constitution and each ring's resonator
operands. -/
structure LoadedAt where
  inner : Con
  res : (g : Ring) → ResOp (V g)

variable (Ring Loc) in
/-- [definition] **The loaded loci**: the medium's loci and each ring's `Resonator(g)`
(`hnn::constitution::Locus::Resonator`). -/
inductive LLocus
  | inner (ℓ : Loc)
  | resonator (g : Ring)

variable (endRing V Ch) in
/-- [definition] The deposit data on the loaded blocks. -/
abbrev LData : Type u :=
  (y z : Ring ⊕ Contact) → List (LoadedM endRing V Ch z × Module.Dual ℝ (LoadedM endRing V Ch y))

/-- [definition] **The data the medium's loci read**: each datum's medium part, its feature's
block and its covector on the block. -/
def projData (d : LData endRing V Ch) : EdgeData endRing V Ch :=
  fun y z => (d y z).map fun t => (t.1.1, t.2.comp (LinearMap.inl ℝ _ _))

open Classical in
/-- [definition] **The data a resonator reads**: the data on its ring's element edge. -/
def resData (d : LData endRing V Ch) (g : Ring) : LData endRing V Ch :=
  fun y z => if z = .inl g ∧ y = .inl g then d y z else []

/-- [definition] **The reading on the loaded blocks**: the medium's receiving map on the block's
covector, the identity on the resonator's. -/
def liftRecv {b : Ring ⊕ Contact}
    (Rd : Module.Dual ℝ (BlockM endRing V Ch b) →ₗ[ℝ] Module.Dual ℝ (BlockM endRing V Ch b)) :
    Module.Dual ℝ (LoadedM endRing V Ch b) →ₗ[ℝ] Module.Dual ℝ (LoadedM endRing V Ch b) where
  toFun p := (Rd (p.comp (LinearMap.inl ℝ _ _))).comp (LinearMap.fst ℝ _ _) +
    p.comp ((LinearMap.inr ℝ _ _).comp (LinearMap.snd ℝ _ _))
  map_add' p q := by
    rw [LinearMap.add_comp, map_add, LinearMap.add_comp, LinearMap.add_comp]
    abel
  map_smul' c p := by
    rw [LinearMap.smul_comp, map_smul, LinearMap.smul_comp, LinearMap.smul_comp, smul_add,
      RingHom.id_apply]

variable (h₀ : ℝ)
  (cross : Λ → Λ → (b : Ring ⊕ Contact) → Ref b → Ref b →
    (LoadedM endRing V Ch b →ₗ[ℝ] LoadedM endRing V Ch b))
  (absorb : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b →ₗ[ℝ] LoadedM endRing V Ch b)
  (Ψo : (g : Ring) → ResOp (V g) → LData endRing V Ch → ResOp (V g))

open Classical in
/-- [definition] **The law with the loaded blocks**, from any law `L` on the medium's blocks: the
loaded operator at the class `L` reads and the field's absolute tick, the medium's loci read as
by `L` and each resonator on its ring's element edge, the opening and the reading on the medium
part, the medium's deposit on the data's medium part and each resonator's by its own law from the
data on its edge, and the release zeroing a released resonator. -/
def loadedLaw (L : TickLaw ℝ (BlockM endRing V Ch) Con Loc Ref Cls Λ Mo Cell Crib) :
    TickLaw ℝ (LoadedM endRing V Ch) (LoadedAt V Con) (LLocus Ring Loc) Ref (Cls × ℕ) Λ Mo Cell
      Crib where
  op c θ := loadedOp (L.op c.1 θ.inner) θ.res h₀ c.2
  reads
    | .inner ℓ, z, y => L.reads ℓ z y
    | .resonator g, z, y => z = .inl g ∧ y = .inl g
  refReads
    | .inner ℓ, b => L.refReads ℓ b
    | .resonator _, _ => False
  openReads
    | .inner ℓ, b => L.openReads ℓ b
    | .resonator _, _ => False
  recvReads
    | .inner ℓ, b => L.recvReads ℓ b
    | .resonator _, _ => False
  agreeOn
    | .inner ℓ, θ, θ' => L.agreeOn ℓ θ.inner θ'.inner
    | .resonator g, θ, θ' => θ.res g = θ'.res g
  ref θ := L.ref θ.inner
  recv θ b := liftRecv (L.recv θ.inner b)
  cls l t := (L.cls l t, t)
  openState θ l m b := (L.openState θ.inner l m b, 0)
  ticks := L.ticks
  cross := cross
  absorb := absorb
  ingestStep := L.ingestStep
  rekey := L.rekey
  apply θ d := ⟨L.apply θ.inner (projData d), fun g => Ψo g (θ.res g) (resData d g)⟩
  release keep θ :=
    ⟨L.release (fun ℓ => keep (.inner ℓ)) θ.inner,
      fun g => if keep (.resonator g) then θ.res g else ResOp.zero (V g)⟩

variable {h₀ cross absorb Ψo} {L : TickLaw ℝ (BlockM endRing V Ch) Con Loc Ref Cls Λ Mo Cell Crib}

/-- The loaded law. -/
local notation "LL" => loadedLaw h₀ cross absorb Ψo L

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] in
theorem projData_congr {d d' : LData endRing V Ch} {y z : Ring ⊕ Contact} (h : d y z = d' y z) :
    projData d y z = projData d' y z := by
  simp only [projData, h]

open Classical in
/-- [proved-derived; formal-checked] **The locus map's laws hold on the loaded blocks** whenever
they hold for the medium's law, for every resonator law. -/
theorem loadedLaw_lawful (hL : L.Lawful (blockAdj endRing)) : (LL).Lawful (blockAdj endRing) where
  sparse c θ := loadedOp_sparse blockAdj_refl (hL.sparse c.1 θ.inner) θ.res h₀ c.2
  reads_adj ℓ z y h := by
    cases ℓ with
    | inner ℓ => exact hL.reads_adj ℓ z y h
    | resonator g =>
      obtain ⟨rfl, rfl⟩ := h
      exact blockAdj_refl _
  op_reads c θ θ' y z h := by
    have hT : ∀ y' z', y' = y → z' = z → L.op c.1 θ.inner y' z' = L.op c.1 θ'.inner y' z' := by
      rintro y' z' rfl rfl
      exact hL.op_reads c.1 θ.inner θ'.inner y' z' fun ℓ hr => h (.inner ℓ) hr
    show loadedOp (L.op c.1 θ.inner) θ.res h₀ c.2 y z =
      loadedOp (L.op c.1 θ'.inner) θ'.res h₀ c.2 y z
    by_cases hzy : z = y
    · subst hzy
      simp only [loadedOp, diagOp_self, liftOp, hT z z rfl rfl]
      congr 1
      cases z with
      | inl g =>
        have hres : θ.res g = θ'.res g := h (.resonator g) ⟨rfl, rfl⟩
        simp only [loadCorr, resStep, elemMap, hT (.inl g) (.inl g) rfl rfl, hres]
      | inr a => rfl
    · simp only [loadedOp, liftOp, hT y z rfl rfl, diagOp_ne _ hzy]
  ref_reads θ θ' b h := hL.ref_reads θ.inner θ'.inner b fun ℓ hr => h (.inner ℓ) hr
  open_reads θ θ' l m b h := by
    show (L.openState θ.inner l m b, (0 : ResState V b)) = (L.openState θ'.inner l m b, 0)
    rw [hL.open_reads θ.inner θ'.inner l m b fun ℓ hr => h (.inner ℓ) hr]
  recv_reads θ θ' b h := by
    show liftRecv (L.recv θ.inner b) = liftRecv (L.recv θ'.inner b)
    rw [hL.recv_reads θ.inner θ'.inner b fun ℓ hr => h (.inner ℓ) hr]
  apply_local θ θ' d d' ℓ hθ hd := by
    cases ℓ with
    | inner ℓ =>
      exact hL.apply_local θ.inner θ'.inner (projData d) (projData d') ℓ hθ
        fun y z hr => projData_congr (hd y z hr)
    | resonator g =>
      show Ψo g (θ.res g) (resData d g) = Ψo g (θ'.res g) (resData d' g)
      have hrd : resData d g = resData d' g := by
        funext y z
        simp only [resData]
        split_ifs with hr
        · exact hd y z ⟨hr.1, hr.2⟩
        · rfl
      rw [show θ.res g = θ'.res g from hθ, hrd]
  release_keeps keep θ ℓ hk := by
    cases ℓ with
    | inner ℓ => exact hL.release_keeps (fun ℓ => keep (.inner ℓ)) θ.inner ℓ hk
    | resonator g =>
      show θ.res g = if keep (.resonator g) then θ.res g else ResOp.zero (V g)
      rw [if_pos hk]

omit [Fintype Ring] [Fintype Contact] in
/-- [proved-derived; formal-checked] **The quiet laws hold on the loaded blocks** whenever they
hold for the medium's law and each resonator law keeps its operands on empty data. -/
theorem loadedLaw_quiet (hQ : L.Quiet) (hΨo : ∀ g p, Ψo g p (fun _ _ => []) = p) :
    (LL).Quiet where
  refl ℓ θ := by
    cases ℓ with
    | inner ℓ => exact hQ.refl ℓ θ.inner
    | resonator g => exact rfl
  trans ℓ _ _ _ h₁ h₂ := by
    cases ℓ with
    | inner ℓ => exact hQ.trans ℓ _ _ _ h₁ h₂
    | resonator g => exact Eq.trans h₁ h₂
  apply_quiet θ d ℓ h := by
    cases ℓ with
    | inner ℓ =>
      refine hQ.apply_quiet θ.inner (projData d) ℓ fun y z hr => ?_
      simp only [projData, h y z hr, List.map_nil]
    | resonator g =>
      show θ.res g = Ψo g (θ.res g) (resData d g)
      have hrd : resData d g = fun _ _ => [] := by
        funext y z
        simp only [resData]
        split_ifs with hr
        · exact h y z ⟨hr.1, hr.2⟩
        · rfl
      rw [hrd, hΨo]

omit [Fintype Ring] [Fintype Contact] in
/-- [proved-derived; formal-checked] **The loaded opening is supported where the medium's is.** -/
theorem loadedOpen_supported {S : Set (Ring ⊕ Contact)}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) :
    ∀ θ l m, SupportedIn ((LL).openState θ l m) S := by
  intro θ l m b hb
  show (L.openState θ.inner l m b, (0 : ResState V b)) = 0
  rw [hopen θ.inner l m b hb]
  rfl

/-- [proved-derived; formal-checked] **The standing on the loaded blocks** (#62): the tick-indexed
standing law of `HNN/TickStanding` at the loaded law, each word running the pump's phase at the
field's absolute tick. -/
def loadedStanding (hL : L.Lawful (blockAdj endRing)) {S R : Set (Ring ⊕ Contact)}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) :
    Holonics.Foundation.Standing.StandingLaw
      (CarryGen Cell Crib (ReceiverFamily ℝ (LoadedM endRing V Ch) R))
      (Option ℕ × ReceiverReading ℝ (LoadedM endRing V Ch) R)
      (ValidResident (blockAdj endRing) LL S) (ValidResident (blockAdj endRing) LL S) ℝ :=
  tickStanding (L := LL) (adj := blockAdj endRing) (S := S) (R := R) (loadedLaw_lawful hL)
    (loadedOpen_supported hopen)

/-- [proved-derived; formal-checked] **On the loaded blocks a deposit between words never reopens a
released locus**, the resonators included. -/
theorem loaded_released_stays_released (hL : L.Lawful (blockAdj endRing)) (hQ : L.Quiet)
    (hΨo : ∀ g p, Ψo g p (fun _ _ => []) = p) {S R : Set (Ring ⊕ Contact)}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (LoadedM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) LL S)
    (h : StagedOff (blockAdj endRing) S R s.1) {ℓ : LLocus Ring Loc}
    (hℓ : ¬ TickStanding.Retained (blockAdj endRing) LL S R ℓ) :
    (LL).agreeOn ℓ ((LL).release (TickStanding.Retained (blockAdj endRing) LL S R) s.1.loci)
      (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) LL (loadedLaw_lawful hL) (loadedOpen_supported hopen)) w
        ⟨retain (blockAdj endRing) LL S R s.1, retain_valid s.2⟩).1.loci :=
  released_stays_released (loadedLaw_lawful hL) (loadedLaw_quiet hQ hΨo)
    (loadedOpen_supported hopen) w s h hℓ

omit [Fintype Ring] [Fintype Contact] in
/-- [proved-derived; formal-checked] **A medium locus is retained on the loaded blocks exactly when
it is retained by the medium's law**: the loaded law reads it on the same edges, references,
openings and readings. -/
theorem retained_inner_iff {S R : Set (Ring ⊕ Contact)} {ℓ : Loc} :
    TickStanding.Retained (blockAdj endRing) LL S R (.inner ℓ) ↔
      TickStanding.Retained (blockAdj endRing) L S R ℓ :=
  Iff.rfl

variable (endRing) in
/-- [definition] **The Rust's retention rule on the loaded blocks**: a medium locus by the
medium's rule `keep`, a resonator when the element of its ring is retained
(`Diamond::retains(Resonator(g))` is `element(g)`). -/
def LoadedRetained (keep : Loc → Prop) (S R : Set (Ring ⊕ Contact)) (e : ℕ) :
    LLocus Ring Loc → Prop
  | .inner ℓ => keep ℓ
  | .resonator g => LocusMap.Retained endRing S R e (.element g)

/-- [proved-derived; formal-checked] **The Rust's rule keeps the retained loci on the loaded
blocks** whenever the medium's rule keeps the medium's retained loci. A resonator is read only
on its ring's element edge `g → g`; a walk edge is in the continuing diamond at `2|B|`, where
`element(g)` is retained. -/
theorem retained_rust_loaded {S R : Set (Ring ⊕ Contact)} {keep : Loc → Prop}
    (hk : ∀ ℓ, TickStanding.Retained (blockAdj endRing) L S R ℓ → keep ℓ) {ℓ : LLocus Ring Loc}
    (h : TickStanding.Retained (blockAdj endRing) LL S R ℓ) :
    LoadedRetained endRing keep S R (2 * Fintype.card (Ring ⊕ Contact)) ℓ := by
  cases ℓ with
  | inner ℓ => exact hk ℓ h
  | resonator g =>
    rcases h with ⟨z, y, ⟨rfl, rfl⟩, hw⟩ | ⟨b, hb, -⟩ | ⟨b, hb, -⟩ | ⟨b, hb, -⟩
    · exact (inDiamond_continuing_iff (adj := blockAdj endRing) S R _ _).mpr hw
    · exact hb.elim
    · exact hb.elim
    · exact hb.elim

/-- [proved-derived; formal-checked] **The collapse the Rust runs is sufficient on the loaded
blocks** whenever the medium's rule keeps the medium's retained loci: releasing every locus the
rule does not retain at `e_last = 2|B|`, the resonators included, changes no admitted face of the
current word or of any pending word, after any word of the generators, at every pump phase. -/
theorem loaded_collapse_sufficient (hL : L.Lawful (blockAdj endRing)) {S R : Set (Ring ⊕ Contact)}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) {keep : Loc → Prop}
    (hk : ∀ ℓ, TickStanding.Retained (blockAdj endRing) L S R ℓ → keep ℓ)
    (q : Option ℕ × ReceiverReading ℝ (LoadedM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (LoadedM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) LL S) :
    observe LL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) LL (loadedLaw_lawful hL) (loadedOpen_supported hopen)) w
        ⟨{ s.1 with loci := (LL).release (LoadedRetained endRing keep S R
            (2 * Fintype.card (Ring ⊕ Contact))) s.1.loci }, s.2⟩).1 =
      observe LL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) LL (loadedLaw_lawful hL) (loadedOpen_supported hopen)) w
        s).1 :=
  keeps_sufficient (loadedLaw_lawful hL) (loadedOpen_supported hopen)
    (fun _ hℓ => retained_rust_loaded hk hℓ) q w s

end Law

/-! ## 3. The ring loci loaded -/

section Rings

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {FE : Ring → Type u} [∀ r, NormedAddCommGroup (FE r)] [∀ r, InnerProductSpace ℝ (FE r)]
  [∀ r, FiniteDimensional ℝ (FE r)]
variable {FC : Contact → Type u} [∀ a, NormedAddCommGroup (FC a)]
  [∀ a, InnerProductSpace ℝ (FC a)] [∀ a, FiniteDimensional ℝ (FC a)]
variable {Q : Ring → Type u} [∀ g, AddCommGroup (Q g)] [∀ g, Module ℝ (Q g)]
variable {U : Ring → Type u} [∀ g, AddCommGroup (U g)] [∀ g, Module ℝ (U g)]
variable {endRing : Contact × Bool → Ring} {Src : Set Ring}
variable {Λ Mo Cell Crib : Type*}
variable {h₀ : ℝ} {χ : LockChart ρ Q endRing} {src : Λ → Mo → (g : Ring) → U g}
  {ticks : Λ → Mo → ℕ}
  {cross₀ : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)}
  {absorb₀ : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b}
  {ingestStep : Cell → Λ × Mo → Λ × Mo} {rekey : Crib → Λ → Λ}
  {Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch →
    ElementFactors (V := V) (FE := FE) (ρ := ρ) r}
  {Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch →
    ChannelFactors (Ch := Ch) (FC := FC) a}
  {Ψq : (g : Ring) → Q g → EdgeData endRing V Ch → Q g}
  {Ψs : (g : Ring) → (U g →ₗ[ℝ] BlockM endRing V Ch (.inl g)) → EdgeData endRing V Ch →
    (U g →ₗ[ℝ] BlockM endRing V Ch (.inl g))}
  {Ψr : (g : Ring) →
    (Module.Dual ℝ (BlockM endRing V Ch (.inl g)) →ₗ[ℝ]
      Module.Dual ℝ (BlockM endRing V Ch (.inl g))) →
    EdgeData endRing V Ch →
    (Module.Dual ℝ (BlockM endRing V Ch (.inl g)) →ₗ[ℝ]
      Module.Dual ℝ (BlockM endRing V Ch (.inl g)))}
  {cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (LoadedM endRing V Ch b →ₗ[ℝ] LoadedM endRing V Ch b)}
  {absorb : (b : Ring ⊕ Contact) → LoadedM endRing V Ch b →ₗ[ℝ] LoadedM endRing V Ch b}
  {Ψo : (g : Ring) → ResOp (V g) → LData endRing V Ch → ResOp (V g)}

/-- The ring loci loaded at the section's operands. -/
local notation "LRL" => loadedLaw h₀ cross absorb Ψo (ringLaw (Cell := Cell) (Crib := Crib) h₀
  χ Src src ticks cross₀ absorb₀ ingestStep rekey Ψe Ψc Ψq Ψs Ψr)

/-- [proved-derived; formal-checked] **The collapse the Rust runs is sufficient on the ring loci
with their resonators loaded**, for every factor, ring-locus and resonator law
(`hnn::retention::collapse` under `Diamond::continuing`). Releasing every locus the Rust's rule
does not retain at `e_last = 2|B|` (the standings, source ports and resonators included) changes
no admitted face of the current word or of any pending word, after any word of the generators, at
every pump phase. -/
theorem loaded_ring_rust_collapse_sufficient {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hSrc : ∀ g ∈ Src, (.inl g : Ring ⊕ Contact) ∈ S)
    (q : Option ℕ × ReceiverReading ℝ (LoadedM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (LoadedM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) LRL S) :
    observe LRL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) LRL (loadedLaw_lawful ringLaw_lawful)
          (loadedOpen_supported (ringOpen_supported hSrc))) w
        ⟨{ s.1 with loci := (LRL).release (LoadedRetained endRing
            (RustRetained endRing Src S R (2 * Fintype.card (Ring ⊕ Contact))) S R
            (2 * Fintype.card (Ring ⊕ Contact))) s.1.loci }, s.2⟩).1 =
      observe LRL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) LRL (loadedLaw_lawful ringLaw_lawful)
          (loadedOpen_supported (ringOpen_supported hSrc))) w s).1 :=
  loaded_collapse_sufficient ringLaw_lawful (ringOpen_supported hSrc)
    (fun _ hℓ => retained_rust_ring hS hR hℓ) q w s

end Rings

end Holonics.HNN.LoadedMedium

#print axioms Holonics.HNN.LoadedMedium.loadedOp_sparse
#print axioms Holonics.HNN.LoadedMedium.loadedOp_self
#print axioms Holonics.HNN.LoadedMedium.loadedOp_self_balance
#print axioms Holonics.HNN.LoadedMedium.loadedLaw_lawful
#print axioms Holonics.HNN.LoadedMedium.loadedLaw_quiet
#print axioms Holonics.HNN.LoadedMedium.loadedOpen_supported
#print axioms Holonics.HNN.LoadedMedium.loadedStanding
#print axioms Holonics.HNN.LoadedMedium.loaded_released_stays_released
#print axioms Holonics.HNN.LoadedMedium.retained_inner_iff
#print axioms Holonics.HNN.LoadedMedium.retained_rust_loaded
#print axioms Holonics.HNN.LoadedMedium.loaded_collapse_sufficient
#print axioms Holonics.HNN.LoadedMedium.loaded_ring_rust_collapse_sufficient
