import ElementaryHolonics.Holon.Element
import ElementaryHolonics.Holon.Restriction

/-!
# Holon.Law: interact, receive, advance, restrict and pullback

[definition] The five statements the Rust core implements.

[proved-derived; formal-checked]

* **interact** — a Holon of Holons is a Holon: two port Holons joined at shared external ports
  form a port Holon with block storage and resistance and a composed Dirac structure
  (`PortHolon.interconnect`); energy and dissipation are additive (`storageEnergy_blocks`,
  `dissipation_blocks`); a composite bond is admitted exactly when some shared bond admits both
  sides (`PortHolon.mem_interconnect`).
* **receive** — the passive coholon (zero flow, every effort) is Dirac
  (`passiveCoholon_isDirac`) and reads an effort by a linear functional with zero power
  (`passive_reading`); any reading of its bond, linear or not, draws zero power
  (`coholon_reading_power`); an active receiver joined through an interface conductance `G`
  satisfies `P_(H→R) + P_(R→H) = −D_Σ`, `D_Σ = ⟨Δ, GΔ⟩ ≥ 0` when `G` is passive
  (`active_receiver_law`). As elements (plan phase 7): an exterior drive closes its own balance
  (`exterior_drive_balance`), a learned relation delivers its declared power
  (`learned_receiver_balance`), and the normalized face's Jacobian `J_p = diag p − p pᵀ` is
  symmetric (`softmaxJacobian_transpose`), so its covector return preserves power
  (`softmax_pullback_power`); its rows vanish on the simplex (`softmaxJacobian_mulVec_one`).
* **advance** — the implicit midpoint step has zero balance residual (`advance_law`).
* **restrict** — `kron_exact` and `scale_square_pow` (in `Holon.Restriction`).
* **pullback** — a port map moves efforts by its transpose and preserves power (`pullback_law`).
-/

noncomputable section

namespace Soma.Holonics.HolonCore

open Matrix

/-! ## 1. interact: a Holon of Holons is a Holon -/

section Interact

variable {𝕜 : Type*} [Field 𝕜]
variable {σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ]

/-- [definition] Pull the shared ports of `A` out to the right. -/
def splitA : Ports σA ρA (πA ⊕ τ) αA ≃ Ports σA ρA πA αA ⊕ τ where
  toFun
    | .inl s => .inl (.inl s)
    | .inr (.inl r) => .inl (.inr (.inl r))
    | .inr (.inr (.inl (.inl p))) => .inl (.inr (.inr (.inl p)))
    | .inr (.inr (.inl (.inr t))) => .inr t
    | .inr (.inr (.inr a)) => .inl (.inr (.inr (.inr a)))
  invFun
    | .inl (.inl s) => .inl s
    | .inl (.inr (.inl r)) => .inr (.inl r)
    | .inl (.inr (.inr (.inl p))) => .inr (.inr (.inl (.inl p)))
    | .inl (.inr (.inr (.inr a))) => .inr (.inr (.inr a))
    | .inr t => .inr (.inr (.inl (.inr t)))
  left_inv := by rintro (s | r | (p | t) | a) <;> rfl
  right_inv := by rintro ((s | r | p | a) | t) <;> rfl

/-- [definition] Pull the shared ports of `B` out to the left. -/
def splitB : Ports σB ρB (τ ⊕ πB) αB ≃ τ ⊕ Ports σB ρB πB αB where
  toFun
    | .inl s => .inr (.inl s)
    | .inr (.inl r) => .inr (.inr (.inl r))
    | .inr (.inr (.inl (.inl t))) => .inl t
    | .inr (.inr (.inl (.inr p))) => .inr (.inr (.inr (.inl p)))
    | .inr (.inr (.inr a)) => .inr (.inr (.inr (.inr a)))
  invFun
    | .inr (.inl s) => .inl s
    | .inr (.inr (.inl r)) => .inr (.inl r)
    | .inr (.inr (.inr (.inl p))) => .inr (.inr (.inl (.inr p)))
    | .inr (.inr (.inr (.inr a))) => .inr (.inr (.inr a))
    | .inl t => .inr (.inr (.inl (.inl t)))
  left_inv := by rintro (s | r | (t | p) | a) <;> rfl
  right_inv := by rintro (t | (s | r | p | a)) <;> rfl

/-- [definition] Merge the two sides kind by kind. -/
def mergeKinds : Ports σA ρA πA αA ⊕ Ports σB ρB πB αB ≃
    Ports (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB) where
  toFun
    | .inl (.inl s) => .inl (.inl s)
    | .inl (.inr (.inl r)) => .inr (.inl (.inl r))
    | .inl (.inr (.inr (.inl p))) => .inr (.inr (.inl (.inl p)))
    | .inl (.inr (.inr (.inr a))) => .inr (.inr (.inr (.inl a)))
    | .inr (.inl s) => .inl (.inr s)
    | .inr (.inr (.inl r)) => .inr (.inl (.inr r))
    | .inr (.inr (.inr (.inl p))) => .inr (.inr (.inl (.inr p)))
    | .inr (.inr (.inr (.inr a))) => .inr (.inr (.inr (.inr a)))
  invFun
    | .inl (.inl s) => .inl (.inl s)
    | .inr (.inl (.inl r)) => .inl (.inr (.inl r))
    | .inr (.inr (.inl (.inl p))) => .inl (.inr (.inr (.inl p)))
    | .inr (.inr (.inr (.inl a))) => .inl (.inr (.inr (.inr a)))
    | .inl (.inr s) => .inr (.inl s)
    | .inr (.inl (.inr r)) => .inr (.inr (.inl r))
    | .inr (.inr (.inl (.inr p))) => .inr (.inr (.inr (.inl p)))
    | .inr (.inr (.inr (.inr a))) => .inr (.inr (.inr (.inr a)))
  left_inv := by rintro ((s | r | p | a) | (s | r | p | a)) <;> rfl
  right_inv := by rintro ((s | s) | (r | r) | (p | p) | (a | a)) <;> rfl

variable [DecidableEq σA] [DecidableEq ρA] [DecidableEq πA] [DecidableEq αA]
  [DecidableEq σB] [DecidableEq ρB] [DecidableEq πB] [DecidableEq αB] [DecidableEq τ]

/-- [definition] **Interconnection of two port Holons** at the shared external ports `τ`:
storage and resistance are block products, the Dirac structures are composed. -/
def PortHolon.interconnect (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA)
    (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB) :
    PortHolon 𝕜 (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB) where
  D := (HolonCore.interconnect (A.D.map (bondReindex (𝕜 := 𝕜) splitA).toLinearMap)
      (B.D.map (bondReindex (𝕜 := 𝕜) splitB).toLinearMap)).map
    (bondReindex (𝕜 := 𝕜) mergeKinds).toLinearMap
  dirac := (interconnect_isDirac (A.dirac.reindex splitA) (B.dirac.reindex splitB)).reindex
    mergeKinds
  Q := Matrix.fromBlocks A.Q 0 0 B.Q
  Q_symm := by rw [Matrix.fromBlocks_transpose, A.Q_symm, B.Q_symm]; simp
  R := Matrix.fromBlocks A.R 0 0 B.R

omit [DecidableEq σA] [DecidableEq σB] in
/-- [proved-derived; formal-checked] **Energy is additive** over an interconnection. -/
theorem storageEnergy_blocks (QA : Matrix σA σA 𝕜) (QB : Matrix σB σB 𝕜) (xA : σA → 𝕜)
    (xB : σB → 𝕜) :
    storageEnergy (Matrix.fromBlocks QA 0 0 QB) (Sum.elim xA xB) =
      storageEnergy QA xA + storageEnergy QB xB := by
  simp only [storageEnergy, Matrix.fromBlocks_mulVec, zero_mulVec, add_zero, zero_add,
    dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_def]
  ring

omit [DecidableEq ρA] [DecidableEq ρB] in
/-- [proved-derived; formal-checked] **Dissipation is additive** over an interconnection. -/
theorem dissipation_blocks (RA : Matrix ρA ρA 𝕜) (RB : Matrix ρB ρB 𝕜) (fA : ρA → 𝕜)
    (fB : ρB → 𝕜) :
    Sum.elim fA fB ⬝ᵥ (Matrix.fromBlocks RA 0 0 RB *ᵥ Sum.elim fA fB) =
      fA ⬝ᵥ (RA *ᵥ fA) + fB ⬝ᵥ (RB *ᵥ fB) := by
  simp only [Matrix.fromBlocks_mulVec, zero_mulVec, add_zero, zero_add, dotProduct,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Function.comp_def]

/-- [proved-derived; formal-checked] **The interact law.** A bond of the composite is admitted
exactly when some shared bond `q` makes the `A` side admitted with `q` and the `B` side admitted
with `(−f_q, e_q)`. -/
theorem PortHolon.mem_interconnect (A : PortHolon 𝕜 σA ρA (πA ⊕ τ) αA)
    (B : PortHolon 𝕜 σB ρB (τ ⊕ πB) αB) (b : Bond 𝕜 (Ports (σA ⊕ σB) (ρA ⊕ ρB) (πA ⊕ πB) (αA ⊕ αB))) :
    b ∈ (A.interconnect B).D ↔ ∃ q : Bond 𝕜 τ,
      (bondReindex splitA).symm (partA ((bondReindex mergeKinds).symm b) q) ∈ A.D ∧
      (bondReindex splitB).symm (partB ((bondReindex mergeKinds).symm b) (-q.1, q.2)) ∈ B.D := by
  simp only [PortHolon.interconnect]
  rw [Submodule.mem_map_equiv, HolonCore.mem_interconnect]
  simp only [Submodule.mem_map_equiv]

end Interact

/-! ## 2. receive: the passive coholon and the active receiver -/

section Receive

variable {𝕜 : Type*} [Field 𝕜] {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- [definition] **The passive coholon** on ports `τ`: it draws no flow and admits every effort. -/
def passiveCoholon (𝕜 τ : Type*) [Field 𝕜] [Fintype τ] : Submodule 𝕜 (Bond 𝕜 τ) where
  carrier := {b | b.1 = 0}
  add_mem' ha hb := by simp_all
  zero_mem' := rfl
  smul_mem' c b hb := by simp_all

/-- [proved-derived; formal-checked] The passive coholon is a Dirac structure (the zero-storage,
zero-power port Holon). -/
theorem passiveCoholon_isDirac : IsDirac (bondForm 𝕜 τ) (passiveCoholon 𝕜 τ) := by
  apply isDirac_of
  · intro x hx y hy
    simp only [passiveCoholon, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_ofPred_eq] at hx hy
    simp [bondForm_apply, hx, hy]
  · intro y hy
    show y.1 = 0
    funext i
    have := hy (0, Pi.single i 1) rfl
    simpa using this

omit [DecidableEq τ] in
/-- [proved-derived; formal-checked] **A passive coholon reads an effort with zero power.** Joined
at a Holon's ports it forces zero flow there; its reading is a linear functional of the effort
(a `Module.Dual` reading, the linear receiver of `Standing`), and the power it draws is `0`. -/
theorem passive_reading (b : Bond 𝕜 τ) (hb : b ∈ passiveCoholon 𝕜 τ)
    (g : Module.Dual 𝕜 (τ → 𝕜)) :
    power b = 0 ∧ g b.2 = (g ∘ₗ LinearMap.snd 𝕜 (τ → 𝕜) (τ → 𝕜)) b := by
  have h : b.1 = 0 := hb
  exact ⟨by simp [power, h], rfl⟩

variable [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

omit [DecidableEq τ] [IsStrictOrderedRing 𝕜] in
/-- [proved-derived; formal-checked] **The active receiver interface law.** A Holon (effort `e_H`)
and a receiver (effort `e_R`) joined through an interface conductance `G` exchange the current
`i = G (e_H − e_R)`; the powers delivered into the two sides sum to `−D_Σ` with
`D_Σ = ⟨Δ, G Δ⟩`, `Δ = e_H − e_R`, and `D_Σ ≥ 0` when `G` is passive. -/
theorem active_receiver_law (G : Matrix τ τ 𝕜) (hG : ∀ v, 0 ≤ v ⬝ᵥ (G *ᵥ v)) (eH eR : τ → 𝕜) :
    power ((-(G *ᵥ (eH - eR)), eH) : Bond 𝕜 τ) + power ((G *ᵥ (eH - eR), eR) : Bond 𝕜 τ) =
      -((eH - eR) ⬝ᵥ (G *ᵥ (eH - eR))) ∧ 0 ≤ (eH - eR) ⬝ᵥ (G *ᵥ (eH - eR)) := by
  refine ⟨?_, hG _⟩
  simp only [power, dotProduct_neg, sub_dotProduct]
  ring

end Receive

/-! ## 2b. receivers as elements: a reading, a drive, a learned relation and a pullback -/

section ReceiverElements

variable {𝕜 : Type*} [Field 𝕜] {τ δ α ι : Type*} [Fintype τ] [Fintype δ] [Fintype α]
  [Fintype ι]

/-- [proved-derived; formal-checked] **Any reading of a coholon bond draws zero power.** Whatever
function `r` of the effort a receiver computes — linear or not (a normalized face) — the bond it
stands on is in the passive coholon, so its power is `0`, and its value depends on the effort alone:
two coholon bonds with one effort read alike. -/
theorem coholon_reading_power {X : Type*} (r : (τ → 𝕜) → X) (b : Bond 𝕜 τ)
    (hb : b ∈ passiveCoholon 𝕜 τ) :
    power b = 0 ∧ ∀ b' ∈ passiveCoholon 𝕜 τ, b'.2 = b.2 → r b'.2 = r b.2 := by
  have h : b.1 = 0 := hb
  exact ⟨by simp [power, h], fun _ _ he => by rw [he]⟩

/-- [proved-derived; formal-checked] **The exterior drive balance.** A receiver that reads at zero
flow (`(0, e_in)`) and injects a current `y` against the Holon's drive effort `e_D` (its bond
`(−y, e_D)`) stores nothing; with the exterior supply `⟨e_D, y⟩` declared as its active power, its
own balance closes exactly: `port + active = 0`. The Holon receives `⟨e_D, y⟩`. -/
theorem exterior_drive_balance (eIn : τ → 𝕜) (y eD : δ → 𝕜) :
    power ((0, eIn) : Bond 𝕜 τ) + power ((-y, eD) : Bond 𝕜 δ) + eD ⬝ᵥ y = 0 := by
  simp [power]

/-- [proved-derived; formal-checked] **A learned receiver's balance.** A learned relation
`e_A = L f_A` delivers its declared power `⟨f_A, L f_A⟩` through the bond `(−f_A, L f_A)`, and its
own balance closes. -/
theorem learned_receiver_balance (L : Matrix α α 𝕜) (f : α → 𝕜) :
    power ((-f, L *ᵥ f) : Bond 𝕜 α) + f ⬝ᵥ (L *ᵥ f) = 0 := by
  simp [power, dotProduct_comm]

/-- [definition] **The normalized face's Jacobian** `J_p = diag p − p pᵀ`. -/
def softmaxJacobian [DecidableEq ι] (p : ι → 𝕜) : Matrix ι ι 𝕜 :=
  Matrix.diagonal p - Matrix.vecMulVec p p

omit [Fintype ι] in
/-- [proved-derived; formal-checked] `J_p` is symmetric, so the normalized receiver's covector
return `J_p g` is its own transpose's pullback. -/
theorem softmaxJacobian_transpose [DecidableEq ι] (p : ι → 𝕜) :
    (softmaxJacobian p)ᵀ = softmaxJacobian p := by
  ext i j
  simp only [softmaxJacobian, Matrix.transpose_apply, Matrix.sub_apply, Matrix.diagonal_apply,
    Matrix.vecMulVec_apply]
  by_cases h : i = j
  · subst h; rfl
  · rw [if_neg h, if_neg (Ne.symm h), mul_comm]

/-- [proved-derived; formal-checked] **The normalized pullback preserves power**: `pullback_law`
at `P = J_p` with `J_pᵀ = J_p`. -/
theorem softmax_pullback_power [DecidableEq ι] (p g d : ι → 𝕜) :
    g ⬝ᵥ (softmaxJacobian p *ᵥ d) = (softmaxJacobian p *ᵥ g) ⬝ᵥ d := by
  conv_rhs => rw [← softmaxJacobian_transpose p]
  exact power_pushforward _ d g

/-- [proved-derived; formal-checked] On the simplex the rows of `J_p` sum to zero: a uniform shift
of the potentials does not move the normalized face. -/
theorem softmaxJacobian_mulVec_one [DecidableEq ι] (p : ι → 𝕜) (h : ∑ i, p i = 1) :
    softmaxJacobian p *ᵥ (fun _ => 1) = 0 := by
  ext i
  simp [softmaxJacobian, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Matrix.diagonal_apply, ← Finset.mul_sum, h]

end ReceiverElements

/-! ## 3. advance, restrict and pullback, as the statements the core implements -/

section Laws

variable {𝕜 : Type*} [Field 𝕜] [CharZero 𝕜] {σ μ ι ι' : Type*} [Fintype σ] [Fintype μ]
  [Fintype ι] [Fintype ι']

/-- [proved-derived; formal-checked] **advance**: one implicit-midpoint step of a linear port Holon
has zero balance residual (`midpoint_balance`). -/
theorem advance_law {Q J R : Matrix σ σ 𝕜} (hQ : Qᵀ = Q) (hJ : Jᵀ = -J) (B : Matrix σ μ 𝕜)
    (h : 𝕜) (q q' : σ → 𝕜) (u : μ → 𝕜)
    (hstep : q' - q = h • ((J - R) *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (q + q'))) + B *ᵥ u)) :
    (storageEnergy Q q' - storageEnergy Q q) -
      (-(h * ((Q *ᵥ ((1 / 2 : 𝕜) • (q + q'))) ⬝ᵥ (R *ᵥ (Q *ᵥ ((1 / 2 : 𝕜) • (q + q')))))) +
        h * ((Q *ᵥ ((1 / 2 : 𝕜) • (q + q'))) ⬝ᵥ (B *ᵥ u))) = 0 := by
  rw [midpoint_balance hQ hJ B h q q' u hstep, sub_self]

omit [CharZero 𝕜] in
/-- [proved-derived; formal-checked] **pullback**: a port map moves efforts by its transpose and
preserves power (`power_pushforward`); the learning covector travels on the effort side. -/
theorem pullback_law (P : Matrix ι' ι 𝕜) (f : ι → 𝕜) (e' : ι' → 𝕜) :
    e' ⬝ᵥ (P *ᵥ f) = (Pᵀ *ᵥ e') ⬝ᵥ f :=
  power_pushforward P f e'

end Laws

end Soma.Holonics.HolonCore
