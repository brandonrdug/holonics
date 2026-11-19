import Holonics.Compression.Core.FaceMap
import Holonics.Holon.Element
import Holonics.Physics.TwoFaceConstitutive
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The face map of a port Holon: supplied power descends to retention, and the Gram counts its modes

[proved-derived; formal-checked] Formal obligations (#410), the box "The face map: the `PortHolon`
power balance joined to it, and its Gram mode count (`Compression/Core/FaceMap`)".

Sources. The owner extended is `Compression/Core/FaceMap` (rebuild step 3, #145): the face map
`F x (ρ, w) = ρ(T_w x)` of a navigator family against terrain, whose kernel is the relevance kernel
(`ker_faceMap_eq_relevanceKernel`), whose kernel quotient is the coarsest retention
(`kernelQuotient_is_coarsest_retention`), and whose finite form keeps the ledger
`rank + dim ker = dim X` (`rank_nullity_ledger`). The balance joined to it is
`Holon/Element.midpoint_balance`: the implicit midpoint step of `q̇ = (J − R)Qq + Bu` changes the
storage `E = ½⟨q, Qq⟩` (`storageEnergy`) by `−h⟨ē, Rē⟩ + h⟨ē, Bu⟩` with `ē = Q q̄`, the discrete
form of `PortHolon.power_balance`. The clocked torus is the record
`research/records/2026-09-08_CLOCKED_TORUS_CURRENTS_CONTINUE_THROUGH_A_RETAINED_FIBRE.md`
(`D z = z₀c₀ + z₁c₁`, `G = DᵀD = [[4,1],[1,4]]`, "the active Gram modes 3 and 5") with
`Physics/TwoFaceConstitutive` (`faceMetric`, `facePlus`, `faceMinus`, `compactExplicitUpdate`). Atlas:
`compression.face-map-kernel`, `compression.kernel-quotient-coarsest-retention`,
`compression.rank-cokernel-ledger`, `holon.port-holon`, `holon.power-balance`,
`holon.midpoint-balance-exact`, `holon.ssm-port-output`, `holarchy.joint-reception`,
`hnn.mode-quotient-descended-run`, `coupling.gram-form-separation`, `encoding.derived-grain`,
`ph.two-face-constitutive`.

What is proved.

1. **The port Holon as navigator and receiver** [definition]. `MidpointPort` holds a symmetric
   storage `Q`, a skew `J`, a dissipation `R`, a supply `B`, a clock interval `h` and an unforced
   step `S`, a linear map with `S q − q = h(J − R)Q(½(q + S q))` for every `q` (a hypothesis; no
   invertibility). Its navigator is `S`; its receiver is the port, the midpoint effort
   `ē = Q(½(q + S q))` pulled back through the supply, `Bᵀē` (`effort`, `port`); its face map is
   `faces`. Its kernel is the set of configurations whose port reading vanishes after every number
   of steps (`mem_ker_faces_iff`). With the storage effort as a second receiver into one face space
   `(μ → K) × (σ → K)` (`portAndEffort`, `facesWithEffort`), the kernel is where the effort itself
   vanishes after every step (`mem_ker_facesWithEffort_iff`), and it lies inside the port kernel
   (`ker_facesWithEffort_le`).
2. **The supplied power descends to retention** (`supplied_energy_descends`). A forced step is
   `q′ = S q + c` with a supply term `c − h(J − R)Q(½c) = hBu` (`SupplyTerm`), which depends on `u`
   alone and makes the step the midpoint step of `q̇ = (J − R)Qq + Bu` (`forced_step_midpoint`);
   the forced motion is `forced`. Under one supply sequence the difference of two forced motions
   runs free, `q_k − q′_k = S^k(x − y)` (`forced_sub`), and their efforts differ by the free effort
   of that difference (`forcedEffort_sub`). So when `x − y` lies in the kernel the port efforts
   agree at every step (`port_effort_descends`), so does the supplied energy `h⟨ē_k, B u_k⟩`, read at
   the port as `h⟨Bᵀē_k, u_k⟩` (`supplied_eq_port`), and so does `E(q_n) − E(q_0) + Σ_(k<n) h⟨ē_k, Rē_k⟩`
   for every `n`, which is the supplied energy summed (`forced_ledger`, through `midpoint_balance`).
3. **A released difference only dissipates.** For `d` in the kernel, the effort of its free motion
   pairs to zero with every supply (`released_receives_no_port_power`); each free step changes the
   storage by `−h⟨ē, Rē⟩` (`free_step_balance`); with `0 ≤ ⟨v, Rv⟩` and `h ≥ 0` the storage
   `E(S^n d)` is nonincreasing in `n` (`released_difference_dissipates`), and with `R = 0` it is
   constant (`released_difference_conserved`). What retention releases is interior motion that
   receives no port power. With the storage effort as a receiver, a released difference keeps its
   storage whatever `R` is (`effort_released_conserved`).
4. **The Gram mode count** [proved-standard; formal-checked]. For a finite matrix `A` over a linear
   ordered field, `AᵀA` and `A` share kernel and rank, and the Gram's rank plus the kernel's
   dimension is the number of columns (`gram_ker_rank`, from `Matrix.ker_mulVecLin_transpose_mul_self`
   and `Matrix.rank_transpose_mul_self`); over `ℝ` the rank is the number of nonzero eigenvalues of
   the Hermitian Gram (`gram_isHermitian`, `rank_eq_card_active_gram_modes`, from
   `Matrix.IsHermitian.rank_eq_card_non_zero_eigs`). The form chosen for the face map: the finite
   face map `horizonFaceMap` with scalar receivers (`V = K`) on the terrain `ι → K`, through its
   matrix in the standard bases (`faceMatrix`, by `LinearMap.toMatrix'`), whose rank is the rank of
   `rank_nullity_ledger` (`faceMatrix_rank`). At every horizon `N ≥ dim X − 1` the Gram's null space
   is the relevance kernel and its rank is `dim X − dim(relevance kernel)`, the dimension of the
   retention `X ⧸ ker F` (`retention_dim_eq_gram_rank`); over `ℝ` that dimension is the count of
   nonzero eigenvalues of the Gram (`retention_dim_eq_card_active_gram_modes`): **the retention's
   dimension is its count of active Gram modes**. A receiver into `Fin k → K` enters as `k` scalar
   receivers.
5. **The clocked torus witness** (`ClockedTorus`). Two square boundaries sharing one edge with one
   orientation, on seven edges: `c₀ = e₁ + e₂ + e₃ + e₄`, `c₁ = e₁ + e₅ + e₆ + e₇`, `D = [c₀ c₁]`
   with `D z = z₀c₀ + z₁c₁` (`D_mulVec`). Then `DᵀD = [[4, 1], [1, 4]]` (`gram`), which is
   `TwoFaceConstitutive.faceMetric` on every `z` (`gram_eq_faceMetric`); `(1, 1)` and `(1, −1)` are
   its modes with values `5` and `3` (`gram_modes`); both are active: determinant `15`, rank `2`,
   `D` of rank `2` with zero kernel (`both_modes_active`), and over `ℝ` the Gram has two nonzero
   eigenvalues (`active_gram_modes_real`). The plus and minus coordinates `facePlus`, `faceMinus`
   are the pairings with the two modes, the Gram scales them by `5` and `3`, and `faceOfPlusMinus`
   is the expansion in the modes (`plus_minus_are_modes`). The compact law's denominators
   `1 + 5τ(μ + ν)` and `1 + 3τ(μ − ν)` are `1 + τ · (mode value) · (material eigenvalue on that
   mode)`: the material `[[μ, ν], [ν, μ]]` has eigenvalues `μ + ν` and `μ − ν` on the same two modes,
   and `z ↦ z + τ M G z` scales each mode by its denominator (`compact_denominators`).

What is not claimed.

- `rank [J D] = 6` on the full four-torus (its `4N⁴` branches): the seven-edge model holds the two
  square currents alone. The Gram on the carrier itself is `Physics/FourTorusTwoFace`
  (`twoFace_gram_one`, `twoFace_gram_two`).
- A nonlinear face map, a nonlinear storage, or a step `S` that is not linear.
- That a forced step exists for a given supply: `SupplyTerm` is a hypothesis, and solving it for `c`
  needs `1 − (h/2)(J − R)Q` to be invertible (`Holarchy/Reception`, `holarchy.joint-reception`).
- The step from a `PortHolon`'s Dirac structure and resistive ports to the state form
  `(Q, J, R, B)`: the balance joined here is `midpoint_balance`, stated in the state form.
- The monotonicity of item 3 does not use the kernel: every free motion's storage is nonincreasing
  under `0 ≤ ⟨v, Rv⟩` and `h ≥ 0`. What the kernel adds is that no supply reaches the released motion
  through the port.
- Mathlib's sorted real eigenvalues of the clocked torus Gram are not computed: their count `2`, and
  the modes `(1, 1)`, `(1, −1)` with values `5`, `3` over `ℚ`, are what is proved.
- A Gram reading of the cokernel ledger, and a face space that is not a coordinate space.

The computational object is the helical pair interaction, read as a port: the supply crosses the
Holon's boundary through the pairing `⟨ē, Bu⟩` of the midpoint effort with the supplied flow, the
power of one contact, and the face map reads that pairing's effort side after every tick of the
midpoint clock; its kernel is the motion the contact cannot hear, which the clock carries only
through the dissipation. The Gram `AᵀA` is the face reading paired with itself, and its active modes
are the directions that pairing does not annihilate; on the clocked torus the two square currents
pair through their one shared edge. Of the winding guide's six general objects this touches faces
and placement (the face map, the port face and the Gram's modes), cell holonomy (the two-face
receiver `Dᵀ` reads a current's circulation around each square, an abelian holonomy) and the tube
(the midpoint step carries the section at one tick to the next, and the forced motion is the span);
the helix, the pair and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.FaceMapPower

open Matrix
open Holonics.Compression.Core.FaceMap
open Holonics.HolonCore

/-! ## 1. The port Holon's midpoint step as navigator, its port as receiver -/

section Port

variable {K : Type} [Field K] {σ μ : Type} [Fintype σ] [Fintype μ]

/-- [definition] **A linear port Holon's midpoint step**: storage `Q` (symmetric), structure `J`
(skew), dissipation `R`, supply `B`, clock interval `h`, and its unforced step `S`, a linear map
with `S q − q = h (J − R) Q (½(q + S q))` for every `q` (no invertibility is assumed). -/
structure MidpointPort (K σ μ : Type) [Field K] [Fintype σ] [Fintype μ] where
  /-- The storage form. -/
  Q : Matrix σ σ K
  /-- The skew structure. -/
  J : Matrix σ σ K
  /-- The dissipation. -/
  R : Matrix σ σ K
  /-- The supply. -/
  B : Matrix σ μ K
  /-- The clock interval. -/
  h : K
  /-- The unforced step. -/
  S : (σ → K) →ₗ[K] (σ → K)
  /-- The storage form is symmetric. -/
  Q_symm : Qᵀ = Q
  /-- The structure is skew. -/
  J_skew : Jᵀ = -J
  /-- The unforced step is the midpoint step of `q̇ = (J − R)Qq`. -/
  step : ∀ q, S q - q = h • ((J - R) *ᵥ (Q *ᵥ ((1 / 2 : K) • (q + S q))))

namespace MidpointPort

variable (P : MidpointPort K σ μ)

/-- [definition] The midpoint effort of the unforced step, `ē = Q(½(q + S q))`. -/
def effort : (σ → K) →ₗ[K] (σ → K) :=
  P.Q.mulVecLin ∘ₗ ((1 / 2 : K) • (LinearMap.id + P.S))

/-- [proved-derived; formal-checked] `ē(q) = Q(½(q + S q))`. -/
theorem effort_apply (q : σ → K) : P.effort q = P.Q *ᵥ ((1 / 2 : K) • (q + P.S q)) := by
  simp [effort]

/-- [definition] The port reading: the midpoint effort pulled back through the supply, `Bᵀ ē`. -/
def port : (σ → K) →ₗ[K] (μ → K) := P.Bᵀ.mulVecLin ∘ₗ P.effort

/-- [proved-derived; formal-checked] The port reads `Bᵀ ē`. -/
theorem port_apply (q : σ → K) : P.port q = P.Bᵀ *ᵥ P.effort q := rfl

/-- [definition] The face map of the port Holon: its one navigator is the unforced step, its one
receiver the port. -/
def faces : (σ → K) →ₗ[K] (Unit × List Unit → (μ → K)) :=
  faceMap (fun _ : Unit => P.port) (fun _ : Unit => P.S)

/-- [proved-derived; formal-checked] A word of the one navigator is the power `S^(length)`. -/
theorem wordMap_unit (w : List Unit) : wordMap (fun _ : Unit => P.S) w = P.S ^ w.length := by
  induction w with
  | nil => rfl
  | cons g w ih => rw [wordMap, ih, List.length_cons, pow_succ']; rfl

/-- [proved-derived; formal-checked] The kernel of the port Holon's face map is the set of
configurations whose port reading vanishes after every number of unforced steps. -/
theorem mem_ker_faces_iff (d : σ → K) :
    d ∈ LinearMap.ker P.faces ↔ ∀ n, P.port ((P.S ^ n) d) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hd n
    have := congrFun hd ((), List.replicate n ())
    simpa [faces, faceMap, wordMap_unit] using this
  · intro hd
    funext request
    simpa [faces, faceMap, wordMap_unit] using hd request.2.length

/-- [definition] **A supply term** `c` for the supply `u`: the forced step is `q′ = S q + c`, and
`c − h(J − R)Q(½c) = h B u`. It depends on `u` alone, so two states under one supply share it. -/
def SupplyTerm (c : σ → K) (u : μ → K) : Prop :=
  c - P.h • ((P.J - P.R) *ᵥ (P.Q *ᵥ ((1 / 2 : K) • c))) = P.h • (P.B *ᵥ u)

/-- [proved-derived; formal-checked] The forced step `q′ = S q + c` with a supply term for `u` is
the midpoint step of `q̇ = (J − R)Qq + Bu`. -/
theorem forced_step_midpoint {c : σ → K} {u : μ → K} (hc : P.SupplyTerm c u) (q : σ → K) :
    (P.S q + c) - q =
      P.h • ((P.J - P.R) *ᵥ (P.Q *ᵥ ((1 / 2 : K) • (q + (P.S q + c)))) + P.B *ᵥ u) := by
  have hs := P.step q
  unfold SupplyTerm at hc
  have hsplit : (1 / 2 : K) • (q + (P.S q + c)) = (1 / 2 : K) • (q + P.S q) + (1 / 2 : K) • c := by
    module
  rw [hsplit, mulVec_add, mulVec_add]
  linear_combination (norm := module) hs + hc

/-- [definition] The forced motion from `x` under supply terms `c₀, c₁, …`:
`q₀ = x`, `q_(k+1) = S q_k + c_k`. -/
def forced (c : ℕ → σ → K) (x : σ → K) : ℕ → σ → K
  | 0 => x
  | k + 1 => P.S (forced c x k) + c k

/-- [definition] The midpoint effort of the forced motion's step `k`, `ē_k = Q(½(q_k + q_(k+1)))`. -/
def forcedEffort (c : ℕ → σ → K) (x : σ → K) (k : ℕ) : σ → K :=
  P.Q *ᵥ ((1 / 2 : K) • (P.forced c x k + P.forced c x (k + 1)))

/-- [proved-derived; formal-checked] Under one supply the difference of two forced motions runs
unforced: `q_k − q′_k = S^k (x − y)`. -/
theorem forced_sub (c : ℕ → σ → K) (x y : σ → K) (k : ℕ) :
    P.forced c x k - P.forced c y k = (P.S ^ k) (x - y) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [forced, forced, pow_succ', Module.End.mul_apply, ← ih, map_sub]
    abel

/-- [proved-derived; formal-checked] Under one supply the forced efforts differ by the unforced
effort of the carried difference: `ē_k(x) − ē_k(y) = ē(S^k (x − y))`. -/
theorem forcedEffort_sub (c : ℕ → σ → K) (x y : σ → K) (k : ℕ) :
    P.forcedEffort c x k - P.forcedEffort c y k = P.effort ((P.S ^ k) (x - y)) := by
  rw [forcedEffort, forcedEffort, ← mulVec_sub, ← smul_sub, add_sub_add_comm, forced_sub,
    forced_sub, pow_succ', Module.End.mul_apply, effort_apply]

/-- [proved-derived; formal-checked] The supplied energy is read at the port:
`⟨ē, B u⟩ = ⟨Bᵀ ē, u⟩`. -/
theorem supplied_eq_port (e : σ → K) (u : μ → K) : e ⬝ᵥ (P.B *ᵥ u) = (P.Bᵀ *ᵥ e) ⬝ᵥ u := by
  rw [dotProduct_mulVec, mulVec_transpose]

/-- [proved-derived; formal-checked] **The port efforts descend to retention.** If `x − y` lies
in the kernel of the face map, then under any common supply the forced motions from `x` and `y`
read one port effort at every step: `Bᵀ ē_k(x) = Bᵀ ē_k(y)`. -/
theorem port_effort_descends {x y : σ → K} (hxy : x - y ∈ LinearMap.ker P.faces)
    (c : ℕ → σ → K) (k : ℕ) :
    P.Bᵀ *ᵥ P.forcedEffort c x k = P.Bᵀ *ᵥ P.forcedEffort c y k := by
  rw [← sub_eq_zero, ← mulVec_sub, forcedEffort_sub]
  exact (P.mem_ker_faces_iff _).mp hxy k

/-- [proved-derived; formal-checked] **A released difference receives no port power**: for `d` in
the kernel, the effort of its free motion pairs to zero with every supply,
`⟨ē(S^n d), B u⟩ = 0` for all `n` and `u`. -/
theorem released_receives_no_port_power {d : σ → K} (hd : d ∈ LinearMap.ker P.faces) (n : ℕ)
    (u : μ → K) : P.effort ((P.S ^ n) d) ⬝ᵥ (P.B *ᵥ u) = 0 := by
  rw [supplied_eq_port, ← port_apply, (P.mem_ker_faces_iff d).mp hd n, zero_dotProduct]

/-- [definition] **The port and the storage effort as two receivers**, into one face space
`(μ → K) × (σ → K)`: `true` reads the port `Bᵀ ē`, `false` reads the midpoint effort `ē`. -/
def portAndEffort : Bool → (σ → K) →ₗ[K] ((μ → K) × (σ → K))
  | true => LinearMap.inl K (μ → K) (σ → K) ∘ₗ P.port
  | false => LinearMap.inr K (μ → K) (σ → K) ∘ₗ P.effort

/-- [definition] The face map of the port Holon with the port and the storage effort as receivers. -/
def facesWithEffort : (σ → K) →ₗ[K] (Bool × List Unit → ((μ → K) × (σ → K))) :=
  faceMap P.portAndEffort (fun _ : Unit => P.S)

/-- [proved-derived; formal-checked] With the storage effort as a second receiver, the kernel is
the set of configurations whose midpoint effort vanishes after every number of unforced steps. -/
theorem mem_ker_facesWithEffort_iff (d : σ → K) :
    d ∈ LinearMap.ker P.facesWithEffort ↔ ∀ n, P.effort ((P.S ^ n) d) = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro hd n
    have := congrFun hd (false, List.replicate n ())
    simpa [facesWithEffort, faceMap, wordMap_unit, portAndEffort] using this
  · intro hd
    funext request
    obtain ⟨b, w⟩ := request
    cases b <;> simp [facesWithEffort, faceMap, wordMap_unit, portAndEffort, port_apply,
      hd w.length]

/-- [proved-derived; formal-checked] The storage effort's kernel lies inside the port kernel: the
second receiver only refines the retention. -/
theorem ker_facesWithEffort_le : LinearMap.ker P.facesWithEffort ≤ LinearMap.ker P.faces := by
  intro d hd
  rw [P.mem_ker_faces_iff]
  intro n
  rw [port_apply, (P.mem_ker_facesWithEffort_iff d).mp hd n, mulVec_zero]

end MidpointPort

end Port

/-! ## 2. Supplied power descends to retention; a released difference only dissipates -/

section Balance

variable {K : Type} [Field K] [CharZero K] {σ μ : Type} [Fintype σ] [Fintype μ]

namespace MidpointPort

variable (P : MidpointPort K σ μ)

/-- [proved-derived; formal-checked] **The ledger of a forced motion** (`midpoint_balance`, step
by step): over `n` steps the storage change plus the dissipation is the supplied energy,
`E(q_n) − E(q_0) + Σ_(k<n) h⟨ē_k, R ē_k⟩ = Σ_(k<n) h⟨ē_k, B u_k⟩`. -/
theorem forced_ledger {c : ℕ → σ → K} {u : ℕ → μ → K} (hc : ∀ k, P.SupplyTerm (c k) (u k))
    (x : σ → K) (n : ℕ) :
    storageEnergy P.Q (P.forced c x n) - storageEnergy P.Q x +
        ∑ k ∈ Finset.range n,
          P.h * (P.forcedEffort c x k ⬝ᵥ (P.R *ᵥ P.forcedEffort c x k)) =
      ∑ k ∈ Finset.range n, P.h * (P.forcedEffort c x k ⬝ᵥ (P.B *ᵥ u k)) := by
  induction n with
  | zero => simp [forced]
  | succ n ih =>
    have hstep := midpoint_balance P.Q_symm P.J_skew P.B P.h (P.forced c x n)
      (P.forced c x (n + 1)) (u n) (P.forced_step_midpoint (hc n) _)
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ← ih]
    simp only [forcedEffort] at hstep ⊢
    linear_combination hstep

/-- [proved-derived; formal-checked] **The supplied power descends to retention.** If `x − y`
lies in the kernel of the port Holon's face map, then under any common supply `u₀, u₁, …` (its
supply terms common to both motions) the port efforts agree at every step, so does the supplied
energy `h⟨ē_k, B u_k⟩`, and so does the storage change plus the dissipation over every number of
steps. -/
theorem supplied_energy_descends {c : ℕ → σ → K} {u : ℕ → μ → K}
    (hc : ∀ k, P.SupplyTerm (c k) (u k)) {x y : σ → K} (hxy : x - y ∈ LinearMap.ker P.faces) :
    (∀ k, P.Bᵀ *ᵥ P.forcedEffort c x k = P.Bᵀ *ᵥ P.forcedEffort c y k) ∧
      (∀ k, P.h * (P.forcedEffort c x k ⬝ᵥ (P.B *ᵥ u k)) =
        P.h * (P.forcedEffort c y k ⬝ᵥ (P.B *ᵥ u k))) ∧
      ∀ n, storageEnergy P.Q (P.forced c x n) - storageEnergy P.Q x +
          ∑ k ∈ Finset.range n,
            P.h * (P.forcedEffort c x k ⬝ᵥ (P.R *ᵥ P.forcedEffort c x k)) =
        storageEnergy P.Q (P.forced c y n) - storageEnergy P.Q y +
          ∑ k ∈ Finset.range n,
            P.h * (P.forcedEffort c y k ⬝ᵥ (P.R *ᵥ P.forcedEffort c y k)) := by
  have hport := P.port_effort_descends hxy c
  have hsupp : ∀ k, P.h * (P.forcedEffort c x k ⬝ᵥ (P.B *ᵥ u k)) =
      P.h * (P.forcedEffort c y k ⬝ᵥ (P.B *ᵥ u k)) := by
    intro k
    rw [supplied_eq_port, supplied_eq_port, hport k]
  refine ⟨hport, hsupp, fun n => ?_⟩
  rw [P.forced_ledger hc x n, P.forced_ledger hc y n]
  exact Finset.sum_congr rfl fun k _ => hsupp k

/-- [proved-derived; formal-checked] **The free step's balance** (`midpoint_balance` at zero
supply): `E(S q) − E(q) = −h⟨ē, R ē⟩`. -/
theorem free_step_balance (q : σ → K) :
    storageEnergy P.Q (P.S q) - storageEnergy P.Q q =
      -(P.h * (P.effort q ⬝ᵥ (P.R *ᵥ P.effort q))) := by
  have hstep : P.S q - q = P.h • ((P.J - P.R) *ᵥ (P.Q *ᵥ ((1 / 2 : K) • (q + P.S q))) +
      P.B *ᵥ (0 : μ → K)) := by
    rw [mulVec_zero, add_zero]; exact P.step q
  have := midpoint_balance P.Q_symm P.J_skew P.B P.h q (P.S q) 0 hstep
  rw [this, effort_apply]
  simp

/-- [proved-derived; formal-checked] **A released difference with no dissipation is conserved**:
with `R = 0`, for `d` in the kernel, the free motion receives no port power and keeps its storage,
`E(S^n d) = E(d)`. -/
theorem released_difference_conserved (hR : P.R = 0) {d : σ → K}
    (hd : d ∈ LinearMap.ker P.faces) :
    (∀ n (u : μ → K), P.effort ((P.S ^ n) d) ⬝ᵥ (P.B *ᵥ u) = 0) ∧
      ∀ n, storageEnergy P.Q ((P.S ^ n) d) = storageEnergy P.Q d := by
  refine ⟨P.released_receives_no_port_power hd, fun n => ?_⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    have := P.free_step_balance ((P.S ^ n) d)
    rw [hR, zero_mulVec, dotProduct_zero, mul_zero, neg_zero, sub_eq_zero] at this
    rw [pow_succ', Module.End.mul_apply, this, ih]

/-- [proved-derived; formal-checked] **With the storage effort as a receiver, a released difference
keeps its storage**: its midpoint effort vanishes at every step, so neither the port nor the
dissipation reaches it, and `E(S^n d) = E(d)` for every `R`. -/
theorem effort_released_conserved {d : σ → K} (hd : d ∈ LinearMap.ker P.facesWithEffort) (n : ℕ) :
    storageEnergy P.Q ((P.S ^ n) d) = storageEnergy P.Q d := by
  have he := (P.mem_ker_facesWithEffort_iff d).mp hd
  induction n with
  | zero => rfl
  | succ n ih =>
    have := P.free_step_balance ((P.S ^ n) d)
    rw [he n, mulVec_zero, dotProduct_zero, mul_zero, neg_zero, sub_eq_zero] at this
    rw [pow_succ', Module.End.mul_apply, this, ih]

end MidpointPort

end Balance

section Dissipation

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {σ μ : Type} [Fintype σ]
  [Fintype μ]

namespace MidpointPort

variable (P : MidpointPort K σ μ)

/-- [proved-derived; formal-checked] **A released difference only dissipates.** For `d` in the
kernel, `R` positive semidefinite (`0 ≤ ⟨v, R v⟩`) and `h ≥ 0`: its free motion receives no port
power from any supply, each step changes its storage by `−h⟨ē, R ē⟩`, and its storage
`E(S^n d)` is nonincreasing in `n`. -/
theorem released_difference_dissipates (hR : ∀ v, 0 ≤ v ⬝ᵥ (P.R *ᵥ v)) (hh : 0 ≤ P.h)
    {d : σ → K} (hd : d ∈ LinearMap.ker P.faces) :
    (∀ n (u : μ → K), P.effort ((P.S ^ n) d) ⬝ᵥ (P.B *ᵥ u) = 0) ∧
      (∀ n, storageEnergy P.Q ((P.S ^ (n + 1)) d) - storageEnergy P.Q ((P.S ^ n) d) =
        -(P.h * (P.effort ((P.S ^ n) d) ⬝ᵥ (P.R *ᵥ P.effort ((P.S ^ n) d))))) ∧
      Antitone fun n => storageEnergy P.Q ((P.S ^ n) d) := by
  have hstep : ∀ n, storageEnergy P.Q ((P.S ^ (n + 1)) d) - storageEnergy P.Q ((P.S ^ n) d) =
      -(P.h * (P.effort ((P.S ^ n) d) ⬝ᵥ (P.R *ᵥ P.effort ((P.S ^ n) d)))) := by
    intro n
    rw [pow_succ', Module.End.mul_apply]
    exact P.free_step_balance _
  refine ⟨P.released_receives_no_port_power hd, hstep, antitone_nat_of_succ_le fun n => ?_⟩
  have := hstep n
  have := mul_nonneg hh (hR (P.effort ((P.S ^ n) d)))
  linarith

end MidpointPort

end Dissipation

/-! ## 3. The Gram mode count -/

section Gram

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- [proved-standard; formal-checked] **A finite face map and its Gram share kernel and rank**
(`Matrix.ker_mulVecLin_transpose_mul_self`, `Matrix.rank_transpose_mul_self`), and the Gram's
rank plus the kernel's dimension is the terrain's dimension. -/
theorem gram_ker_rank (A : Matrix m n K) :
    LinearMap.ker (Aᵀ * A).mulVecLin = LinearMap.ker A.mulVecLin ∧ (Aᵀ * A).rank = A.rank ∧
      (Aᵀ * A).rank + Module.finrank K (LinearMap.ker A.mulVecLin) = Fintype.card n := by
  refine ⟨ker_mulVecLin_transpose_mul_self A, rank_transpose_mul_self A, ?_⟩
  rw [rank_transpose_mul_self, Matrix.rank, LinearMap.finrank_range_add_finrank_ker,
    Module.finrank_fintype_fun_eq_card]

end Gram

section GramReal

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] Over `ℝ` the Gram `AᵀA` is Hermitian. -/
theorem gram_isHermitian (A : Matrix m n ℝ) : (Aᵀ * A).IsHermitian := by
  simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self A

/-- [proved-standard; formal-checked] **The rank of a real face map is its count of active Gram
modes**: the number of nonzero eigenvalues of the Hermitian Gram `AᵀA`
(`Matrix.IsHermitian.rank_eq_card_non_zero_eigs`). -/
theorem rank_eq_card_active_gram_modes (A : Matrix m n ℝ) :
    A.rank = Fintype.card {i // (gram_isHermitian A).eigenvalues i ≠ 0} := by
  rw [← rank_transpose_mul_self]
  exact (gram_isHermitian A).rank_eq_card_non_zero_eigs

end GramReal

section HorizonGram

variable {K : Type} [Field K]
variable {Navigator Receiver ι : Type} [Fintype ι] [DecidableEq ι]
  (read : Receiver → (ι → K) →ₗ[K] K) (transport : Navigator → (ι → K) →ₗ[K] (ι → K))

/-- [definition] **The face matrix**: the finite face map at horizon `N` (scalar receivers on the
terrain `ι → K`) in the standard bases, one row per request (receiver, word of length `≤ N`). -/
def faceMatrix (N : ℕ) : Matrix (Receiver × BoundedWord Navigator N) ι K :=
  LinearMap.toMatrix' (horizonFaceMap read transport N)

/-- [proved-derived; formal-checked] The face matrix acts as the finite face map. -/
theorem faceMatrix_mulVecLin (N : ℕ) :
    (faceMatrix read transport N).mulVecLin = horizonFaceMap read transport N := by
  rw [faceMatrix, ← Matrix.toLin'_apply', Matrix.toLin'_toMatrix']

/-- [proved-derived; formal-checked] The face matrix's rank is the finite face map's rank, the
`rank` of `FaceMap.rank_nullity_ledger`. -/
theorem faceMatrix_rank (N : ℕ) :
    (faceMatrix read transport N).rank =
      Module.finrank K (LinearMap.range (horizonFaceMap read transport N)) := by
  rw [Matrix.rank, faceMatrix_mulVecLin]

variable [LinearOrder K] [IsStrictOrderedRing K] [Fintype Navigator] [Fintype Receiver]

/-- [proved-derived; formal-checked] **The retention's dimension is its count of active Gram
modes.** At any horizon `N ≥ dim X − 1` the Gram `AᵀA` of the face matrix has the relevance
kernel as its null space, and its rank is `dim X − dim(relevance kernel)`, the dimension of the
kernel quotient (retention). -/
theorem retention_dim_eq_gram_rank {N : ℕ} (hN : Fintype.card ι - 1 ≤ N) :
    LinearMap.ker ((faceMatrix read transport N)ᵀ * faceMatrix read transport N).mulVecLin =
        LinearMap.ker (faceMap read transport) ∧
      Module.finrank K ((ι → K) ⧸ LinearMap.ker (faceMap read transport)) =
        ((faceMatrix read transport N)ᵀ * faceMatrix read transport N).rank ∧
      Fintype.card ι - Module.finrank K (LinearMap.ker (faceMap read transport)) =
        ((faceMatrix read transport N)ᵀ * faceMatrix read transport N).rank := by
  have hker : LinearMap.ker (horizonFaceMap read transport N) =
      LinearMap.ker (faceMap read transport) := by
    rw [ker_horizonFaceMap, horizonBlind_eq_ker_of_le read transport
      (by rw [Module.finrank_fintype_fun_eq_card]; exact hN)]
  have hledger := rank_nullity_ledger read transport N
  rw [hker, Module.finrank_fintype_fun_eq_card] at hledger
  have hquot := Submodule.finrank_quotient_add_finrank (LinearMap.ker (faceMap read transport))
  rw [Module.finrank_fintype_fun_eq_card] at hquot
  obtain ⟨hgker, hgrank, -⟩ := gram_ker_rank (faceMatrix read transport N)
  rw [faceMatrix_mulVecLin, hker] at hgker
  rw [faceMatrix_rank] at hgrank
  refine ⟨hgker, ?_, ?_⟩ <;> omega

end HorizonGram

section HorizonGramReal

variable {Navigator Receiver ι : Type} [Fintype Navigator] [Fintype Receiver] [Fintype ι]
  [DecidableEq ι] (read : Receiver → (ι → ℝ) →ₗ[ℝ] ℝ) (transport : Navigator → (ι → ℝ) →ₗ[ℝ] (ι → ℝ))

/-- [proved-derived; formal-checked] **Over `ℝ`, the retention's dimension is the number of
nonzero eigenvalues of the face matrix's Gram**, at any horizon `N ≥ dim X − 1`. -/
theorem retention_dim_eq_card_active_gram_modes {N : ℕ} (hN : Fintype.card ι - 1 ≤ N) :
    Module.finrank ℝ ((ι → ℝ) ⧸ LinearMap.ker (faceMap read transport)) =
      Fintype.card {i // (gram_isHermitian (faceMatrix read transport N)).eigenvalues i ≠ 0} := by
  rw [(retention_dim_eq_gram_rank read transport hN).2.1, rank_transpose_mul_self]
  exact rank_eq_card_active_gram_modes _

end HorizonGramReal

/-! ## 4. The clocked torus: the active Gram modes `5` and `3` -/

namespace ClockedTorus

open Holonics.Physics.TwoFaceConstitutive

/-- [definition] The oriented boundary of the first square on seven edges, `c₀ = e₁ + e₂ + e₃ + e₄`. -/
def c₀ : Fin 7 → ℚ := ![1, 1, 1, 1, 0, 0, 0]

/-- [definition] The oriented boundary of the second square, `c₁ = e₁ + e₅ + e₆ + e₇`: it shares the
edge `e₁` with the first, with the same orientation. -/
def c₁ : Fin 7 → ℚ := ![1, 0, 0, 0, 1, 1, 1]

/-- [definition] **The two-face matrix** `D = [c₀ c₁]`, read as a finite face map of the faces
`z` on the seven edges. -/
def D : Matrix (Fin 7) (Fin 2) ℚ := Matrix.of fun e j => ![c₀, c₁] j e

/-- [proved-derived; formal-checked] `D z = z₀ c₀ + z₁ c₁`. -/
theorem D_mulVec (z : Fin 2 → ℚ) : D *ᵥ z = z 0 • c₀ + z 1 • c₁ := by
  ext e
  simp [D, mulVec, dotProduct, Fin.sum_univ_two, mul_comm]

/-- [proved-derived; formal-checked] **The Gram of the two square currents**: `DᵀD = [[4, 1], [1, 4]]`
(each square has four edges, and they share one with the same orientation). -/
theorem gram : Dᵀ * D = !![4, 1; 1, 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D, c₀, c₁, mul_apply, Fin.sum_univ_succ] <;> norm_num

/-- [proved-derived; formal-checked] **The Gram is `TwoFaceConstitutive.faceMetric`**. -/
theorem gram_eq_faceMetric (z : Face) : (Dᵀ * D) *ᵥ z = faceMetric z := by
  rw [gram]
  ext i
  fin_cases i <;> simp [faceMetric, mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **The two modes**: `(1, 1)` with value `5` and `(1, −1)` with
value `3`. -/
theorem gram_modes :
    (Dᵀ * D) *ᵥ ![1, 1] = (5 : ℚ) • ![1, 1] ∧ (Dᵀ * D) *ᵥ ![1, -1] = (3 : ℚ) • ![1, -1] := by
  rw [gram]
  constructor <;> ext i <;> fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num

/-- [proved-derived; formal-checked] **Both modes are active**: the Gram has determinant `15` and
rank `2`, `D` has rank `2`, and the face reading `D` has zero kernel (the retention keeps both faces). -/
theorem both_modes_active :
    (Dᵀ * D).det = 15 ∧ (Dᵀ * D).rank = 2 ∧ D.rank = 2 ∧ LinearMap.ker D.mulVecLin = ⊥ := by
  have hdet : (Dᵀ * D).det = 15 := by
    rw [gram, det_fin_two_of]; norm_num
  have hrank : (Dᵀ * D).rank = 2 := by
    rw [rank_of_det_ne_zero (by rw [hdet]; norm_num), Fintype.card_fin]
  obtain ⟨-, hgr, hsum⟩ := gram_ker_rank D
  refine ⟨hdet, hrank, hgr ▸ hrank, ?_⟩
  rw [hrank, Fintype.card_fin] at hsum
  exact Submodule.finrank_eq_zero.mp (by omega)

/-- [proved-derived; formal-checked] **The plus and minus coordinates are the two modes**:
`z₊ = ⟨(1, 1), z⟩`, `z₋ = ⟨(1, −1), z⟩`, the Gram scales them by `5` and `3`, and
`faceOfPlusMinus p m = (p/2)(1, 1) + (m/2)(1, −1)`. -/
theorem plus_minus_are_modes (z : Face) (p m : ℚ) :
    facePlus z = ![1, 1] ⬝ᵥ z ∧ faceMinus z = ![1, -1] ⬝ᵥ z ∧
      facePlus (faceMetric z) = 5 * facePlus z ∧ faceMinus (faceMetric z) = 3 * faceMinus z ∧
      faceOfPlusMinus p m = (p / 2) • ![1, 1] + (m / 2) • ![1, -1] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [facePlus, dotProduct, Fin.sum_univ_two]
  · simp [faceMinus, dotProduct, Fin.sum_univ_two]; ring
  · simp [facePlus, faceMetric]; ring
  · simp [faceMinus, faceMetric]; ring
  · ext i
    fin_cases i <;> simp [faceOfPlusMinus] <;> ring

/-- [proved-derived; formal-checked] **The compact law's denominators are `1 + τ · (mode value) ·
(material eigenvalue)`**: the material `[[μ, ν], [ν, μ]]` has eigenvalue `μ + ν` on `(1, 1)` and
`μ − ν` on `(1, −1)`, and `z ↦ z + τ M G z` scales them by `1 + 5τ(μ + ν)` and `1 + 3τ(μ − ν)`,
the denominators of `compactPlusUpdate` and `compactMinusUpdate`. -/
theorem compact_denominators (tau mu nu : ℚ) :
    materialMap mu nu ![1, 1] = (mu + nu) • ![1, 1] ∧
      materialMap mu nu ![1, -1] = (mu - nu) • ![1, -1] ∧
      ![1, 1] + tau • materialMap mu nu (faceMetric ![1, 1]) =
        (1 + 5 * tau * (mu + nu)) • ![1, 1] ∧
      ![1, -1] + tau • materialMap mu nu (faceMetric ![1, -1]) =
        (1 + 3 * tau * (mu - nu)) • ![1, -1] := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i <;> fin_cases i <;> simp [materialMap, faceMetric] <;> ring

/-- [definition] The two-face matrix over `ℝ`. -/
def DReal : Matrix (Fin 7) (Fin 2) ℝ := D.map (Rat.cast : ℚ → ℝ)

/-- [proved-derived; formal-checked] **Over `ℝ` the Gram of the two square currents has two
nonzero eigenvalues**: the count of active Gram modes is `2`. -/
theorem active_gram_modes_real :
    Fintype.card {i // (gram_isHermitian DReal).eigenvalues i ≠ 0} = 2 := by
  have hgram : DRealᵀ * DReal = !![4, 1; 1, 4] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [DReal, D, c₀, c₁, mul_apply, Fin.sum_univ_succ] <;>
      norm_num
  rw [← rank_eq_card_active_gram_modes, ← rank_transpose_mul_self, hgram,
    rank_of_det_ne_zero (by rw [det_fin_two_of]; norm_num), Fintype.card_fin]

end ClockedTorus

end Holonics.Compression.FaceMapPower
