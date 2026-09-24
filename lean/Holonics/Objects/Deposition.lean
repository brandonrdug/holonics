import Holonics.Transport.JunctionLaw
import Holonics.Foundation.Standing
import Holonics.Physics.AccumulatedNormalResponse
import Holonics.Computation.HolonicWorldReturnDeposit

/-!
# Object 8: deposition, the only law by which a constitution changes

[definition] `docs/ELEMENTARY_OBJECTS.md` §8. On a finite graph with node × edge incidence `d`
(the coboundary `d₀`), the **constitution** `Θ` is a positive conductance per edge. It is the
edge weight `w₁` of a `Foundation/HodgeReceiver.lean::WeightedComplex` (`complexOf`), so the
codifferential of that complex is the divergence of the flux and nothing is founded twice:

```text
flux          j = Θ · dφ                        (edgewise)
balance       ∂j = dᵀ j = σ                     JunctionLaw.balanced_iff_divergence
deposition    Θ'_e = Θ_e + Γ_e(j_e, (dφ)_e)     Γ_e reads only edge e
```

[proved-derived; formal-checked] What is proved.

1. **The solve is the junction law, and its flux is unique.** `solves_iff_boundary_flux` and
   `solves_iff_balanced` identify the balance with `JunctionLaw.Balanced` for every interface
   split. Two potentials solving one balance on one constitution have the same drop and the same
   flux (`drop_unique`, `flux_unique`), from `JunctionLaw.tellegen` and the definiteness
   `HodgeReceiver.ip_eq_zero`: the gauge of the potential is not a quantity the flux carries.
2. **Joule/Tellegen ledger.** `⟨j, dφ⟩ = ⟨dφ, Θ dφ⟩ = ⟨φ, σ⟩` for a solved `φ`
   (`joule_ledger`); it is nonnegative and vanishes exactly when no flux moves
   (`dissipation_zero_iff_no_flux`). A source admitting a balance has zero total charge
   (`source_total_zero`), and a route return of `HolonicWorldReturnDeposit` has it
   (`route_return_has_zero_charge`, from `sum_routeDeposit`).
3. **Locality.** Deposits agreeing edgewise agree (`deposit_local_edges`); potentials agreeing on
   the nodes incident to a region deposit identically on it (`deposit_local_region`); an edge
   reached by no flux is unchanged when `Γ_e(0,0) = 0` (`unreached_edge_unchanged`).
4. **The constitution suffices for every solver's future; the last flux does not.** For *every*
   solver — including one that consults the flux record to choose its potential gauge — the
   constitution is a lawful retention (`Foundation/Standing.lean::StandingLaw`) whose future
   observation is the flux of the actual later solve (`constitutionStanding`). The separation
   witness: two histories with the same last flux leave different constitutions, a later source
   separates them, and therefore the last flux is not a lawful retention (StandingLaw)
   (`last_flux_is_not_a_standing`). Nothing here refutes the complete flux record as a
   retention. The constitution is **not minimal**: on the parallel pair under the square law,
   the distinct constitutions `(1,1)` and `(2,2)` agree under every admitted future
   (`constitution_is_not_minimal`), so the minimal retention is a proper quotient of it.
5. **A deposit bends later flux** on two parallel edges: the split `(1/3, 2/3)` becomes
   `(5/16, 11/16)` under the square law `Γ_e = j_e²` (`square_deposit_bends_the_next_split`),
   while the Joule law `Γ_e = j_e (dφ)_e`, proportional here, leaves it unchanged
   (`joule_deposit_keeps_the_split`). The bend depends on the declared law, not on the fact of
   depositing.
6. **The normal law is a deposition.** `AccumulatedNormalResponse.updatedGram` `H ↦ H + x xᴴ`
   changes entry `(i,j)` only where `x i ≠ 0` and `x j ≠ 0` (`normal_law_local`), keeps a positive
   semidefinite constitution positive semidefinite (`normal_law_keeps_posSemidef`), and the edge
   square law is the diagonal normal law summed over one feature per edge
   (`square_law_is_the_edgewise_normal_law`).

[open] Not proved here: existence of a solve (solvability on a connected graph of every source of
zero total charge); the dielectric-breakdown growth measure `∝ |⟨dφ, e⟩|^η`; Exner erosion;
convergence of repeated deposition. The solve's existence is carried as a hypothesis wherever it is
used, and the witnesses exhibit it.
-/

noncomputable section

namespace Holonics.Objects.Deposition

open Holonics
open Holonics.Foundation.HodgeReceiver
open Holonics.Foundation.Standing
open Holonics.Millennium.Chronology
open Matrix

variable {p q : ℕ}

/-! ## 1. Constitution, flux and the balance -/

/-- [definition] A **constitution**: one positive conductance per edge. -/
abbrev Constitution (q : ℕ) := {θ : Fin q → ℚ // ∀ e, 0 < θ e}

/-- [definition] The weighted complex whose edge weight is the constitution: unit node weight, no
two-cells. Its `codiff₀` is the divergence of `Θ · y`. -/
def complexOf (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) : WeightedComplex p q 0 where
  d₀ := d
  d₁ := 0
  w₀ := fun _ => 1
  w₁ := Θ.1
  w₂ := fun i => i.elim0
  w₀pos := fun _ => one_pos
  w₁pos := Θ.2
  w₂pos := fun i => i.elim0
  dd := Matrix.zero_mul _

/-- [definition] The flux `j = Θ · dφ`, edgewise. -/
def flux (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) (φ : Fin p → ℚ) : Fin q → ℚ :=
  fun e => Θ.1 e * (d *ᵥ φ) e

/-- [definition] `φ` solves the balance with source `σ` on the constitution `Θ`. -/
def Solves (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) (φ σ : Fin p → ℚ) : Prop :=
  (complexOf d Θ).codiff₀ *ᵥ (d *ᵥ φ) = σ

/-- [proved-derived; formal-checked] The codifferential of `complexOf` is `dᵀ (Θ · y)`. -/
theorem codiff_mulVec (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) (y : Fin q → ℚ) :
    (complexOf d Θ).codiff₀ *ᵥ y = dᵀ *ᵥ (fun e => Θ.1 e * y e) := by
  funext i
  simp only [mulVec, dotProduct, WeightedComplex.codiff₀, complexOf, transpose_apply, div_one]
  exact Finset.sum_congr rfl fun e _ => by ring

/-- [proved-derived; formal-checked] **The balance is `∂j = σ`.** -/
theorem solves_iff_boundary_flux (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q)
    (φ σ : Fin p → ℚ) : Solves d Θ φ σ ↔ dᵀ *ᵥ flux d Θ φ = σ := by
  rw [Solves, codiff_mulVec]
  rfl

/-- [proved-derived; formal-checked] **The balance is the junction law's normal half**, for every
declared interface split (`JunctionLaw.balanced_iff_divergence`). -/
theorem solves_iff_balanced (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q)
    (φ σ : Fin p → ℚ) (I : Transport.JunctionLaw.SideSplit q) :
    Solves d Θ φ σ ↔ Transport.JunctionLaw.Balanced (complexOf d Θ) I (d *ᵥ φ) σ :=
  (Transport.JunctionLaw.balanced_iff_divergence _ I _ _).symm

/-! ## 2. The Joule/Tellegen ledger and uniqueness of the flux -/

/-- [proved-derived; formal-checked] **Joule/Tellegen ledger.** For a solved potential,
`⟨j, dφ⟩ = ⟨dφ, Θ dφ⟩ = ⟨φ, σ⟩`: `JunctionLaw.tellegen` at `v = φ`, `f = dφ`. -/
theorem joule_ledger {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q} {φ σ : Fin p → ℚ}
    (h : Solves d Θ φ σ) :
    flux d Θ φ ⬝ᵥ (d *ᵥ φ) = ip Θ.1 (d *ᵥ φ) (d *ᵥ φ) ∧ ip Θ.1 (d *ᵥ φ) (d *ᵥ φ) = φ ⬝ᵥ σ := by
  have ht := Transport.JunctionLaw.tellegen (complexOf d Θ) φ (d *ᵥ φ) σ h
  refine ⟨?_, ?_⟩
  · simp only [flux, dotProduct, ip]
    exact Finset.sum_congr rfl fun e _ => by ring
  · change ip Θ.1 (d *ᵥ φ) (d *ᵥ φ) = ip (fun _ => 1) φ σ at ht
    rw [ht]
    simp [ip, dotProduct]

/-- [proved-derived; formal-checked] **Dissipation is nonnegative and vanishes exactly when no
flux moves.** -/
theorem dissipation_zero_iff_no_flux {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q}
    {φ σ : Fin p → ℚ} (h : Solves d Θ φ σ) :
    0 ≤ φ ⬝ᵥ σ ∧ (φ ⬝ᵥ σ = 0 ↔ flux d Θ φ = 0) := by
  have hl := (joule_ledger h).2
  refine ⟨hl ▸ ip_self_nonneg Θ.2 _, ?_⟩
  constructor
  · intro h0
    have hdrop : d *ᵥ φ = 0 := ip_eq_zero Θ.2 (hl.trans h0)
    funext e
    simp [flux, hdrop]
  · intro h0
    have hdrop : d *ᵥ φ = 0 := by
      funext e
      have he := congrFun h0 e
      simp only [flux, Pi.zero_apply] at he
      rcases mul_eq_zero.mp he with hθ | hg
      · exact absurd hθ (ne_of_gt (Θ.2 e))
      · exact hg
    rw [← hl, hdrop]
    simp [ip]

/-- [proved-derived; formal-checked] **The drop is unique.** Two potentials solving one balance
on one constitution have the same coboundary: their difference solves the source-free balance, so
its Joule dissipation `⟨dψ, Θ dψ⟩ = ⟨ψ, 0⟩ = 0` and the positive constitution forces `dψ = 0`. -/
theorem drop_unique {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q} {φ φ' σ : Fin p → ℚ}
    (h : Solves d Θ φ σ) (h' : Solves d Θ φ' σ) : d *ᵥ φ = d *ᵥ φ' := by
  have hψ : Solves d Θ (φ - φ') 0 := by
    unfold Solves at h h' ⊢
    rw [mulVec_sub, mulVec_sub, h, h', sub_self]
  have hl := (joule_ledger hψ).2
  rw [dotProduct_zero] at hl
  have hzero := ip_eq_zero Θ.2 hl
  rw [mulVec_sub, sub_eq_zero] at hzero
  exact hzero

/-- [proved-derived; formal-checked] **The flux is unique**: it is a function of the constitution
and the source alone, whatever gauge the solved potential carries. -/
theorem flux_unique {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q} {φ φ' σ : Fin p → ℚ}
    (h : Solves d Θ φ σ) (h' : Solves d Θ φ' σ) : flux d Θ φ = flux d Θ φ' := by
  funext e
  simp [flux, drop_unique h h']

/-- [proved-derived; formal-checked] **A source admitting a balance has zero total charge**, when
every edge is a difference (`d` has zero row sums): Tellegen at the constant potential. -/
theorem source_total_zero {d : Matrix (Fin q) (Fin p) ℚ} (rowSum : ∀ e, ∑ i, d e i = 0)
    {Θ : Constitution q} {φ σ : Fin p → ℚ} (h : Solves d Θ φ σ) : ∑ i, σ i = 0 := by
  have hconst : d *ᵥ (fun _ => (1 : ℚ)) = 0 := by
    funext e
    simp [mulVec, dotProduct, rowSum e]
  have ht := Transport.JunctionLaw.tellegen (complexOf d Θ) (fun _ => 1) (d *ᵥ φ) σ h
  change ip Θ.1 (d *ᵥ fun _ => 1) (d *ᵥ φ) = ip (fun _ => 1) (fun _ => 1) σ at ht
  rw [hconst, ip_zero_left] at ht
  simpa [ip] using ht.symm

/-- [proved-derived; formal-checked] **A route return is an admissible charge.** A rational source
whose complex image is a `HolonicWorldReturnDeposit.routeDeposit` has zero total, which is the
necessary condition `source_total_zero` places on every balanced source. -/
theorem route_return_has_zero_charge (δ : ℂ)
    (route : List (Computation.HolonicWorldReturnDeposit.RouteStep (Fin p)))
    (σ : Fin p → ℚ)
    (hσ : ∀ i, (σ i : ℂ) = Computation.HolonicWorldReturnDeposit.routeDeposit δ route i) :
    ∑ i, σ i = 0 := by
  have h := Computation.HolonicWorldReturnDeposit.sum_routeDeposit δ route
  simp_rw [← hσ] at h
  exact_mod_cast h

/-! ## 3. Deposition and its locality -/

/-- [definition] **A deposition law.** `Γ e j g` is the change of edge `e`'s conductance, reading
only that edge's flux `j` and drop `g`; it keeps every actual (`j = θ g`) constitution positive. -/
structure DepositionLaw (q : ℕ) where
  /-- The edgewise deposit. -/
  Γ : Fin q → ℚ → ℚ → ℚ
  /-- A deposit at an actual flux keeps the conductance positive. -/
  keepsPositive : ∀ e θ g, 0 < θ → 0 < θ + Γ e (θ * g) g

/-- [definition] **Deposition**: `Θ'_e = Θ_e + Γ_e(j_e, (dφ)_e)`. -/
def deposit (L : DepositionLaw q) (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q)
    (φ : Fin p → ℚ) : Constitution q :=
  ⟨fun e => Θ.1 e + L.Γ e (flux d Θ φ e) ((d *ᵥ φ) e),
    fun e => L.keepsPositive e _ _ (Θ.2 e)⟩

/-- [proved-derived; formal-checked] **Edgewise locality.** Two configurations that agree in
conductance, flux and drop on the edges of `U` deposit identical constitutions on `U`. -/
theorem deposit_local_edges (L : DepositionLaw q) {d d' : Matrix (Fin q) (Fin p) ℚ}
    {Θ Θ' : Constitution q} {φ φ' : Fin p → ℚ} (U : Finset (Fin q))
    (hΘ : ∀ e ∈ U, Θ.1 e = Θ'.1 e) (hj : ∀ e ∈ U, flux d Θ φ e = flux d' Θ' φ' e)
    (hg : ∀ e ∈ U, (d *ᵥ φ) e = (d' *ᵥ φ') e) :
    ∀ e ∈ U, (deposit L d Θ φ).1 e = (deposit L d' Θ' φ').1 e := by
  intro e he
  simp only [deposit]
  rw [hΘ e he, hj e he, hg e he]

/-- [proved-derived; formal-checked] **Regional locality.** If the potentials agree on a node
region `A` containing every node incident to the edges of `U`, and the constitutions agree on
`U`, the deposited constitutions agree on `U`: what happened off `A` does not reach `U`. -/
theorem deposit_local_region (L : DepositionLaw q) (d : Matrix (Fin q) (Fin p) ℚ)
    {Θ Θ' : Constitution q} {φ φ' : Fin p → ℚ} (A : Finset (Fin p)) (U : Finset (Fin q))
    (incident : ∀ e ∈ U, ∀ i, d e i ≠ 0 → i ∈ A) (hφ : ∀ i ∈ A, φ i = φ' i)
    (hΘ : ∀ e ∈ U, Θ.1 e = Θ'.1 e) :
    ∀ e ∈ U, (deposit L d Θ φ).1 e = (deposit L d Θ' φ').1 e := by
  have hg : ∀ e ∈ U, (d *ᵥ φ) e = (d *ᵥ φ') e := by
    intro e he
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : d e i = 0
    · simp [hi]
    · rw [hφ i (incident e he i hi)]
  refine deposit_local_edges L U hΘ ?_ hg
  intro e he
  simp only [flux]
  rw [hΘ e he, hg e he]

/-- [proved-derived; formal-checked] **An edge reached by no flux is unchanged** when the law
deposits nothing at zero flux and zero drop: a positive conductance with zero flux has zero drop. -/
theorem unreached_edge_unchanged (L : DepositionLaw q) (hzero : ∀ e, L.Γ e 0 0 = 0)
    (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) (φ : Fin p → ℚ) {e : Fin q}
    (he : flux d Θ φ e = 0) : (deposit L d Θ φ).1 e = Θ.1 e := by
  have hg : (d *ᵥ φ) e = 0 := by
    rcases mul_eq_zero.mp he with hθ | hg
    · exact absurd hθ (ne_of_gt (Θ.2 e))
    · exact hg
  simp only [deposit]
  rw [he, hg, hzero, add_zero]

/-- [proved-derived; formal-checked] Deposition depends on the solved potential only through the
constitution and the source: any two solutions deposit the same constitution. -/
theorem deposit_eq_of_solves (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ}
    {Θ : Constitution q} {φ φ' σ : Fin p → ℚ} (h : Solves d Θ φ σ) (h' : Solves d Θ φ' σ) :
    deposit L d Θ φ = deposit L d Θ φ' := by
  apply Subtype.ext
  funext e
  simp [deposit, flux_unique h h', drop_unique h h']

/-! ## 4. The constitution suffices for every solver's future; the last flux does not -/

/-- [definition] The present of a depositing medium: its constitution together with the complete
record of the fluxes that shaped it. The record is carried so that its insufficiency can be
proved, not because anything reads it. -/
structure DepositState (q : ℕ) where
  /-- The constitution. -/
  constitution : Constitution q
  /-- The flux record, most recent first. -/
  record : List (Fin q → ℚ)

/-- [definition] **A solver.** It may consult the whole flux record (for example to choose the
gauge of its potential); it must return a solution whenever one exists. -/
structure Solver (d : Matrix (Fin q) (Fin p) ℚ) where
  /-- The returned potential. -/
  solve : List (Fin q → ℚ) → Constitution q → (Fin p → ℚ) → (Fin p → ℚ)
  /-- It solves whenever the balance is solvable. -/
  solves : ∀ record Θ σ, (∃ φ, Solves d Θ φ σ) → Solves d Θ (solve record Θ σ) σ

open Classical in
/-- [definition] **One admitted step.** Under a source `σ`: solve the balance, deposit, and append
the flux to the record. An unsolvable source changes nothing. -/
def step (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ} (S : Solver d) (σ : Fin p → ℚ)
    (state : DepositState q) : DepositState q :=
  if ∃ φ, Solves d state.constitution φ σ then
    ⟨deposit L d state.constitution (S.solve state.record state.constitution σ),
      flux d state.constitution (S.solve state.record state.constitution σ) :: state.record⟩
  else state

open Classical in
/-- [definition] **The future observation**: the flux of the actual solve under a source, or
`none` when the source admits no balance. -/
def observe {d : Matrix (Fin q) (Fin p) ℚ} (S : Solver d) (σ : Fin p → ℚ)
    (state : DepositState q) : Option (Fin q → ℚ) :=
  if ∃ φ, Solves d state.constitution φ σ then
    some (flux d state.constitution (S.solve state.record state.constitution σ))
  else none

open Classical in
/-- [definition] The canonical potential: some solution when one exists. -/
def canonicalSolve (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) (σ : Fin p → ℚ) :
    Fin p → ℚ :=
  if h : ∃ φ, Solves d Θ φ σ then h.choose else 0

open Classical in
/-- [definition] The step read on the constitution alone. -/
def stepConstitution (L : DepositionLaw q) (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ)
    (Θ : Constitution q) : Constitution q :=
  if ∃ φ, Solves d Θ φ σ then deposit L d Θ (canonicalSolve d Θ σ) else Θ

open Classical in
/-- [definition] The observation read on the constitution alone. -/
def observeConstitution (d : Matrix (Fin q) (Fin p) ℚ) (σ : Fin p → ℚ) (Θ : Constitution q) :
    Option (Fin q → ℚ) :=
  if ∃ φ, Solves d Θ φ σ then some (flux d Θ (canonicalSolve d Θ σ)) else none

theorem canonicalSolve_solves {d : Matrix (Fin q) (Fin p) ℚ} {Θ : Constitution q}
    {σ : Fin p → ℚ} (h : ∃ φ, Solves d Θ φ σ) : Solves d Θ (canonicalSolve d Θ σ) σ := by
  rw [canonicalSolve, dif_pos h]
  exact h.choose_spec

/-- [proved-derived; formal-checked] A solvable step deposits and records the flux of *any*
solution. -/
theorem step_of_solves (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ} (S : Solver d)
    {σ φ : Fin p → ℚ} {state : DepositState q} (h : Solves d state.constitution φ σ) :
    step L S σ state =
      ⟨deposit L d state.constitution φ, flux d state.constitution φ :: state.record⟩ := by
  have hS := S.solves state.record state.constitution σ ⟨φ, h⟩
  rw [step, if_pos ⟨φ, h⟩, deposit_eq_of_solves L hS h, flux_unique hS h]

/-- [proved-derived; formal-checked] A solvable observation reads the flux of any solution. -/
theorem observe_of_solves {d : Matrix (Fin q) (Fin p) ℚ} (S : Solver d)
    {σ φ : Fin p → ℚ} {state : DepositState q} (h : Solves d state.constitution φ σ) :
    observe S σ state = some (flux d state.constitution φ) := by
  have hS := S.solves state.record state.constitution σ ⟨φ, h⟩
  rw [observe, if_pos ⟨φ, h⟩, flux_unique hS h]

theorem step_constitution (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ} (S : Solver d)
    (σ : Fin p → ℚ) (state : DepositState q) :
    (step L S σ state).constitution = stepConstitution L d σ state.constitution := by
  by_cases h : ∃ φ, Solves d state.constitution φ σ
  · rw [step_of_solves L S (canonicalSolve_solves h), stepConstitution, if_pos h]
  · rw [step, if_neg h, stepConstitution, if_neg h]

theorem observe_eq_observeConstitution {d : Matrix (Fin q) (Fin p) ℚ} (S : Solver d)
    (σ : Fin p → ℚ) (state : DepositState q) :
    observe S σ state = observeConstitution d σ state.constitution := by
  by_cases h : ∃ φ, Solves d state.constitution φ σ
  · rw [observe_of_solves S (canonicalSolve_solves h), observeConstitution, if_pos h]
  · rw [observe, if_neg h, observeConstitution, if_neg h]

/-- [proved-derived; formal-checked] Along every ordered history the constitution evolves by the
constitution-only step: the record and the solver's gauge never enter it. -/
theorem transportWord_constitution (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ}
    (S : Solver d) (word : List (Fin p → ℚ)) (state : DepositState q) :
    (transportWord (step L S) word state).constitution =
      transportWord (stepConstitution L d) word state.constitution := by
  induction word with
  | nil => rfl
  | cons σ word ih => rw [transportWord_cons, transportWord_cons, step_constitution, ih]

/-- [proved-derived; formal-checked] **The constitution is a lawful retention (StandingLaw).**
It suffices for every solver's future; it is not claimed minimal. Receivers are
admitted sources; histories are ordered source words; the future observation is the flux of the
actual later solve. The constitution alone reopens every such observation, for every solver —
including one whose potential depends on the flux record. -/
def constitutionStanding (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ} (S : Solver d) :
    StandingLaw (Fin p → ℚ) (Fin p → ℚ) (DepositState q) (Constitution q)
      (Option (Fin q → ℚ)) where
  transport := step L S
  observe := observe S
  retain := DepositState.constitution
  reopen σ word Θ := observeConstitution d σ (transportWord (stepConstitution L d) word Θ)
  sufficient σ word state := by
    rw [observe_eq_observeConstitution, transportWord_constitution]

/-- [proved-derived; formal-checked] Equal constitutions carry equal admitted futures, whatever
flux records lie behind them (`StandingLaw.futureAgreement_of_retain_eq`). -/
theorem equal_constitution_equal_future (L : DepositionLaw q) {d : Matrix (Fin q) (Fin p) ℚ}
    (S : Solver d) {left right : DepositState q} (h : left.constitution = right.constitution) :
    Foundation.CausalRelevance.NonLinear.futureAgreement (observe S) (step L S) left right :=
  (constitutionStanding L S).futureAgreement_of_retain_eq h

/-! ## 5. The smallest instance: two parallel edges -/

/-- [definition] Two parallel edges from node `0` to node `1`. -/
def parallel : Matrix (Fin 2) (Fin 2) ℚ := !![-1, 1; -1, 1]

/-- [definition] The unit source: one unit leaves at node `0` and arrives at node `1`. -/
def unitSource : Fin 2 → ℚ := ![-1, 1]

/-- [definition] **The square law** `Γ_e = j_e²`: breakdown/erosion raising conductance by the
square of the current carried. -/
def squareLaw : DepositionLaw 2 where
  Γ _ j _ := j ^ 2
  keepsPositive _ _ _ hθ := by positivity

/-- [definition] **The Joule law** `Γ_e = j_e (dφ)_e`, the power dissipated on the edge. -/
def jouleLaw : DepositionLaw 2 where
  Γ _ j g := j * g
  keepsPositive _ θ g hθ := by nlinarith [sq_nonneg g, mul_pos hθ hθ]

/-- [definition] The starting constitution `(1, 2)`. -/
def Θ₀ : Constitution 2 := ⟨![1, 2], by intro e; fin_cases e <;> norm_num⟩

/-- [proved-derived; formal-checked] On the parallel pair, `φ` solves the unit source exactly
when the common drop times the total conductance is one. -/
theorem parallel_solves_iff (Θ : Constitution 2) (φ : Fin 2 → ℚ) :
    Solves parallel Θ φ unitSource ↔ (Θ.1 0 + Θ.1 1) * (φ 1 - φ 0) = 1 := by
  rw [solves_iff_boundary_flux]
  constructor
  · intro h
    have h1 := congrFun h 1
    simp [parallel, unitSource, flux, mulVec, dotProduct, Fin.sum_univ_two] at h1
    linarith
  · intro h
    funext i
    fin_cases i <;>
      simp [parallel, unitSource, flux, mulVec, dotProduct, Fin.sum_univ_two] <;> linarith

/-- [proved-derived; formal-checked] The zero source is solved by the zero potential. -/
theorem zero_solves (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) : Solves d Θ 0 0 := by
  simp [Solves]

theorem flux_zero (d : Matrix (Fin q) (Fin p) ℚ) (Θ : Constitution q) : flux d Θ 0 = 0 := by
  funext e; simp [flux]

/-- [definition] The constitution after one square-law unit stroke on `Θ₀`: `(10/9, 22/9)`. -/
def Θ₁ : Constitution 2 := ⟨![10 / 9, 22 / 9], by intro e; fin_cases e <;> norm_num⟩

/-- [definition] The constitution after one Joule-law unit stroke on `Θ₀`: `(10/9, 20/9)`. -/
def Θ₁' : Constitution 2 := ⟨![10 / 9, 20 / 9], by intro e; fin_cases e <;> norm_num⟩

theorem solves_Θ₀ : Solves parallel Θ₀ ![0, 1 / 3] unitSource := by
  rw [parallel_solves_iff]; simp [Θ₀]; norm_num

theorem solves_Θ₁ : Solves parallel Θ₁ ![0, 9 / 32] unitSource := by
  rw [parallel_solves_iff]; simp [Θ₁]; norm_num

theorem solves_Θ₁' : Solves parallel Θ₁' ![0, 3 / 10] unitSource := by
  rw [parallel_solves_iff]; simp [Θ₁']; norm_num

theorem flux_Θ₀ : flux parallel Θ₀ ![0, 1 / 3] = ![1 / 3, 2 / 3] := by
  funext e; fin_cases e <;> simp [flux, Θ₀, parallel, mulVec, dotProduct]; norm_num

theorem deposit_square_Θ₀ : deposit squareLaw parallel Θ₀ ![0, 1 / 3] = Θ₁ := by
  apply Subtype.ext
  funext e
  fin_cases e <;> simp [deposit, squareLaw, flux, Θ₀, Θ₁, parallel, mulVec, dotProduct] <;> norm_num

theorem deposit_joule_Θ₀ : deposit jouleLaw parallel Θ₀ ![0, 1 / 3] = Θ₁' := by
  apply Subtype.ext
  funext e
  fin_cases e <;> simp [deposit, jouleLaw, flux, Θ₀, Θ₁', parallel, mulVec, dotProduct] <;> norm_num

/-- [proved-derived; formal-checked] **A deposit bends later flux.** On `Θ₀ = (1, 2)` the unit
source splits `(1/3, 2/3)`. The square law deposits `(1/9, 4/9)`, and every potential solving
the same source on the deposited constitution splits it `(5/16, 11/16)`: the heavier channel's
share grows from `2/3` to `11/16`. This is the lightning/canyon mechanism at its smallest. -/
theorem square_deposit_bends_the_next_split :
    (∀ φ, Solves parallel Θ₀ φ unitSource → flux parallel Θ₀ φ = ![1 / 3, 2 / 3]) ∧
      (∀ φ, Solves parallel Θ₀ φ unitSource → deposit squareLaw parallel Θ₀ φ = Θ₁) ∧
      (∀ φ, Solves parallel Θ₁ φ unitSource → flux parallel Θ₁ φ = ![5 / 16, 11 / 16]) ∧
      (2 / 3 : ℚ) < 11 / 16 := by
  refine ⟨fun φ h => ?_, fun φ h => ?_, fun φ h => ?_, by norm_num⟩
  · rw [flux_unique h solves_Θ₀, flux_Θ₀]
  · rw [deposit_eq_of_solves squareLaw h solves_Θ₀, deposit_square_Θ₀]
  · rw [flux_unique h solves_Θ₁]
    funext e; fin_cases e <;> simp [flux, Θ₁, parallel, mulVec, dotProduct] <;> norm_num

/-- [proved-derived; formal-checked] **A proportional deposit does not bend.** The Joule law on
the parallel pair deposits in proportion `(1/9, 2/9)` to the conductances, so the constitution
changes to `(10/9, 20/9)` and the next split is again `(1/3, 2/3)`. -/
theorem joule_deposit_keeps_the_split :
    (∀ φ, Solves parallel Θ₀ φ unitSource → deposit jouleLaw parallel Θ₀ φ = Θ₁') ∧
      Θ₁' ≠ Θ₀ ∧
      (∀ φ, Solves parallel Θ₁' φ unitSource → flux parallel Θ₁' φ = ![1 / 3, 2 / 3]) := by
  refine ⟨fun φ h => ?_, ?_, fun φ h => ?_⟩
  · rw [deposit_eq_of_solves jouleLaw h solves_Θ₀, deposit_joule_Θ₀]
  · intro h
    have := congrArg (fun Θ : Constitution 2 => Θ.1 0) h
    norm_num [Θ₁', Θ₀] at this
  · rw [flux_unique h solves_Θ₁']
    funext e; fin_cases e <;> simp [flux, Θ₁', parallel, mulVec, dotProduct] <;> norm_num

/-! ### The separation witness -/

/-- [definition] The fresh medium: constitution `Θ₀`, empty record. -/
def fresh : DepositState 2 := ⟨Θ₀, []⟩

/-- [definition] The last flux, a proposed (and refuted) retention. -/
def lastFlux (state : DepositState q) : Option (Fin q → ℚ) := state.record.head?

theorem history_quiet (S : Solver parallel) :
    transportWord (step squareLaw S) [0] fresh = ⟨Θ₀, [0]⟩ := by
  rw [transportWord_cons, transportWord_nil, step_of_solves squareLaw S (zero_solves _ _)]
  congr 1
  · apply Subtype.ext
    funext e
    simp [deposit, squareLaw, flux, fresh]
  · simp [fresh, flux_zero]

theorem history_struck (S : Solver parallel) :
    transportWord (step squareLaw S) [0, unitSource] fresh = ⟨Θ₁, [0, ![1 / 3, 2 / 3]]⟩ := by
  rw [transportWord_cons, transportWord_cons, transportWord_nil,
    step_of_solves squareLaw S (state := fresh) solves_Θ₀]
  simp only [fresh]
  rw [deposit_square_Θ₀, flux_Θ₀, step_of_solves squareLaw S (zero_solves _ _)]
  congr 1
  · apply Subtype.ext
    funext e
    simp [deposit, squareLaw, flux]
  · simp [flux_zero]

/-- [proved-derived; formal-checked] **Equal last flux, different constitution, separated by a
later source.** One history is quiet (a zero source on `Θ₀`); the other strikes once with the
unit source and then is quiet. Both end with zero flux. Their constitutions differ, and the next
unit source splits `(1/3, 2/3)` on one and `(5/16, 11/16)` on the other — for every solver. -/
theorem equal_last_flux_separated_later (S : Solver parallel) :
    lastFlux (transportWord (step squareLaw S) [0] fresh) =
        lastFlux (transportWord (step squareLaw S) [0, unitSource] fresh) ∧
      (transportWord (step squareLaw S) [0] fresh).constitution ≠
        (transportWord (step squareLaw S) [0, unitSource] fresh).constitution ∧
      observe S unitSource (transportWord (step squareLaw S) [0] fresh) =
        some ![1 / 3, 2 / 3] ∧
      observe S unitSource (transportWord (step squareLaw S) [0, unitSource] fresh) =
        some ![5 / 16, 11 / 16] := by
  rw [history_quiet, history_struck]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun Θ : Constitution 2 => Θ.1 0) h
    norm_num [Θ₁, Θ₀] at this
  · rw [observe_of_solves S (state := ⟨Θ₀, [0]⟩) solves_Θ₀, flux_Θ₀]
  · rw [observe_of_solves S (state := ⟨Θ₁, _⟩) solves_Θ₁]
    congr 1
    funext e; fin_cases e <;> simp [flux, Θ₁, parallel, mulVec, dotProduct] <;> norm_num

/-- [counterexample; formal-checked] **The last flux is not a lawful retention (StandingLaw).**
No `StandingLaw` for
the square-law medium retains only the last flux: the later unit source separates two presents
with equal last flux (`StandingLaw.separating_future_refutes_the_standing`). -/
theorem last_flux_is_not_a_standing (S : Solver parallel) :
    ¬ ∃ L : StandingLaw (Fin 2 → ℚ) (Fin 2 → ℚ) (DepositState 2) (Option (Fin 2 → ℚ))
        (Option (Fin 2 → ℚ)),
      L.transport = step squareLaw S ∧ L.observe = observe S ∧ L.retain = lastFlux := by
  rintro ⟨L, htransport, hobserve, hretain⟩
  obtain ⟨hlast, -, hA, hB⟩ := equal_last_flux_separated_later S
  have hsep : L.observe unitSource (transportWord L.transport []
        (transportWord (step squareLaw S) [0] fresh)) ≠
      L.observe unitSource (transportWord L.transport []
        (transportWord (step squareLaw S) [0, unitSource] fresh)) := by
    rw [hobserve, transportWord_nil, transportWord_nil, hA, hB]
    intro h
    have := congrFun (Option.some.inj h) 0
    norm_num at this
  exact L.separating_future_refutes_the_standing unitSource [] hsep (by rw [hretain]; exact hlast)

/-! ### The constitution is sufficient but not minimal -/

/-- [proved-derived; formal-checked] On the parallel pair, `φ` solves `σ` exactly when `σ` is the
signed common drop times the total conductance. -/
theorem parallel_solves_iff_source (Θ : Constitution 2) (φ σ : Fin 2 → ℚ) :
    Solves parallel Θ φ σ ↔
      σ = ![-((Θ.1 0 + Θ.1 1) * (φ 1 - φ 0)), (Θ.1 0 + Θ.1 1) * (φ 1 - φ 0)] := by
  rw [solves_iff_boundary_flux]
  have key : parallelᵀ *ᵥ flux parallel Θ φ =
      ![-((Θ.1 0 + Θ.1 1) * (φ 1 - φ 0)), (Θ.1 0 + Θ.1 1) * (φ 1 - φ 0)] := by
    funext i
    fin_cases i <;> simp [parallel, flux, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  rw [key]
  exact eq_comm

/-- [definition] A symmetric constitution on the parallel pair. -/
def Symmetric (Θ : Constitution 2) : Prop := Θ.1 0 = Θ.1 1

/-- [proved-derived; formal-checked] On a symmetric constitution a source is solvable exactly when
its total charge is zero, and every solution splits it evenly. -/
theorem symmetric_solve {Θ : Constitution 2} (hs : Symmetric Θ) (σ : Fin 2 → ℚ) :
    ((∃ φ, Solves parallel Θ φ σ) ↔ σ 0 + σ 1 = 0) ∧
      ∀ φ, Solves parallel Θ φ σ → flux parallel Θ φ = ![σ 1 / 2, σ 1 / 2] := by
  have hpos : 0 < Θ.1 0 + Θ.1 1 := add_pos (Θ.2 0) (Θ.2 1)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro ⟨φ, h⟩
    rw [parallel_solves_iff_source] at h
    rw [h]
    simp
  · intro hσ
    refine ⟨![0, σ 1 / (Θ.1 0 + Θ.1 1)], ?_⟩
    rw [parallel_solves_iff_source]
    funext i
    fin_cases i
    · simp; field_simp; linarith
    · simp; field_simp
  · intro φ h
    rw [parallel_solves_iff_source] at h
    have h1 := congrFun h 1
    simp at h1
    funext e
    fin_cases e <;> simp [flux, parallel, mulVec, dotProduct, Fin.sum_univ_two] <;>
      rw [h1, hs] <;> ring

/-- [proved-derived; formal-checked] The square law keeps a symmetric constitution symmetric. -/
theorem symmetric_stepConstitution {Θ : Constitution 2} (hs : Symmetric Θ) (σ : Fin 2 → ℚ) :
    Symmetric (stepConstitution squareLaw parallel σ Θ) := by
  unfold stepConstitution
  split_ifs with h
  · have hflux := (symmetric_solve hs σ).2 _ (canonicalSolve_solves h)
    unfold Symmetric
    simp only [deposit, squareLaw]
    rw [hflux, hs]
    simp
  · exact hs

theorem symmetric_transportWord {Θ : Constitution 2} (hs : Symmetric Θ)
    (word : List (Fin 2 → ℚ)) :
    Symmetric (transportWord (stepConstitution squareLaw parallel) word Θ) := by
  induction word with
  | nil => exact hs
  | cons σ word ih => exact symmetric_stepConstitution ih σ

open Classical in
/-- [proved-derived; formal-checked] On a symmetric constitution the observation depends on the
source alone. -/
theorem symmetric_observe {Θ : Constitution 2} (hs : Symmetric Θ) (σ : Fin 2 → ℚ) :
    observeConstitution parallel σ Θ =
      if σ 0 + σ 1 = 0 then some ![σ 1 / 2, σ 1 / 2] else none := by
  by_cases h : ∃ φ, Solves parallel Θ φ σ
  · rw [observeConstitution, if_pos h, if_pos ((symmetric_solve hs σ).1.mp h),
      (symmetric_solve hs σ).2 _ (canonicalSolve_solves h)]
  · rw [observeConstitution, if_neg h,
      if_neg (fun h' => h ((symmetric_solve hs σ).1.mpr h'))]

/-- [definition] The symmetric constitutions `(1, 1)` and `(2, 2)`. -/
def Θone : Constitution 2 := ⟨![1, 1], by intro e; fin_cases e <;> norm_num⟩
def Θtwo : Constitution 2 := ⟨![2, 2], by intro e; fin_cases e <;> norm_num⟩

/-- [counterexample; formal-checked] **The constitution is not minimal.** Under the square law on
the parallel pair, the distinct constitutions `(1, 1)` and `(2, 2)` — with any flux records —
return identical flux under every admitted source after every ordered history, for every solver.
The constitution is a sufficient retention (StandingLaw); the minimal one is a proper quotient
of it (here, at least, symmetric constitutions collapse). -/
theorem constitution_is_not_minimal (S : Solver parallel) (left right : List (Fin 2 → ℚ)) :
    Θone ≠ Θtwo ∧
      Foundation.CausalRelevance.NonLinear.futureAgreement (observe S) (step squareLaw S)
        ⟨Θone, left⟩ ⟨Θtwo, right⟩ := by
  have hone : Symmetric Θone := by simp [Symmetric, Θone]
  have htwo : Symmetric Θtwo := by simp [Symmetric, Θtwo]
  refine ⟨?_, ?_⟩
  · intro h
    have := congrArg (fun Θ : Constitution 2 => Θ.1 0) h
    norm_num [Θone, Θtwo] at this
  · intro σ word
    rw [observe_eq_observeConstitution, observe_eq_observeConstitution,
      transportWord_constitution, transportWord_constitution,
      symmetric_observe (symmetric_transportWord hone word),
      symmetric_observe (symmetric_transportWord htwo word)]

/-! ## 6. The normal law is a deposition on a symmetric-form constitution -/

section Normal

open Holonics.Physics.AccumulatedNormalResponse
open scoped ComplexOrder

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- [proved-derived; formal-checked] **The normal law is local to the support of its feature.**
`H + x xᴴ` changes entry `(i, j)` only where both `x i` and `x j` are nonzero. -/
theorem normal_law_local (H : Matrix ι ι ℂ) (x : Column ι) (i j : ι)
    (h : x i () = 0 ∨ x j () = 0) : updatedGram H x i j = H i j := by
  rcases h with h | h <;> simp [updatedGram, Matrix.mul_apply, h]

/-- [proved-derived; formal-checked] **The normal law keeps a positive semidefinite constitution
positive semidefinite.** -/
theorem normal_law_keeps_posSemidef {H : Matrix ι ι ℂ} (hH : H.PosSemidef) (x : Column ι) :
    (updatedGram H x).PosSemidef :=
  hH.add (Matrix.posSemidef_self_mul_conjTranspose x)

omit [Fintype ι] in
/-- [proved-derived; formal-checked] **The weighted normal law** `H ↦ H + w f fᴴ` with
`w = c² ≥ 0` is `updatedGram` at the scaled feature `c f`. -/
theorem weighted_normal_law (H : Matrix ι ι ℂ) (x : Column ι) (c : ℝ) :
    updatedGram H ((c : ℂ) • x) = H + ((c ^ 2 : ℝ) : ℂ) • (x * xᴴ) := by
  rw [updatedGram, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring_nf

/-- [definition] The single-edge feature carrying the flux of edge `e`. -/
def edgeFeature (j : Fin q → ℚ) (e : Fin q) : Column (Fin q) :=
  fun i _ => if i = e then ((j e : ℚ) : ℂ) else 0

/-- [proved-derived; formal-checked] **The edge square law is the edgewise normal law.** The
diagonal of the square-law deposit `Θ_e + j_e²` is the normal law's rank-one increment summed over
one single-edge feature per edge, each local to its own edge by `normal_law_local`. -/
theorem square_law_is_the_edgewise_normal_law (Θ j : Fin q → ℚ) :
    Matrix.diagonal (fun e => (((Θ e + j e ^ 2 : ℚ)) : ℂ)) =
      Matrix.diagonal (fun e => ((Θ e : ℚ) : ℂ)) +
        ∑ e, edgeFeature j e * (edgeFeature j e)ᴴ := by
  ext a b
  simp only [Matrix.add_apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    edgeFeature, Finset.univ_unique, Finset.sum_singleton]
  by_cases hab : a = b
  · subst hab
    simp [Matrix.diagonal_apply_eq, pow_two]
  · rw [Matrix.diagonal_apply_ne _ hab, Matrix.diagonal_apply_ne _ hab, zero_add]
    symm
    apply Finset.sum_eq_zero
    intro e _
    by_cases hae : a = e
    · subst hae
      simp [Ne.symm hab]
    · simp [hae]

end Normal

end Holonics.Objects.Deposition

section Audit
open Holonics.Objects.Deposition
#print axioms solves_iff_boundary_flux
#print axioms solves_iff_balanced
#print axioms joule_ledger
#print axioms dissipation_zero_iff_no_flux
#print axioms drop_unique
#print axioms flux_unique
#print axioms source_total_zero
#print axioms route_return_has_zero_charge
#print axioms deposit_local_edges
#print axioms deposit_local_region
#print axioms unreached_edge_unchanged
#print axioms deposit_eq_of_solves
#print axioms transportWord_constitution
#print axioms constitutionStanding
#print axioms equal_constitution_equal_future
#print axioms square_deposit_bends_the_next_split
#print axioms joule_deposit_keeps_the_split
#print axioms equal_last_flux_separated_later
#print axioms last_flux_is_not_a_standing
#print axioms symmetric_solve
#print axioms constitution_is_not_minimal
#print axioms normal_law_local
#print axioms normal_law_keeps_posSemidef
#print axioms weighted_normal_law
#print axioms square_law_is_the_edgewise_normal_law
end Audit
