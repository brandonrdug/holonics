import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Nat.Lattice
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Tactic

/-!
# Frustration is a class function, and relaxing the potential keeps every holonomy

The record `research/records/2026-10-26_INFORMATION_DIFFUSES_IN_THE_POTENTIAL_TRAVELS_IN_THE_TURN_AND_A_KEY_IS_READ_FROM_DIFFUSION_ONLY_TO_ITS_SQUARE_ROOT.md`
(§0 statements 3 and 7; atlas `key.gauge-orbit`, `key.connection-cheeger`) reads the frustration of
a connection, the least weight of the contacts a section must break, as a function of its holonomy
class, and reads relaxation by the potential as a move inside that class. #410 owes both; this file
proves them on any finite graph with a connection valued in an additive group (`ℤ_k`, `ℤ`, a
torus). It extends `Holon/Complex.exact_closed_iff_flat` (a pure gauge is flat) from one triangle to
every closed chain.

[proved-standard; formal-checked] What is proved.

1. **A gauge move carries the broken contacts** (`holds_gauge`, `cost_gauge`): moving the
   connection by the coboundary of `g`, `c' = c + d₀g`, and the section by `g`, `σ' = σ + g`, keeps
   exactly the same contacts closed, so the same weight broken.
2. **Frustration is a class function** (`frustration_gauge_invariant`): the least broken weight is
   unchanged by every gauge move.
3. **An exact cochain has no circulation on a cycle** (`circulation_coboundary`,
   `circulation_gauge`): `Σ_e z_e (g(tgt e) − g(src e)) = Σ_v (∂z)(v) g(v)`, which vanishes when
   `∂z = 0`, so a gauge move keeps every circulation.
4. **Relaxing the potential keeps every holonomy and every frustration** (`relax_eq_gauge`,
   `relax_keeps_holonomy`, `frustration_relax`): the step `c ← c − τ d₀(d₀ᵀc)` is the gauge move by
   `−τ d₀ᵀc`, so it keeps every circulation and never lowers a frustration.

The computational object is the helical pair interaction: a contact carries its turn, a section is
a reading of the strand, and a contact breaks where the reading slips. Of the winding guide's six
general objects this touches the pair (the contact's turn) and the cell holonomy (the circulation
on a cycle); the helix, faces and placement, the tube and the tower thread stay attached.

Consumers: the atlas rows `key.gauge-orbit` and `key.connection-cheeger`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.Frustration

/-- [definition] The contacts of a graph: each contact runs from `src` to `tgt`. -/
structure Contacts (V E : Type*) where
  /-- The contact's source vertex. -/
  src : E → V
  /-- The contact's target vertex. -/
  tgt : E → V

namespace Contacts

variable {V E G : Type*} [AddCommGroup G] (Γ : Contacts V E)

/-- [definition] The coboundary `(d₀ g)(e) = g(tgt e) − g(src e)`. -/
def coboundary (g : V → G) (e : E) : G := g (Γ.tgt e) - g (Γ.src e)

/-- [definition] The gauge move of a connection by `g`: `c + d₀ g`. -/
def gauge (c : E → G) (g : V → G) : E → G := c + Γ.coboundary g

/-- [proved-standard; formal-checked] **A gauge move carries the closed contacts:** the moved
section closes a contact of the moved connection exactly where the section closed it. -/
theorem holds_gauge (c : E → G) (g σ : V → G) (e : E) :
    (σ + g) (Γ.tgt e) = (σ + g) (Γ.src e) + Γ.gauge c g e ↔ σ (Γ.tgt e) = σ (Γ.src e) + c e := by
  have h : (σ + g) (Γ.src e) + Γ.gauge c g e = σ (Γ.src e) + c e + g (Γ.tgt e) := by
    simp only [gauge, coboundary, Pi.add_apply]
    abel
  rw [h, Pi.add_apply, add_left_inj]

section Cost

variable [Fintype E] [DecidableEq G]

/-- [definition] The weight of the contacts a section breaks. -/
def cost (w : E → ℕ) (c : E → G) (σ : V → G) : ℕ :=
  ∑ e, if σ (Γ.tgt e) = σ (Γ.src e) + c e then 0 else w e

/-- [definition] The frustration of a connection: the least weight a section must break. -/
noncomputable def frustration (w : E → ℕ) (c : E → G) : ℕ := ⨅ σ : V → G, Γ.cost w c σ

/-- [proved-standard; formal-checked] A gauge move keeps the broken weight of the moved section. -/
theorem cost_gauge (w : E → ℕ) (c : E → G) (g σ : V → G) :
    Γ.cost w (Γ.gauge c g) (σ + g) = Γ.cost w c σ := by
  unfold cost
  refine Finset.sum_congr rfl fun e _ => ?_
  by_cases h : σ (Γ.tgt e) = σ (Γ.src e) + c e
  · rw [if_pos ((Γ.holds_gauge c g σ e).mpr h), if_pos h]
  · rw [if_neg (mt (Γ.holds_gauge c g σ e).mp h), if_neg h]

/-- [proved-standard; formal-checked] **Frustration is a class function:** it is unchanged by every
gauge move. -/
theorem frustration_gauge_invariant (w : E → ℕ) (c : E → G) (g : V → G) :
    Γ.frustration w (Γ.gauge c g) = Γ.frustration w c := by
  unfold frustration
  refine (Equiv.iInf_congr (Equiv.addRight g) fun σ => ?_).symm
  first
    | exact Γ.cost_gauge w c g σ
    | simpa using Γ.cost_gauge w c g σ

end Cost

section Circulation

variable [Fintype E]

/-- [definition] The circulation of a connection on an integral chain, `Σ_e z_e c_e`. -/
def circulation (z : E → ℤ) (c : E → G) : G := ∑ e, z e • c e

/-- [proved-standard; formal-checked] Circulation is additive in the connection. -/
theorem circulation_add (z : E → ℤ) (c c' : E → G) :
    circulation z (c + c') = circulation z c + circulation z c' := by
  simp only [circulation, Pi.add_apply, smul_add, Finset.sum_add_distrib]

variable [Fintype V] [DecidableEq V]

/-- [definition] The boundary of an integral chain, `(∂z)(v) = Σ_(tgt e = v) z_e − Σ_(src e = v) z_e`. -/
def boundary (z : E → ℤ) (v : V) : ℤ :=
  ∑ e, (if Γ.tgt e = v then z e else 0) - ∑ e, (if Γ.src e = v then z e else 0)

/-- [proved-standard; formal-checked] Summing over the ends of the contacts. -/
theorem sum_end (z : E → ℤ) (g : V → G) (π : E → V) :
    ∑ v, (∑ e, if π e = v then z e else 0) • g v = ∑ e, z e • g (π e) := by
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp

/-- [proved-standard; formal-checked] **The circulation of an exact cochain is read on the boundary:**
`Σ_e z_e (g(tgt e) − g(src e)) = Σ_v (∂z)(v) g(v)`. -/
theorem circulation_coboundary (z : E → ℤ) (g : V → G) :
    circulation z (Γ.coboundary g) = ∑ v, Γ.boundary z v • g v := by
  simp only [circulation, coboundary, boundary, smul_sub, sub_smul, Finset.sum_sub_distrib,
    sum_end]

/-- [proved-standard; formal-checked] **A gauge move keeps every circulation of a cycle.** -/
theorem circulation_gauge (z : E → ℤ) (hz : ∀ v, Γ.boundary z v = 0) (c : E → G) (g : V → G) :
    circulation z (Γ.gauge c g) = circulation z c := by
  rw [gauge, circulation_add, circulation_coboundary]
  simp [hz]

omit [Fintype V] in
/-- [definition] The divergence of a connection, `(d₀ᵀc)(v) = Σ_(tgt e = v) c_e − Σ_(src e = v) c_e`. -/
def codiff (c : E → G) (v : V) : G :=
  ∑ e, (if Γ.tgt e = v then c e else 0) - ∑ e, (if Γ.src e = v then c e else 0)

omit [Fintype V] in
/-- [definition] One relaxation step by the potential, `c ← c − τ d₀(d₀ᵀc)`. -/
def relax (τ : ℤ) (c : E → G) : E → G := c - Γ.coboundary (τ • Γ.codiff c)

omit [Fintype V] in
/-- [proved-standard; formal-checked] **Relaxing the potential is a gauge move**, by `−τ d₀ᵀc`. -/
theorem relax_eq_gauge (τ : ℤ) (c : E → G) : Γ.relax τ c = Γ.gauge c (-(τ • Γ.codiff c)) := by
  funext e
  simp only [relax, gauge, coboundary, Pi.add_apply, Pi.sub_apply, Pi.neg_apply]
  abel

/-- [proved-standard; formal-checked] **Relaxing the potential keeps every holonomy:** it changes the
connection by an exact cochain, so every circulation on a cycle stays. -/
theorem relax_keeps_holonomy (z : E → ℤ) (hz : ∀ v, Γ.boundary z v = 0) (τ : ℤ) (c : E → G) :
    circulation z (Γ.relax τ c) = circulation z c := by
  rw [relax_eq_gauge, circulation_gauge Γ z hz]

omit [Fintype V] in
/-- [proved-standard; formal-checked] **Relaxing the potential never lowers a frustration:** it keeps
it exactly. -/
theorem frustration_relax [DecidableEq G] (w : E → ℕ) (τ : ℤ) (c : E → G) :
    Γ.frustration w (Γ.relax τ c) = Γ.frustration w c := by
  rw [relax_eq_gauge, frustration_gauge_invariant]

end Circulation

end Contacts

end Holonics.Geometry.Frustration
