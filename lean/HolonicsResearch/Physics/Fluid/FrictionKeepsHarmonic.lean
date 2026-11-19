import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Holonics.Foundation.HodgeReceiver

/-!
# Friction keeps only the harmonic part, and a lattice gas conserves its faces bit by bit

[proved-standard] The source is #410's box "Faces read on cycles" (record
`research/records/2026-10-24_FACES_ARE_READ_ON_CYCLES_A_FACE_IS_A_COHOMOLOGY_CLASS_THE_CARRY_IS_ITS_BOCKSTEIN_AND_FRICTION_KEEPS_ONLY_THE_HARMONIC_PART.md`,
§5 and §7; atlas `fluid.friction-keeps-harmonic`), its fluid clauses. The algebraic clauses (the carry, the seam,
the Künneth cross part, the replicator) are `Compression/FacesOnCycles`.

What is proved.

1. **The Laplacian keeps each Hodge part** (§1), extending `Foundation/HodgeReceiver`. On a weighted complex the two
   codifferentials compose to zero, `codiff₀ ∘ codiff₁ = 0` (`codiff₀_mul_codiff₁`, the adjoint of `d₁ ∘ d₀ = 0`);
   so `Δ` sends an exact cochain to an exact one and a coexact to a coexact one (`laplacian_mem_exact`,
   `laplacian_mem_coexact`), and kills the harmonic part (`laplacian_harmonic`).
2. **A viscous step fixes the harmonic part** (§1). The step `u ↦ u − νΔu` (`viscousStep`) sends
   `a + b + h` to `(a − νΔa) + (b − νΔb) + h` with the parts in their spaces (`viscousStep_split`), so the harmonic
   part of the stepped cochain is the harmonic part it started with, at every rate `ν` (`viscousStep_keeps_harmonic`)
   and after every number of steps (`viscousStep_iterate_keeps_harmonic`): what survives dissipation is cohomology.
3. **The HPP collision** (§2). Four direction bits a site (east, north, west, south); a head-on pair turns a quarter
   (`collide`). The collision conserves the mass and both momenta (`collide_mass`, `collide_px`, `collide_py`), is an
   involution (`collide_involutive`), and changes exactly 2 of the 16 site states (`collide_moves_two`). Streaming
   on the torus `ℤ/m × ℤ/m` moves each direction's bits one site along it (`stream`), and one step of the gas,
   streaming then collision, conserves the total mass and both total momenta (`step_mass`, `step_px`, `step_py`).

Limits. The record's census numbers (the 6×6 torus grid's energies `33,703/280`, `34,547/280`, `37/4`, the harmonic
dimension 2 and the six steps at `ν = 1/8`; the 16×16 HPP torus over 64 steps with invariants `(387, −1, 0)`) stay
checked by its receipts. That the exact and coexact energies fall strictly needs `ν` below the stability bound and is
not stated; nor is the hydrodynamic limit of the hexagonal FHP gas (Frisch, Hasslacher, Pomeau 1986).

The computational object is the helical pair interaction: a contact's slip is a 1-cochain, its friction is the
Laplacian's step, and what no friction touches is the period a cycle reads. Of the winding guide's six general
objects this touches the cell holonomy (the harmonic part, read only on cycles) and faces and placement (the Hodge
split, the lattice gas's conserved faces); the helix, the pair, the tube and the tower thread stay attached.

Consumers: the atlas row `fluid.friction-keeps-harmonic` and the #410 box "Faces read on cycles".

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.Fluid.FrictionKeepsHarmonic

open Matrix Finset Holonics.Foundation.HodgeReceiver

/-! ## 1. The Laplacian keeps each Hodge part -/

section Viscous

variable {p q r : ℕ} (C : WeightedComplex p q r)

/-- [proved-standard; formal-checked] The two codifferentials compose to zero, the adjoint of `d₁ ∘ d₀ = 0`. -/
theorem codiff₀_mul_codiff₁ : C.codiff₀ * C.codiff₁ = 0 := by
  ext i k
  have hdd := congrFun (congrFun C.dd k) i
  simp only [Matrix.mul_apply, Matrix.zero_apply] at hdd
  have h0 := (C.w₀pos i).ne'
  simp only [Matrix.mul_apply, Matrix.zero_apply, WeightedComplex.codiff₀, WeightedComplex.codiff₁]
  calc ∑ j, C.w₁ j * C.d₀ j i / C.w₀ i * (C.w₂ k * C.d₁ k j / C.w₁ j)
      = C.w₂ k / C.w₀ i * ∑ j, C.d₁ k j * C.d₀ j i := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have h1 := (C.w₁pos j).ne'
        field_simp
    _ = 0 := by rw [hdd, mul_zero]

/-- [proved-standard; formal-checked] `Δ` sends an exact cochain to an exact one. -/
theorem laplacian_mem_exact {a : Fin q → ℚ} (ha : a ∈ C.exactPart) : C.laplacian *ᵥ a ∈ C.exactPart := by
  obtain ⟨x, rfl⟩ := (C.mem_exactPart_iff a).1 ha
  refine (C.mem_exactPart_iff _).2 ⟨C.codiff₀ *ᵥ (C.d₀ *ᵥ x), ?_⟩
  have hz : C.d₁ *ᵥ (C.d₀ *ᵥ x) = 0 := by rw [Matrix.mulVec_mulVec, C.dd, Matrix.zero_mulVec]
  rw [C.laplacian_mulVec, hz, Matrix.mulVec_zero, add_zero]

/-- [proved-standard; formal-checked] `Δ` sends a coexact cochain to a coexact one. -/
theorem laplacian_mem_coexact {b : Fin q → ℚ} (hb : b ∈ C.coexactPart) :
    C.laplacian *ᵥ b ∈ C.coexactPart := by
  obtain ⟨y, rfl⟩ := (C.mem_coexactPart_iff b).1 hb
  refine (C.mem_coexactPart_iff _).2 ⟨C.d₁ *ᵥ (C.codiff₁ *ᵥ y), ?_⟩
  have hz : C.codiff₀ *ᵥ (C.codiff₁ *ᵥ y) = 0 := by
    rw [Matrix.mulVec_mulVec, codiff₀_mul_codiff₁, Matrix.zero_mulVec]
  rw [C.laplacian_mulVec, hz, Matrix.mulVec_zero, zero_add]

/-- [proved-standard; formal-checked] **The Hodge Laplacian kills the harmonic part.** -/
theorem laplacian_harmonic {h : Fin q → ℚ} (hh : h ∈ C.harmonic) : C.laplacian *ᵥ h = 0 := hh

/-- [definition] One viscous step at rate `ν`: `u ↦ u − νΔu`. -/
def viscousStep (ν : ℚ) (u : Fin q → ℚ) : Fin q → ℚ := u - ν • (C.laplacian *ᵥ u)

/-- [proved-standard; formal-checked] A viscous step moves the exact and coexact parts within their spaces and leaves
the harmonic part where it was. -/
theorem viscousStep_split (ν : ℚ) {a b h : Fin q → ℚ} (ha : a ∈ C.exactPart) (hb : b ∈ C.coexactPart)
    (hh : h ∈ C.harmonic) :
    a - ν • (C.laplacian *ᵥ a) ∈ C.exactPart ∧ b - ν • (C.laplacian *ᵥ b) ∈ C.coexactPart ∧
      viscousStep C ν (a + b + h) = (a - ν • (C.laplacian *ᵥ a)) + (b - ν • (C.laplacian *ᵥ b)) + h := by
  refine ⟨C.exactPart.sub_mem ha (C.exactPart.smul_mem ν (laplacian_mem_exact C ha)),
    C.coexactPart.sub_mem hb (C.coexactPart.smul_mem ν (laplacian_mem_coexact C hb)), ?_⟩
  simp only [viscousStep, Matrix.mulVec_add, laplacian_harmonic C hh, add_zero, smul_add]
  abel

/-- [proved-standard; formal-checked] **Friction keeps only the harmonic part**: whatever the rate, the harmonic part
of a stepped cochain is the harmonic part of the cochain. -/
theorem viscousStep_keeps_harmonic (ν : ℚ) {a b h a' b' h' : Fin q → ℚ} (ha : a ∈ C.exactPart)
    (hb : b ∈ C.coexactPart) (hh : h ∈ C.harmonic) (ha' : a' ∈ C.exactPart) (hb' : b' ∈ C.coexactPart)
    (hh' : h' ∈ C.harmonic) (hstep : viscousStep C ν (a + b + h) = a' + b' + h') : h' = h := by
  obtain ⟨hea, heb, he⟩ := viscousStep_split C ν ha hb hh
  exact (C.hodge_decomposition_unique ha' hb' hh' hea heb hh (hstep.symm.trans he)).2.2

/-- [proved-standard; formal-checked] After any number of viscous steps the cochain still splits with the harmonic
part it started with. -/
theorem viscousStep_iterate_split (ν : ℚ) {a b h : Fin q → ℚ} (ha : a ∈ C.exactPart) (hb : b ∈ C.coexactPart)
    (hh : h ∈ C.harmonic) (k : ℕ) :
    ∃ aₖ ∈ C.exactPart, ∃ bₖ ∈ C.coexactPart, (viscousStep C ν)^[k] (a + b + h) = aₖ + bₖ + h := by
  induction k with
  | zero => exact ⟨a, ha, b, hb, rfl⟩
  | succ k ih =>
    obtain ⟨aₖ, haₖ, bₖ, hbₖ, hk⟩ := ih
    obtain ⟨hea, heb, he⟩ := viscousStep_split C ν haₖ hbₖ hh
    refine ⟨_, hea, _, heb, ?_⟩
    rw [Function.iterate_succ_apply', hk, he]

/-- [proved-standard; formal-checked] **What survives dissipation is cohomology**: after `k` viscous steps, the
harmonic part of the cochain is the one it started with. -/
theorem viscousStep_iterate_keeps_harmonic (ν : ℚ) {a b h a' b' h' : Fin q → ℚ} (ha : a ∈ C.exactPart)
    (hb : b ∈ C.coexactPart) (hh : h ∈ C.harmonic) (k : ℕ) (ha' : a' ∈ C.exactPart)
    (hb' : b' ∈ C.coexactPart) (hh' : h' ∈ C.harmonic)
    (hstep : (viscousStep C ν)^[k] (a + b + h) = a' + b' + h') : h' = h := by
  obtain ⟨aₖ, haₖ, bₖ, hbₖ, hk⟩ := viscousStep_iterate_split C ν ha hb hh k
  exact (C.hodge_decomposition_unique ha' hb' hh' haₖ hbₖ hh (hstep.symm.trans hk)).2.2

end Viscous

/-! ## 2. The HPP lattice gas conserves its faces bit by bit -/

section HPP

/-- [definition] A site's four direction bits: east, north, west, south. -/
abbrev Site := Bool × Bool × Bool × Bool

/-- [definition] The HPP collision: a head-on pair turns a quarter, every other state stays. -/
def collide : Site → Site
  | (true, false, true, false) => (false, true, false, true)
  | (false, true, false, true) => (true, false, true, false)
  | s => s

/-- [definition] A site's mass, its count of particles. -/
def mass (s : Site) : ℤ := (s.1.toNat : ℤ) + s.2.1.toNat + s.2.2.1.toNat + s.2.2.2.toNat

/-- [definition] A site's east–west momentum. -/
def px (s : Site) : ℤ := (s.1.toNat : ℤ) - s.2.2.1.toNat

/-- [definition] A site's north–south momentum. -/
def py (s : Site) : ℤ := (s.2.1.toNat : ℤ) - s.2.2.2.toNat

/-- [proved-standard; formal-checked] The collision conserves the mass. -/
theorem collide_mass (s : Site) : mass (collide s) = mass s := by
  rcases s with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;> rfl

/-- [proved-standard; formal-checked] The collision conserves the east–west momentum. -/
theorem collide_px (s : Site) : px (collide s) = px s := by
  rcases s with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;> rfl

/-- [proved-standard; formal-checked] The collision conserves the north–south momentum. -/
theorem collide_py (s : Site) : py (collide s) = py s := by
  rcases s with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;> rfl

/-- [proved-standard; formal-checked] The collision is an involution. -/
theorem collide_involutive (s : Site) : collide (collide s) = s := by
  rcases s with ⟨_ | _, _ | _, _ | _, _ | _⟩ <;> rfl

/-- [proved-standard; formal-checked] The collision changes exactly 2 of the 16 site states. -/
theorem collide_moves_two : (Finset.univ.filter fun s : Site => collide s ≠ s).card = 2 := by
  decide

variable {m : ℕ} [NeZero m]

/-- [definition] Streaming on the torus `ℤ/m × ℤ/m`: each direction's bit moves one site along its direction. -/
def stream (F : ZMod m × ZMod m → Site) (z : ZMod m × ZMod m) : Site :=
  ((F (z - (1, 0))).1, (F (z - (0, 1))).2.1, (F (z + (1, 0))).2.2.1, (F (z + (0, 1))).2.2.2)

/-- [proved-standard; formal-checked] A sum over the torus is unchanged by a shift back. -/
theorem sum_sub_shift (G : ZMod m × ZMod m → ℤ) (c : ZMod m × ZMod m) :
    ∑ z, G (z - c) = ∑ z, G z :=
  Fintype.sum_equiv (Equiv.subRight c) _ _ (fun _ => rfl)

/-- [proved-standard; formal-checked] A sum over the torus is unchanged by a shift forward. -/
theorem sum_add_shift (G : ZMod m × ZMod m → ℤ) (c : ZMod m × ZMod m) :
    ∑ z, G (z + c) = ∑ z, G z :=
  Fintype.sum_equiv (Equiv.addRight c) _ _ (fun _ => rfl)

/-- [definition] One step of the gas: stream, then collide at every site. -/
def step (F : ZMod m × ZMod m → Site) (z : ZMod m × ZMod m) : Site := collide (stream F z)

/-- [proved-standard; formal-checked] One step of the gas conserves the total mass. -/
theorem step_mass (F : ZMod m × ZMod m → Site) : ∑ z, mass (step F z) = ∑ z, mass (F z) := by
  simp only [step, collide_mass]
  simp only [mass, stream, Finset.sum_add_distrib]
  rw [sum_sub_shift (fun z => ((F z).1.toNat : ℤ)) (1, 0), sum_sub_shift (fun z => ((F z).2.1.toNat : ℤ)) (0, 1),
    sum_add_shift (fun z => ((F z).2.2.1.toNat : ℤ)) (1, 0),
    sum_add_shift (fun z => ((F z).2.2.2.toNat : ℤ)) (0, 1)]

/-- [proved-standard; formal-checked] One step of the gas conserves the total east–west momentum. -/
theorem step_px (F : ZMod m × ZMod m → Site) : ∑ z, px (step F z) = ∑ z, px (F z) := by
  simp only [step, collide_px]
  simp only [px, stream, Finset.sum_sub_distrib]
  rw [sum_sub_shift (fun z => ((F z).1.toNat : ℤ)) (1, 0),
    sum_add_shift (fun z => ((F z).2.2.1.toNat : ℤ)) (1, 0)]

/-- [proved-standard; formal-checked] One step of the gas conserves the total north–south momentum. -/
theorem step_py (F : ZMod m × ZMod m → Site) : ∑ z, py (step F z) = ∑ z, py (F z) := by
  simp only [step, collide_py]
  simp only [py, stream, Finset.sum_sub_distrib]
  rw [sum_sub_shift (fun z => ((F z).2.1.toNat : ℤ)) (0, 1),
    sum_add_shift (fun z => ((F z).2.2.2.toNat : ℤ)) (0, 1)]

end HPP

end Holonics.Physics.Fluid.FrictionKeepsHarmonic
