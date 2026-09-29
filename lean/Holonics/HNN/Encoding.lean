import Holonics.HNN.IndexedOpen
import Holonics.Physics.ReflectedBoundaryMemory
import Holonics.Transport.SourceMoment
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# HNN.Encoding: Holonic Encoding's squares, its reduced recurrence, its separator, and the open
that reads no window

[definition] THE_REBUILD U6, the `hnn::encoding` loop (its pin,
`research/records/2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_PINNED_BEFORE_ITS_RUN.md`; the
construction record's law 12). A passage chart's encoding `E` is founded by closing the receiving
forms under the admitted transports on the reached span (Rust `hnn::encoding::Encoding`, through the
founding law `Compression/Landmark/Context/Birth`). Its consumers read it through three equations,
which this module proves on any linear chart over a field:

```text
E T = U E  ⇒  E (T x + f) = U (E x) + E f                        (injection_square)
E T_a = U_a E ∀ a  ⇒  E (drive T B l) = drive U (E ∘ B) l         (encoding_reduced_recurrence)
E (moment l) = moment′ l,  moment′ = (U, E ∘ I, encode)           (moment_reduced_recurrence)
ρ = D E for some D  ∨  ∃ v, E v = 0 ∧ ρ v ≠ 0                     (encoding_separator)
(∃ U, E T = U E) ↔ T carries ker E into ker E                      (encoding_descends_iff)
```

The first is `Physics/ReflectedBoundaryMemory.boundary_reduction_with_forcing` read with no interior:
the injected cell is transported by the same next encoding. The second and third are the source
moment's one-step law (`Transport/SourceMoment.moment_append_one`) carried into the founded chart:
the encoded moment runs in the founded chart alone and never expands the interior. The fourth is the
linear form of `Holon/Restriction.descent_total`: a reading factors through the encoding exactly when
no merged direction separates it (`separator_refutes_factoring`), and the fifth is the linear form of
`Foundation/JointReceiverDescent.joint_generator_descends_iff`.

[proved-derived; formal-checked] **The open reads no window** (Rust `hnn::moment`). The pair port is
read over the whole offset moment, normalized by its pair population
(`HNN/IndexedOpen.{pairPopulation, pairNormalized}`), never at an address a buffer supplies:
the whole read is the count read over the pair population (`whole_pair_read_counts`), the offset
moment of the passage on a closing ring over it (`whole_pair_read_offset_moment`, composing
`HNN/IndexedOpen.pairRead_offsetCounts`); it is unchanged by a repeated population
(`whole_pair_read_population_invariant`); it reads only the retained table
(`whole_pair_read_tape_free`); and an empty population reads zero (`whole_pair_read_zero`).

[open] The founded dimension on the reached span equals the emission's Hankel rank (measured on the
moiré, a copy ring and the rotor crib in `hnn::tests::encoding`); its proof is owed in #62 with
Birth's Hankel identification.

The computational object is the helical pair interaction. Of the winding guide's six objects this
module touches the **helix** (the transports and the moment's advance), the **pair** (the offset
moment read whole) and **faces and placement** (the readout `D` and the separator); the cell
holonomy, the tube and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Encoding

open Holonics.Physics.ReflectedBoundaryMemory
open Holonics.Transport.SourceMoment

/-! ## 1. The factor and the separator -/

section Factor

variable {K X Q V : Type*} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Q] [Module K Q]
  [AddCommGroup V] [Module K V]

/-- [proved-derived; formal-checked] **A reading blind to the merged directions factors through the
encoding**: `ker E ≤ ker ρ` gives a linear `D` with `ρ = D E`. -/
theorem factor_of_ker_le (E : X →ₗ[K] Q) (ρ : X →ₗ[K] V)
    (h : LinearMap.ker E ≤ LinearMap.ker ρ) : ∃ D : Q →ₗ[K] V, ρ = D.comp E := by
  let f : LinearMap.range E →ₗ[K] V :=
    ((LinearMap.ker E).liftQ ρ h).comp E.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g, hg⟩ := LinearMap.exists_extend f
  refine ⟨g, LinearMap.ext fun x => ?_⟩
  have hx := LinearMap.congr_fun hg ⟨E x, LinearMap.mem_range_self E x⟩
  simp only [LinearMap.comp_apply, Submodule.coe_subtype] at hx
  rw [LinearMap.comp_apply, hx]
  simp [f, LinearMap.quotKerEquivRange_symm_apply_image]

/-- [proved-derived; formal-checked] **The separator** (Rust `hnn::encoding::Encoding::separator`):
a reading factors through the encoding, or a direction the encoding merges separates it. -/
theorem encoding_separator (E : X →ₗ[K] Q) (ρ : X →ₗ[K] V) :
    (∃ D : Q →ₗ[K] V, ρ = D.comp E) ∨ ∃ v, E v = 0 ∧ ρ v ≠ 0 := by
  by_cases h : ∀ v, E v = 0 → ρ v = 0
  · exact Or.inl (factor_of_ker_le E ρ fun v hv => h v hv)
  · push Not at h
    exact Or.inr h

/-- [proved-derived; formal-checked] **A separator refutes every factor**: a merged direction on
which the reading is nonzero leaves no `D` with `ρ = D E`. -/
theorem separator_refutes_factoring (E : X →ₗ[K] Q) (ρ : X →ₗ[K] V) {v : X} (hv : E v = 0)
    (hρ : ρ v ≠ 0) : ¬ ∃ D : Q →ₗ[K] V, ρ = D.comp E := by
  rintro ⟨D, rfl⟩
  exact hρ (by simp [hv])

/-- [proved-derived; formal-checked] **A transport descends to the encoding exactly when it keeps
the merged directions merged**: `U` with `E T = U E` exists iff `T (ker E) ⊆ ker E`. -/
theorem encoding_descends_iff (E : X →ₗ[K] Q) (T : X →ₗ[K] X) :
    (∃ U : Q →ₗ[K] Q, E.comp T = U.comp E) ↔ ∀ v, E v = 0 → E (T v) = 0 := by
  constructor
  · rintro ⟨U, hU⟩ v hv
    have h := LinearMap.congr_fun hU v
    simp only [LinearMap.comp_apply, hv, map_zero] at h
    exact h
  · intro h
    exact factor_of_ker_le E (E.comp T) fun v hv => h v hv

end Factor

/-! ## 2. The injection square and the reduced recurrence -/

section Recurrence

variable {K X Q : Type*} [Field K] [AddCommGroup X] [Module K X] [AddCommGroup Q] [Module K Q]

/-- [proved-derived; formal-checked] **The injection square** (Rust
`hnn::encoding::Encoding::squares`): with `E T = U E`, a state transported and driven by an injected
cell `f` encodes as `U (E x) + E f`; the injected cell is carried by the same next encoding
(`boundary_reduction_with_forcing` with no interior). -/
theorem injection_square (T : X →ₗ[K] X) (E : X →ₗ[K] Q) (U : Q →ₗ[K] Q)
    (hT : E.comp T = U.comp E) (x f : X) : E (T x + f) = U (E x) + E f := by
  have h := boundary_reduction_with_forcing (Z := X) T 0 E E U hT (by simp) x 0 f
  simpa using h

/-- [definition] **A driven passage**: from zero, each step `(a, u)` transports by `T a` and
injects `B u`. -/
def drive {W ι A : Type*} [AddCommGroup W] [Module K W] (T : ι → W →ₗ[K] W) (B : A → W)
    (l : List (ι × A)) : W :=
  l.foldl (fun s p => T p.1 s + B p.2) 0

theorem drive_append_one {W ι A : Type*} [AddCommGroup W] [Module K W] (T : ι → W →ₗ[K] W)
    (B : A → W) (l : List (ι × A)) (p : ι × A) :
    drive T B (l ++ [p]) = T p.1 (drive T B l) + B p.2 := by
  simp [drive, List.foldl_append]

/-- [proved-derived; formal-checked] **The reduced recurrence** (Rust
`hnn::encoding::Encoding::reduced_moment`): when every admitted transport descends (`E T_a = U_a E`),
the encoded driven passage is the founded chart's own driven passage, `z ← U_a z + J u` with
`J = E B`, run without the interior. -/
theorem encoding_reduced_recurrence {ι A : Type*} (T : ι → X →ₗ[K] X) (B : A → X)
    (E : X →ₗ[K] Q) (U : ι → Q →ₗ[K] Q) (hT : ∀ a, E.comp (T a) = (U a).comp E)
    (l : List (ι × A)) : E (drive T B l) = drive U (fun u => E (B u)) l := by
  induction l using List.reverseRecOn with
  | nil => simp [drive]
  | append_singleton l p ih =>
    rw [drive_append_one, drive_append_one, injection_square (T p.1) E (U p.1) (hT p.1), ih]

/-- [proved-derived; formal-checked] **The source moment descends**: for a moment machine
(`Transport/SourceMoment.MomentMachine`) whose advance descends to the encoding, the encoded moment
is the moment of the reduced machine `(U, E ∘ I, encode)`, for every source passage. -/
theorem moment_reduced_recurrence {S Letter : Type*} [AddCommGroup S] [Module K S]
    (M : MomentMachine K X S Letter) (E : S →ₗ[K] Q) (U : Q →ₗ[K] Q)
    (hU : E.comp M.advance = U.comp E) (l : List Letter) :
    E (M.moment l) = (⟨U, E.comp M.inject, M.encode⟩ : MomentMachine K X Q Letter).moment l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l u ih =>
    rw [MomentMachine.moment_append_one, MomentMachine.moment_append_one,
      injection_square M.advance E U hU, ih]
    rfl

end Recurrence

/-! ## 3. The open reads no window -/

section Whole

open Holonics.HNN.IndexedOpen
open Holonics.HNN.Moment (back offsetCounts offsetContribution)

variable {A : Type*} [Fintype A] [DecidableEq A]
variable {X S : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup S] [Module ℚ S]

/-- [proved-derived; formal-checked] **The whole read is the count read over the pair
population**: at a positive pair population, the pair port read on `C/n_δ` is `n_δ⁻¹` times the read
of the counts. No address enters. -/
theorem whole_pair_read_counts (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (F : (A × A → ℚ) →ₗ[ℚ] X) {d : ℕ} {C : ℕ → A → A → ℕ} (h : 0 < pairPopulation d C) :
    pairRead P I F d (pairNormalized d C) =
      (pairPopulation d C : ℚ)⁻¹ • pairRead P I F d (fun c x b => (C c x b : ℚ)) := by
  simp only [pairRead, pairNormalized, if_neg h.ne', Finset.smul_sum, smul_smul, div_eq_inv_mul]

/-- [proved-derived; formal-checked] **The whole read is the passage's offset moment over its pair
population**: on a closing ring, reading the offset counts of the passage whole gives
`HNN/Moment.offsetContribution`, every pair of the passage at the offset, over `n_δ`. -/
theorem whole_pair_read_offset_moment {P : (Module.End ℚ S)ˣ} {d : ℕ} (hd : 0 < d)
    (hP : P ^ d = 1) (I : X →ₗ[ℚ] S) (F : (A × A → ℚ) →ₗ[ℚ] X) (u : ℕ → A) (τ : ℕ → ℕ)
    (n δ : ℕ) (h : 0 < pairPopulation d (offsetCounts u τ d n δ)) :
    pairRead P I F d (pairNormalized d (offsetCounts u τ d n δ)) =
      (pairPopulation d (offsetCounts u τ d n δ) : ℚ)⁻¹ • offsetContribution P I F u τ n δ := by
  rw [whole_pair_read_counts P I F h, pairRead_offsetCounts hd hP I F u τ n δ]

omit [DecidableEq A] in
theorem pairPopulation_mul (d : ℕ) (C : ℕ → A → A → ℕ) (k : ℕ) :
    pairPopulation d (fun c x b => k * C c x b) = k * pairPopulation d C := by
  simp only [pairPopulation, Finset.mul_sum]

/-- [proved-derived; formal-checked] **The whole read is population invariant**: scaling every
offset count by a positive integer leaves the normalized table, and so its read under every pair
port, unchanged. -/
theorem whole_pair_read_population_invariant (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (F : (A × A → ℚ) →ₗ[ℚ] X) (d : ℕ) (C : ℕ → A → A → ℕ) {k : ℕ} (hk : 0 < k) :
    pairNormalized d (fun c x b => k * C c x b) = pairNormalized d C ∧
      pairRead P I F d (pairNormalized d (fun c x b => k * C c x b)) =
        pairRead P I F d (pairNormalized d C) := by
  have hnorm : pairNormalized d (fun c x b => k * C c x b) = pairNormalized d C := by
    funext c x b
    unfold pairNormalized
    rw [pairPopulation_mul]
    by_cases h0 : pairPopulation d C = 0
    · simp [h0]
    · have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
      rw [if_neg (Nat.mul_ne_zero hk.ne' h0), if_neg h0]
      push_cast
      rw [mul_div_mul_left _ _ hk']
  exact ⟨hnorm, by rw [hnorm]⟩

/-- [proved-derived; formal-checked] **The whole read needs no tape**: two retained tables equal
below the period give one read under every pair port. -/
theorem whole_pair_read_tape_free (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (d : ℕ)
    {C C' : ℕ → A → A → ℕ} (hC : ∀ c < d, ∀ x a, C c x a = C' c x a)
    (F : (A × A → ℚ) →ₗ[ℚ] X) :
    pairRead P I F d (pairNormalized d C) = pairRead P I F d (pairNormalized d C') := by
  have hpop : pairPopulation d C = pairPopulation d C' :=
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl
      fun a _ => hC c (Finset.mem_range.mp hc) x a
  unfold pairRead
  refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun x _ =>
    Finset.sum_congr rfl fun b _ => ?_
  simp only [pairNormalized, hpop, hC c (Finset.mem_range.mp hc) x b]

/-- [proved-derived; formal-checked] **An empty pair population reads zero** under every pair port. -/
theorem whole_pair_read_zero (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (F : (A × A → ℚ) →ₗ[ℚ] X) {d : ℕ} {C : ℕ → A → A → ℕ} (h : pairPopulation d C = 0) :
    pairRead P I F d (pairNormalized d C) = 0 := by
  simp [pairRead, pairNormalized, h]

end Whole

section Audit

#print axioms factor_of_ker_le
#print axioms encoding_separator
#print axioms separator_refutes_factoring
#print axioms encoding_descends_iff
#print axioms injection_square
#print axioms encoding_reduced_recurrence
#print axioms moment_reduced_recurrence
#print axioms whole_pair_read_counts
#print axioms whole_pair_read_offset_moment
#print axioms whole_pair_read_population_invariant
#print axioms whole_pair_read_tape_free
#print axioms whole_pair_read_zero

end Audit

end Holonics.HNN.Encoding
