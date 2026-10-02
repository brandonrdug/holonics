import Holonics.HNN.Moment
import Mathlib.Data.Rat.Floor

/-!
# HNN.IndexedOpen: the source opens on its indexed, normalized counts

[definition; agent-inferred] Decision 26 of the step 4 design (`docs/plans/THE_REBUILD.md`,
campaign 1's repair), from the located failure and Sol's derivation. A source ring `g` retains
its phase counts `M_g[c, x]` and, per declared offset `δ`, its pair counts `C^δ_g[c, x, a]`
(phase class `c`, cell `x`, and the cell `a` that stood `δ` back: `HNN/Moment`'s `counts`,
`offsetCounts` and `StreamState.{bins, pairBins}`). The unnormalized open reads the counts
themselves, so its amplitude grows with every ingested cell. The repair opens on the counts
normalized by their populations, as exact ratios, and reads the pair port only at the address the
retained window supplies:

```text
populations   n_g = Σ_(c,x) M_g[c,x] ,  N_(g,δ,a) = Σ_(c,x) C^δ_g[c,x,a] ,  n_(g,δ) = Σ_a N_(g,δ,a)
marginal      M_g[c,x] / n_g                         (exact ratio, with division and remainder)
conditional   P^δ_(g,a)[c,x] = C^δ_g[c,x,a] / N_(g,δ,a)      at the address a_δ = window[δ − 1]
open          Σ_(c,x) (M/n)[c,x] P^(−c) I E(e_x)
                + Σ_δ Σ_(c,x) P^δ_(g,a_δ)[c,x] P^(−c) I F^δ(e_x ⊗ e_(a_δ))
```

The address `a_δ` is the navigator address the already retained window supplies (the shift
register of `HNN/Moment`, most recent first, so the cell `δ` back is `window[δ − 1]`); it selects
a column of the existing pair-count table, and no earlier-cell tape is added. No rounded
probability is stored: the ratios are read exactly from the integer tables. A zero population is
an unsupported fibre: it contributes nothing, and no conditional value is invented.

[proved-derived; formal-checked] What is proved.

1. **Mass and remainder** (`normalized_phase_counts_mass`, `conditional_mass`,
   `normalized_div_rem`): at a positive population the normalized counts sum to one, and each is
   the exact ratio `⌊M/n⌋ + (M mod n)/n` with its remainder below the population.
2. **The indexed read is the column contraction** (`indexed_pair_read_eq_column_contraction`): the
   pair port read on `P^δ_a ⊗ e_a` is the contraction of the port's column at `a` with the
   normalized column `C[·,·,a]/N_a`, and at a positive population it is `N_a⁻¹` times the
   contraction with the counts. The conditional is the indexed normalized table divided by its
   column mass (`conditional_eq_normalized_column`).
3. **The adjoint** (`indexed_pair_adjoint_pairing`): the read is linear in the pair port, and every
   covector `g` pairs with it as the port covector `pairAdjoint`, supported on the address `a`
   alone and contracting with the same normalized slice.
4. **Population invariance** (`normalized_open_population_invariant`): scaling every count by a
   positive integer (a repeated population with the same empirical ratios) leaves the marginal,
   the conditional and the whole source open unchanged; the unnormalized read scales with it
   (`unnormalized_read_scales`).
5. **The zero-population fibre** (`normalized_zero_population`, `conditional_zero_population`,
   `indexed_read_zero_population`): an empty population reads zero by definition, an empty column
   is exactly a column of zero counts and its indexed read is zero under every port, and an
   unavailable address contributes nothing (`pairTerm_none`).
6. **Tape freedom and the owner's joins** (`indexed_open_tape_free`, `marginalRead_counts`,
   `pairRead_offsetCounts`, `normalized_marginal_eq_scaled_read`): equal retained tables and window
   give equal opens under every contemporary encoder and port; on a closing ring the marginal read
   of the counts is `HNN/Moment.encoderMoment` and the pair read of the offset counts is
   `HNN/Moment.offsetContribution`, and the normalized marginal open is the moment divided by its
   population.

[open] Normalizing the count read bounds its amplitude; it does not certify the conditioning of
the receiving locus's Gram, which needs a lower bound on feature excitation. The moment's
capacity count and overwrite law (`HNN/Moment.moment_capacity`) are unchanged.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.IndexedOpen

open Holonics.HNN.Moment (back counts offsetCounts offsetContribution encoderMoment
  encoderMoment_contract exteriorOffset_independent_of_E)

variable {A : Type*} [Fintype A]

/-! ## 1. Populations and normalized counts -/

section Normalized

/-- [definition] **The population** `n = Σ_(c<d) Σ_x M[c, x]` of a phase-count table. -/
def population (d : ℕ) (M : ℕ → A → ℕ) : ℕ := ∑ c ∈ Finset.range d, ∑ x, M c x

/-- [definition] **The normalized counts** `M[c, x]/n`, an exact ratio; a zero population reads
zero (the unsupported fibre, `normalized_zero_population`). -/
def normalized (d : ℕ) (M : ℕ → A → ℕ) (c : ℕ) (x : A) : ℚ :=
  if population d M = 0 then 0 else (M c x : ℚ) / population d M

/-- [proved-derived; formal-checked] At a positive population the normalized count is the exact
ratio `M[c, x]/n`. -/
theorem normalized_of_pos {d : ℕ} {M : ℕ → A → ℕ} (h : 0 < population d M) (c : ℕ) (x : A) :
    normalized d M c x = (M c x : ℚ) / population d M := by
  rw [normalized, if_neg h.ne']

/-- [proved-derived; formal-checked] **The zero-population fibre.** A table with zero population
reads zero at every phase and cell (by definition, never by a division by zero): an empty table
contributes nothing and no value is invented. `population_eq_zero_iff` says when this happens. -/
theorem normalized_zero_population {d : ℕ} {M : ℕ → A → ℕ} (h : population d M = 0) :
    normalized d M = fun _ _ => 0 := by
  funext c x
  rw [normalized, if_pos h]

/-- [proved-derived; formal-checked] A population vanishes exactly when every count below the
period vanishes. -/
theorem population_eq_zero_iff (d : ℕ) (M : ℕ → A → ℕ) :
    population d M = 0 ↔ ∀ c < d, ∀ x, M c x = 0 := by
  simp [population, Finset.sum_eq_zero_iff]

/-- [proved-derived; formal-checked] **The normalized phase counts carry unit mass**:
`Σ_(c<d) Σ_x M[c, x]/n = 1` for a positive population `n = Σ M`. -/
theorem normalized_phase_counts_mass {d : ℕ} {M : ℕ → A → ℕ} (h : 0 < population d M) :
    ∑ c ∈ Finset.range d, ∑ x, normalized d M c x = 1 := by
  have hn : (population d M : ℚ) ≠ 0 := by exact_mod_cast h.ne'
  simp only [normalized_of_pos h, ← Finset.sum_div]
  rw [div_eq_one_iff_eq hn]
  simp [population]

/-- [proved-derived; formal-checked] **The normalized count with its remainder**: at a positive
population `n`, `M/n = ⌊M/n⌋ + (M mod n)/n` exactly, with `M mod n < n`. -/
theorem normalized_div_rem {d : ℕ} {M : ℕ → A → ℕ} (h : 0 < population d M) (c : ℕ) (x : A) :
    normalized d M c x = ((M c x / population d M : ℕ) : ℚ) +
        ((M c x % population d M : ℕ) : ℚ) / population d M ∧
      M c x % population d M < population d M := by
  refine ⟨?_, Nat.mod_lt _ h⟩
  have hn : (population d M : ℚ) ≠ 0 := by exact_mod_cast h.ne'
  rw [normalized_of_pos h]
  have hsplit := Nat.div_add_mod (M c x) (population d M)
  have hcast : (M c x : ℚ) = (population d M : ℚ) * ((M c x / population d M : ℕ) : ℚ) +
      ((M c x % population d M : ℕ) : ℚ) := by
    exact_mod_cast hsplit.symm
  rw [hcast]
  field_simp

/-- [proved-derived; formal-checked] The population of a repeated table is `k` times its
population. -/
theorem population_mul (d : ℕ) (M : ℕ → A → ℕ) (k : ℕ) :
    population d (fun c x => k * M c x) = k * population d M := by
  simp only [population, Finset.mul_sum]

/-- [proved-derived; formal-checked] Repeating a population leaves its normalized counts. -/
theorem normalized_mul {d : ℕ} (M : ℕ → A → ℕ) {k : ℕ} (hk : 0 < k) :
    normalized d (fun c x => k * M c x) = normalized d M := by
  funext c x
  unfold normalized
  rw [population_mul]
  by_cases h : population d M = 0
  · simp [h]
  · have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
    have hn : (population d M : ℚ) ≠ 0 := by exact_mod_cast h
    rw [if_neg (Nat.mul_ne_zero hk.ne' h), if_neg h]
    push_cast
    field_simp

end Normalized

/-! ## 2. The indexed pair table and its conditional column -/

section Conditional

/-- [definition] The column of a pair table at address `a`: `(c, x) ↦ C[c, x, a]`. -/
def column (C : ℕ → A → A → ℕ) (a : A) : ℕ → A → ℕ := fun c x => C c x a

/-- [definition] **The address population** `N_a = Σ_(c<d) Σ_x C[c, x, a]`. -/
def addressPopulation (d : ℕ) (C : ℕ → A → A → ℕ) (a : A) : ℕ := population d (column C a)

/-- [definition] **The pair population** `n_δ = Σ_(c<d) Σ_(x, a) C[c, x, a]`. -/
def pairPopulation (d : ℕ) (C : ℕ → A → A → ℕ) : ℕ :=
  ∑ c ∈ Finset.range d, ∑ x, ∑ a, C c x a

/-- [definition] **The indexed normalized pair table** `C[c, x, a]/n_δ`, zero at zero
population. -/
def pairNormalized (d : ℕ) (C : ℕ → A → A → ℕ) (c : ℕ) (x a : A) : ℚ :=
  if pairPopulation d C = 0 then 0 else (C c x a : ℚ) / pairPopulation d C

/-- [definition] **The conditional slice** `P_a[c, x] = C[c, x, a]/N_a`: the normalized column at
address `a`, zero where the column is empty. -/
def conditional (d : ℕ) (C : ℕ → A → A → ℕ) (a : A) : ℕ → A → ℚ := normalized d (column C a)

/-- [proved-derived; formal-checked] At a positive address population the conditional is the exact
ratio `C[c, x, a]/N_a`. -/
theorem conditional_of_pos {d : ℕ} {C : ℕ → A → A → ℕ} {a : A} (h : 0 < addressPopulation d C a)
    (c : ℕ) (x : A) :
    conditional d C a c x = (C c x a : ℚ) / addressPopulation d C a :=
  normalized_of_pos h c x

/-- [proved-derived; formal-checked] At a positive address population the conditional slice
carries unit mass. -/
theorem conditional_mass {d : ℕ} {C : ℕ → A → A → ℕ} {a : A} (h : 0 < addressPopulation d C a) :
    ∑ c ∈ Finset.range d, ∑ x, conditional d C a c x = 1 :=
  normalized_phase_counts_mass h

theorem addressPopulation_le_pairPopulation (d : ℕ) (C : ℕ → A → A → ℕ) (a : A) :
    addressPopulation d C a ≤ pairPopulation d C := by
  unfold addressPopulation population column pairPopulation
  exact Finset.sum_le_sum fun c _ => Finset.sum_le_sum fun x _ =>
    Finset.single_le_sum (fun b _ => Nat.zero_le (C c x b)) (Finset.mem_univ a)

/-- [proved-derived; formal-checked] **The conditional is the indexed normalized table divided by
its column mass.** At a positive address population, the column mass of the normalized pair table
is `N_a/n_δ`, and `C[c, x, a]/N_a = (C[c, x, a]/n_δ) / (N_a/n_δ)`: the conditional division is
exactly the indexed normalized table divided by its indexed population. -/
theorem conditional_eq_normalized_column {d : ℕ} {C : ℕ → A → A → ℕ} {a : A}
    (h : 0 < addressPopulation d C a) (c : ℕ) (x : A) :
    ∑ c' ∈ Finset.range d, ∑ x', pairNormalized d C c' x' a =
        (addressPopulation d C a : ℚ) / pairPopulation d C ∧
      conditional d C a c x = pairNormalized d C c x a /
        ∑ c' ∈ Finset.range d, ∑ x', pairNormalized d C c' x' a := by
  have hpos : 0 < pairPopulation d C := h.trans_le (addressPopulation_le_pairPopulation d C a)
  have hn : (pairPopulation d C : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
  have hN : (addressPopulation d C a : ℚ) ≠ 0 := by exact_mod_cast h.ne'
  have hmass : ∑ c' ∈ Finset.range d, ∑ x', pairNormalized d C c' x' a =
      (addressPopulation d C a : ℚ) / pairPopulation d C := by
    simp only [pairNormalized, if_neg hpos.ne', ← Finset.sum_div]
    simp [addressPopulation, population, column]
  refine ⟨hmass, ?_⟩
  rw [hmass, conditional_of_pos h, pairNormalized, if_neg hpos.ne']
  field_simp

/-- [proved-derived; formal-checked] **The empty column.** A zero address population is exactly a
column of zero counts, and its conditional slice reads zero: the unsupported fibre. -/
theorem conditional_zero_population {d : ℕ} {C : ℕ → A → A → ℕ} {a : A}
    (h : addressPopulation d C a = 0) :
    (∀ c < d, ∀ x, C c x a = 0) ∧ conditional d C a = fun _ _ => 0 :=
  ⟨(population_eq_zero_iff d (column C a)).mp h, normalized_zero_population h⟩

end Conditional

/-! ## 3. The reads, the indexed open and its adjoint -/

section Read

variable [DecidableEq A]
variable {X S : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup S] [Module ℚ S]

/-- [definition] **The marginal read** of a rational phase table `T` through the encoder `E`:
`Σ_(c<d) Σ_x T[c, x] P^(−c) I E(e_x)`. -/
def marginalRead (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (E : (A → ℚ) →ₗ[ℚ] X) (d : ℕ)
    (T : ℕ → A → ℚ) : S :=
  ∑ c ∈ Finset.range d, ∑ x, T c x • back P c (I (E (Pi.single x 1)))

/-- [definition] **The pair-port read** of a rational pair table `T` through the pair port `F` on
the exterior pair chart: `Σ_(c<d) Σ_(x, b) T[c, x, b] P^(−c) I F(e_x ⊗ e_b)`. -/
def pairRead (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (F : (A × A → ℚ) →ₗ[ℚ] X) (d : ℕ)
    (T : ℕ → A → A → ℚ) : S :=
  ∑ c ∈ Finset.range d, ∑ x, ∑ b, T c x b • back P c (I (F (Pi.single (x, b) 1)))

/-- [definition] **The addressed slice** `P_a ⊗ e_a`: the conditional slice at address `a`, placed
on the address coordinate `a`. -/
def addressedSlice (d : ℕ) (C : ℕ → A → A → ℕ) (a : A) : ℕ → A → A → ℚ :=
  fun c x b => if b = a then conditional d C a c x else 0

/-- [definition] **The pair term of one offset** at the address the window supplies: nothing when
the window holds no cell `δ` back, the pair read on the addressed slice otherwise. -/
def pairTerm (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (F : (A × A → ℚ) →ₗ[ℚ] X) (d : ℕ)
    (C : ℕ → A → A → ℕ) : Option A → S
  | none => 0
  | some a => pairRead P I F d (addressedSlice d C a)

/-- [definition] **The indexed, normalized source open** of a source ring: the marginal read on
the normalized phase counts, plus, for every declared offset `δ`, the pair term at the address
`window[δ − 1]` (the cell `δ` back, as `HNN/Moment.SourceDecl.ingest` bins it). -/
def sourceOpen (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (E : (A → ℚ) →ₗ[ℚ] X) (d : ℕ)
    (M : ℕ → A → ℕ) (offsets : Finset ℕ) (F : ℕ → (A × A → ℚ) →ₗ[ℚ] X)
    (C : ℕ → ℕ → A → A → ℕ) (window : List A) : S :=
  marginalRead P I E d (normalized d M) +
    ∑ δ ∈ offsets, pairTerm P I (F δ) d (C δ) window[δ - 1]?

/-- [proved-derived; formal-checked] **An unavailable address contributes nothing.** -/
theorem pairTerm_none (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (F : (A × A → ℚ) →ₗ[ℚ] X)
    (d : ℕ) (C : ℕ → A → A → ℕ) : pairTerm P I F d C none = 0 := rfl

/-- [proved-derived; formal-checked] **The indexed read is the column contraction.** The pair port
read on `P_a ⊗ e_a` is the contraction of the port's column at `a` with the normalized column,
`Σ_(c<d) Σ_x (C[c, x, a]/N_a) P^(−c) I F(e_x ⊗ e_a)`; at a positive address population it is
`N_a⁻¹` times the contraction with the counts `C[·, ·, a]`. -/
theorem indexed_pair_read_eq_column_contraction (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (F : (A × A → ℚ) →ₗ[ℚ] X) (d : ℕ) (C : ℕ → A → A → ℕ) (a : A) :
    pairRead P I F d (addressedSlice d C a) =
        ∑ c ∈ Finset.range d, ∑ x, conditional d C a c x • back P c (I (F (Pi.single (x, a) 1))) ∧
      (0 < addressPopulation d C a → pairRead P I F d (addressedSlice d C a) =
        (addressPopulation d C a : ℚ)⁻¹ •
          ∑ c ∈ Finset.range d, ∑ x, (C c x a : ℚ) • back P c (I (F (Pi.single (x, a) 1)))) := by
  have h1 : pairRead P I F d (addressedSlice d C a) =
      ∑ c ∈ Finset.range d, ∑ x, conditional d C a c x • back P c (I (F (Pi.single (x, a) 1))) := by
    simp [pairRead, addressedSlice, ite_smul]
  refine ⟨h1, fun h => ?_⟩
  rw [h1, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [conditional_of_pos h, smul_smul, div_eq_inv_mul]

/-- [proved-derived; formal-checked] **An empty column contributes nothing**: at zero address
population the indexed read is zero under every pair port. -/
theorem indexed_read_zero_population (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (F : (A × A → ℚ) →ₗ[ℚ] X) (d : ℕ) (C : ℕ → A → A → ℕ) (a : A)
    (h : addressPopulation d C a = 0) :
    pairRead P I F d (addressedSlice d C a) = 0 := by
  rw [(indexed_pair_read_eq_column_contraction P I F d C a).1, (conditional_zero_population h).2]
  simp

/-- [definition] **The port covector** of a covector `g` on the ring: at the pair coordinate
`(x, b)`, the covector `Σ_(c<d) P_a[c, x] · I*(P^(−c))*g` on the port's value when `b = a`, and
zero at every other address. -/
def pairAdjoint (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (d : ℕ) (C : ℕ → A → A → ℕ) (a : A)
    (g : Module.Dual ℚ S) : A × A → Module.Dual ℚ X :=
  fun p => if p.2 = a then
    ∑ c ∈ Finset.range d, conditional d C a c p.1 • I.dualMap ((back P c).dualMap g) else 0

/-- [proved-derived; formal-checked] **The indexed pair adjoint.** The indexed read is linear in the
pair port, and every covector `g` pairs with it through the port covector:
`g(read(F)) = Σ_(x, b) (pairAdjoint g)(x, b) (F(e_x ⊗ e_b))`. The port covector is supported on
the address `a` alone and contracts with the same normalized slice `P_a` as the read. -/
theorem indexed_pair_adjoint_pairing (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (d : ℕ)
    (C : ℕ → A → A → ℕ) (a : A) (g : Module.Dual ℚ S) :
    (∀ F δF : (A × A → ℚ) →ₗ[ℚ] X,
      pairRead P I (F + δF) d (addressedSlice d C a) =
        pairRead P I F d (addressedSlice d C a) + pairRead P I δF d (addressedSlice d C a)) ∧
    (∀ F : (A × A → ℚ) →ₗ[ℚ] X,
      g (pairRead P I F d (addressedSlice d C a)) =
        ∑ p : A × A, pairAdjoint P I d C a g p (F (Pi.single p 1))) ∧
    ∀ p : A × A, p.2 ≠ a → pairAdjoint P I d C a g p = 0 := by
  refine ⟨fun F δF => ?_, fun F => ?_, fun p hp => by simp [pairAdjoint, hp]⟩
  · simp only [pairRead, LinearMap.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  · have hΦ : ∀ x, ∑ b, pairAdjoint P I d C a g (x, b) (F (Pi.single (x, b) 1)) =
        ∑ c ∈ Finset.range d,
          conditional d C a c x * g (back P c (I (F (Pi.single (x, a) 1)))) := by
      intro x
      have hb : ∀ b, pairAdjoint P I d C a g (x, b) (F (Pi.single (x, b) 1)) =
          if b = a then ∑ c ∈ Finset.range d,
            conditional d C a c x * g (back P c (I (F (Pi.single (x, a) 1)))) else 0 := by
        intro b
        by_cases hba : b = a
        · subst hba
          simp [pairAdjoint]
        · simp [pairAdjoint, hba]
      rw [Finset.sum_congr rfl fun b _ => hb b, Finset.sum_ite_eq' Finset.univ a,
        if_pos (Finset.mem_univ a)]
    rw [(indexed_pair_read_eq_column_contraction P I F d C a).1, Fintype.sum_prod_type,
      Finset.sum_congr rfl fun x _ => hΦ x, Finset.sum_comm]
    simp only [map_sum, map_smul, smul_eq_mul]

/-- [proved-derived; formal-checked] **The unnormalized read scales with the population.** Reading
the counts themselves, a repeated population `k·M` reads `k` times the marginal: the amplitude grows
with ingestion alone, which the normalized open removes. -/
theorem unnormalized_read_scales (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (E : (A → ℚ) →ₗ[ℚ] X) (d : ℕ) (M : ℕ → A → ℕ) (k : ℕ) :
    marginalRead P I E d (fun c x => ((k * M c x : ℕ) : ℚ)) =
      (k : ℚ) • marginalRead P I E d (fun c x => (M c x : ℚ)) := by
  simp only [marginalRead, Finset.smul_sum, smul_smul, Nat.cast_mul]

/-- [proved-derived; formal-checked] **The normalized open is population invariant.** Scaling every
count by a positive integer `k` (a repeated population with the same empirical ratios) leaves:
* the normalized phase counts;
* every conditional slice;
* the whole indexed, normalized source open, under every encoder and pair port. -/
theorem normalized_open_population_invariant (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (E : (A → ℚ) →ₗ[ℚ] X) (d : ℕ) (M : ℕ → A → ℕ) (offsets : Finset ℕ)
    (F : ℕ → (A × A → ℚ) →ₗ[ℚ] X) (C : ℕ → ℕ → A → A → ℕ) (window : List A) {k : ℕ}
    (hk : 0 < k) :
    normalized d (fun c x => k * M c x) = normalized d M ∧
      (∀ δ a, conditional d (fun c x b => k * C δ c x b) a = conditional d (C δ) a) ∧
      sourceOpen P I E d (fun c x => k * M c x) offsets F (fun δ c x b => k * C δ c x b) window =
        sourceOpen P I E d M offsets F C window := by
  have hM := normalized_mul (d := d) M hk
  have hC : ∀ δ a, conditional d (fun c x b => k * C δ c x b) a = conditional d (C δ) a :=
    fun δ a => normalized_mul (d := d) (column (C δ) a) hk
  refine ⟨hM, hC, ?_⟩
  unfold sourceOpen
  rw [hM]
  congr 1
  refine Finset.sum_congr rfl fun δ _ => ?_
  cases window[δ - 1]? with
  | none => rfl
  | some a =>
    have hs : addressedSlice d (fun c x b => k * C δ c x b) a = addressedSlice d (C δ) a := by
      unfold addressedSlice
      rw [hC δ a]
    simp only [pairTerm, hs]

/-- [proved-derived; formal-checked] **The open needs no tape.** Two source states with equal phase
counts and pair counts below the period and one window give one open under every contemporary
encoder `E` and pair ports `F^δ`: the open is read off the retained tables and window alone. -/
theorem indexed_open_tape_free (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (d : ℕ)
    {M M' : ℕ → A → ℕ} {C C' : ℕ → ℕ → A → A → ℕ} (offsets : Finset ℕ) (window : List A)
    (hM : ∀ c < d, ∀ x, M c x = M' c x) (hC : ∀ δ, ∀ c < d, ∀ x a, C δ c x a = C' δ c x a)
    (E : (A → ℚ) →ₗ[ℚ] X) (F : ℕ → (A × A → ℚ) →ₗ[ℚ] X) :
    sourceOpen P I E d M offsets F C window = sourceOpen P I E d M' offsets F C' window := by
  have hpop : population d M = population d M' :=
    Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun x _ =>
      hM c (Finset.mem_range.mp hc) x
  have hcol : ∀ δ a, addressPopulation d (C δ) a = addressPopulation d (C' δ) a :=
    fun δ a => Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun x _ =>
      hC δ c (Finset.mem_range.mp hc) x a
  unfold sourceOpen marginalRead
  congr 1
  · refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun x _ => ?_
    simp only [normalized, hpop, hM c (Finset.mem_range.mp hc) x]
  · refine Finset.sum_congr rfl fun δ _ => ?_
    cases window[δ - 1]? with
    | none => rfl
    | some a =>
      simp only [pairTerm, pairRead, addressedSlice]
      refine Finset.sum_congr rfl fun c hc => Finset.sum_congr rfl fun x _ =>
        Finset.sum_congr rfl fun b _ => ?_
      have hcond : conditional d (C δ) a c x = conditional d (C' δ) a c x := by
        have h1 := hcol δ a
        unfold addressPopulation at h1
        simp only [conditional, normalized, h1, column, hC δ c (Finset.mem_range.mp hc) x a]
      rw [hcond]

/-- [proved-derived; formal-checked] **The normalized marginal is the count read over its
population**: at a positive population, the marginal read of `M/n` is `n⁻¹` times the read of the
counts. -/
theorem normalized_marginal_eq_scaled_read (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S)
    (E : (A → ℚ) →ₗ[ℚ] X) {d : ℕ} {M : ℕ → A → ℕ} (h : 0 < population d M) :
    marginalRead P I E d (normalized d M) =
      (population d M : ℚ)⁻¹ • marginalRead P I E d (fun c x => (M c x : ℚ)) := by
  simp only [marginalRead, Finset.smul_sum, smul_smul, normalized_of_pos h, div_eq_inv_mul]

/-- [proved-derived; formal-checked] **The marginal read of the counts is the owner's moment.** On a
closing ring (`P^d = 1`), the marginal read of the phase counts `counts u τ d (range n)` is
`HNN/Moment.encoderMoment` (`encoderMoment_contract`); so the normalized marginal open is that
moment divided by its population (`normalized_marginal_eq_scaled_read`). -/
theorem marginalRead_counts {P : (Module.End ℚ S)ˣ} {d : ℕ} (hd : 0 < d) (hP : P ^ d = 1)
    (I : X →ₗ[ℚ] S) (E : (A → ℚ) →ₗ[ℚ] X) (u : ℕ → A) (τ : ℕ → ℕ) (n : ℕ) :
    marginalRead P I E d (fun c x => (counts u τ d (Finset.range n) c x : ℚ)) =
      encoderMoment P I E u τ n :=
  (encoderMoment_contract hd hP I E u τ n).symm

/-- [proved-derived; formal-checked] **The pair read of the offset counts is the owner's offset
contribution.** On a closing ring, the pair read of `offsetCounts u τ d n δ` through any pair port
is `HNN/Moment.offsetContribution` (`exteriorOffset_independent_of_E`); the indexed open reads
one normalized column of that table. -/
theorem pairRead_offsetCounts {P : (Module.End ℚ S)ˣ} {d : ℕ} (hd : 0 < d) (hP : P ^ d = 1)
    (I : X →ₗ[ℚ] S) (F : (A × A → ℚ) →ₗ[ℚ] X) (u : ℕ → A) (τ : ℕ → ℕ) (n δ : ℕ) :
    pairRead P I F d (fun c x b => (offsetCounts u τ d n δ c x b : ℚ)) =
      offsetContribution P I F u τ n δ :=
  ((exteriorOffset_independent_of_E hd hP I u τ n δ).1 F).symm

end Read

/-! ## 4. The passage continued by its section: one span and its transported weights

[definition; agent-inferred, September 30] (`holonics::hnn::moment::SourceMoment::continued`,
`holonics::hnn::prediction::BankPlacement`.) A generated section continues the request's passage
along the receiving ring's clock: the request's cells cross at the ring's ticks up to `τ`, the
section's stations at `τ + 1 + j`, one clocked span. Each crossing's datum is carried to the reading
frame by the ring's transport and the span is read over its transported mass:
`w_k = m_k / Σ_(l∈span) m_l` (`transportedWeight`), `m_k` the transport's modulus from the
crossing's tick. The weights sum to one (`transported_weight_mass`), do not depend on the frame the
span is read in (`transported_weight_frame_invariant`, `decayed_weight_frame_free`), and do not
depend on where the request ends and the section begins (`passage_weight_split_invariant`).

* **A unitary transport** (a closing rotor ring: a rotation, modulus one on every node) weighs
  every crossing `1/(n + v)` (`transported_weight_unitary`, `decayed_weight_lossless`): the
  request's counts and the section's are one table (`passage`, `passage_population`), read over
  one population (`passage_weight_one_population`, `passage_read`). The retired reading placed the
  section over its own population `v` and the request over its own `n`, which weighs a section
  datum `n/v` times a request cell, one only when `n = v` (`separate_populations_ratio`).
* **A dissipative transport** of modulus `0 < ρ ≤ 1` a tick weighs a crossing `a` ticks old by
  `ρ^a` over the span's sum: older crossings weigh no more (`decayed_weight_antitone`), none past
  its own crossing, and every crossing still enters.
* **Why the frontier needs dissipation**: in a phase-carried face `Σ_k u^(r_k) g_k` at a unit
  phase `u`, a lossless transport gives every crossing's term its own modulus at every lag
  (`lossless_term_modulus`), so no reading of the face can mark the span's frontier; a transport of
  modulus `ρ` weighs the term at lag `r` by `ρ^r` (`dissipative_term_modulus`). -/

section Passage

variable {X S : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup S] [Module ℚ S]

/-- [definition] **The passage's counts**: the request's phase counts `M` with its section's `N`
counted into the same table. -/
def passage (M N : ℕ → A → ℕ) : ℕ → A → ℕ := fun c x => M c x + N c x

/-- [proved-derived; formal-checked] **The passage's population** is the request's plus the
section's. -/
theorem passage_population (d : ℕ) (M N : ℕ → A → ℕ) :
    population d (passage M N) = population d M + population d N := by
  simp [population, passage, Finset.sum_add_distrib]

/-- [proved-derived; formal-checked] **One population weighs every datum alike**: a request cell
and a section datum at `(c, x)` enter the passage's normalized counts over the one population
`n + v`. -/
theorem passage_weight_one_population {d : ℕ} {M N : ℕ → A → ℕ}
    (h : 0 < population d M + population d N) (c : ℕ) (x : A) :
    normalized d (passage M N) c x =
      ((M c x : ℚ) + N c x) / ((population d M : ℚ) + population d N) := by
  have hp : 0 < population d (passage M N) := by rw [passage_population]; exact h
  rw [normalized_of_pos hp, passage_population]
  simp [passage]

/-- [proved-derived; formal-checked] **The passage's read** is the request's count read plus the
section's, over the one population (`BankPlacement::storage`'s law at a unitary transport). -/
theorem passage_read [DecidableEq A] (P : (Module.End ℚ S)ˣ) (I : X →ₗ[ℚ] S) (E : (A → ℚ) →ₗ[ℚ] X) {d : ℕ}
    {M N : ℕ → A → ℕ} (h : 0 < population d M + population d N) :
    marginalRead P I E d (normalized d (passage M N)) =
      ((population d M : ℚ) + population d N)⁻¹ •
        (marginalRead P I E d (fun c x => (M c x : ℚ)) +
          marginalRead P I E d (fun c x => (N c x : ℚ))) := by
  have hp : 0 < population d (passage M N) := by rw [passage_population]; exact h
  rw [normalized_marginal_eq_scaled_read P I E hp, passage_population]
  congr 1
  · push_cast; rfl
  · simp only [marginalRead, passage, Nat.cast_add, add_smul, Finset.sum_add_distrib]

/-- [proved-derived; formal-checked] **Separate populations weigh a section datum `n/v` times a
request cell** (the September 30 located cause: at the open section `v = 1` and `n = 40`), and the
two weigh alike only when `n = v`. -/
theorem separate_populations_ratio {n v : ℕ} (hn : 0 < n) (hv : 0 < v) :
    (v : ℚ)⁻¹ / (n : ℚ)⁻¹ = (n : ℚ) / v ∧ ((v : ℚ)⁻¹ / (n : ℚ)⁻¹ = 1 ↔ n = v) := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have hv' : (v : ℚ) ≠ 0 := by exact_mod_cast hv.ne'
  have hratio : (v : ℚ)⁻¹ / (n : ℚ)⁻¹ = (n : ℚ) / v := by field_simp
  refine ⟨hratio, ?_⟩
  rw [hratio, div_eq_one_iff_eq hv']
  exact_mod_cast Iff.rfl

end Passage

section Transported

variable {ι : Type*}

/-- [definition] **A crossing's transported weight** over a span `s`: its transport's modulus `m k`
to the reading frame over the span's transported mass `Σ_(l∈s) m l`. -/
def transportedWeight (s : Finset ι) (m : ι → ℚ) (k : ι) : ℚ := m k / ∑ l ∈ s, m l

/-- [proved-derived; formal-checked] **The transported weights carry unit mass.** -/
theorem transported_weight_mass {s : Finset ι} {m : ι → ℚ} (h : (∑ l ∈ s, m l) ≠ 0) :
    ∑ k ∈ s, transportedWeight s m k = 1 := by
  simp only [transportedWeight, ← Finset.sum_div]
  exact div_self h

/-- [proved-derived; formal-checked] **The weights are frame-free**: a common factor of every
modulus (another reading frame) leaves every weight. -/
theorem transported_weight_frame_invariant (s : Finset ι) (m : ι → ℚ) {c : ℚ} (hc : c ≠ 0)
    (k : ι) : transportedWeight s (fun l => c * m l) k = transportedWeight s m k := by
  simp only [transportedWeight, ← Finset.mul_sum]
  by_cases h : ∑ l ∈ s, m l = 0
  · simp [h]
  · rw [mul_div_mul_left _ _ hc]

/-- [proved-derived; formal-checked] **A unitary transport weighs every crossing of the span
alike**: `1/|s|`, the one population. -/
theorem transported_weight_unitary {s : Finset ι} {m : ι → ℚ} (hm : ∀ l ∈ s, m l = 1) {k : ι}
    (hk : k ∈ s) : transportedWeight s m k = 1 / s.card := by
  simp only [transportedWeight, hm k hk, Finset.sum_congr rfl hm, Finset.sum_const, nsmul_eq_mul,
    mul_one]

/-- [proved-derived; formal-checked] **The span, not its split, sets the weights**: two splits of one
span into request and section give one weight to every crossing. -/
theorem passage_weight_split_invariant [DecidableEq ι] {R N R' N' : Finset ι}
    (h : R ∪ N = R' ∪ N') (m : ι → ℚ) :
    transportedWeight (R ∪ N) m = transportedWeight (R' ∪ N') m := by
  rw [h]

/-- [proved-derived; formal-checked] **A dissipative transport's moduli fall with age**: at
`0 ≤ ρ ≤ 1` a tick, a crossing `b ≥ a` ticks old weighs no more than one `a` ticks old, and no
modulus exceeds one (passive). -/
theorem decayed_weight_antitone {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {a b : ℕ} (hab : a ≤ b) :
    ρ ^ b ≤ ρ ^ a ∧ ρ ^ a ≤ 1 :=
  ⟨pow_le_pow_of_le_one h0 h1 hab, pow_le_one₀ h0 h1⟩

/-- [proved-derived; formal-checked] **A dissipative transport's weights are frame-free**: reading
the span `shift` ticks later multiplies every modulus by `ρ^shift`, which leaves every weight. -/
theorem decayed_weight_frame_free (s : Finset ι) (age : ι → ℕ) {ρ : ℚ} (hρ : ρ ≠ 0)
    (shift : ℕ) (k : ι) :
    transportedWeight s (fun l => ρ ^ (age l + shift)) k =
      transportedWeight s (fun l => ρ ^ age l) k := by
  have hfun : (fun l => ρ ^ (age l + shift)) = fun l => ρ ^ shift * ρ ^ age l := by
    funext l
    rw [pow_add, mul_comm]
  rw [hfun, transported_weight_frame_invariant s _ (pow_ne_zero _ hρ)]

/-- [proved-derived; formal-checked] **At `ρ = 1` the dissipative law is the one population.** -/
theorem decayed_weight_lossless {s : Finset ι} (age : ι → ℕ) {k : ι} (hk : k ∈ s) :
    transportedWeight s (fun l => (1 : ℚ) ^ age l) k = 1 / s.card :=
  transported_weight_unitary (fun _ _ => one_pow _) hk

/-- [proved-derived; formal-checked] **A lossless transport cannot mark the frontier**: in a
phase-carried face `Σ_k u^(r_k) g_k` at a unit phase `u`, the term of a crossing at lag `r` has the
modulus of its datum's `g` whatever `r` is. -/
theorem lossless_term_modulus (u g : ℂ) (hu : ‖u‖ = 1) (r : ℕ) : ‖u ^ r * g‖ = ‖g‖ := by
  rw [norm_mul, norm_pow, hu, one_pow, one_mul]

/-- [proved-derived; formal-checked] **A dissipative transport weighs the term at lag `r` by
`ρ^r`**: at modulus `ρ ≥ 0` a tick, the term of a crossing `r` ticks back has modulus `ρ^r |g|`. -/
theorem dissipative_term_modulus (u g : ℂ) (hu : ‖u‖ = 1) {ρ : ℝ} (hρ : 0 ≤ ρ) (r : ℕ) :
    ‖((ρ : ℂ) * u) ^ r * g‖ = ρ ^ r * ‖g‖ := by
  rw [norm_mul, norm_pow, norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg hρ]

/-- [proved-derived; formal-checked] **A later datum's landing splits into its normalization and its
entry** (loop 1c's pin §2.3; `holonics::hnn::prediction::BankPlacement::storage_over`). Over a span
`s` of positive transported mass, a datum `k ∉ s` of positive modulus lands: the read of
`insert k s` is the read of `s` scaled by `M(s)/M(insert k s)` (**the normalization**: `k`'s share
of the mass taken from every earlier datum alike) plus `k`'s own image at its weight (**the entry**).
The two parts are the paired counterfactual's two factors; the realization charts each weight
(`PopulationChart::chart`), so on the chart the identity holds per cell, not across cells. -/
theorem transported_weight_insert [DecidableEq ι] {V : Type*} [AddCommGroup V] [Module ℚ V]
    {s : Finset ι} {k : ι} (hk : k ∉ s) (m : ι → ℚ) (hs : 0 < ∑ l ∈ s, m l) (hmk : 0 < m k)
    (v : ι → V) :
    ∑ l ∈ insert k s, transportedWeight (insert k s) m l • v l =
      ((∑ l ∈ s, m l) / ∑ l ∈ insert k s, m l) • ∑ l ∈ s, transportedWeight s m l • v l +
        transportedWeight (insert k s) m k • v k := by
  have hM : (∑ l ∈ s, m l) ≠ 0 := hs.ne'
  have hM' : (∑ l ∈ insert k s, m l) ≠ 0 := by
    rw [Finset.sum_insert hk]
    exact (add_pos hmk hs).ne'
  rw [Finset.sum_insert hk, add_comm, Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [smul_smul]
  congr 1
  simp only [transportedWeight]
  field_simp

/-- [proved-derived; formal-checked] **The normalization's scale lies strictly between zero and
one**: a landing of positive modulus takes a positive share of a positive span's mass, never all of
it. -/
theorem transported_weight_insert_scale [DecidableEq ι] {s : Finset ι} {k : ι} (hk : k ∉ s)
    (m : ι → ℚ) (hs : 0 < ∑ l ∈ s, m l) (hmk : 0 < m k) :
    0 < (∑ l ∈ s, m l) / (∑ l ∈ insert k s, m l) ∧
      (∑ l ∈ s, m l) / (∑ l ∈ insert k s, m l) < 1 := by
  rw [Finset.sum_insert hk]
  refine ⟨div_pos hs (add_pos hmk hs), ?_⟩
  rw [div_lt_one (add_pos hmk hs)]
  linarith

end Transported

/-! ## 5. Read from a station: the two-sided transport distance

[definition; agent-inferred, September 30] (`holonics::hnn::prediction::BankPlacement`, the
re-entry diagnosis §6.) The section is a joint field, refined whole: a candidate at station `j`
reads every datum of the span at its two-sided transport distance from `j`,
`w_j(k) = ρ^|τ_j − τ_k| / Σ_(l∈span) ρ^|τ_j − τ_l|` (`framedWeight`), the dissipative tube's
stationary response falling by `ρ` a tick in both directions. The one-way weight read at the span's
end, `ρ^(τ_end − τ_k)`, grows backward from `j`: a datum `r` ticks after the station read weighs
`ρ^(−r)` times the station's own candidate (`oneway_later_weight_ratio`), which is how a late lock
took the span's mass and quenched the earlier stations.

* **Normalization and entry** (`framed_weight_mass`, `framed_weight_pos`): at `ρ > 0` the weights
  read from any station carry unit mass, and every datum of the span enters with positive weight
  (no datum is dropped by its distance: no window).
* **One-sided on older data** (`framed_weight_one_sided`): on a span whose data lie no later than
  the station read, the weights are the one-way law read at any later frame (the common factor
  `ρ^(e − j)` cancels), so the open section and a station read after every lock read as before.
* **A distant datum weighs little** (`framed_weight_ratio`, `framed_weight_le_pow`): read from `j`,
  a datum `r` ticks away, on either side, weighs `ρ^r` times the station's own candidate, and, the
  candidate in the span, at most `ρ^r`.
* **Two-sided and translation-free** (`framed_weight_symmetric`, `framed_weight_translation`): data
  at equal distance on either side weigh alike, and a common shift of every tick and the station
  leaves every weight: the law reads only distances on the clock, whatever the modality.
* **Lossless** (`framed_weight_lossless`): at `ρ = 1` the weights are the one population `1/|s|`. -/

section Framed

variable {ι : Type*}

/-- [definition] **A datum's weight read from a station**: over a span `s` whose data cross at
`tick`, read from the station's tick `j` through a transport of modulus `ρ` a tick, the datum `k`
weighs `ρ^|j − tick k|` over the span's mass read from `j`. -/
def framedWeight (s : Finset ι) (tick : ι → ℤ) (ρ : ℚ) (j : ℤ) (k : ι) : ℚ :=
  transportedWeight s (fun l => ρ ^ (j - tick l).natAbs) k

/-- [proved-derived; formal-checked] **The weights read from any station carry unit mass.** -/
theorem framed_weight_mass {s : Finset ι} (hs : s.Nonempty) (tick : ι → ℤ) {ρ : ℚ} (hρ : 0 < ρ)
    (j : ℤ) : ∑ k ∈ s, framedWeight s tick ρ j k = 1 :=
  transported_weight_mass (Finset.sum_pos (fun _ _ => pow_pos hρ _) hs).ne'

/-- [proved-derived; formal-checked] **Every datum of the span enters**: at `ρ > 0` each weighs
strictly more than zero, whatever its distance from the station read. -/
theorem framed_weight_pos {s : Finset ι} (tick : ι → ℤ) {ρ : ℚ} (hρ : 0 < ρ) (j : ℤ) {k : ι}
    (hk : k ∈ s) : 0 < framedWeight s tick ρ j k :=
  div_pos (pow_pos hρ _) (Finset.sum_pos (fun _ _ => pow_pos hρ _) ⟨k, hk⟩)

/-- [proved-derived; formal-checked] **On data no later than the station read, the one-way law**:
if every datum of the span crosses at or before `j`, the weights read from `j` are the one-way
weights `ρ^(e − tick l)` read at any frame `e ≥ j` (the common factor `ρ^(e − j)` cancels). -/
theorem framed_weight_one_sided {s : Finset ι} (tick : ι → ℤ) {ρ : ℚ} (hρ : ρ ≠ 0) {j e : ℤ}
    (hpast : ∀ l ∈ s, tick l ≤ j) (hje : j ≤ e) {k : ι} (hk : k ∈ s) :
    framedWeight s tick ρ j k = transportedWeight s (fun l => ρ ^ (e - tick l).toNat) k := by
  have hsplit : ∀ l ∈ s,
      ρ ^ (e - tick l).toNat = ρ ^ (e - j).toNat * ρ ^ (j - tick l).natAbs := by
    intro l hl
    rw [← pow_add]
    congr 1
    have := hpast l hl
    omega
  simp only [framedWeight, transportedWeight]
  rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, hsplit k hk,
    mul_div_mul_left _ _ (pow_ne_zero _ hρ)]

/-- [proved-derived; formal-checked] **Read from a station, a datum weighs `ρ^r` times the
station's own candidate**, `r` its distance on either side. -/
theorem framed_weight_ratio (s : Finset ι) (tick : ι → ℤ) (ρ : ℚ) {j : ℤ} {i : ι}
    (hij : tick i = j) (k : ι) :
    framedWeight s tick ρ j k = ρ ^ (j - tick k).natAbs * framedWeight s tick ρ j i := by
  simp only [framedWeight, transportedWeight]
  rw [hij, sub_self, Int.natAbs_zero, pow_zero, mul_one_div]

/-- [proved-derived; formal-checked] **A datum `r` ticks from the station read weighs at most
`ρ^r`**, when the station's own candidate is in the span (it weighs one before the normalization):
a far lock no longer takes the span's mass. -/
theorem framed_weight_le_pow {s : Finset ι} (tick : ι → ℤ) {ρ : ℚ} (h0 : 0 ≤ ρ) {j : ℤ} {i : ι}
    (hi : i ∈ s) (hij : tick i = j) (k : ι) :
    framedWeight s tick ρ j k ≤ ρ ^ (j - tick k).natAbs := by
  simp only [framedWeight, transportedWeight]
  have hmass : (1 : ℚ) ≤ ∑ l ∈ s, ρ ^ (j - tick l).natAbs := by
    calc (1 : ℚ) = ρ ^ (j - tick i).natAbs := by rw [hij, sub_self, Int.natAbs_zero, pow_zero]
      _ ≤ ∑ l ∈ s, ρ ^ (j - tick l).natAbs :=
        Finset.single_le_sum (f := fun l => ρ ^ (j - tick l).natAbs)
          (fun l _ => pow_nonneg h0 _) hi
  exact div_le_self (pow_nonneg h0 _) hmass

/-- [proved-derived; formal-checked] **The one-way law weighs a later datum `ρ^(−r)` times an
earlier one**: read at the span's end `e`, a datum `i` crossing `r = tick k − tick i` ticks before
`k` weighs `ρ^r` times `k`, so, read at the end, a lock `r` ticks after the station read weighs
`ρ^(−r)` times the station's candidate (the re-entry diagnosis: the far lock took the mass). -/
theorem oneway_later_weight_ratio (s : Finset ι) (tick : ι → ℤ) (ρ : ℚ) {e : ℤ} {i k : ι}
    (hik : tick i ≤ tick k) (hke : tick k ≤ e) :
    transportedWeight s (fun l => ρ ^ (e - tick l).toNat) i =
      ρ ^ (tick k - tick i).toNat * transportedWeight s (fun l => ρ ^ (e - tick l).toNat) k := by
  have h : (e - tick i).toNat = (tick k - tick i).toNat + (e - tick k).toNat := by omega
  simp only [transportedWeight]
  rw [h, pow_add, mul_div_assoc]

/-- [proved-derived; formal-checked] **Two-sided**: two data at equal distance on either side of
the station read weigh alike. -/
theorem framed_weight_symmetric (s : Finset ι) (tick : ι → ℤ) (ρ : ℚ) {j : ℤ} {a b : ι}
    (hab : tick a + tick b = 2 * j) : framedWeight s tick ρ j a = framedWeight s tick ρ j b := by
  have h : (j - tick a).natAbs = (j - tick b).natAbs := by omega
  simp only [framedWeight, transportedWeight]
  rw [h]

/-- [proved-derived; formal-checked] **The law reads only distances on the clock**: shifting every
tick and the station read by one amount leaves every weight. -/
theorem framed_weight_translation (s : Finset ι) (tick : ι → ℤ) (ρ : ℚ) (j c : ℤ) (k : ι) :
    framedWeight s (fun l => tick l + c) ρ (j + c) k = framedWeight s tick ρ j k := by
  simp only [framedWeight, add_sub_add_right_eq_sub]

/-- [proved-derived; formal-checked] **At `ρ = 1` the framed law is the one population**, from any
station. -/
theorem framed_weight_lossless {s : Finset ι} (tick : ι → ℤ) (j : ℤ) {k : ι} (hk : k ∈ s) :
    framedWeight s tick 1 j k = 1 / s.card :=
  transported_weight_unitary (fun _ _ => one_pow _) hk

end Framed

/-! ## 6. The founding off the lossless boundary

[definition; agent-inferred, September 30] (`holonics::hnn::constitution::Constitution::
founding_transport`; the modulus's record,
`research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md`.) The
modulus one is the passive set's boundary and the law's degenerate point: no recency is marked
(`lossless_term_modulus`), and a datum a whole turn farther weighs what the nearer does
(`lossless_alias`), so the phase record, which carries a datum's age only within one turn, reads
the transport only by not reading it. Founded there, the executed comparison's certified move
stays there (the record measures its slope at the opening pointing outward). The transport is
founded at the largest lattice modulus whose one-turn transport carries a datum to one unit of the
weights' chart.

* **The alias** (`founded_modulus_alias`, `founded_modulus_alias_le`): read from a station, of two
  data on its older side `d` ticks apart, the farther weighs `ρ^d` times the nearer; with
  `ρ^d ≤ 2^(−L)` at most `2^(−L)` times it. At `ρ = 1` they weigh alike (`lossless_alias`).
* **The founding** (`IsFounding`): the numerator `k` on the lattice `2^(−L_s)ℤ` with
  `k^d 2^L ≤ (2^L_s)^d < (k + 1)^d 2^L`, so `ρ₀ = k 2^(−L_s)` has `ρ₀^d ≤ 2^(−L)`
  (`founded_modulus_pow_le`), is the greatest such lattice modulus (`founded_modulus_greatest`), lies
  strictly below one when `L ≥ 1` (`founded_modulus_lt_one`) and above zero when `L ≤ L_s d`
  (`founded_modulus_pos`).
* **The order-2 declaration's founding** (`order_founding`): `d = 60`, `L_ν = 21`, `L_s = 21`
  found at `k = 1645392`, `ρ₀ = 102837/131072`. -/

section Founding

variable {ι : Type*}

/-- [proved-derived; formal-checked] **A datum a whole turn farther weighs the turn's transport
times the nearer**: read from `j`, of two data on its older side `d` ticks apart, the farther weighs
`ρ^d` times the nearer. -/
theorem founded_modulus_alias (s : Finset ι) (tick : ι → ℤ) (ρ : ℚ) {j : ℤ} {a b : ι} (d : ℕ)
    (hturn : tick b + d = tick a) (ha : tick a ≤ j) :
    framedWeight s tick ρ j b = ρ ^ d * framedWeight s tick ρ j a := by
  have h : (j - tick b).natAbs = d + (j - tick a).natAbs := by omega
  simp only [framedWeight, transportedWeight]
  rw [h, pow_add, mul_div_assoc]

/-- [proved-derived; formal-checked] **The founding's alias is at most one chart unit**: with
`ρ^d ≤ 2^(−L)`, a datum a whole turn farther weighs at most `2^(−L)` times the nearer. -/
theorem founded_modulus_alias_le (s : Finset ι) (tick : ι → ℤ) {ρ : ℚ} (h0 : 0 ≤ ρ) {j : ℤ}
    {a b : ι} {d L : ℕ} (hturn : tick b + d = tick a) (ha : tick a ≤ j)
    (hfound : ρ ^ d ≤ (1 / 2 : ℚ) ^ L) :
    framedWeight s tick ρ j b ≤ (1 / 2 : ℚ) ^ L * framedWeight s tick ρ j a := by
  rw [founded_modulus_alias s tick ρ d hturn ha]
  exact mul_le_mul_of_nonneg_right hfound
    (div_nonneg (pow_nonneg h0 _) (Finset.sum_nonneg fun _ _ => pow_nonneg h0 _))

/-- [proved-derived; formal-checked] **At `ρ = 1` a whole turn farther weighs alike**: the phase
record's one-turn alias is invisible to the lossless transport only because it reads no age. -/
theorem lossless_alias (s : Finset ι) (tick : ι → ℤ) {j : ℤ} {a b : ι} (d : ℕ)
    (hturn : tick b + d = tick a) (ha : tick a ≤ j) :
    framedWeight s tick 1 j b = framedWeight s tick 1 j a := by
  rw [founded_modulus_alias s tick 1 d hturn ha, one_pow, one_mul]

/-- [definition] **The founding numerator** on the lattice `2^(−L_s)ℤ`: `k` with
`k^d 2^L ≤ (2^L_s)^d < (k + 1)^d 2^L`, the greatest lattice modulus `k 2^(−L_s)` whose `d`-th
power is at most `2^(−L)`. -/
def IsFounding (Ls d L k : ℕ) : Prop :=
  k ^ d * 2 ^ L ≤ (2 ^ Ls) ^ d ∧ (2 ^ Ls) ^ d < (k + 1) ^ d * 2 ^ L

/-- [proved-derived; formal-checked] **The founding's one-turn transport is at most one chart
unit**: `(k 2^(−L_s))^d ≤ 2^(−L)`. -/
theorem founded_modulus_pow_le {Ls d L k : ℕ} (h : IsFounding Ls d L k) :
    ((k : ℚ) / 2 ^ Ls) ^ d ≤ (1 / 2 : ℚ) ^ L := by
  have hcast : ((k ^ d * 2 ^ L : ℕ) : ℚ) ≤ (((2 ^ Ls) ^ d : ℕ) : ℚ) := by exact_mod_cast h.1
  push_cast at hcast
  have hpos : (0 : ℚ) < (2 ^ Ls) ^ d := by positivity
  have hL : (0 : ℚ) < 2 ^ L := by positivity
  rw [div_pow, one_div_pow, div_le_div_iff₀ hpos hL, one_mul]
  exact hcast

/-- [proved-derived; formal-checked] **The founding is the greatest such lattice modulus**: any
lattice numerator whose modulus's `d`-th power is at most `2^(−L)` is at most `k`. -/
theorem founded_modulus_greatest {Ls d L k k' : ℕ} (h : IsFounding Ls d L k)
    (h' : k' ^ d * 2 ^ L ≤ (2 ^ Ls) ^ d) : k' ≤ k := by
  by_contra hlt
  have hk : k + 1 ≤ k' := by omega
  have hpow : (k + 1) ^ d * 2 ^ L ≤ k' ^ d * 2 ^ L :=
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hk d)
  have := h.2
  omega

/-- [proved-derived; formal-checked] **The founding lies strictly below one**: with a chart grain
`L ≥ 1`, `k < 2^L_s`, so `ρ₀ < 1`: the founding is off the lossless boundary. -/
theorem founded_modulus_lt_one {Ls d L k : ℕ} (h : IsFounding Ls d L k) (hL : 1 ≤ L) :
    k < 2 ^ Ls := by
  by_contra hge
  have hk : 2 ^ Ls ≤ k := by omega
  have hpow : (2 ^ Ls) ^ d ≤ k ^ d := Nat.pow_le_pow_left hk d
  have h2 : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  have hbig : (2 ^ Ls) ^ d * 2 ≤ k ^ d * 2 ^ L :=
    Nat.mul_le_mul hpow h2
  have hposd : 0 < (2 ^ Ls) ^ d := by positivity
  have := h.1
  omega

/-- [proved-derived; formal-checked] **The founding lies above zero** when the lattice carries it,
`L ≤ L_s d`. -/
theorem founded_modulus_pos {Ls d L k : ℕ} (h : IsFounding Ls d L k) (hcarry : L ≤ Ls * d) :
    0 < k := by
  by_contra h0
  have hk : k = 0 := by omega
  have h2 := h.2
  rw [hk, zero_add, one_pow, one_mul, ← pow_mul] at h2
  exact absurd (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2) |>.mp h2) (by omega)

/-- [proved-derived; formal-checked] **The order-2 declaration's founding**: the ring of period
`d = 60`, the weights' chart `L_ν = 21` and the source port's lattice `L_s = 21` found at
`k = 1645392`, `ρ₀ = 1645392/2^21 = 102837/131072`. -/
theorem order_founding : IsFounding 21 60 21 1645392 := by
  unfold IsFounding
  constructor <;> norm_num

end Founding

/-! ## 7. The leaky count

[definition; agent-inferred, October 2] (`holonics::hnn::moment`, "The leaky count";
`SourceMoment::open_with`; the contact loop record §24.) Below modulus one the phase record reads
a datum's age only within one turn (`founded_modulus_alias`). The leaky count carries the age in
the counts instead: at each of the ring's ticks every count is multiplied by `ρ`, and a datum then
enters at its phase. The counts are integer coordinates on the lattice `2^(−u)`, `u = L_ν + m`,
`m` the least with `2^m (1 − ρ) ≥ 1`, and each product is read at the nearest lattice point, ties
up (`nearest`). In lattice units:

```text
tick          v ← ⌊(2 v k + 2^s) / 2^(s+1)⌋ = nearest(ρ v)   (ρ = k 2^(−s); leaky_tick_eq_nearest)
ingest        v ← v + 2^u                                      (exact: one datum, weight one)
section       v ← v + nearest(ρ^a 2^u)                         (a datum entered a ticks old)
read          w = chart(L̂[slot] / Σ L̂)
```

* **One half unit per rounding** (`nearest_sub_le`); the Rust tick is the nearest point
  (`leaky_tick_eq_nearest`).
* **The carried count** (`leaky_count_error_le`, `leaky_count_ingest`): over any sequence of
  ticks, exact entries and `r` rounded entries, a carried count stays within
  `1/(2(1 − ρ)) + r/2` lattice units of the exact decayed count. The ingest enters exact units, so
  its counts stay within `1/(2(1 − ρ))` units over a passage of any length, and with
  `2^m (1 − ρ) ≥ 1` that is at most `2^(−L_ν−1)`, half a population-chart unit
  (`leaky_lattice_le_half_chart`). A section's datum is rounded once when it enters
  (`SourceMoment::continued` reads it `ρ^a` at its age), so a section adds up to half a lattice
  unit a rounded entry; the half-chart-unit bound is not shown on that path.
* **The normalized read** (`leaky_read_error`): with every carried count within `δ` of its exact
  count over `N` slots, the read of slot `k` is within `(δ + w_k N δ)/Σ L̂` of its transported
  weight `w_k`, before the chart rounds it (half a chart unit more). The slots' errors add in the
  mass, so the read is not within one chart unit in general:
  `leaky_read_exceeds_chart_unit` is the law's own instance at campaign 1's founding
  (`campaign_one_founding`, `ρ₀ = 10809/2^17`, `L_ν = 18`, `m = 1`) on a passage the ingest takes:
  205 data entering one phase of ring 0 (a code its lock selects, then the 204 it does not), then
  two of its ticks, where the newest datum's read is more than eight chart units from its
  transported weight, before and after the chart rounds it. -/

section Leaky

/-- [definition] **The nearest lattice point**, ties up: `⌊y + 1/2⌋`. -/
def nearest (y : ℚ) : ℤ := ⌊y + 1 / 2⌋

/-- [proved-derived; formal-checked] **One rounding is at most half a lattice unit**. -/
theorem nearest_sub_le (y : ℚ) : |(nearest y : ℚ) - y| ≤ 1 / 2 := by
  unfold nearest
  have h1 := Int.floor_le (y + 1 / 2)
  have h2 := Int.lt_floor_add_one (y + 1 / 2)
  rw [abs_le]
  constructor <;> linarith

/-- [proved-derived; formal-checked] **The Rust tick is the nearest point**: the integer step
`⌊(2 v k + 2^s)/2^(s+1)⌋` of `Leaky::decay` is `nearest(ρ v)` at `ρ = k 2^(−s)` (Lean's integer
division is the floor; the Rust's truncation agrees on the counts, which are nonnegative). -/
theorem leaky_tick_eq_nearest (v k : ℤ) (s : ℕ) :
    (2 * v * k + 2 ^ s) / 2 ^ (s + 1) = nearest ((k : ℚ) / 2 ^ s * v) := by
  unfold nearest
  have h : ((k : ℚ) / 2 ^ s * v + 1 / 2) = ((2 * v * k + 2 ^ s : ℤ) : ℚ) / ((2 ^ (s + 1) : ℕ) : ℚ) := by
    push_cast
    field_simp
    ring
  rw [h, Rat.floor_intCast_div_natCast]
  push_cast
  rfl

/-- [definition] **One step of the leaky count**: a tick of the transport, an exact lattice amount
entering (the ingest's datum, `2^u`), or a datum entering at the nearest point to `y` (a section's
datum, `y = ρ^a 2^u`). -/
inductive LeakyStep
  | tick
  | unit (n : ℤ)
  | entry (y : ℚ)

/-- [definition] **The carried count** after the steps, in lattice units. -/
def carried (ρ : ℚ) : ℤ → List LeakyStep → ℤ
  | v, [] => v
  | v, .tick :: l => carried ρ (nearest (ρ * v)) l
  | v, .unit n :: l => carried ρ (v + n) l
  | v, .entry y :: l => carried ρ (v + nearest y) l

/-- [definition] **The exact decayed count** after the steps, in lattice units. -/
def exactCount (ρ : ℚ) : ℚ → List LeakyStep → ℚ
  | x, [] => x
  | x, .tick :: l => exactCount ρ (ρ * x) l
  | x, .unit n :: l => exactCount ρ (x + n) l
  | x, .entry y :: l => exactCount ρ (x + y) l

/-- [definition] **The rounded entries** among the steps. -/
def rounded : List LeakyStep → ℕ
  | [] => 0
  | .entry _ :: l => rounded l + 1
  | _ :: l => rounded l

/-- [proved-derived; formal-checked] **The carried count's error**: over any steps, a carried count
within `1/(2(1 − ρ)) + c/2` lattice units of the exact one stays within
`1/(2(1 − ρ)) + (c + r)/2`, `r` the rounded entries. A tick takes the error `e` to at most
`ρ e + 1/2`, whose fixed point is `1/(2(1 − ρ))`; an exact entry leaves it; a rounded entry adds at
most `1/2`. -/
theorem leaky_count_error_le {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) (l : List LeakyStep) :
    ∀ (v : ℤ) (x : ℚ) (c : ℕ), |(v : ℚ) - x| ≤ 1 / (2 * (1 - ρ)) + c / 2 →
      |(carried ρ v l : ℚ) - exactCount ρ x l| ≤ 1 / (2 * (1 - ρ)) + (c + rounded l) / 2 := by
  have hgap : 0 < 1 - ρ := by linarith
  induction l with
  | nil => intro v x c h; simpa [carried, exactCount, rounded] using h
  | cons st l ih =>
    intro v x c h
    cases st with
    | tick =>
      simp only [carried, exactCount, rounded]
      apply ih
      have hr := nearest_sub_le (ρ * v)
      have hfix : 1 / (2 * (1 - ρ)) = 1 / 2 + ρ * (1 / (2 * (1 - ρ))) := by
        field_simp
        ring
      have hc : (0 : ℚ) ≤ c := by positivity
      calc |(nearest (ρ * v) : ℚ) - ρ * x|
          = |((nearest (ρ * v) : ℚ) - ρ * v) + ρ * ((v : ℚ) - x)| := by ring_nf
        _ ≤ |(nearest (ρ * v) : ℚ) - ρ * v| + |ρ * ((v : ℚ) - x)| := abs_add_le _ _
        _ ≤ 1 / 2 + ρ * (1 / (2 * (1 - ρ)) + c / 2) := by
          rw [abs_mul, abs_of_nonneg h0]
          exact add_le_add hr (mul_le_mul_of_nonneg_left h h0)
        _ ≤ 1 / (2 * (1 - ρ)) + c / 2 := by
          rw [hfix]
          nlinarith
    | unit n =>
      simp only [carried, exactCount, rounded]
      apply ih
      push_cast
      calc |(v : ℚ) + n - (x + n)| = |(v : ℚ) - x| := by ring_nf
        _ ≤ _ := h
    | entry y =>
      simp only [carried, exactCount, rounded]
      have := ih (v + nearest y) (x + y) (c + 1) (by
        push_cast
        calc |(v : ℚ) + nearest y - (x + y)| = |((v : ℚ) - x) + ((nearest y : ℚ) - y)| := by
              ring_nf
          _ ≤ |(v : ℚ) - x| + |(nearest y : ℚ) - y| := abs_add_le _ _
          _ ≤ 1 / (2 * (1 - ρ)) + c / 2 + 1 / 2 := add_le_add h (nearest_sub_le y)
          _ = 1 / (2 * (1 - ρ)) + ((c : ℚ) + 1) / 2 := by ring)
      calc _ ≤ 1 / (2 * (1 - ρ)) + (((c + 1 : ℕ) : ℚ) + rounded l) / 2 := this
        _ = _ := by push_cast; ring

/-- [proved-derived; formal-checked] **The ingest's count over a passage of any length**: from an
empty count, ticks and exact entries alone keep the carried count within `1/(2(1 − ρ))` lattice
units of the exact decayed count. -/
theorem leaky_count_ingest {ρ : ℚ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) {l : List LeakyStep}
    (hl : rounded l = 0) : |(carried ρ 0 l : ℚ) - exactCount ρ 0 l| ≤ 1 / (2 * (1 - ρ)) := by
  have hgap : 0 < 1 - ρ := by linarith
  have := leaky_count_error_le h0 h1 l 0 0 0 (by
    simp only [Int.cast_zero, sub_zero, abs_zero, Nat.cast_zero, zero_div, add_zero]
    positivity)
  simpa [hl] using this

/-- [proved-derived; formal-checked] **On the lattice `2^(−L_ν−m)` the ingest's bound is half a
chart unit**: with `2^m (1 − ρ) ≥ 1`, `2^(−L_ν−m)/(2(1 − ρ)) ≤ 2^(−L_ν−1)`. -/
theorem leaky_lattice_le_half_chart {ρ : ℚ} (h1 : ρ < 1) {L m : ℕ} (hm : 1 ≤ 2 ^ m * (1 - ρ)) :
    (1 / 2 : ℚ) ^ (L + m) * (1 / (2 * (1 - ρ))) ≤ (1 / 2) ^ (L + 1) := by
  have hgap : 0 < 1 - ρ := by linarith
  have h2m : (0 : ℚ) < 2 ^ m := by positivity
  rw [pow_add, pow_add, pow_one, one_div_pow (n := m), mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [div_mul_div_comm, one_mul, div_le_iff₀ (by positivity)]
  nlinarith

/-- [proved-derived; formal-checked] **The normalized read's error**: with every carried count
within `δ` of its exact count over the slots `s` (exact counts nonnegative, both masses positive),
the read of slot `k` is within `(δ + w_k |s| δ)/Σ L̂` of its transported weight `w_k = L_k/Σ L`:
the mass carries every slot's error. -/
theorem leaky_read_error {ι : Type*} (s : Finset ι) (Lh L : ι → ℚ) {δ : ℚ}
    (hδ : ∀ i ∈ s, |Lh i - L i| ≤ δ) (hL : ∀ i ∈ s, 0 ≤ L i) (hMh : 0 < ∑ i ∈ s, Lh i)
    (hM : 0 < ∑ i ∈ s, L i) {k : ι} (hk : k ∈ s) :
    |Lh k / ∑ i ∈ s, Lh i - L k / ∑ i ∈ s, L i|
      ≤ (δ + L k / (∑ i ∈ s, L i) * (s.card * δ)) / ∑ i ∈ s, Lh i := by
  set Mh := ∑ i ∈ s, Lh i
  set M := ∑ i ∈ s, L i
  have hw : 0 ≤ L k / M := div_nonneg (hL k hk) hM.le
  have hmass : |Mh - M| ≤ s.card * δ := by
    calc |Mh - M| = |∑ i ∈ s, (Lh i - L i)| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ i ∈ s, |Lh i - L i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ s, δ := Finset.sum_le_sum hδ
      _ = s.card * δ := by rw [Finset.sum_const, nsmul_eq_mul]
  have heq : Lh k / Mh - L k / M = ((Lh k - L k) - L k / M * (Mh - M)) / Mh := by
    field_simp
    ring
  rw [heq, abs_div, abs_of_pos hMh]
  apply div_le_div_of_nonneg_right _ hMh.le
  calc |(Lh k - L k) - L k / M * (Mh - M)|
      ≤ |Lh k - L k| + |L k / M * (Mh - M)| := abs_sub _ _
    _ ≤ δ + L k / M * (s.card * δ) := by
      rw [abs_mul, abs_of_nonneg hw]
      exact add_le_add (hδ k hk) (mul_le_mul_of_nonneg_left hmass hw)

/-- [proved-derived; formal-checked] **Campaign 1's founding**: period `d = 5`, chart `L_ν = 18`
and the source port's lattice `2^(−18)` (both `⌈log₂(32 n*)⌉` at a declared population
`4096 < n* ≤ 8192`, as in the leaky-count tests' `campaign_one(6148)`) found ring 0 at `k = 21618`,
`ρ₀ = 21618/2^18 = 10809/2^17`; there `m = 1` (`2 (1 − ρ₀) ≥ 1`). -/
theorem campaign_one_founding :
    IsFounding 18 5 18 21618 ∧ (21618 / 2 ^ 18 : ℚ) = 10809 / 2 ^ 17 ∧
      (1 : ℚ) ≤ 2 ^ 1 * (1 - 10809 / 2 ^ 17) := by
  unfold IsFounding
  refine ⟨⟨by norm_num, by norm_num⟩, by norm_num, by norm_num⟩

/-- [proved-derived; formal-checked] **The read is not within one chart unit in general**: at
campaign 1's founding (`ρ₀ = 10809/2^17`, lattice `2^(−19)`, chart `2^(−18)`), on a passage the
ingest takes. Ring 0 ticks only at the codes its lock selects (`x ≡ 0 mod 5` on the residue port
chart), and each tick's datum enters at the new phase, so code 5 and then the 204 codes the lock
does not select enter 205 slots of one phase; codes 0 and 10 then tick the ring twice, each entering
a new slot. Each of the 205 slots carries `3566` against its exact `ρ₀² 2^19 = 116834481/2^15`, a
rounding of the same sign in every slot, so the mass is off by `205 · 16207/2^15 = 101 +
12867/2^15` lattice units; the middle datum carries `43236 = ρ₀ 2^19` exactly. The newest datum's
read `2^19/(2^19 + 43236 + 205·3566)` is more than eight chart units from its transported weight
`1/(1 + ρ₀ + 205 ρ₀²)`, and so is the chart's read of it, `nearest` at `2^18`, `105840/2^18`
(`holonics::hnn::tests::moment::the_leaky_read_is_not_within_one_chart_unit_in_general` reads this
value on the Rust ingest). -/
theorem leaky_read_exceeds_chart_unit :
    carried (10809 / 2 ^ 17) 0 [.unit (2 ^ 19), .tick] = 43236 ∧
    exactCount (10809 / 2 ^ 17) 0 [.unit (2 ^ 19), .tick] = 43236 ∧
    carried (10809 / 2 ^ 17) 0 [.unit (2 ^ 19), .tick, .tick] = 3566 ∧
    exactCount (10809 / 2 ^ 17) 0 [.unit (2 ^ 19), .tick, .tick] = 116834481 / 2 ^ 15 ∧
    8 * (1 / 2 : ℚ) ^ 18 <
      1 / (1 + 10809 / 2 ^ 17 + 205 * (10809 / 2 ^ 17) ^ 2)
        - 2 ^ 19 / (2 ^ 19 + 43236 + 205 * 3566) ∧
    nearest (2 ^ 18 * (2 ^ 19 / (2 ^ 19 + 43236 + 205 * 3566))) = 105840 ∧
    8 * (1 / 2 : ℚ) ^ 18 <
      1 / (1 + 10809 / 2 ^ 17 + 205 * (10809 / 2 ^ 17) ^ 2)
        - (nearest (2 ^ 18 * (2 ^ 19 / (2 ^ 19 + 43236 + 205 * 3566))) : ℚ) / 2 ^ 18 := by
  have h1 : nearest (10809 / 2 ^ 17 * ((0 + 2 ^ 19 : ℤ) : ℚ)) = 43236 := by
    unfold nearest
    rw [Int.floor_eq_iff]
    norm_num
  have h2 : nearest (10809 / 2 ^ 17 * ((43236 : ℤ) : ℚ)) = 3566 := by
    unfold nearest
    rw [Int.floor_eq_iff]
    norm_num
  have hn : nearest (2 ^ 18 * (2 ^ 19 / (2 ^ 19 + 43236 + 205 * 3566))) = 105840 := by
    unfold nearest
    rw [Int.floor_eq_iff]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, by norm_num, hn, ?_⟩
  · simp only [carried]
    rw [h1]
  · simp only [exactCount]
    norm_num
  · simp only [carried]
    rw [h1, h2]
  · simp only [exactCount]
    norm_num
  · rw [hn]
    norm_num

end Leaky

section Audit

#print axioms normalized_of_pos
#print axioms normalized_zero_population
#print axioms population_eq_zero_iff
#print axioms normalized_phase_counts_mass
#print axioms normalized_div_rem
#print axioms conditional_of_pos
#print axioms conditional_mass
#print axioms conditional_eq_normalized_column
#print axioms conditional_zero_population
#print axioms pairTerm_none
#print axioms indexed_read_zero_population
#print axioms indexed_pair_read_eq_column_contraction
#print axioms indexed_pair_adjoint_pairing
#print axioms unnormalized_read_scales
#print axioms normalized_mul
#print axioms normalized_open_population_invariant
#print axioms indexed_open_tape_free
#print axioms normalized_marginal_eq_scaled_read
#print axioms marginalRead_counts
#print axioms pairRead_offsetCounts
#print axioms passage_population
#print axioms passage_weight_one_population
#print axioms passage_read
#print axioms separate_populations_ratio
#print axioms transported_weight_mass
#print axioms transported_weight_frame_invariant
#print axioms transported_weight_unitary
#print axioms transported_weight_insert
#print axioms transported_weight_insert_scale
#print axioms passage_weight_split_invariant
#print axioms decayed_weight_antitone
#print axioms decayed_weight_frame_free
#print axioms decayed_weight_lossless
#print axioms lossless_term_modulus
#print axioms dissipative_term_modulus
#print axioms framed_weight_mass
#print axioms framed_weight_pos
#print axioms framed_weight_one_sided
#print axioms framed_weight_ratio
#print axioms framed_weight_le_pow
#print axioms oneway_later_weight_ratio
#print axioms framed_weight_symmetric
#print axioms framed_weight_translation
#print axioms framed_weight_lossless
#print axioms founded_modulus_alias
#print axioms founded_modulus_alias_le
#print axioms lossless_alias
#print axioms founded_modulus_pow_le
#print axioms founded_modulus_greatest
#print axioms founded_modulus_lt_one
#print axioms founded_modulus_pos
#print axioms order_founding
#print axioms nearest_sub_le
#print axioms leaky_tick_eq_nearest
#print axioms leaky_count_error_le
#print axioms leaky_count_ingest
#print axioms leaky_lattice_le_half_chart
#print axioms leaky_read_error
#print axioms campaign_one_founding
#print axioms leaky_read_exceeds_chart_unit

end Audit

end Holonics.HNN.IndexedOpen
