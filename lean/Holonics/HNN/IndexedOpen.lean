import Holonics.HNN.Moment

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

end Audit

end Holonics.HNN.IndexedOpen
