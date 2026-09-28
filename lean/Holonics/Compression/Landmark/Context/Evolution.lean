import Holonics.Compression.Landmark.Context.Population

/-!
# The evolved prior across aeons, and species collapse relative to the admitted future

[definition; agent-inferred] The population's two remaining laws (Rust
`receiver::population::{evolution, species}`; `docs/ELEMENTARY_OBJECTS.md`, "Keys, locks and
navigation": "across aeons the population's prior over families learns from its own deaths and
selections … a retention of selection counts over families, never a tape of attempts"; and "The
egg": a species is the class of eggs every admitted future receiver reads alike).

**The evolved prior.** Across aeons a receiver retains, for each family's declared identity, three
counts read from the aeons' receipts: the aeons it was declared in (`a`), selected in (`s`) and
died in (`d ≤ a`). Nothing else is retained. At an aeon's opening the declared families are
weighed by

```text
σ_f = (2(a_f − d_f) + 1)/(2(2a_f + 1))                   the survival pseudo-count, in (0, ½]
D(f) = (s_f + σ_f)/Σ_g (s_g + σ_g)                       the Dirichlet face of the selections
π(f) = λ D(f) + (1 − λ) 2^(−ℓ_f)/M,   M = Σ_g 2^(−ℓ_g)    the evolved prior, λ ∈ [0, 1] declared
m_f = M π(f)                                             the declared masses: Σ_f m_f = M
```

A family never declared, or one that never died, has `σ = ½`, so with no deaths `D` is the
Krichevsky–Trofimov (Dirichlet-½) face of the selection counts (`kt_face`, `survivalPseudo_zero_
deaths`). Each death lowers the pseudo-count (`survivalPseudo_death_lt`): a family that keeps
winning is founded sooner, one that keeps dying later. [agent-inferred] Survival without selection
is no evidence for a family (every receiving tree survives every aeon), so it leaves `σ` at `½`;
only deaths thin it.

* `dirichletFace_isPrior`, `descriptionPrior_isPrior`, `evolved_isPrior`, `masses_total`
  [proved-derived; formal-checked]: the normalization. The masses keep the declared total `M`, so
  the reserve `1 − M` from which births draw is unchanged.
* `evolved_code_le_face`, `evolved_code_le_description` [proved-derived; formal-checked]: the
  mixture costs at most `−log₂ λ` over the Dirichlet face and at most `−log₂(1 − λ)` over the
  description prior (at `λ = ½`, one bit over the better of the two).
* `evolved_aeon_code` [proved-derived; formal-checked]: **the aeon's code is at most the selected
  family's code plus `−log₂` of its evolved prior**, `−log₂ ∏ q ≤ −log₂ π(f) − log₂ L_f`, for every
  living family (`Population.population_mixture` under the evolved prior).

**Species collapse.** Keys `k` with weights `w_k` and faces `f_k(t)`, and a species map
`σ : κ → S` with a representative `rep s`, such that every key's face agrees with its species'
representative's at every tick of the admitted future `t < h` (the conditioned faces agree for every
admitted receiver). The collapsed mixture carries one member a species at the summed weight
`W_s = Σ_(σ k = s) w_k`:

* `species_mixture`, `species_face`, `species_collapse_code` [proved-derived; formal-checked]: over
  the admitted future the collapsed mixture's forward weights, its face at every tick and its product
  are the uncollapsed ones: **the collapse changes no code for the admitted future**.
* `species_split` [proved-derived; formal-checked]: within the admitted future each member's weight
  is its species' weight times its prior share within the species, `w_k L_k = (w_k/W_(σ k)) ·
  W_(σ k) L_(rep(σ k))`, so a species kept with every member's seed splits exactly when the
  admitted future grows.

The computational object is the helical pair interaction read as a receiver's population of eggs
across aeons. Of the winding guide's six general objects this module touches the **tube** (the
aeons, each a span whose receipt adds one count), **faces and placement** (the population's face,
unchanged by a collapse) and, through the families' keys, the **helix** (a key's clock winding
through the admitted future); the pair, the cell holonomy and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Evolution

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing
open Holonics.Compression.Landmark.Context.Population

section Pseudo

/-- [definition] **The survival pseudo-count** of a family declared in `a` aeons that died in `d`
of them: `σ(a, d) = (2(a − d) + 1)/(2(2a + 1))`. -/
def survivalPseudo (a d : ℕ) : ℚ := (2 * ((a : ℚ) - d) + 1) / (2 * (2 * a + 1))

theorem survivalPseudo_pos {a d : ℕ} (h : d ≤ a) : 0 < survivalPseudo a d := by
  have hd : (d : ℚ) ≤ a := by exact_mod_cast h
  unfold survivalPseudo
  exact div_pos (by linarith) (by positivity)

theorem survivalPseudo_le_half (a d : ℕ) : survivalPseudo a d ≤ 1 / 2 := by
  have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  unfold survivalPseudo
  rw [div_le_iff₀ (by positivity)]
  linarith

/-- With no deaths the pseudo-count is the Krichevsky–Trofimov `½`. -/
theorem survivalPseudo_zero_deaths (a : ℕ) : survivalPseudo a 0 = 1 / 2 := by
  unfold survivalPseudo
  rw [div_eq_iff (by positivity)]
  push_cast
  ring

/-- Each death lowers the pseudo-count: a family that keeps dying is founded later. -/
theorem survivalPseudo_death_lt (a d : ℕ) : survivalPseudo a (d + 1) < survivalPseudo a d := by
  unfold survivalPseudo
  have hden : (0 : ℚ) < 2 * (2 * a + 1) := by positivity
  rw [div_lt_div_iff_of_pos_right hden]
  push_cast
  linarith

end Pseudo

section Prior

variable {ι : Type*} [Fintype ι]

/-- [definition] **The Dirichlet face of the selection counts** `s` with pseudo-counts `σ`:
`D(f) = (s_f + σ_f)/Σ_g (s_g + σ_g)`. -/
def dirichletFace (s : ι → ℕ) (σ : ι → ℚ) : ι → ℚ :=
  fun f => ((s f : ℚ) + σ f) / ∑ g, ((s g : ℚ) + σ g)

theorem dirichlet_total_pos [Nonempty ι] (s : ι → ℕ) {σ : ι → ℚ} (hσ : ∀ f, 0 < σ f) :
    0 < ∑ g, ((s g : ℚ) + σ g) :=
  sum_pos (fun g _ => add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (hσ g)) univ_nonempty

theorem dirichletFace_pos [Nonempty ι] (s : ι → ℕ) {σ : ι → ℚ} (hσ : ∀ f, 0 < σ f) (f : ι) :
    0 < dirichletFace s σ f :=
  div_pos (add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) (hσ f)) (dirichlet_total_pos s hσ)

/-- [proved-derived; formal-checked] **The Dirichlet face is a prior** over the declared families
whenever every pseudo-count is positive. -/
theorem dirichletFace_isPrior [Nonempty ι] (s : ι → ℕ) {σ : ι → ℚ} (hσ : ∀ f, 0 < σ f) :
    IsPrior (dirichletFace s σ) := by
  refine ⟨fun f => (dirichletFace_pos s hσ f).le, ?_⟩
  unfold dirichletFace
  rw [← sum_div, div_self (dirichlet_total_pos s hσ).ne']

/-- [proved-derived; formal-checked] **At pseudo-count `½` the Dirichlet face is the KT face**
`(s_f + ½)/(Σ_g s_g + |F|/2)`. -/
theorem kt_face (s : ι → ℕ) (f : ι) :
    dirichletFace s (fun _ => (1 : ℚ) / 2) f =
      ((s f : ℚ) + 1 / 2) / ((∑ g, (s g : ℚ)) + Fintype.card ι / 2) := by
  unfold dirichletFace
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- With no deaths the evolved Dirichlet face is the KT face. -/
theorem dirichletFace_no_deaths (s : ι → ℕ) (a : ι → ℕ) :
    dirichletFace s (fun f => survivalPseudo (a f) 0) = dirichletFace s (fun _ => (1 : ℚ) / 2) := by
  funext f
  simp only [survivalPseudo_zero_deaths]

/-- [definition] **The description prior** `2^(−ℓ_f)/M`, `M = Σ_g 2^(−ℓ_g)`. -/
def descriptionPrior (ℓ : ι → ℕ) : ι → ℚ :=
  fun f => (1 / 2 : ℚ) ^ ℓ f / ∑ g, (1 / 2 : ℚ) ^ ℓ g

theorem descriptionPrior_isPrior [Nonempty ι] (ℓ : ι → ℕ) : IsPrior (descriptionPrior ℓ) := by
  have hM : 0 < ∑ g, (1 / 2 : ℚ) ^ ℓ g := sum_pos (fun g _ => by positivity) univ_nonempty
  refine ⟨fun f => div_nonneg (by positivity) hM.le, ?_⟩
  unfold descriptionPrior
  rw [← sum_div, div_self hM.ne']

/-- [definition] **The evolved prior** `π(f) = λ D(f) + (1 − λ) P(f)` at the declared weight `λ`. -/
def evolved (w : ℚ) (D P : ι → ℚ) : ι → ℚ := fun f => w * D f + (1 - w) * P f

/-- [proved-derived; formal-checked] **The evolved prior is a prior**. -/
theorem evolved_isPrior {w : ℚ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {D P : ι → ℚ} (hD : IsPrior D)
    (hP : IsPrior P) : IsPrior (evolved w D P) := by
  refine ⟨fun f => add_nonneg (mul_nonneg hw0 (hD.1 f)) (mul_nonneg (by linarith) (hP.1 f)), ?_⟩
  simp only [evolved, sum_add_distrib, ← mul_sum, hD.2, hP.2]
  ring

/-- [proved-derived; formal-checked] **The declared masses keep the declared total**:
`Σ_f M π(f) = M`, so the reserve `1 − M` is unchanged. -/
theorem masses_total (M : ℚ) {π : ι → ℚ} (hπ : IsPrior π) : ∑ f, M * π f = M := by
  rw [← mul_sum, hπ.2, mul_one]

/-- [proved-derived; formal-checked] **The mixture costs at most `−log₂ λ` over the Dirichlet
face.** -/
theorem evolved_code_le_face {w : ℚ} (hw0 : 0 < w) (hw1 : w ≤ 1) {D P : ι → ℚ}
    (hP : ∀ f, 0 ≤ P f) {f : ι} (hDf : 0 < D f) :
    -Real.logb 2 (evolved w D P f : ℝ) ≤ -Real.logb 2 (w : ℝ) - Real.logb 2 (D f : ℝ) := by
  have hle : w * D f ≤ evolved w D P f := by
    have := mul_nonneg (sub_nonneg.2 hw1) (hP f)
    unfold evolved
    linarith
  have hpos : (0 : ℝ) < ((w * D f : ℚ) : ℝ) := by exact_mod_cast mul_pos hw0 hDf
  have hb := neg_logb_le_of_le (b := ((evolved w D P f : ℚ) : ℝ)) hpos (by exact_mod_cast hle)
  push_cast at hb
  rw [Real.logb_mul (by exact_mod_cast hw0.ne') (by exact_mod_cast hDf.ne')] at hb
  linarith

/-- [proved-derived; formal-checked] **The mixture costs at most `−log₂(1 − λ)` over the
description prior.** -/
theorem evolved_code_le_description {w : ℚ} (hw0 : 0 ≤ w) (hw1 : w < 1) {D P : ι → ℚ}
    (hD : ∀ f, 0 ≤ D f) {f : ι} (hPf : 0 < P f) :
    -Real.logb 2 (evolved w D P f : ℝ) ≤ -Real.logb 2 ((1 - w : ℚ) : ℝ) - Real.logb 2 (P f : ℝ) := by
  have hle : (1 - w) * P f ≤ evolved w D P f := by
    have := mul_nonneg hw0 (hD f)
    unfold evolved
    linarith
  have hw : (0 : ℚ) < 1 - w := by linarith
  have hpos : (0 : ℝ) < (((1 - w) * P f : ℚ) : ℝ) := by exact_mod_cast mul_pos hw hPf
  have hb := neg_logb_le_of_le (b := ((evolved w D P f : ℚ) : ℝ)) hpos (by exact_mod_cast hle)
  rw [Rat.cast_mul, Real.logb_mul (by exact_mod_cast hw.ne') (by exact_mod_cast hPf.ne')] at hb
  linarith

/-- [proved-derived; formal-checked] **`evolved_aeon_code`: the aeon's code is at most the selected
family's code plus `−log₂` of its evolved prior.** Under the evolved prior every forward total of the
aeon's passage is positive while a family with positive prior keeps a positive likelihood, and the
population codes within `−log₂ π(x)` of that family's own code (`Population.population_mixture`). -/
theorem evolved_aeon_code [DecidableEq ι] {w : ℚ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) {D P : ι → ℚ}
    (hD : IsPrior D) (hP : IsPrior P) {f : ι → ℕ → ℚ} (hf : ∀ x t, 0 ≤ f x t) (n : ℕ) {x : ι}
    (hx : 0 < evolved w D P x) (hL : 0 < seqLik (f x) n) :
    -Real.logb 2 ((∏ t ∈ range n, fwdMix (evolved w D P) f idKernel t : ℚ) : ℝ) ≤
      -Real.logb 2 (evolved w D P x : ℝ) - Real.logb 2 (seqLik (f x) n : ℝ) := by
  have hπ := evolved_isPrior hw0 hw1 hD hP
  have hlive : 0 < ∑ y, evolved w D P y * seqLik (f y) n :=
    lt_of_lt_of_le (mul_pos hx hL)
      (single_le_sum (f := fun y => evolved w D P y * seqLik (f y) n)
        (fun y _ => mul_nonneg (hπ.1 y) (seqLik_nonneg (hf y) n)) (mem_univ x))
  exact (population_mixture hπ hf n hlive).2.2.2 x hx hL

end Prior

section Species

variable {κ S : Type*} [Fintype κ] [Fintype S] [DecidableEq κ] [DecidableEq S]

/-- [definition] **A species' weight** `W_s = Σ_(σ k = s) w_k`: its members' summed posterior. -/
def speciesWeight (σ : κ → S) (w : κ → ℚ) (s : S) : ℚ :=
  ∑ k ∈ univ.filter (fun k => σ k = s), w k

theorem speciesWeight_total (σ : κ → S) (w : κ → ℚ) : ∑ s, speciesWeight σ w s = ∑ k, w k :=
  sum_fiberwise univ σ w

theorem speciesWeight_isPrior (σ : κ → S) {w : κ → ℚ} (hw : IsPrior w) :
    IsPrior (speciesWeight σ w) :=
  ⟨fun _ => sum_nonneg fun k _ => hw.1 k, by rw [speciesWeight_total, hw.2]⟩

/-- Over the admitted future a member's likelihood is its representative's. -/
theorem species_likelihood (σ : κ → S) (rep : S → κ) {f : κ → ℕ → ℚ} {h : ℕ}
    (hagree : ∀ k, ∀ t < h, f k t = f (rep (σ k)) t) {n : ℕ} (hn : n ≤ h) (k : κ) :
    seqLik (f k) n = seqLik (f (rep (σ k))) n :=
  prod_congr rfl fun t ht => hagree k t (lt_of_lt_of_le (mem_range.1 ht) hn)

/-- [proved-derived; formal-checked] **The collapsed mixture's weights**: over the admitted future
`Σ_k w_k L_k(n) = Σ_s W_s L_(rep s)(n)`. -/
theorem species_mixture (σ : κ → S) (rep : S → κ) (w : κ → ℚ) {f : κ → ℕ → ℚ} {h : ℕ}
    (hagree : ∀ k, ∀ t < h, f k t = f (rep (σ k)) t) {n : ℕ} (hn : n ≤ h) :
    ∑ k, w k * seqLik (f k) n = ∑ s, speciesWeight σ w s * seqLik (f (rep s)) n := by
  rw [← sum_fiberwise univ σ (fun k => w k * seqLik (f k) n)]
  refine sum_congr rfl fun s _ => ?_
  unfold speciesWeight
  rw [sum_mul]
  refine sum_congr rfl fun k hk => ?_
  rw [species_likelihood σ rep hagree hn k, (mem_filter.1 hk).2]

/-- [proved-derived; formal-checked] **The collapsed face is the population's face** at every tick
of the admitted future. -/
theorem species_face (σ : κ → S) (rep : S → κ) (w : κ → ℚ) {f : κ → ℕ → ℚ} {h : ℕ}
    (hagree : ∀ k, ∀ t < h, f k t = f (rep (σ k)) t) {t : ℕ} (ht : t < h) :
    fwdMix w f idKernel t = fwdMix (speciesWeight σ w) (fun s => f (rep s)) idKernel t := by
  unfold fwdMix
  simp only [fwd_id]
  have hnum : ∑ k, w k * seqLik (f k) t * f k t =
      ∑ s, speciesWeight σ w s * seqLik (f (rep s)) t * f (rep s) t := by
    have := species_mixture σ rep w hagree (n := t + 1) ht
    simpa only [seqLik_succ, mul_assoc] using this
  rw [hnum, species_mixture σ rep w hagree ht.le]

/-- [proved-derived; formal-checked] **`species_collapse_code`: the collapse changes no code for
the admitted future.** The collapsed mixture's product over any passage within the admitted future is
the population's. -/
theorem species_collapse_code (σ : κ → S) (rep : S → κ) (w : κ → ℚ) {f : κ → ℕ → ℚ} {h : ℕ}
    (hagree : ∀ k, ∀ t < h, f k t = f (rep (σ k)) t) {n : ℕ} (hn : n ≤ h) :
    ∏ t ∈ range n, fwdMix w f idKernel t =
      ∏ t ∈ range n, fwdMix (speciesWeight σ w) (fun s => f (rep s)) idKernel t :=
  prod_congr rfl fun t ht => species_face σ rep w hagree (lt_of_lt_of_le (mem_range.1 ht) hn)

/-- [proved-derived; formal-checked] **`species_split`: a species splits exactly.** Within the
admitted future each member's weight is its species' weight times its prior share within the
species. -/
theorem species_split (σ : κ → S) (rep : S → κ) (w : κ → ℚ) {f : κ → ℕ → ℚ} {h : ℕ}
    (hagree : ∀ k, ∀ t < h, f k t = f (rep (σ k)) t) {n : ℕ} (hn : n ≤ h) (k : κ)
    (hW : speciesWeight σ w (σ k) ≠ 0) :
    w k * seqLik (f k) n =
      w k / speciesWeight σ w (σ k) * (speciesWeight σ w (σ k) * seqLik (f (rep (σ k))) n) := by
  rw [species_likelihood σ rep hagree hn k]
  field_simp

end Species

section Audit

#print axioms survivalPseudo_pos
#print axioms survivalPseudo_le_half
#print axioms survivalPseudo_zero_deaths
#print axioms survivalPseudo_death_lt
#print axioms dirichletFace_isPrior
#print axioms kt_face
#print axioms dirichletFace_no_deaths
#print axioms descriptionPrior_isPrior
#print axioms evolved_isPrior
#print axioms masses_total
#print axioms evolved_code_le_face
#print axioms evolved_code_le_description
#print axioms evolved_aeon_code
#print axioms speciesWeight_isPrior
#print axioms species_mixture
#print axioms species_face
#print axioms species_collapse_code
#print axioms species_split

end Audit

end Holonics.Compression.Landmark.Context.Evolution
