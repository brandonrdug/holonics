import Holonics.Compression.Landmark.Context.Population

/-!
# Composition at ports: a keystone's keys weigh the family that reads its port

[definition; agent-inferred] Eggs compose at ports, a Holarchy of eggs (`docs/ELEMENTARY_OBJECTS.md`,
"The egg: a generator read as a whole", keystones; Rust `receiver::population::composition`). A
**keystone** `A` is a declared finite key space `κ` of navigators, each exposing its state at a port
(the arithmetic terrain's record clock exposes the record's phase and the records completed). A
**conditioned family** `B` reads that port: under key `a` its face of class `c` at tick `t` is
`P_a(t, c)`, its own face given the port path key `a` drives. The composed family `A ⊳ B` is the
mixture over the keystone's keys weighed by what `B` read under each:

```text
F_t(a) = π_a ∏_(s<t) P_a(s, x_s),     q_t(c) = Σ_a F_t(a) P_a(t, c) / Σ_a F_t(a)
```

so `P_(A⊳B)(x_t | past) = Σ_a P_A(a | past) P_B(x_t | past, a)`: the keystone's posterior times the
conditioned face. On the received cell it is the population's forward mixture
(`LocalWeighing.fwdMix` under the identity kernel), so a keystone key whose conditioned face gives a
received cell zero dies (`Population.population_mixture`): **a deterministic keystone is survivor
filtered by the family that reads it.**

* `composedFace_received` [proved-derived; formal-checked]: on the received cell the composed face
  is the forward mixture's face.
* `composedFace_nonneg`, `composedFace_sum_one`, `composedFace_pos` [proved-derived;
  formal-checked]: the composed face is a face wherever the constituents' are: nonnegative, summing
  to one over the classes once some key keeps positive weight, and positive on a class that some
  key of positive weight gives positive face.
* `composed_telescope` [proved-derived; formal-checked]: the composed faces of the received cells
  multiply to `Σ_a π_a L_a(n)`, `L_a(n) = ∏_(t<n) P_a(t, x_t)`, the conditioned family's likelihood
  under each key.
* `chain_rule` [proved-derived; formal-checked]: **the chain rule along the surviving keys.** Under
  the uniform prior over the keystone's keys, with `S_n = {a : L_a(n) > 0}` its survivors,
  `code(A⊳B) = (log₂ |κ| − log₂ #S_n) + code(B | A)`, `code(B | A) = −log₂ (Σ_(a∈S_n) L_a(n)/#S_n)`:
  the keystone's code is its key description less its surviving fibre (`Population.survivor_code`'s
  form), and the conditioned family pays the mean of its likelihoods over the surviving keys.
* `chain_rule_of_species` [proved-derived; formal-checked]: when every surviving key gives the
  conditioned family one likelihood `ℓ` (one survivor, or a species every admitted receiver reads
  alike), `code(A⊳B) = (log₂ |κ| − log₂ #S_n) − log₂ ℓ`: the keystone's key plus the conditioned
  family's code under the located key.

**The staged face** (the boundary egg, Rust `receiver::population::boundary`): a keystone of one
key whose port is read from the coded past (the part clock) locates nothing, and the family reading
it factors each tick's face through a stage map `σ : C → S` of the classes (a byte or a section
letter): `q_t(c) = h_t(σ c) · r_t(c)`, the stage's face (the hazard) times the conditioned face within
the stage (the byte tree's face within the bytes, the letter tree's within the letters).

* `stagedFace_nonneg`, `stagedFace_sum_one` [proved-derived; formal-checked]: the staged face is a
  face when the stage face is one and the conditioned face is one on every stage's fibre.
* `staged_chain_rule`, `staged_code` [proved-derived; formal-checked]: **the chain rule at every
  tick**: the staged faces of the received cells multiply to the stage faces' product times the
  conditioned faces' product, so the staged code is the stage's code plus the conditioned code,
  `−log₂ ∏ q_t(x_t) = −log₂ ∏ h_t(σ x_t) − log₂ ∏ r_t(x_t)`.

The computational object is the helical pair interaction read as eggs joined at ports. Of the
winding guide's six general objects this module touches **faces and placement** (the composed face
and its normalization, the staged face) and, through the keystone's port, the **helix** (the clock's
phase and its winding); the pair, the cell holonomy, the tube and the tower thread stay attached
through the constituents' owners.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.Context.Composition

open Finset
open Holonics.Compression.Landmark.Context.Tree
open Holonics.Compression.Landmark.Context.LocalWeighing
open Holonics.Compression.Landmark.Context.Population

variable {κ C : Type*} [Fintype κ] [DecidableEq κ]

/-- [definition] **The conditioned family's face of the received cell**, key by key:
`f_a(t) = P_a(t, x_t)`. -/
def received (P : κ → ℕ → C → ℚ) (x : ℕ → C) : κ → ℕ → ℚ := fun a t => P a t (x t)

/-- [definition] **The composed face** `q_t(c) = Σ_a F_t(a) P_a(t, c) / Σ_a F_t(a)`: the keystone's
keys weighed by the prior times the conditioned family's likelihood under each, then each key's
conditioned face. -/
def composedFace (π : κ → ℚ) (P : κ → ℕ → C → ℚ) (x : ℕ → C) (t : ℕ) (c : C) : ℚ :=
  (∑ a, fwd π (received P x) idKernel t a * P a t c) / ∑ a, fwd π (received P x) idKernel t a

/-- [proved-derived; formal-checked] **On the received cell the composed face is the forward
mixture's face.** -/
theorem composedFace_received (π : κ → ℚ) (P : κ → ℕ → C → ℚ) (x : ℕ → C) (t : ℕ) :
    composedFace π P x t (x t) = fwdMix π (received P x) idKernel t := rfl

/-- The keystone's forward weight is the prior times the conditioned likelihood. -/
theorem composed_weight (π : κ → ℚ) (P : κ → ℕ → C → ℚ) (x : ℕ → C) (t : ℕ) (a : κ) :
    fwd π (received P x) idKernel t a = π a * seqLik (received P x a) t :=
  fwd_id π (received P x) t a

theorem composed_weight_nonneg {π : κ → ℚ} {P : κ → ℕ → C → ℚ} (hπ : ∀ a, 0 ≤ π a)
    (hP : ∀ a t c, 0 ≤ P a t c) (x : ℕ → C) (t : ℕ) (a : κ) :
    0 ≤ fwd π (received P x) idKernel t a :=
  fwd_nonneg hπ (fun a s => hP a s (x s)) idKernel_stochastic.1 t a

/-- [proved-derived; formal-checked] **The composed face is nonnegative** where the prior and the
conditioned faces are. -/
theorem composedFace_nonneg {π : κ → ℚ} {P : κ → ℕ → C → ℚ} (hπ : ∀ a, 0 ≤ π a)
    (hP : ∀ a t c, 0 ≤ P a t c) (x : ℕ → C) (t : ℕ) (c : C) :
    0 ≤ composedFace π P x t c :=
  div_nonneg (sum_nonneg fun a _ => mul_nonneg (composed_weight_nonneg hπ hP x t a) (hP a t c))
    (sum_nonneg fun a _ => composed_weight_nonneg hπ hP x t a)

/-- [proved-derived; formal-checked] **The composed face sums to one** over the classes when every
conditioned face does and some key keeps positive weight. -/
theorem composedFace_sum_one [Fintype C] {π : κ → ℚ} {P : κ → ℕ → C → ℚ} (x : ℕ → C) (t : ℕ)
    (hnorm : ∀ a, ∑ c, P a t c = 1) (hpos : 0 < ∑ a, fwd π (received P x) idKernel t a) :
    ∑ c, composedFace π P x t c = 1 := by
  unfold composedFace
  rw [← sum_div, sum_comm]
  have : ∑ a, ∑ c, fwd π (received P x) idKernel t a * P a t c =
      ∑ a, fwd π (received P x) idKernel t a := by
    refine sum_congr rfl fun a _ => ?_
    rw [← mul_sum, hnorm a, mul_one]
  rw [this, div_self hpos.ne']

/-- [proved-derived; formal-checked] **The composed face is positive** on a class that some key of
positive weight gives positive conditioned face. -/
theorem composedFace_pos {π : κ → ℚ} {P : κ → ℕ → C → ℚ} (hπ : ∀ a, 0 ≤ π a)
    (hP : ∀ a t c, 0 ≤ P a t c) (x : ℕ → C) (t : ℕ) (c : C) (a : κ)
    (ha : 0 < fwd π (received P x) idKernel t a) (hc : 0 < P a t c) :
    0 < composedFace π P x t c := by
  have hnn := composed_weight_nonneg hπ hP x t
  have hnum : 0 < ∑ b, fwd π (received P x) idKernel t b * P b t c :=
    lt_of_lt_of_le (mul_pos ha hc)
      (single_le_sum (f := fun b => fwd π (received P x) idKernel t b * P b t c)
        (fun b _ => mul_nonneg (hnn b) (hP b t c)) (mem_univ a))
  have hden : 0 < ∑ b, fwd π (received P x) idKernel t b :=
    lt_of_lt_of_le ha
      (single_le_sum (f := fun b => fwd π (received P x) idKernel t b) (fun b _ => hnn b)
        (mem_univ a))
  exact div_pos hnum hden

/-- [proved-derived; formal-checked] **The composed faces telescope** to the keystone's prior mixture
of the conditioned family's likelihoods, while some key keeps a positive likelihood. -/
theorem composed_telescope {π : κ → ℚ} {P : κ → ℕ → C → ℚ} (hπ : IsPrior π)
    (hP : ∀ a t c, 0 ≤ P a t c) (x : ℕ → C) (n : ℕ)
    (hlive : 0 < ∑ a, π a * seqLik (received P x a) n) :
    ∏ t ∈ range n, composedFace π P x t (x t) = ∑ a, π a * seqLik (received P x a) n := by
  obtain ⟨-, hprod, -, -⟩ := population_mixture hπ (fun a s => hP a s (x s)) n hlive
  exact hprod

/-- [definition] **The keystone's survivors** at `n`: the keys under which the conditioned family
still gives the received cells a positive likelihood. -/
def keySurvivors (P : κ → ℕ → C → ℚ) (x : ℕ → C) (n : ℕ) : Finset κ :=
  univ.filter fun a => 0 < seqLik (received P x a) n

omit [DecidableEq κ] in
/-- A key outside the survivors has likelihood zero (the conditioned faces being nonnegative). -/
theorem seqLik_eq_zero_of_not_mem {P : κ → ℕ → C → ℚ} (hP : ∀ a t c, 0 ≤ P a t c) (x : ℕ → C)
    (n : ℕ) {a : κ} (ha : a ∉ keySurvivors P x n) : seqLik (received P x a) n = 0 := by
  simp only [keySurvivors, mem_filter, mem_univ, true_and, not_lt] at ha
  exact le_antisymm ha (seqLik_nonneg (fun s => hP a s (x s)) n)

omit [DecidableEq κ] in
/-- The likelihoods summed over every key are summed over the survivors. -/
theorem sum_seqLik_survivors {P : κ → ℕ → C → ℚ} (hP : ∀ a t c, 0 ≤ P a t c) (x : ℕ → C)
    (n : ℕ) :
    ∑ a, seqLik (received P x a) n = ∑ a ∈ keySurvivors P x n, seqLik (received P x a) n := by
  refine (sum_subset (subset_univ _) fun a _ ha => ?_).symm
  exact seqLik_eq_zero_of_not_mem hP x n ha

/-- [proved-derived; formal-checked] **`chain_rule`: the chain rule along the surviving keys.** Under
the uniform prior over the keystone's keys and nonnegative conditioned faces, while some key
survives, the composed code is the keystone's code (its key description less its surviving fibre)
plus the conditioned family's code at the mean of its likelihoods over the surviving keys:
`−log₂ ∏_(t<n) q_t(x_t) = (log₂ |κ| − log₂ #S_n) + (−log₂ (Σ_(a∈S_n) L_a(n) / #S_n))`. -/
theorem chain_rule [Nonempty κ] {P : κ → ℕ → C → ℚ} (hP : ∀ a t c, 0 ≤ P a t c) (x : ℕ → C)
    (n : ℕ) (hS : (keySurvivors P x n).Nonempty) :
    -Real.logb 2 ((∏ t ∈ range n, composedFace uniformPrior P x t (x t) : ℚ) : ℝ) =
      (Real.logb 2 (Fintype.card κ) - Real.logb 2 (keySurvivors P x n).card) +
        -Real.logb 2 (((∑ a ∈ keySurvivors P x n, seqLik (received P x a) n) /
          (keySurvivors P x n).card : ℚ) : ℝ) := by
  set S := keySurvivors P x n with hSdef
  set Z : ℚ := ∑ a ∈ S, seqLik (received P x a) n with hZ
  have hK : (0 : ℚ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hZpos : 0 < Z := by
    obtain ⟨a, ha⟩ := hS
    refine lt_of_lt_of_le ?_ (single_le_sum (f := fun b => seqLik (received P x b) n)
      (fun b _ => seqLik_nonneg (fun s => hP b s (x s)) n) ha)
    simpa [hSdef, keySurvivors] using ha
  have hmix : ∑ a, uniformPrior a * seqLik (received P x a) n = Z / Fintype.card κ := by
    simp only [uniformPrior, one_div]
    rw [← mul_sum, sum_seqLik_survivors hP x n, ← hSdef, ← hZ]
    field_simp
  have hlive : 0 < ∑ a, uniformPrior a * seqLik (received P x a) n := by
    rw [hmix]; exact div_pos hZpos hK
  rw [composed_telescope uniformPrior_isPrior hP x n hlive, hmix]
  have hcard : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hKr : (0 : ℝ) < Fintype.card κ := by exact_mod_cast hK
  have hZr : (0 : ℝ) < (Z : ℝ) := by exact_mod_cast hZpos
  push_cast
  rw [Real.logb_div hZr.ne' hKr.ne', Real.logb_div hZr.ne' hcard.ne']
  ring

/-- [proved-derived; formal-checked] **`chain_rule_of_species`: a located key.** When every surviving
key gives the conditioned family one likelihood `ℓ` (one survivor, or a species every admitted
receiver reads alike), the composed code is the keystone's key description less its surviving fibre,
plus the conditioned family's code under the located key:
`−log₂ ∏_(t<n) q_t(x_t) = (log₂ |κ| − log₂ #S_n) − log₂ ℓ`. -/
theorem chain_rule_of_species [Nonempty κ] {P : κ → ℕ → C → ℚ} (hP : ∀ a t c, 0 ≤ P a t c)
    (x : ℕ → C) (n : ℕ) (hS : (keySurvivors P x n).Nonempty) (ℓ : ℚ)
    (hℓ : ∀ a ∈ keySurvivors P x n, seqLik (received P x a) n = ℓ) :
    -Real.logb 2 ((∏ t ∈ range n, composedFace uniformPrior P x t (x t) : ℚ) : ℝ) =
      (Real.logb 2 (Fintype.card κ) - Real.logb 2 (keySurvivors P x n).card) -
        Real.logb 2 (ℓ : ℝ) := by
  rw [chain_rule hP x n hS]
  have hcard : ((keySurvivors P x n).card : ℚ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  have hmean : (∑ a ∈ keySurvivors P x n, seqLik (received P x a) n) /
      (keySurvivors P x n).card = ℓ := by
    rw [sum_congr rfl hℓ, sum_const, nsmul_eq_mul]
    field_simp
  rw [hmean]
  ring

/-! ### The staged face: a face factored through a stage at every tick -/

section Staged

variable {S : Type*}

/-- [definition] **The staged face**: a class's stage face times its conditioned face within the
stage, `q_t(c) = h_t(σ c) · r_t(c)`. -/
def stagedFace (σ : C → S) (h : ℕ → S → ℚ) (r : ℕ → C → ℚ) (t : ℕ) (c : C) : ℚ :=
  h t (σ c) * r t c

/-- [proved-derived; formal-checked] **The staged face is nonnegative** where the stage face and the
conditioned face are. -/
theorem stagedFace_nonneg {σ : C → S} {h : ℕ → S → ℚ} {r : ℕ → C → ℚ}
    (hh : ∀ t s, 0 ≤ h t s) (hr : ∀ t c, 0 ≤ r t c) (t : ℕ) (c : C) :
    0 ≤ stagedFace σ h r t c :=
  mul_nonneg (hh t (σ c)) (hr t c)

/-- [proved-derived; formal-checked] **The staged face sums to one** over the classes when the stage
face sums to one over the stages and the conditioned face sums to one on every stage's fibre. -/
theorem stagedFace_sum_one [Fintype C] [Fintype S] [DecidableEq S] {σ : C → S}
    {h : ℕ → S → ℚ} {r : ℕ → C → ℚ} (t : ℕ) (hh : ∑ s, h t s = 1)
    (hr : ∀ s, ∑ c ∈ univ.filter (fun c => σ c = s), r t c = 1) :
    ∑ c, stagedFace σ h r t c = 1 := by
  have hfib : ∀ s, ∑ c ∈ univ.filter (fun c => σ c = s), stagedFace σ h r t c = h t s := by
    intro s
    rw [sum_congr rfl fun c hc => by
      rw [stagedFace, (mem_filter.mp hc).2], ← mul_sum, hr s, mul_one]
  rw [← sum_fiberwise univ σ (stagedFace σ h r t), sum_congr rfl fun s _ => hfib s, hh]

/-- [proved-derived; formal-checked] **`staged_chain_rule`: the chain rule at every tick.** The
staged faces of the received cells multiply to the stage faces' product times the conditioned
faces' product. -/
theorem staged_chain_rule (σ : C → S) (h : ℕ → S → ℚ) (r : ℕ → C → ℚ) (x : ℕ → C) (n : ℕ) :
    ∏ t ∈ range n, stagedFace σ h r t (x t) =
      (∏ t ∈ range n, h t (σ (x t))) * ∏ t ∈ range n, r t (x t) :=
  prod_mul_distrib

/-- [proved-derived; formal-checked] **`staged_code`: the staged code is the stage's code plus the
conditioned code**, while every received cell's stage face and conditioned face are positive. -/
theorem staged_code {σ : C → S} {h : ℕ → S → ℚ} {r : ℕ → C → ℚ} (x : ℕ → C) (n : ℕ)
    (hh : ∀ t ∈ range n, 0 < h t (σ (x t))) (hr : ∀ t ∈ range n, 0 < r t (x t)) :
    -Real.logb 2 ((∏ t ∈ range n, stagedFace σ h r t (x t) : ℚ) : ℝ) =
      -Real.logb 2 ((∏ t ∈ range n, h t (σ (x t)) : ℚ) : ℝ) +
        -Real.logb 2 ((∏ t ∈ range n, r t (x t) : ℚ) : ℝ) := by
  have h1 : (0 : ℝ) < ((∏ t ∈ range n, h t (σ (x t)) : ℚ) : ℝ) := by
    exact_mod_cast prod_pos hh
  have h2 : (0 : ℝ) < ((∏ t ∈ range n, r t (x t) : ℚ) : ℝ) := by
    exact_mod_cast prod_pos hr
  rw [staged_chain_rule, Rat.cast_mul, Real.logb_mul h1.ne' h2.ne', neg_add]

end Staged

section Audit

#print axioms composedFace_received
#print axioms composed_weight
#print axioms composedFace_nonneg
#print axioms composedFace_sum_one
#print axioms composedFace_pos
#print axioms composed_telescope
#print axioms seqLik_eq_zero_of_not_mem
#print axioms sum_seqLik_survivors
#print axioms chain_rule
#print axioms chain_rule_of_species
#print axioms stagedFace_nonneg
#print axioms stagedFace_sum_one
#print axioms staged_chain_rule
#print axioms staged_code

end Audit

end Holonics.Compression.Landmark.Context.Composition
