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
  living family (`Population.population_mixture` under the evolved prior), in an aeon without
  births. A birth draws `m_g` from the reserve and renormalizes the priors over the founded mass
  `M_n = M + Σ_g m_g`, so with births the bound is `−log₂(m_f/M_n) − log₂ L_f` (Rust
  `receiver::population::evolution`; `evolved_code_with_births` below).
* `selection_telescope`, `dirichlet_telescope`, `dirichlet_telescope_counts`
  [proved-derived; formal-checked]: **the Dirichlet face telescoped along a sequence of
  selections.** With the pseudo-counts unchanged, the faces of the selected families multiply to the
  Dirichlet-multinomial face of the counts, `∏_(k<K) D_k(sel k) = ∏_f (s₀_f + σ_f)⋯(s₀_f + σ_f +
  c_f − 1)/S(S + 1)⋯(S + K − 1)`, `S = Σ_g (s₀_g + σ_g)`, so the order of the aeons does not matter
  and the counts are its retention. `dirichlet_telescope_le` [proved-derived; formal-checked]: with
  deaths the pseudo-counts move, and a floor `ρ ≤ σ_k` with a ceiling `Σ_g σ_k(g) ≤ T` (`T = |F|/2`
  by `survivalPseudo_le_half`) bounds the product below by the telescope at `ρ` over `S₀ + T`.
* `evolved_aeons_code` [proved-derived; formal-checked]: **the multi-aeon code.** Over `K` aeons
  without births, the population's summed code is at most the selected families' own codes plus
  `K(−log₂ λ)` plus the Dirichlet face's code of the selection sequence, `−log₂ ∏_(k<K) D_k(sel k)`:
  the regret the evolved prior carries across aeons is the telescope's code.

**The newborn** (Rust `receiver::population`, "Birth from reserved mass"). Every family stands in
one static mixture at its declared mass `m_x`, born or not. A family born at cell `t_x` abstains
before it: it predicts with the population's own face (`Abstains`). A declared family has
`t_x = 0`, and `foundedBy n` is the set of families born by `n`, of mass `M_n`.

* `abstaining_face` [proved-derived; formal-checked]: the unborn leave the face unmoved. At every
  cell the mixture's face is the founded families' face.
* `abstaining_mixture`, `abstaining_exists` [proved-derived; formal-checked]: the abstaining
  newborn exists. The founded population's face, read through its own earlier faces
  (`bornFace`), is the static mixture's face when every unborn family reads it. So the Rust
  population, which holds only the founded families, computes the mixture, and the predicate
  `Abstains` is not vacuous.
* `newborn_likelihood`, `founded_likelihood` [proved-derived; formal-checked]: **the newborn's
  telescope.** A family founded at `t_x` inherits the population's likelihood there,
  `L_x(n) = W_(t_x) L_x[t_x, n)`, and the founded mass telescopes,
  `W_n = [Σ_f m_f L_f + Σ_g m_g W_(t_g) L_g[t_g, n)]/M_n`.
* `newborn_code`, `founded_code` [proved-derived; formal-checked]: the newborn pays its charge
  once, `−log₂ W_n ≤ −log₂(m_x/M_n) − log₂ W_(t_x) − log₂ L_x[t_x, n)`.
* `evolved_code_with_births` [proved-derived; formal-checked]: once births have founded the mass
  `M_n`, a declared family's bound under the evolved prior gains `log₂(M_n/M)`,
  `−log₂ W_n ≤ −log₂ π(f) + log₂(M_n/M) − log₂ L_f`. Without births it is `evolved_aeon_code`.

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
* `species_collapse_standing` [proved-derived; formal-checked]: **the collapse is a standing for
  its certified future** (U2, the [retention contract](../../../../../docs/ELEMENTARY_OBJECTS.md#the-retention-contract)).
  The family's state is its tick and each key's weight `(t, v)`; a cell `c` multiplies each weight
  by its key's face `f_k(t)(c)` inside the admitted future and is refused past it (`keyStep`), and
  the receiver reads the mixture's mass of a class there (`keyRead`). When every member agrees with
  its representative at every admitted tick and cell, the retention `(t, W)` with `W_s` the species'
  summed weight (`speciesRetain`) is a `Foundation/Standing.StandingLaw` for every cell word, read
  by the collapsed family (`speciesStep`, `speciesRead`), through
  `Standing.statistical_sufficiency_gives_standing`. Every cell word includes every word a release
  commits, so the future is action-sufficient. Its recoverability is `species_split`.

**The whole-future signature** (Rust `Emitters::signature` under `AdmittedFuture::Whole`). A key
whose clock winds without the cells emits a periodic word, and its signature over the whole future
is its word over one least period (`leastPeriod`, Mathlib's minimal period of the shift `wordShift`).

* `leastPeriod_dvd` [proved-standard; formal-checked]: the least period divides every period.
* `agree_forever_iff`, `signature_eq_iff` [proved-derived; formal-checked]: **two periodic words
  agree forever exactly when their least periods agree and they agree over one period**, so two keys
  are one species over the whole future exactly when their signatures are equal.
* `shiftHolds_iff`, `leastPeriod_isLeast` [proved-derived; formal-checked]: on a declared period `P`,
  a divisor `d` with `u(t + d) = u(t)` wherever `t + d < P` is a period of the whole word, so the
  Rust search for the least such divisor returns the least period.

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
population codes within `−log₂ π(x)` of that family's own code (`Population.population_mixture`):
the mixture of the declared families alone, an aeon without births (a birth renormalizes the priors
to `m_f/M_n`, module header). -/
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

/-! ### The newborn: birth from reserved mass -/

section Newborn

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [definition] **The founded families** at cell `s`: those born by `s`, `born x ≤ s`. A declared
family has `born x = 0`. -/
def foundedBy (born : ι → ℕ) (s : ℕ) : Finset ι := univ.filter fun x => born x ≤ s

/-- [definition; agent-inferred] **An abstaining newborn** (Rust `receiver::population`, "Birth from
reserved mass"): before its birth cell a family predicts with the population's own face,
`f_x(t) = q_t` for `t < born x`. Every family stands in one static mixture at its prior mass,
born or not. The predicate is a fixed point of the population's face; `abstaining_exists`
constructs it. -/
def Abstains (π : ι → ℚ) (f : ι → ℕ → ℚ) (born : ι → ℕ) : Prop :=
  ∀ x t, t < born x → f x t = fwdMix π f idKernel t

/-- [proved-derived; formal-checked] **`abstaining_face`: the unborn leave the face unmoved.** At
every cell the mixture's face over every family is the face of the founded families alone, each at
its forward weight: an unborn family predicts with the face itself, so it adds `q` times its weight
to the numerator and its weight to the denominator. The population's code therefore does not move
at a birth. -/
theorem abstaining_face {π : ι → ℚ} {f : ι → ℕ → ℚ} {born : ι → ℕ} (hπ : ∀ x, 0 ≤ π x)
    (hf : ∀ x t, 0 ≤ f x t) (habs : Abstains π f born) (t : ℕ)
    (hB : 0 < ∑ x ∈ foundedBy born t, fwd π f idKernel t x) :
    fwdMix π f idKernel t
      = (∑ x ∈ foundedBy born t, fwd π f idKernel t x * f x t)
          / ∑ x ∈ foundedBy born t, fwd π f idKernel t x := by
  set q := fwdMix π f idKernel t
  set S := foundedBy born t
  have hnn := fwd_nonneg hπ hf idKernel_stochastic.1
  have hU : ∀ x ∈ univ.filter (fun x => ¬ born x ≤ t), f x t = q := fun x hx =>
    habs x t (by simpa using (mem_filter.mp hx).2)
  have htot : ∑ x, fwd π f idKernel t x
      = (∑ x ∈ S, fwd π f idKernel t x)
          + ∑ x ∈ univ.filter (fun x => ¬ born x ≤ t), fwd π f idKernel t x :=
    (sum_filter_add_sum_filter_not univ (fun x => born x ≤ t) _).symm
  have hnum : ∑ x, fwd π f idKernel t x * f x t
      = (∑ x ∈ S, fwd π f idKernel t x * f x t)
          + (∑ x ∈ univ.filter (fun x => ¬ born x ≤ t), fwd π f idKernel t x) * q := by
    rw [← sum_filter_add_sum_filter_not univ (fun x => born x ≤ t), sum_mul]
    congr 1
    exact sum_congr rfl fun x hx => by rw [hU x hx]
  have hu : 0 ≤ ∑ x ∈ univ.filter (fun x => ¬ born x ≤ t), fwd π f idKernel t x :=
    sum_nonneg fun x _ => hnn t x
  have hq : q * ∑ x, fwd π f idKernel t x = ∑ x, fwd π f idKernel t x * f x t := by
    simp only [q, fwdMix]
    rw [div_mul_cancel₀]
    rw [htot]; positivity
  rw [eq_div_iff hB.ne']
  rw [htot, hnum] at hq
  linarith

/-- [definition] **A founded family's likelihood** at cell `t`, given the population's earlier
faces `q` and the family's own faces `g` after its birth: `W_(born x) · L_x[born x, t)`, with
`W_s = ∏_(r<s) q_r`. -/
def bornLik (born : ι → ℕ) (g : ι → ℕ → ℚ) (q : ℕ → ℚ) (t : ℕ) (x : ι) : ℚ :=
  (∏ s ∈ range (born x), q s) * ∏ s ∈ Ico (born x) t, g x s

/-- [definition] **The founded population's face** at cell `t`: the founded families' faces
weighed by `π_x · bornLik`, the face of a population that holds only the families founded so far. -/
def foundedFace (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) (q : ℕ → ℚ) (t : ℕ) : ℚ :=
  (∑ x ∈ foundedBy born t, π x * bornLik born g q t x * g x t)
    / ∑ x ∈ foundedBy born t, π x * bornLik born g q t x

/-- [definition] The founded population's faces below cell `n`, each read from the earlier ones (a
face at `t` reads `q` only below `t`, `foundedFace_congr`). -/
def bornFaces (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) : ℕ → ℕ → ℚ
  | 0 => fun _ => 0
  | n + 1 =>
    Function.update (bornFaces π g born n) n (foundedFace π g born (bornFaces π g born n) n)

/-- [definition] **The founded population's face** at cell `t`, read through its own earlier
faces. -/
def bornFace (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) (t : ℕ) : ℚ :=
  bornFaces π g born (t + 1) t

/-- [definition] **The abstaining faces**: before its birth a family reads the founded population's
face, from its birth on its own face `g`. -/
def abstainingFaces (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) : ι → ℕ → ℚ :=
  fun x t => if t < born x then bornFace π g born t else g x t

omit [DecidableEq ι] in
/-- The founded face at `t` reads the population's faces only below `t`. -/
theorem foundedFace_congr {π : ι → ℚ} {g : ι → ℕ → ℚ} {born : ι → ℕ} {q q' : ℕ → ℚ} {t : ℕ}
    (h : ∀ s < t, q s = q' s) : foundedFace π g born q t = foundedFace π g born q' t := by
  have hl : ∀ x ∈ foundedBy born t, bornLik born g q t x = bornLik born g q' t x := by
    intro x hx
    have hb : born x ≤ t := (mem_filter.mp hx).2
    simp only [bornLik]
    congr 1
    exact prod_congr rfl fun s hs => h s (lt_of_lt_of_le (mem_range.mp hs) hb)
  simp only [foundedFace]
  congr 1
  · exact sum_congr rfl fun x hx => by rw [hl x hx]
  · exact sum_congr rfl fun x hx => by rw [hl x hx]

omit [DecidableEq ι] in
/-- A face once read stays: later rows keep the earlier entries. -/
theorem bornFaces_stable (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) (n k : ℕ) {s : ℕ}
    (hs : s < n) : bornFaces π g born (n + k) s = bornFaces π g born n s := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← add_assoc, bornFaces, Function.update_of_ne (by omega), ih]

omit [DecidableEq ι] in
/-- [proved-derived; formal-checked] **The founded face is read through itself**:
`q_t = foundedFace q t`. -/
theorem bornFace_eq (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) (t : ℕ) :
    bornFace π g born t = foundedFace π g born (bornFace π g born) t := by
  have h1 : bornFace π g born t = foundedFace π g born (bornFaces π g born t) t := by
    simp only [bornFace, bornFaces, Function.update_self]
  rw [h1]
  apply foundedFace_congr
  intro s hs
  obtain ⟨k, rfl⟩ : ∃ k, t = s + 1 + k := ⟨t - (s + 1), by omega⟩
  exact bornFaces_stable π g born (s + 1) k (by omega)

omit [DecidableEq ι] in
/-- The founded face is nonnegative where the earlier faces are. -/
theorem foundedFace_nonneg {π : ι → ℚ} {g : ι → ℕ → ℚ} {born : ι → ℕ} (hπ : ∀ x, 0 ≤ π x)
    (hg : ∀ x t, 0 ≤ g x t) {q : ℕ → ℚ} {t : ℕ} (hq : ∀ s < t, 0 ≤ q s) :
    0 ≤ foundedFace π g born q t := by
  have hl : ∀ x ∈ foundedBy born t, 0 ≤ bornLik born g q t x := fun x hx => by
    have hb : born x ≤ t := (mem_filter.mp hx).2
    exact mul_nonneg (prod_nonneg fun s hs => hq s (lt_of_lt_of_le (mem_range.mp hs) hb))
      (prod_nonneg fun s _ => hg x s)
  exact div_nonneg (sum_nonneg fun x hx => mul_nonneg (mul_nonneg (hπ x) (hl x hx)) (hg x t))
    (sum_nonneg fun x hx => mul_nonneg (hπ x) (hl x hx))

omit [DecidableEq ι] in
/-- The founded population's face is nonnegative. -/
theorem bornFace_nonneg {π : ι → ℚ} {g : ι → ℕ → ℚ} {born : ι → ℕ} (hπ : ∀ x, 0 ≤ π x)
    (hg : ∀ x t, 0 ≤ g x t) (t : ℕ) : 0 ≤ bornFace π g born t := by
  induction t using Nat.strong_induction_on with
  | _ t ih => rw [bornFace_eq]; exact foundedFace_nonneg hπ hg ih

omit [DecidableEq ι] in
/-- A founded family's likelihood under the abstaining faces is `W_(born x) · L_x[born x, t)`. -/
theorem abstaining_seqLik_founded (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) {x : ι} {t : ℕ}
    (hb : born x ≤ t) :
    seqLik (abstainingFaces π g born x) t = bornLik born g (bornFace π g born) t x := by
  rw [seqLik, ← prod_range_mul_prod_Ico _ hb, bornLik]
  congr 1
  · exact prod_congr rfl fun s hs => by simp [abstainingFaces, mem_range.mp hs]
  · exact prod_congr rfl fun s hs => by simp [abstainingFaces, not_lt.mpr (mem_Ico.mp hs).1]

omit [DecidableEq ι] in
/-- An unborn family's likelihood under the abstaining faces is the population's `W_t`. -/
theorem abstaining_seqLik_unborn (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) {x : ι} {t : ℕ}
    (ht : t < born x) :
    seqLik (abstainingFaces π g born x) t = ∏ s ∈ range t, bornFace π g born s := by
  rw [seqLik]
  exact prod_congr rfl fun s hs => by simp [abstainingFaces, lt_trans (mem_range.mp hs) ht]

/-- [proved-derived; formal-checked] **`abstaining_mixture`: the static mixture reads the founded
population's face.** Under the abstaining faces the mixture over every family, the unborn at their
prior masses, has at every cell the founded population's face. No positivity is needed: where no
founded family carries weight, both faces are zero. So the Rust population, which holds only the
families founded so far, computes this mixture. -/
theorem abstaining_mixture {π : ι → ℚ} {g : ι → ℕ → ℚ} {born : ι → ℕ} (hπ : ∀ x, 0 ≤ π x)
    (hg : ∀ x t, 0 ≤ g x t) (t : ℕ) :
    fwdMix π (abstainingFaces π g born) idKernel t = bornFace π g born t := by
  set f := abstainingFaces π g born with hfdef
  set W := ∏ s ∈ range t, bornFace π g born s
  set u := ∑ x ∈ univ.filter (fun x => ¬ born x ≤ t), π x
  set A := ∑ x ∈ foundedBy born t, π x * bornLik born g (bornFace π g born) t x * g x t
  set B := ∑ x ∈ foundedBy born t, π x * bornLik born g (bornFace π g born) t x
  have hq : bornFace π g born t = A / B := bornFace_eq π g born t
  have hS : ∀ x ∈ univ.filter (fun x => born x ≤ t),
      fwd π f idKernel t x = π x * bornLik born g (bornFace π g born) t x ∧ f x t = g x t :=
    fun x hx => by
      have hb : born x ≤ t := (mem_filter.mp hx).2
      exact ⟨by rw [fwd_id, abstaining_seqLik_founded π g born hb],
        by simp [hfdef, abstainingFaces, not_lt.mpr hb]⟩
  have hU : ∀ x ∈ univ.filter (fun x => ¬ born x ≤ t),
      fwd π f idKernel t x = π x * W ∧ f x t = bornFace π g born t :=
    fun x hx => by
      have ht : t < born x := by simpa using (mem_filter.mp hx).2
      exact ⟨by rw [fwd_id, abstaining_seqLik_unborn π g born ht],
        by simp [hfdef, abstainingFaces, ht]⟩
  have hnum : ∑ x, fwd π f idKernel t x * f x t = A + u * W * bornFace π g born t := by
    rw [← sum_filter_add_sum_filter_not univ (fun x => born x ≤ t)]
    congr 1
    · exact sum_congr rfl fun x hx => by rw [(hS x hx).1, (hS x hx).2]
    · rw [sum_mul, sum_mul]
      exact sum_congr rfl fun x hx => by rw [(hU x hx).1, (hU x hx).2]
  have hden : ∑ x, fwd π f idKernel t x = B + u * W := by
    rw [← sum_filter_add_sum_filter_not univ (fun x => born x ≤ t)]
    congr 1
    · exact sum_congr rfl fun x hx => by rw [(hS x hx).1]
    · rw [sum_mul]
      exact sum_congr rfl fun x hx => by rw [(hU x hx).1]
  have hl : ∀ x ∈ foundedBy born t, 0 ≤ π x * bornLik born g (bornFace π g born) t x :=
    fun x _ => mul_nonneg (hπ x) (mul_nonneg (prod_nonneg fun s _ => bornFace_nonneg hπ hg s)
      (prod_nonneg fun s _ => hg x s))
  have huW : 0 ≤ u * W :=
    mul_nonneg (sum_nonneg fun x _ => hπ x) (prod_nonneg fun s _ => bornFace_nonneg hπ hg s)
  rw [fwdMix, hnum, hden]
  rcases (sum_nonneg hl : 0 ≤ B).eq_or_lt with hB | hB
  · have hA : A = 0 := by
      have hz := (sum_eq_zero_iff_of_nonneg hl).mp hB.symm
      exact sum_eq_zero fun x hx => by rw [hz x hx, zero_mul]
    rw [hq, hA]
    simp
  · change 0 < B at hB
    have hBW : B + u * W ≠ 0 := by positivity
    rw [hq, div_eq_iff hBW]
    field_simp

/-- [proved-derived; formal-checked] **`abstaining_exists`: the abstaining newborn exists.** For a
nonnegative prior and nonnegative faces after birth, the abstaining faces abstain, so the bounds
below are not vacuous. -/
theorem abstaining_exists {π : ι → ℚ} {g : ι → ℕ → ℚ} {born : ι → ℕ} (hπ : ∀ x, 0 ≤ π x)
    (hg : ∀ x t, 0 ≤ g x t) : Abstains π (abstainingFaces π g born) born := by
  intro x t ht
  rw [abstaining_mixture hπ hg t]
  simp [abstainingFaces, ht]

omit [DecidableEq ι] in
/-- From its birth on, an abstaining family reads its own face. -/
theorem abstaining_after_birth (π : ι → ℚ) (g : ι → ℕ → ℚ) (born : ι → ℕ) {x : ι} {t : ℕ}
    (hb : born x ≤ t) : abstainingFaces π g born x t = g x t := by
  simp [abstainingFaces, not_lt.mpr hb]

/-- [proved-derived; formal-checked] **`newborn_likelihood`: the newborn inherits the population's
likelihood.** An abstaining family born at cell `t_x ≤ n` has `L_x(n) = W_(t_x) · L_x[t_x, n)`. -/
theorem newborn_likelihood {π : ι → ℚ} {f : ι → ℕ → ℚ} {born : ι → ℕ}
    (habs : Abstains π f born) {x : ι} {n : ℕ} (hb : born x ≤ n) :
    seqLik (f x) n
      = (∏ t ∈ range (born x), fwdMix π f idKernel t) * ∏ t ∈ Ico (born x) n, f x t := by
  rw [seqLik, ← prod_range_mul_prod_Ico _ hb]
  congr 1
  exact prod_congr rfl fun t ht => habs x t (mem_range.mp ht)

/-- [proved-derived; formal-checked] **`founded_likelihood`: the founded mass telescopes.** With
`F_s = Σ_(born x ≤ s) π_x`, `F_s · W_s = Σ_(born x ≤ s) π_x L_x(s)`. At declared masses this is
the Rust telescope `W_n = [Σ_f m_f L_f + Σ_g m_g W_(t_g) L_g[t_g, n)]/M_n`. -/
theorem founded_likelihood {π : ι → ℚ} {f : ι → ℕ → ℚ} {born : ι → ℕ} (hπ : IsPrior π)
    (hf : ∀ x t, 0 ≤ f x t) (habs : Abstains π f born) (s : ℕ)
    (hlive : 0 < ∑ x, π x * seqLik (f x) s) :
    (∑ x ∈ foundedBy born s, π x) * ∏ t ∈ range s, fwdMix π f idKernel t
      = ∑ x ∈ foundedBy born s, π x * seqLik (f x) s := by
  set W := ∏ t ∈ range s, fwdMix π f idKernel t
  have htel : W = ∑ x, π x * seqLik (f x) s := (population_mixture hπ hf s hlive).2.1
  have hU : ∀ x ∈ univ.filter (fun x => ¬ born x ≤ s), seqLik (f x) s = W := by
    intro x hx
    have hlt : s < born x := by simpa using (mem_filter.mp hx).2
    exact prod_congr rfl fun t ht => habs x t (lt_trans (mem_range.mp ht) hlt)
  have hUsum : ∑ x ∈ univ.filter (fun x => ¬ born x ≤ s), π x * seqLik (f x) s
      = (∑ x ∈ univ.filter (fun x => ¬ born x ≤ s), π x) * W := by
    rw [sum_mul]; exact sum_congr rfl fun x hx => by rw [hU x hx]
  have e1 := sum_filter_add_sum_filter_not univ (fun x => born x ≤ s)
    (fun x => π x * seqLik (f x) s)
  have e3 := sum_filter_add_sum_filter_not univ (fun x => born x ≤ s) π
  rw [hπ.2] at e3
  rw [← htel, hUsum] at e1
  simp only [foundedBy]
  linear_combination W * e3 - e1

/-- [proved-derived; formal-checked] **`newborn_code`: the newborn pays its charge once.**
`−log₂ W_n ≤ −log₂(π_x/F_n) − log₂ W_(t_x) − log₂ L_x[t_x, n)`: the population's code is at most
its code up to the birth, plus the newborn's share of the founded mass, plus the newborn's own code
from its birth. -/
theorem newborn_code {π : ι → ℚ} {f : ι → ℕ → ℚ} {born : ι → ℕ} (hπ : IsPrior π)
    (hf : ∀ x t, 0 ≤ f x t) (habs : Abstains π f born) {n : ℕ} {x : ι} (hb : born x ≤ n)
    (hx : 0 < π x) (hW : 0 < ∏ t ∈ range (born x), fwdMix π f idKernel t)
    (hL : 0 < ∏ t ∈ Ico (born x) n, f x t) :
    -Real.logb 2 ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ) ≤
      -Real.logb 2 ((π x / ∑ y ∈ foundedBy born n, π y : ℚ) : ℝ)
        - Real.logb 2 ((∏ t ∈ range (born x), fwdMix π f idKernel t : ℚ) : ℝ)
        - Real.logb 2 ((∏ t ∈ Ico (born x) n, f x t : ℚ) : ℝ) := by
  set Wb := ∏ t ∈ range (born x), fwdMix π f idKernel t
  set Lx := ∏ t ∈ Ico (born x) n, f x t
  set F := ∑ y ∈ foundedBy born n, π y
  have hseq : seqLik (f x) n = Wb * Lx := newborn_likelihood habs hb
  have hxF : x ∈ foundedBy born n := by simp [foundedBy, hb]
  have hFx : π x ≤ F := single_le_sum (f := π) (fun y _ => hπ.1 y) hxF
  have hF : 0 < F := lt_of_lt_of_le hx hFx
  have hterm : 0 < π x * seqLik (f x) n := by rw [hseq]; positivity
  have hlive : 0 < ∑ y, π y * seqLik (f y) n :=
    lt_of_lt_of_le hterm (single_le_sum (f := fun y => π y * seqLik (f y) n)
      (fun y _ => mul_nonneg (hπ.1 y) (seqLik_nonneg (hf y) n)) (mem_univ x))
  have hfl := founded_likelihood hπ hf habs n hlive
  have hge : π x * seqLik (f x) n ≤ F * ∏ t ∈ range n, fwdMix π f idKernel t := by
    rw [hfl]
    exact single_le_sum (f := fun y => π y * seqLik (f y) n)
      (fun y _ => mul_nonneg (hπ.1 y) (seqLik_nonneg (hf y) n)) hxF
  have hle : π x / F * Wb * Lx ≤ ∏ t ∈ range n, fwdMix π f idKernel t := by
    rw [hseq] at hge
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hF]
    linarith
  have hpos : 0 < π x / F * Wb * Lx := by positivity
  have hb' := neg_logb_le_of_le (a := ((π x / F * Wb * Lx : ℚ) : ℝ))
    (b := ((∏ t ∈ range n, fwdMix π f idKernel t : ℚ) : ℝ)) (by exact_mod_cast hpos)
    (by exact_mod_cast hle)
  have h1 : (0 : ℝ) < ((π x / F : ℚ) : ℝ) := by exact_mod_cast div_pos hx hF
  have h2 : (0 : ℝ) < ((Wb : ℚ) : ℝ) := by exact_mod_cast hW
  have h3 : (0 : ℝ) < ((Lx : ℚ) : ℝ) := by exact_mod_cast hL
  rw [Rat.cast_mul, Rat.cast_mul, Real.logb_mul (by positivity) h3.ne',
    Real.logb_mul h1.ne' h2.ne'] at hb'
  linarith

/-- [definition] **The prior of declared masses** `m_x/Σ_y m_y`: every family, born or not, at its
declared mass. -/
def massPrior (m : ι → ℚ) : ι → ℚ := fun x => m x / ∑ y, m y

omit [DecidableEq ι] in
/-- Nonnegative masses with a positive total give a prior. -/
theorem massPrior_isPrior {m : ι → ℚ} (hm : ∀ x, 0 ≤ m x) (hM : 0 < ∑ x, m x) :
    IsPrior (massPrior m) :=
  ⟨fun x => div_nonneg (hm x) hM.le, by simp only [massPrior]; rw [← sum_div, div_self hM.ne']⟩

omit [DecidableEq ι] in
/-- The share of the founded mass does not see the total: `(m_x/M)/(F_n/M) = m_x/M_n`, with
`M_n = Σ_(born y ≤ n) m_y`. -/
theorem founded_share {m : ι → ℚ} (hM : ∑ y, m y ≠ 0) (born : ι → ℕ) (n : ℕ) (x : ι) :
    massPrior m x / ∑ y ∈ foundedBy born n, massPrior m y = m x / ∑ y ∈ foundedBy born n, m y := by
  simp only [massPrior]
  rw [← sum_div, div_div_div_cancel_right₀ hM]

/-- [proved-derived; formal-checked] **`founded_code`: the Rust bound.** At declared masses,
`−log₂ W_n ≤ −log₂(m_x/M_n) − log₂ W_(t_x) − log₂ L_x[t_x, n)`, with `M_n` the mass founded by
`n` (Rust `receiver::population`, "Birth from reserved mass"). -/
theorem founded_code {m : ι → ℚ} (hm : ∀ x, 0 ≤ m x) (hM : 0 < ∑ x, m x) {f : ι → ℕ → ℚ}
    {born : ι → ℕ} (hf : ∀ x t, 0 ≤ f x t) (habs : Abstains (massPrior m) f born) {n : ℕ} {x : ι}
    (hb : born x ≤ n) (hx : 0 < m x)
    (hW : 0 < ∏ t ∈ range (born x), fwdMix (massPrior m) f idKernel t)
    (hL : 0 < ∏ t ∈ Ico (born x) n, f x t) :
    -Real.logb 2 ((∏ t ∈ range n, fwdMix (massPrior m) f idKernel t : ℚ) : ℝ) ≤
      -Real.logb 2 ((m x / ∑ y ∈ foundedBy born n, m y : ℚ) : ℝ)
        - Real.logb 2 ((∏ t ∈ range (born x), fwdMix (massPrior m) f idKernel t : ℚ) : ℝ)
        - Real.logb 2 ((∏ t ∈ Ico (born x) n, f x t : ℚ) : ℝ) := by
  rw [← founded_share hM.ne' born n x]
  exact newborn_code (massPrior_isPrior hm hM) hf habs hb (div_pos hx hM) hW hL

/-- [proved-derived; formal-checked] **`evolved_code_with_births`: the evolved bound once births have
founded mass.** A declared family (`born x = 0`) at mass `m_x = M π(x)` under the evolved prior:
`−log₂ W_n ≤ −log₂ π(x) + log₂(M_n/M) − log₂ L_x(n)`. Without births `M_n = M`, and this is
`evolved_aeon_code`. -/
theorem evolved_code_with_births {m : ι → ℚ} (hm : ∀ x, 0 ≤ m x) (hM : 0 < ∑ x, m x)
    {f : ι → ℕ → ℚ} {born : ι → ℕ} (hf : ∀ x t, 0 ≤ f x t) (habs : Abstains (massPrior m) f born)
    (n : ℕ) {M w : ℚ} {D P : ι → ℚ} (hM0 : 0 < M) {x : ι} (hx0 : born x = 0)
    (hmx : m x = M * evolved w D P x) (hx : 0 < evolved w D P x) (hL : 0 < seqLik (f x) n) :
    -Real.logb 2 ((∏ t ∈ range n, fwdMix (massPrior m) f idKernel t : ℚ) : ℝ) ≤
      -Real.logb 2 (evolved w D P x : ℝ)
        + Real.logb 2 (((∑ y ∈ foundedBy born n, m y) / M : ℚ) : ℝ)
        - Real.logb 2 (seqLik (f x) n : ℝ) := by
  have hmx0 : 0 < m x := by rw [hmx]; exact mul_pos hM0 hx
  have hb : born x ≤ n := by omega
  have hxF : x ∈ foundedBy born n := by simp [foundedBy, hb]
  have hMn : 0 < ∑ y ∈ foundedBy born n, m y :=
    lt_of_lt_of_le hmx0 (single_le_sum (f := m) (fun y _ => hm y) hxF)
  have hIco : ∏ t ∈ Ico (born x) n, f x t = seqLik (f x) n := by
    rw [hx0, seqLik, range_eq_Ico]
  have hc := founded_code hm hM hf habs hb hmx0 (by simp [hx0]) (by rw [hIco]; exact hL)
  rw [hIco, hx0, prod_range_zero, Rat.cast_one, Real.logb_one, sub_zero, hmx] at hc
  have h1 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM0
  have h2 : (0 : ℝ) < (evolved w D P x : ℝ) := by exact_mod_cast hx
  have h3 : (0 : ℝ) < ((∑ y ∈ foundedBy born n, m y : ℚ) : ℝ) := by exact_mod_cast hMn
  rw [Rat.cast_div, Rat.cast_mul, Real.logb_div (by positivity) h3.ne',
    Real.logb_mul h1.ne' h2.ne'] at hc
  rw [Rat.cast_div, Real.logb_div h3.ne' h1.ne']
  linarith

end Newborn

/-! ### The evolved prior across aeons -/

section Aeons

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [definition] **The selections of a family in the first `k` aeons** of the sequence `sel`. -/
def selCount (sel : ℕ → ι) (k : ℕ) (x : ι) : ℕ := ((range k).filter (fun j => sel j = x)).card

/-- [definition] **The retained selection counts at aeon `k`**: the counts `s₀` retained before the
sequence plus its first `k` selections. -/
def aeonCounts (s₀ : ι → ℕ) (sel : ℕ → ι) (k : ℕ) : ι → ℕ := fun x => s₀ x + selCount sel k x

/-- [definition] **The rising product** `a(a + 1)⋯(a + n − 1)`. -/
def rising (a : ℚ) (n : ℕ) : ℚ := ∏ j ∈ range n, (a + j)

theorem rising_succ (a : ℚ) (n : ℕ) : rising a (n + 1) = rising a n * (a + n) := by
  unfold rising
  rw [prod_range_succ]

theorem rising_pos {a : ℚ} (ha : 0 < a) (n : ℕ) : 0 < rising a n :=
  prod_pos (fun j _ => by positivity)

omit [Fintype ι] in
theorem selCount_succ (sel : ℕ → ι) (k : ℕ) (x : ι) :
    selCount sel (k + 1) x = selCount sel k x + if sel k = x then 1 else 0 := by
  unfold selCount
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · rfl

theorem sum_selCount (sel : ℕ → ι) (k : ℕ) : ∑ x, selCount sel k x = k := by
  induction k with
  | zero => simp [selCount]
  | succ k ih =>
    simp only [selCount_succ, sum_add_distrib, ih, sum_ite_eq, mem_univ, if_true]

/-- The Dirichlet face's total at aeon `k` is the retained total plus `k`. -/
theorem aeonCounts_total (s₀ : ι → ℕ) (σ : ι → ℚ) (sel : ℕ → ι) (k : ℕ) :
    ∑ g, ((aeonCounts s₀ sel k g : ℚ) + σ g) = (∑ g, ((s₀ g : ℚ) + σ g)) + k := by
  have h := congrArg (fun n : ℕ => (n : ℚ)) (sum_selCount sel k)
  simp only [Nat.cast_sum] at h
  simp only [aeonCounts, Nat.cast_add, sum_add_distrib, h]
  ring

/-- [proved-derived; formal-checked] **The general telescope.** For base weights `a` and a positive
base total `B`, the per-aeon ratios `(a_(sel k) + c_k(sel k))/(B + k)` multiply to
`∏_x a_x(a_x + 1)⋯(a_x + c_x − 1) / B(B + 1)⋯(B + K − 1)`, with `c_x` the selections of `x` in the
`K` aeons: the product depends on the sequence only through its counts. -/
theorem selection_telescope (a : ι → ℚ) {B : ℚ} (hB : 0 < B) (sel : ℕ → ι) (K : ℕ) :
    ∏ k ∈ range K, (a (sel k) + selCount sel k (sel k)) / (B + k) =
      (∏ x, rising (a x) (selCount sel K x)) / rising B K := by
  induction K with
  | zero => simp [selCount, rising]
  | succ K ih =>
    rw [prod_range_succ, ih, rising_succ]
    have hnum : ∏ x, rising (a x) (selCount sel (K + 1) x) =
        (∏ x, rising (a x) (selCount sel K x)) * (a (sel K) + selCount sel K (sel K)) := by
      have hx : ∀ x, rising (a x) (selCount sel (K + 1) x) =
          rising (a x) (selCount sel K x) *
            (if sel K = x then a x + selCount sel K x else 1) := by
        intro x
        rw [selCount_succ]
        split_ifs with h
        · rw [rising_succ]
        · rw [add_zero, mul_one]
      rw [prod_congr rfl (fun x _ => hx x), prod_mul_distrib, prod_ite_eq univ (sel K)]
      simp
    rw [hnum]
    have hR := rising_pos hB K
    have hBK : (0 : ℚ) < B + K := by positivity
    field_simp

/-- [proved-derived; formal-checked] **The Dirichlet face telescoped along a sequence of
selections.** With the pseudo-counts `σ` unchanged across the aeons, the product of the Dirichlet
faces of the selected families is the Dirichlet-multinomial face of the counts,
`∏_(k<K) D_k(sel k) = ∏_f (s₀_f + σ_f)⋯(s₀_f + σ_f + c_f − 1) / S(S + 1)⋯(S + K − 1)`,
`S = Σ_g (s₀_g + σ_g)`: it depends on the sequence only through its counts. -/
theorem dirichlet_telescope [Nonempty ι] (s₀ : ι → ℕ) {σ : ι → ℚ} (hσ : ∀ f, 0 < σ f)
    (sel : ℕ → ι) (K : ℕ) :
    ∏ k ∈ range K, dirichletFace (aeonCounts s₀ sel k) σ (sel k) =
      (∏ x, rising ((s₀ x : ℚ) + σ x) (selCount sel K x)) /
        rising (∑ g, ((s₀ g : ℚ) + σ g)) K := by
  rw [← selection_telescope (fun x => (s₀ x : ℚ) + σ x) (dirichlet_total_pos s₀ hσ) sel K]
  refine prod_congr rfl (fun k _ => ?_)
  unfold dirichletFace
  rw [aeonCounts_total]
  simp only [aeonCounts, Nat.cast_add]
  ring

/-- [proved-derived; formal-checked] **The counts are the retention of the Dirichlet code**: two
sequences of selections with the same counts have the same telescoped face, in any order. -/
theorem dirichlet_telescope_counts [Nonempty ι] (s₀ : ι → ℕ) {σ : ι → ℚ} (hσ : ∀ f, 0 < σ f)
    {sel sel' : ℕ → ι} {K : ℕ} (hc : ∀ x, selCount sel K x = selCount sel' K x) :
    ∏ k ∈ range K, dirichletFace (aeonCounts s₀ sel k) σ (sel k) =
      ∏ k ∈ range K, dirichletFace (aeonCounts s₀ sel' k) σ (sel' k) := by
  rw [dirichlet_telescope s₀ hσ, dirichlet_telescope s₀ hσ]
  simp only [hc]

/-- [proved-derived; formal-checked] **Deaths along the sequence.** When the pseudo-counts move from
aeon to aeon (each death thins one), a floor `ρ ≤ σ_k` and a ceiling `Σ_g σ_k(g) ≤ T` bound the
product from below by the telescope at the floor over the ceiling's total:
`∏_(k<K) D_k(sel k) ≥ ∏_f (s₀_f + ρ_f)⋯(s₀_f + ρ_f + c_f − 1) / (S₀ + T)⋯(S₀ + T + K − 1)`,
`S₀ = Σ_g s₀_g`. -/
theorem dirichlet_telescope_le (s₀ : ι → ℕ) {σ : ℕ → ι → ℚ} {ρ : ι → ℚ} {T : ℚ}
    (hρ : ∀ x, 0 < ρ x) (hρσ : ∀ k x, ρ x ≤ σ k x) (hT : ∀ k, ∑ g, σ k g ≤ T)
    (sel : ℕ → ι) (K : ℕ) :
    (∏ x, rising ((s₀ x : ℚ) + ρ x) (selCount sel K x)) /
        rising ((∑ g, (s₀ g : ℚ)) + T) K ≤
      ∏ k ∈ range K, dirichletFace (aeonCounts s₀ sel k) (σ k) (sel k) := by
  have hσ : ∀ k x, 0 < σ k x := fun k x => lt_of_lt_of_le (hρ x) (hρσ k x)
  have hT0 : 0 < T := lt_of_lt_of_le (lt_of_lt_of_le (hσ 0 (sel 0))
    (single_le_sum (fun g _ => (hσ 0 g).le) (mem_univ (sel 0)))) (hT 0)
  have hB : 0 < (∑ g, (s₀ g : ℚ)) + T := by
    have : 0 ≤ ∑ g, (s₀ g : ℚ) := sum_nonneg (fun g _ => Nat.cast_nonneg _)
    linarith [hT0]
  rw [← selection_telescope (fun x => (s₀ x : ℚ) + ρ x) hB sel K]
  refine prod_le_prod (fun k _ => ?_) (fun k _ => ?_)
  · have : 0 ≤ (s₀ (sel k) : ℚ) + ρ (sel k) + selCount sel k (sel k) := by
      have := hρ (sel k); positivity
    exact div_nonneg this (by positivity)
  · have hNe : Nonempty ι := ⟨sel 0⟩
    unfold dirichletFace
    rw [aeonCounts_total]
    refine div_le_div₀ ?_ ?_ ?_ ?_
    · have := hσ k (sel k); positivity
    · simp only [aeonCounts, Nat.cast_add]
      linarith [hρσ k (sel k)]
    · have := dirichlet_total_pos s₀ (hσ k); linarith [Nat.cast_nonneg (α := ℚ) k]
    · have h1 := hT k
      simp only [sum_add_distrib]
      linarith

/-- [proved-derived; formal-checked] **The evolved prior across aeons: the multi-aeon code
telescoped along the selections.** In aeon `k` the population codes its passage `F k` under the
evolved prior `π_k = λ D_k + (1 − λ) P`, `D_k` the Dirichlet face of the counts retained from the
earlier aeons' selections; over `K` aeons its code is at most the selected families' own codes plus
`K` times `−log₂ λ` plus the Dirichlet face's code of the selection sequence:
`Σ_(k<K) −log₂ W_k ≤ K(−log₂ λ) − log₂ ∏_(k<K) D_k(sel k) − Σ_(k<K) log₂ L_k(sel k)`. With the
pseudo-counts unchanged the product is `dirichlet_telescope`'s face of the counts; with deaths
`dirichlet_telescope_le` bounds it. Aeons without births (a birth adds `log₂(M_n/M)` to its aeon,
`evolved_code_with_births`). -/
theorem evolved_aeons_code {w : ℚ} (hw0 : 0 < w) (hw1 : w ≤ 1) (s₀ : ι → ℕ) {σ : ℕ → ι → ℚ}
    (hσ : ∀ k x, 0 < σ k x) {P : ι → ℚ} (hP : IsPrior P) (sel : ℕ → ι) {F : ℕ → ι → ℕ → ℚ}
    (hF : ∀ k x t, 0 ≤ F k x t) (n : ℕ → ℕ) (hL : ∀ k, 0 < seqLik (F k (sel k)) (n k)) (K : ℕ) :
    ∑ k ∈ range K, -Real.logb 2 ((∏ t ∈ range (n k), fwdMix
        (evolved w (dirichletFace (aeonCounts s₀ sel k) (σ k)) P) (F k) idKernel t : ℚ) : ℝ) ≤
      K * -Real.logb 2 (w : ℝ) -
        Real.logb 2 ((∏ k ∈ range K, dirichletFace (aeonCounts s₀ sel k) (σ k) (sel k) : ℚ) : ℝ) -
        ∑ k ∈ range K, Real.logb 2 (seqLik (F k (sel k)) (n k) : ℝ) := by
  have : Nonempty ι := ⟨sel 0⟩
  have hD : ∀ k, 0 < dirichletFace (aeonCounts s₀ sel k) (σ k) (sel k) :=
    fun k => dirichletFace_pos _ (hσ k) _
  have hstep : ∀ k ∈ range K, -Real.logb 2 ((∏ t ∈ range (n k),
      fwdMix (evolved w (dirichletFace (aeonCounts s₀ sel k) (σ k)) P) (F k) idKernel t : ℚ) : ℝ) ≤
        -Real.logb 2 (w : ℝ) -
          Real.logb 2 (dirichletFace (aeonCounts s₀ sel k) (σ k) (sel k) : ℝ) -
          Real.logb 2 (seqLik (F k (sel k)) (n k) : ℝ) := by
    intro k _
    have hDp := dirichletFace_isPrior (aeonCounts s₀ sel k) (hσ k)
    have hx : 0 < evolved w (dirichletFace (aeonCounts s₀ sel k) (σ k)) P (sel k) := by
      unfold evolved
      have := mul_nonneg (sub_nonneg.2 hw1) (hP.1 (sel k))
      have := mul_pos hw0 (hD k)
      linarith
    have h1 := evolved_aeon_code hw0.le hw1 hDp hP (hF k) (n k) hx (hL k)
    have h2 := evolved_code_le_face hw0 hw1 (D := dirichletFace (aeonCounts s₀ sel k) (σ k))
      hP.1 (hD k)
    linarith
  refine (sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Rat.cast_prod, Real.logb_prod _ _ (fun k _ => by exact_mod_cast (hD k).ne'),
    sum_sub_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]

end Aeons

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

/-! ### The collapse is a standing for its certified future -/

variable {C : Type*}

/-- [definition] **A key family's step on a cell** `c` at its tick: each key's weight multiplies by
its face of the cell; past the admitted future `h` the collapsed family refuses the cell and nothing
moves. -/
def keyStep (f : κ → ℕ → C → ℚ) (h : ℕ) (c : C) (x : ℕ × (κ → ℚ)) : ℕ × (κ → ℚ) :=
  if x.1 < h then (x.1 + 1, fun k => x.2 k * f k x.1 c) else x

/-- [definition] **The receiver's reading of a class** at the family's tick: the mixture's mass of it
inside the admitted future, nothing past it. -/
def keyRead (f : κ → ℕ → C → ℚ) (h : ℕ) (c : C) (x : ℕ × (κ → ℚ)) : ℚ :=
  if x.1 < h then ∑ k, x.2 k * f k x.1 c else 0

/-- [definition] **The species collapse's retention**: the tick and each species' summed weight. -/
def speciesRetain (σ : κ → S) (x : ℕ × (κ → ℚ)) : ℕ × (S → ℚ) := (x.1, speciesWeight σ x.2)

/-- [definition] **The collapsed family's step**: each species at its representative's face. -/
def speciesStep (rep : S → κ) (f : κ → ℕ → C → ℚ) (h : ℕ) (c : C) (y : ℕ × (S → ℚ)) :
    ℕ × (S → ℚ) :=
  if y.1 < h then (y.1 + 1, fun s => y.2 s * f (rep s) y.1 c) else y

/-- [definition] **The collapsed family's reading.** -/
def speciesRead (rep : S → κ) (f : κ → ℕ → C → ℚ) (h : ℕ) (c : C) (y : ℕ × (S → ℚ)) : ℚ :=
  if y.1 < h then ∑ s, y.2 s * f (rep s) y.1 c else 0

omit [Fintype S] [DecidableEq κ] in
/-- A species' weight after a factor its members share is its weight times the factor. -/
theorem speciesWeight_mul (σ : κ → S) (rep : S → κ) (v g : κ → ℚ)
    (hg : ∀ k, g k = g (rep (σ k))) (s : S) :
    speciesWeight σ (fun k => v k * g k) s = speciesWeight σ v s * g (rep s) := by
  unfold speciesWeight
  rw [sum_mul]
  refine sum_congr rfl fun k hk => ?_
  show v k * g k = v k * g (rep s)
  rw [hg k, (mem_filter.1 hk).2]

omit [DecidableEq κ] in
/-- [proved-derived; formal-checked] **`species_collapse_standing`: the collapse is a standing for its
certified future.** When every key agrees with its species' representative at every tick `t < h` of
the admitted future and every cell, the retention `(t, W)` is a `Foundation/Standing.StandingLaw` of
the key family (`keyStep`, `keyRead`) for every cell word, reopened by the collapsed family. -/
theorem species_collapse_standing (σ : κ → S) (rep : S → κ) (f : κ → ℕ → C → ℚ) (h : ℕ)
    (hagree : ∀ k t c, t < h → f k t c = f (rep (σ k)) t c) :
    ∃ L : Holonics.Foundation.Standing.StandingLaw C C (ℕ × (κ → ℚ)) (ℕ × (S → ℚ)) ℚ,
      L.transport = keyStep f h ∧ L.observe = keyRead f h ∧ L.retain = speciesRetain σ ∧
        ∀ c w y, L.reopen c w y = speciesRead rep f h c
          (Holonics.Foundation.Chronology.transportWord (speciesStep rep f h) w y) := by
  refine Holonics.Foundation.Standing.statistical_sufficiency_gives_standing (keyRead f h)
    (keyStep f h) (speciesRetain σ) (speciesRead rep f h) (speciesStep rep f h) ?_ ?_
  · intro c x
    unfold keyRead speciesRead speciesRetain
    split_ifs with ht
    · rw [← sum_fiberwise univ σ (fun k => x.2 k * f k x.1 c)]
      refine sum_congr rfl fun s _ => ?_
      have := speciesWeight_mul σ rep x.2 (fun k => f k x.1 c) (fun k => hagree k x.1 c ht) s
      unfold speciesWeight at this
      exact this
    · rfl
  · intro c x
    unfold keyStep speciesStep speciesRetain
    split_ifs with ht
    · simp only [Prod.mk.injEq, true_and]
      funext s
      exact speciesWeight_mul σ rep x.2 (fun k => f k x.1 c) (fun k => hagree k x.1 c ht) s
    · rfl

end Species

/-! ### The whole-future signature -/

section Signature

variable {α : Type*}

/-- [definition] **The shift of a word** `u : ℕ → α`, one tick later. -/
def wordShift (u : ℕ → α) : ℕ → α := fun t => u (t + 1)

theorem wordShift_iterate (n : ℕ) (u : ℕ → α) : wordShift^[n] u = fun t => u (t + n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    funext t
    simp only [wordShift, add_assoc, add_comm 1 n]

/-- A word is a periodic point of the shift exactly when it is periodic. -/
theorem isPeriodicPt_wordShift_iff {n : ℕ} {u : ℕ → α} :
    Function.IsPeriodicPt wordShift n u ↔ Function.Periodic u n := by
  unfold Function.IsPeriodicPt Function.IsFixedPt
  rw [wordShift_iterate]
  exact ⟨fun h t => congrFun h t, fun h => funext h⟩

/-- [definition] **The least period of a word**: the least `d > 0` with `u(t + d) = u(t)` at every
tick, Mathlib's minimal period of the shift (zero for an aperiodic word). -/
def leastPeriod (u : ℕ → α) : ℕ := Function.minimalPeriod wordShift u

theorem leastPeriod_periodic (u : ℕ → α) : Function.Periodic u (leastPeriod u) :=
  isPeriodicPt_wordShift_iff.1 (Function.isPeriodicPt_minimalPeriod _ _)

theorem leastPeriod_pos {u : ℕ → α} {P : ℕ} (hP : 0 < P) (hu : Function.Periodic u P) :
    0 < leastPeriod u :=
  Function.minimalPeriod_pos_of_mem_periodicPts
    (Function.mk_mem_periodicPts hP (isPeriodicPt_wordShift_iff.2 hu))

/-- [proved-standard; formal-checked] **The least period of a periodic word divides each of its
periods.** -/
theorem leastPeriod_dvd {u : ℕ → α} {P : ℕ} (hu : Function.Periodic u P) : leastPeriod u ∣ P :=
  (isPeriodicPt_wordShift_iff.2 hu).minimalPeriod_dvd

theorem leastPeriod_le {u : ℕ → α} {P : ℕ} (hP : 0 < P) (hu : Function.Periodic u P) :
    leastPeriod u ≤ P :=
  (isPeriodicPt_wordShift_iff.2 hu).minimalPeriod_le hP

/-- [proved-derived; formal-checked] **Two periodic words agree forever exactly when their least
periods agree and they agree over one period.** Only one of the two need be declared periodic: a
word whose least period equals a positive one is periodic with it. -/
theorem agree_forever_iff {u v : ℕ → α} {P : ℕ} (hP : 0 < P) (hu : Function.Periodic u P) :
    (∀ t, u t = v t) ↔ leastPeriod u = leastPeriod v ∧ ∀ t < leastPeriod u, u t = v t := by
  constructor
  · intro h
    have : u = v := funext h
    subst this
    exact ⟨rfl, fun t _ => rfl⟩
  · rintro ⟨hd, hag⟩ t
    rw [← (leastPeriod_periodic u).map_mod_nat t, ← (leastPeriod_periodic v).map_mod_nat t, ← hd]
    exact hag _ (Nat.mod_lt _ (leastPeriod_pos hP hu))

/-- [definition] **The finite shift test** on one declared period `P` (Rust
`Emitters::signature`): `d` divides `P` and `u(t + d) = u(t)` wherever `t + d < P`. -/
def ShiftHolds (u : ℕ → α) (P d : ℕ) : Prop := d ∣ P ∧ ∀ t, t + d < P → u (t + d) = u t

/-- [proved-derived; formal-checked] **The finite test reads a period of the whole word**: on a
declared period `P`, a divisor `d` passes the test over the one period exactly when it is a period
of the whole future. -/
theorem shiftHolds_iff {u : ℕ → α} {P d : ℕ} (hP : 0 < P) (hu : Function.Periodic u P) :
    ShiftHolds u P d ↔ d ∣ P ∧ Function.Periodic u d := by
  constructor
  · rintro ⟨⟨m, hm⟩, h⟩
    refine ⟨⟨m, hm⟩, fun t => ?_⟩
    have hit : ∀ j x, x + d * j < P → u (x + d * j) = u x := by
      intro j
      induction j with
      | zero => intro x _; simp
      | succ j ih =>
        intro x hx
        have he : x + d * (j + 1) = x + d * j + d := by ring
        rw [he] at hx ⊢
        rw [h _ hx, ih x (lt_of_le_of_lt (Nat.le_add_right _ _) hx)]
    have hm1 : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · rw [h0, mul_zero] at hm; omega
      · exact h0
    have hD : d * (m - 1) + d = P := by
      rw [hm, ← Nat.mul_succ]; congr 1; omega
    have hred : ∀ x, u (x + P * (t / P)) = u x := fun x => by
      rw [mul_comm]; exact (hu.nat_mul (t / P)) x
    have ht : t = t % P + P * (t / P) := (Nat.mod_add_div t P).symm
    have hr : t % P < P := Nat.mod_lt _ hP
    rw [ht, show t % P + P * (t / P) + d = (t % P + d) + P * (t / P) by ring, hred, hred]
    by_cases hlt : t % P + d < P
    · exact h _ hlt
    · have hx : t % P + d = (t % P + d - P) + P := by omega
      rw [hx, hu]
      have hr' : t % P = (t % P + d - P) + d * (m - 1) := by omega
      rw [hr'] at hr ⊢
      rw [hit (m - 1) _ hr]
      congr 1
      omega
  · rintro ⟨hdvd, hper⟩
    exact ⟨hdvd, fun t _ => hper t⟩

/-- [proved-derived; formal-checked] **The least period is the least divisor passing the finite
test**: Rust `Emitters::signature`'s search `(1..=P).find(d ∣ P ∧ shift holds)` returns the least
period of the whole word. -/
theorem leastPeriod_isLeast {u : ℕ → α} {P : ℕ} (hP : 0 < P) (hu : Function.Periodic u P) :
    IsLeast {d | 0 < d ∧ ShiftHolds u P d} (leastPeriod u) := by
  refine ⟨⟨leastPeriod_pos hP hu, (shiftHolds_iff hP hu).2
    ⟨leastPeriod_dvd hu, leastPeriod_periodic u⟩⟩, ?_⟩
  rintro d ⟨hd, hs⟩
  exact leastPeriod_le hd ((shiftHolds_iff hP hu).1 hs).2

/-- [definition] **A word's whole-future signature**: its letters over one least period. -/
def signature (u : ℕ → α) : List α := (List.range (leastPeriod u)).map u

/-- [proved-derived; formal-checked] **The whole-future species check.** Two keys whose emitted
words are periodic have equal signatures exactly when they emit one class at every future tick
(Rust `Emitters::signature` under `AdmittedFuture::Whole`, compared as words). -/
theorem signature_eq_iff {u v : ℕ → α} {P : ℕ} (hP : 0 < P) (hu : Function.Periodic u P) :
    signature u = signature v ↔ ∀ t, u t = v t := by
  rw [agree_forever_iff hP hu]
  unfold signature
  constructor
  · intro h
    have hl := congrArg List.length h
    simp only [List.length_map, List.length_range] at hl
    refine ⟨hl, fun t ht => ?_⟩
    have := congrArg (fun l => l[t]?) h
    simp only [List.getElem?_map, List.getElem?_range ht, List.getElem?_range (hl ▸ ht),
      Option.map_some] at this
    exact Option.some.inj this
  · rintro ⟨hd, h⟩
    rw [← hd]
    exact List.map_congr_left (fun t ht => h t (List.mem_range.1 ht))

end Signature

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
#print axioms abstaining_face
#print axioms bornFace_eq
#print axioms abstaining_mixture
#print axioms abstaining_exists
#print axioms newborn_likelihood
#print axioms founded_likelihood
#print axioms newborn_code
#print axioms massPrior_isPrior
#print axioms founded_share
#print axioms founded_code
#print axioms evolved_code_with_births
#print axioms selection_telescope
#print axioms dirichlet_telescope
#print axioms dirichlet_telescope_counts
#print axioms dirichlet_telescope_le
#print axioms evolved_aeons_code
#print axioms speciesWeight_isPrior
#print axioms species_mixture
#print axioms species_face
#print axioms species_collapse_code
#print axioms species_split
#print axioms speciesWeight_mul
#print axioms species_collapse_standing
#print axioms leastPeriod_dvd
#print axioms agree_forever_iff
#print axioms shiftHolds_iff
#print axioms leastPeriod_isLeast
#print axioms signature_eq_iff

end Audit

end Holonics.Compression.Landmark.Context.Evolution
