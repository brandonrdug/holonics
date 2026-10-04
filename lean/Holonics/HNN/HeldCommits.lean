import Holonics.HNN.DepositHold

/-!
# HNN.HeldCommits: the commits between two refines compose at held momentum

[definition] #62 (5975646405, item 2; record B §2.3–§2.4). Under the reception carry a commit
moves the constitution while the carried change stands (`hnn::word::WordBalance::commit_held`,
`hnn::word::PowerForm::held`). Each carried contact and resonator keeps its position `u` and holds
its momentum: its rate moves to `w′` with `C′ w′ = C w` (`held_rate`, `held_resonator_rate`; for a
resonator `K` is the pumped stiffness at its carried phase). The waves stay: ring storage on its
admittance, arrivals on their conductances. The commit's work is the deposit term on each held
locus (`DepositHold.depositTerm`) plus the same-state work of the waves, and the committed power is
the power before plus that work (`WordBalance::closes` under `commit_held`). Between two refines
the resident may commit several staged deposits `c_1 … c_m` (`m ≥ 0`), each on the change the last
one left.

[proved-derived; formal-checked] What is proved, for any finite set of held loci and of waves, each
locus in its own inner product space, every capacity symmetric, no sign and no invertibility
assumed.

1. **One commit closes** (`commit_closes`): `P_(j+1)(x_(j+1)) = P_j(x_j) + work_j`, the Rust's
   `committed == end + deposition` (`DepositHold.hold_energy` on every locus).
2. **The momentum is held across the chain** (`held_chain_momentum`): `C_m w_m = C_0 w_0` on every
   locus.
3. **The works telescope** (`commits_telescope`): `Σ_(j<m) work_j = P_m(x_m) − P_0(x_0)`. This sum
   is the `dep k` that `HNN/ChainedBalance.chain_telescopes` takes between word `k` and word
   `k + 1` (`commits_are_dep`).
4. **Commits compose: the chain is one held commit** (`commits_compose`): the summed work equals
   the work of the single commit from the first material to the last at the momentum the chain
   held. So the order of the staged commits and their grouping do not change the work, and the end
   power is a function of the held momentum alone: two rates holding one momentum in one symmetric
   mass store the same kinetic energy (`held_kinetic_unique`, `held_end_power_unique`), without
   invertibility.

`HNN/DepositHold`, `HNN/PumpCarry` and `HNN/ChainedBalance` are unchanged. No `sorry`, no `axiom`,
no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.HeldCommits

open Holonics.HNN.Propagation Holonics.HNN.DepositHold
open scoped BigOperators

/-! ## 1. One locus -/

section Locus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [proved-derived; formal-checked] **Two rates holding one momentum in one symmetric mass store
the same kinetic energy**: `C w₁ = C w₂` gives `⟨w₁, C w₁⟩ = ⟨w₂, C w₂⟩`, with no invertibility. -/
theorem held_kinetic_unique (C : E →L[ℝ] E) (hC : ∀ x y, inner ℝ (C x) y = inner ℝ x (C y))
    {w₁ w₂ : E} (h : C w₁ = C w₂) : inner ℝ w₁ (C w₁) = inner ℝ w₂ (C w₂) := by
  calc inner ℝ w₁ (C w₁) = inner ℝ w₁ (C w₂) := by rw [h]
    _ = inner ℝ (C w₁) w₂ := by rw [hC]
    _ = inner ℝ (C w₂) w₂ := by rw [h]
    _ = inner ℝ w₂ (C w₂) := real_inner_comm _ _

/-- [proved-derived; formal-checked] **The momentum is held along a chain of held commits**:
`C_(j+1) w_(j+1) = C_j w_j` at every commit gives `C_m w_m = C_0 w_0`. -/
theorem held_chain_momentum (C : ℕ → E →L[ℝ] E) (w : ℕ → E)
    (hheld : ∀ j, C (j + 1) (w (j + 1)) = C j (w j)) (m : ℕ) : C m (w m) = C 0 (w 0) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [hheld m, ih]

/-- [proved-derived; formal-checked] **One locus's held works telescope**: the energy at the last
material is the first plus every commit's deposit term. -/
theorem locus_telescope (C K : ℕ → E →L[ℝ] E)
    (hC : ∀ j x y, inner ℝ (C j x) y = inner ℝ x (C j y)) (u : E) (w : ℕ → E)
    (hheld : ∀ j, C (j + 1) (w (j + 1)) = C j (w j)) (m : ℕ) :
    contactEnergy (C m) (K m) u (w m) - contactEnergy (C 0) (K 0) u (w 0) =
      ∑ j ∈ Finset.range m,
        depositTerm (C j) (C (j + 1)) (K j) (K (j + 1)) u (w j) (w (j + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ← ih,
      ← hold_energy (C m) (C (m + 1)) (K m) (K (m + 1)) (hC m) u (w m) (w (m + 1)) (hheld m)]
    ring

/-- [proved-derived; formal-checked] **One locus's held commits compose**: their summed deposit
terms are the deposit term of the single held commit from the first material to the last. -/
theorem locus_compose (C K : ℕ → E →L[ℝ] E)
    (hC : ∀ j x y, inner ℝ (C j x) y = inner ℝ x (C j y)) (u : E) (w : ℕ → E)
    (hheld : ∀ j, C (j + 1) (w (j + 1)) = C j (w j)) (m : ℕ) :
    ∑ j ∈ Finset.range m,
        depositTerm (C j) (C (j + 1)) (K j) (K (j + 1)) u (w j) (w (j + 1)) =
      depositTerm (C 0) (C m) (K 0) (K m) u (w 0) (w m) := by
  rw [← locus_telescope C K hC u w hheld m,
    hold_energy (C 0) (C m) (K 0) (K m) (hC 0) u (w 0) (w m) (held_chain_momentum C w hheld m)]

end Locus

/-! ## 2. The whole carried change -/

section Field

variable {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ a, NormedAddCommGroup (E a)]
  [∀ a, InnerProductSpace ℝ (E a)]
variable {ω : Type*} [Fintype ω]

/-- [definition] **The power of the carried change at commit `j`**: the waves' power on their
coefficients `Y_j` (admittances times `h/4`, conductances times `h/4`) at their fixed squared
readings `q`, plus each held locus's storage at its material `(C_j, K_j)` (`PowerForm::power` and
`PowerForm::resonator_power`). -/
def power (Y : ℕ → ω → ℝ) (q : ω → ℝ) (C K : ℕ → (a : ι) → E a →L[ℝ] E a) (u : (a : ι) → E a)
    (w : ℕ → (a : ι) → E a) (j : ℕ) : ℝ :=
  ∑ i, Y j i * q i + ∑ a, contactEnergy (C j a) (K j a) (u a) (w j a)

/-- [definition] **The work of commit `j` at held momentum** (`PowerForm::held`'s `deposition`):
the waves' same-state work plus each held locus's deposit term. -/
def commitWork (Y : ℕ → ω → ℝ) (q : ω → ℝ) (C K : ℕ → (a : ι) → E a →L[ℝ] E a)
    (u : (a : ι) → E a) (w : ℕ → (a : ι) → E a) (j : ℕ) : ℝ :=
  ∑ i, (Y (j + 1) i - Y j i) * q i +
    ∑ a, depositTerm (C j a) (C (j + 1) a) (K j a) (K (j + 1) a) (u a) (w j a) (w (j + 1) a)

variable (Y : ℕ → ω → ℝ) (q : ω → ℝ) (C K : ℕ → (a : ι) → E a →L[ℝ] E a) (u : (a : ι) → E a)
  (w : ℕ → (a : ι) → E a)

/-- [proved-derived; formal-checked] **One commit at held momentum closes**: the committed power is
the power before plus the commit's work (`WordBalance::commit_held`, `WordBalance::closes`). -/
theorem commit_closes (hC : ∀ j a x y, inner ℝ (C j a x) y = inner ℝ x (C j a y))
    (hheld : ∀ j a, C (j + 1) a (w (j + 1) a) = C j a (w j a)) (j : ℕ) :
    power Y q C K u w (j + 1) = power Y q C K u w j + commitWork Y q C K u w j := by
  have hloc : ∀ a, contactEnergy (C (j + 1) a) (K (j + 1) a) (u a) (w (j + 1) a) =
      contactEnergy (C j a) (K j a) (u a) (w j a) +
        depositTerm (C j a) (C (j + 1) a) (K j a) (K (j + 1) a) (u a) (w j a) (w (j + 1) a) :=
    fun a => by
      rw [← hold_energy (C j a) (C (j + 1) a) (K j a) (K (j + 1) a) (hC j a) (u a) (w j a)
        (w (j + 1) a) (hheld j a)]
      ring
  simp only [power, commitWork, Finset.sum_congr rfl fun a _ => hloc a, Finset.sum_add_distrib,
    sub_mul, Finset.sum_sub_distrib]
  ring

/-- [proved-derived; formal-checked] **The commits between two refines telescope**: their summed
work is the change of the carried change's power from the first material to the last. -/
theorem commits_telescope (hC : ∀ j a x y, inner ℝ (C j a x) y = inner ℝ x (C j a y))
    (hheld : ∀ j a, C (j + 1) a (w (j + 1) a) = C j a (w j a)) (m : ℕ) :
    ∑ j ∈ Finset.range m, commitWork Y q C K u w j =
      power Y q C K u w m - power Y q C K u w 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, commit_closes Y q C K u w hC hheld m]
    ring

/-- [proved-derived; formal-checked] **The summed work is the `dep k` of the chained balance**:
the opening of word `k + 1` stands at the power of word `k`'s end plus the commits' summed work
(`HNN/ChainedBalance.chain_telescopes`'s `dep k`). -/
theorem commits_are_dep (hC : ∀ j a x y, inner ℝ (C j a x) y = inner ℝ x (C j a y))
    (hheld : ∀ j a, C (j + 1) a (w (j + 1) a) = C j a (w j a)) (m : ℕ) :
    power Y q C K u w m = power Y q C K u w 0 + ∑ j ∈ Finset.range m, commitWork Y q C K u w j := by
  rw [commits_telescope Y q C K u w hC hheld m]
  ring

/-- [proved-derived; formal-checked] **The commits compose into one held commit**: their summed
work is the work of the single commit from the first material to the last, at the momentum the
chain held (`C_m w_m = C_0 w_0` on every locus). -/
theorem commits_compose (hC : ∀ j a x y, inner ℝ (C j a x) y = inner ℝ x (C j a y))
    (hheld : ∀ j a, C (j + 1) a (w (j + 1) a) = C j a (w j a)) (m : ℕ) :
    (∀ a, C m a (w m a) = C 0 a (w 0 a)) ∧
      ∑ j ∈ Finset.range m, commitWork Y q C K u w j =
        ∑ i, (Y m i - Y 0 i) * q i +
          ∑ a, depositTerm (C 0 a) (C m a) (K 0 a) (K m a) (u a) (w 0 a) (w m a) := by
  refine ⟨fun a => held_chain_momentum (fun j => C j a) (fun j => w j a) (fun j => hheld j a) m,
    ?_⟩
  have hloc : ∀ a, contactEnergy (C m a) (K m a) (u a) (w m a) =
      contactEnergy (C 0 a) (K 0 a) (u a) (w 0 a) +
        depositTerm (C 0 a) (C m a) (K 0 a) (K m a) (u a) (w 0 a) (w m a) := fun a => by
    rw [← hold_energy (C 0 a) (C m a) (K 0 a) (K m a) (hC 0 a) (u a) (w 0 a) (w m a)
      (held_chain_momentum (fun j => C j a) (fun j => w j a) (fun j => hheld j a) m)]
    ring
  rw [commits_telescope Y q C K u w hC hheld m]
  simp only [power, Finset.sum_congr rfl fun a _ => hloc a, Finset.sum_add_distrib, sub_mul,
    Finset.sum_sub_distrib]
  ring

/-- [proved-derived; formal-checked] **The end power is a function of the held momentum**: any two
rates holding the first momentum in the last mass give the same end power, so the order of the
commits does not change where the chain stands. -/
theorem held_end_power_unique (hC : ∀ j a x y, inner ℝ (C j a x) y = inner ℝ x (C j a y))
    (m : ℕ) (w' : ℕ → (a : ι) → E a) (h : ∀ a, C m a (w' m a) = C m a (w m a)) :
    power Y q C K u w' m = power Y q C K u w m := by
  simp only [power, contactEnergy]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [held_kinetic_unique (C m a) (hC m a) (h a)]

end Field

end Holonics.HNN.HeldCommits
