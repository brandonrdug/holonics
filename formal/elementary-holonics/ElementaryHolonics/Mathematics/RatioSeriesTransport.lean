import Mathlib

/-!
# Ratio-series transport

An exact rational series is carried by its current term and its partial sum.  A ratio word
acts on that pair; a compiled block keeps the two coefficients needed to replay the same
action.  The order of the word remains visible in the partial sum, even when the final term
commutes.
-/

namespace Soma.Holonics.Mathematics.RatioSeriesTransport

abbrev State := ℚ × ℚ

def step (r : ℚ) (s : State) : State := (r * s.1, s.2 + r * s.1)

def execute : List ℚ → State → State
  | [], s => s
  | r :: rs, s => execute rs (step r s)

structure Block where
  length : ℕ
  alpha : ℚ
  beta : ℚ

def Block.act (b : Block) (s : State) : State :=
  (b.alpha * s.1, s.2 + b.beta * s.1)

def Block.single (r : ℚ) : Block := ⟨1, r, r⟩

/- Composition is chronological: `compose first second` acts by first and then second. -/
def Block.compose (first second : Block) : Block :=
  ⟨first.length + second.length,
    second.alpha * first.alpha,
    first.beta + second.beta * first.alpha⟩

theorem step_eq_single_act (r : ℚ) (s : State) : step r s = (Block.single r).act s := by
  rfl

theorem compose_act (first second : Block) (s : State) :
    second.act (first.act s) = (first.compose second).act s := by
  simp [Block.act, Block.compose]
  constructor <;> ring

def compile : List ℚ → Block
  | [] => ⟨0, 1, 0⟩
  | r :: rs => (Block.single r).compose (compile rs)

theorem compile_length (rs : List ℚ) : (compile rs).length = rs.length := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [compile, Block.single, Block.compose, ih, Nat.add_comm]

theorem compile_act (rs : List ℚ) (s : State) : (compile rs).act s = execute rs s := by
  induction rs generalizing s with
  | nil => norm_num [compile, Block.act, execute]
  | cons r rs ih =>
      calc
        (compile (r :: rs)).act s =
            (compile rs).act ((Block.single r).act s) := by
              symm
              exact compose_act (Block.single r) (compile rs) s
        _ = execute rs ((Block.single r).act s) := ih _
        _ = execute (r :: rs) s := by rfl

theorem compile_preserves_length (rs : List ℚ) :
    (compile rs).length = rs.length := compile_length rs

theorem equal_blocks_same_receiver (b c : Block) (h : b = c) (rs : List ℚ) (s : State) :
    execute rs (b.act s) = execute rs (c.act s) := by
  rw [h]

theorem equal_blocks_preserve_every_ratio_word (b c : Block) (h : b = c) :
    ∀ rs : List ℚ, ∀ s : State, execute rs (b.act s) = execute rs (c.act s) := by
  intro rs s
  exact equal_blocks_same_receiver b c h rs s

/- Equal partial sums do not determine the next partial sum when the term differs. -/
theorem equal_partial_sums_different_next_sums :
    (step 1 (1, 0)).2 ≠ (step 1 (2, 0)).2 ∧
      (1, 0).2 = (2, 0).2 := by
  norm_num [step]

theorem two_steps_terms_commute (r q a S : ℚ) :
    (execute [q] (step r (a, S))).1 =
      (execute [r] (step q (a, S))).1 := by
  simp [execute, step]
  ring

theorem two_steps_sums_differ_by (r q a S : ℚ) :
    (execute [q] (step r (a, S))).2 -
        (execute [r] (step q (a, S))).2 = (r - q) * a := by
  simp [execute, step]
  ring

/- The arctangent power-series ratio, retained as an exact rational recurrence. -/
def arctanTerm (x : ℚ) (n : ℕ) : ℚ :=
  ((-1 : ℚ) ^ n) * x ^ (2 * n + 1) / (2 * n + 1)

def arctanRatio (x : ℚ) (n : ℕ) : ℚ :=
  -x ^ 2 * (2 * n + 1) / (2 * n + 3)

theorem arctanTerm_succ (x : ℚ) (n : ℕ) :
    arctanTerm x (n + 1) = arctanRatio x n * arctanTerm x n := by
  simp [arctanTerm, arctanRatio, pow_add]
  field_simp
  ring


/-- A future ratio may depend on the preserved series index. -/
abbrev ClockedState := ℕ × State

def Block.run (b : Block) (s : ClockedState) : ClockedState :=
  (s.1 + b.length, b.act s.2)

def continueSeries (ratio : ℕ → ℚ) : ℕ → ClockedState → ClockedState
  | 0, s => s
  | k + 1, s => continueSeries ratio k (s.1 + 1, step (ratio s.1) s.2)

theorem compiled_words_preserve_clocked_future
    (u v : List ℚ) (same : compile u = compile v)
    (ratio : ℕ → ℚ) (steps : ℕ) (s : ClockedState) :
    continueSeries ratio steps ((compile u).run s) =
      continueSeries ratio steps ((compile v).run s) := by rw [same]

theorem distinct_routes_same_block :
    compile [1, 1, 1] = compile [(1 : ℚ)/2, 3, (2 : ℚ)/3] := by
  norm_num [compile, Block.single, Block.compose]

theorem equal_block_different_interior :
    (step 1 (1, 0)).2 ≠ (step ((1 : ℚ)/2) (1, 0)).2 := by
  norm_num [step]

/-- A rational family of routes; the singular parameter values remain excluded explicitly. -/
theorem route_family (t : ℚ) (ht : t ≠ 0) (htwo : t ≠ 2) :
    compile [t, 2/t - 1, 1/(2-t)] = (⟨3,1,3⟩ : Block) := by
  have hden : 2-t ≠ 0 := sub_ne_zero.mpr (Ne.symm htwo)
  simp only [compile, Block.single, Block.compose]
  congr 1 <;> field_simp <;> ring

/-- Every three-event block has a family of rational factorizations with the same complete action. -/
theorem general_route_family (alpha beta t : ℚ) (ht : t ≠ 0)
    (hden : beta-alpha-t ≠ 0) :
    compile [t, (beta-alpha-t)/t, alpha/(beta-alpha-t)] =
      (⟨3,alpha,beta⟩ : Block) := by
  simp only [compile, Block.single, Block.compose]
  congr 1 <;> field_simp <;> ring

/-- A concrete bridge in the arctan(1/5) arm of a Machin presentation.
The interior terms differ; the complete three-event action and clock agree. -/
theorem arctan_fifth_three_event_bridge :
    compile [arctanRatio ((1 : ℚ)/5) 0, arctanRatio ((1 : ℚ)/5) 1,
      arctanRatio ((1 : ℚ)/5) 2] =
    compile [(-3 : ℚ)/125, (-721 : ℚ)/1575, (-3 : ℚ)/3605] := by
  norm_num [arctanRatio, compile, Block.single, Block.compose]

end Soma.Holonics.Mathematics.RatioSeriesTransport
