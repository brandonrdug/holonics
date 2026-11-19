import Holonics.HNN.Encoding
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic

/-!
# The resident pair face: its rows are the whole table's rank gradient, and a binding moves each by its own term

The resident pair face of the October machine (Rust `hnn::moment::resident_pair_face::ResidentPairFace`, the file
`crates/holonics/src/hnn/moment/resident_pair_face.rs` at commit `d5ed4adc1`) keeps, beside the offset counts
`C[c, x, y]` of one ring at one offset (`c` the phase, `x` the current cell, `y` the earlier one), the derived series a
pair port with current reads `a_ρ`, earlier reads `b_ρ` and outputs `e_ρ` reads:

```text
W_c[ρ] = Σ_(x,y) C[c, x, y] a_ρ[x] b_ρ[y]      R_c[x][ρ] = Σ_y C[c, x, y] b_ρ[y]      L_c[y][ρ] = Σ_x C[c, x, y] a_ρ[x]
n_c = Σ_(x,y) C[c, x, y]                      S = Σ_(c,x,y) C[c, x, y]²             occupied = #{C[c, x, y] ≠ 0}
```

Its output series at phase `c` is `ν̂ Σ_ρ W_c[ρ] e_ρ` (`output_series`), and against a turned opening `h_c` its gradient
reads `ν̂ Σ_c W_c[ρ] h_c` for the outputs, `ν̂ Σ_c (e_ρ·h_c) R_c[x][ρ]` and `ν̂ Σ_c (e_ρ·h_c) L_c[y][ρ]` for the reads,
and the energy `ν̂² S` (`gradient`). The test oracle `hnn::reference::whole_pair_gradient` reads the same four from the
whole normalized table, slot by occupied slot, `C[c, x, y] ν̂` at unit modulus (`SourceMoment::normalized`).

[proved-derived; formal-checked] What is proved.

1. **The face's rows are the whole-table rank gradient.** The comparison `Φ = Σ_c ⟨h_c, ν̂ Σ_ρ W_c[ρ] e_ρ⟩` is affine
   in each coordinate of the port, with the face's rows as its coefficients: moving `e_ρ[o]`, `a_ρ[x]` or `b_ρ[y]` by
   `t` moves `Φ` by exactly `t` times the face's gradient entry (`pairing_shiftOutput`, `pairing_shiftCurrent`,
   `pairing_shiftEarlier`, over any commutative ring), so over `ℝ` each entry is the derivative
   (`hasDerivAt_shiftOutput`, `hasDerivAt_shiftCurrent`, `hasDerivAt_shiftEarlier`). A phase with no population adds
   nothing, as the Rust's skip assumes (`gradOutput_eq_populated`).
2. **Each equals the sum over occupied bindings** (`whole_pair_gradient`, joining `gradOutput_eq_whole`,
   `gradCurrent_eq_whole`, `gradEarlier_eq_whole`, `energy_eq_whole`): the three rank gradients and the energy read from
   the face's rows equal the oracle's sums over the slots with a nonzero count, at value `C ν̂`.
3. **A binding moves each series by its own term** (`bind_laws`): one count added at `(c₀, x₀, y₀)` adds
   `a_ρ[x₀] b_ρ[y₀]` to `W_(c₀)[ρ]`, `b_ρ[y₀]` to `R_(c₀)[x₀][ρ]`, `a_ρ[x₀]` to `L_(c₀)[y₀][ρ]`, one to `n_(c₀)` and to
   the pair population, `2 C_old + 1` to `S` with `C_old = C[c₀, x₀, y₀]` the count before the binding, as the Rust's
   caller passes it (`moment::bind_pair_count`), and one to the occupied count exactly when `C_old = 0`; every other
   phase and row is unchanged (`faceW_bind`, `faceR_bind`, `faceL_bind`, `phasePopulation_bind`, `pairPopulation_bind`,
   `sumSquares_bind`, `occupied_card_bind`). The build's `add` of a whole count is the same law with `k` in place of
   one (`faceW_add`, `faceR_add`, `faceL_add`).
4. **Joined to the pair read** (`pairRead_eq_face`, `pairRead_bind_face`): the port's bilinear form `portForm` reads a
   phase's counts as the face's output row at `ν̂ = 1` (`portForm_counts`), so `HNN/IndexedOpen.pairRead` of the counts
   is the face's rows carried back through the ring, and `HNN/Encoding.pair_read_counts_bind`'s step is the binding's
   own term `Σ_ρ a_ρ[x₀] b_ρ[y₀] e_ρ` carried back from phase `c₀`.

The computational object is the helical pair interaction: the offset moment read whole through the pair port. Of the
winding guide's six general objects this touches the pair (the offset counts and the port's reads) and faces and
placement (the face's rows and the gradient against the turned opening); the helix enters only through `back`, and the
cell holonomy, the tube and the tower thread stay attached.

Scope: the face at unit modulus over a commutative ring (over `ℚ` where it joins the pair read, over `ℝ` where a
derivative is read). The integer charts the Rust holds the reads on (numerators over one denominator, each family
normalized once) are the realization of these sums and are not modelled; nor are the leaky counts, the covector bound
`max |h|` over the occupied phases, the ray speeds, or the copy-on-write sharing of the rows.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ResidentPairFace

open Finset
open Holonics.HNN.IndexedOpen (pairPopulation pairRead)
open Holonics.HNN.Moment (back)

variable {A K O : Type*} [Fintype A] [DecidableEq A] [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O]

/-! ## 1. The port, the face's series and its gradient -/

/-- A pair port's reads: current reads `a_ρ`, earlier reads `b_ρ` (both over the alphabet) and outputs `e_ρ`. -/
structure Port (R A K O : Type*) where
  current : K → A → R
  earlier : K → A → R
  output : K → O → R

section Ring

variable {R : Type*} [CommRing R]

/-- `W_c[ρ] = Σ_(x,y) C[c, x, y] a_ρ[x] b_ρ[y]` (the Rust `weights`). -/
def faceW (C : ℕ → A → A → ℕ) (p : Port R A K O) (c : ℕ) (ρ : K) : R :=
  ∑ x, ∑ y, (C c x y : R) * p.current ρ x * p.earlier ρ y

/-- `R_c[x][ρ] = Σ_y C[c, x, y] b_ρ[y]` (the Rust `current` rows). -/
def faceR (C : ℕ → A → A → ℕ) (p : Port R A K O) (c : ℕ) (x : A) (ρ : K) : R :=
  ∑ y, (C c x y : R) * p.earlier ρ y

/-- `L_c[y][ρ] = Σ_x C[c, x, y] a_ρ[x]` (the Rust `earlier` rows). -/
def faceL (C : ℕ → A → A → ℕ) (p : Port R A K O) (c : ℕ) (y : A) (ρ : K) : R :=
  ∑ x, (C c x y : R) * p.current ρ x

/-- A phase's population `n_c`. -/
def phasePopulation (C : ℕ → A → A → ℕ) (c : ℕ) : ℕ := ∑ x, ∑ y, C c x y

/-- The sum of squares `S = Σ_(c<d,x,y) C[c, x, y]²`. -/
def sumSquares (d : ℕ) (C : ℕ → A → A → ℕ) : ℕ := ∑ c ∈ range d, ∑ x, ∑ y, C c x y ^ 2

/-- The occupied bindings: the slots below the period with a nonzero count. -/
def occupied (d : ℕ) (C : ℕ → A → A → ℕ) : Finset (ℕ × A × A) :=
  (range d ×ˢ (univ : Finset (A × A))).filter fun s => C s.1 s.2.1 s.2.2 ≠ 0

/-- The face's output series at phase `c`: `ν̂ Σ_ρ W_c[ρ] e_ρ` (`output_series`). -/
def outputSeries (ν : R) (C : ℕ → A → A → ℕ) (p : Port R A K O) (c : ℕ) (o : O) : R :=
  ν * ∑ ρ, faceW C p c ρ * p.output ρ o

/-- The comparison against a turned opening `h`: `Φ = Σ_(c<d) ⟨h_c, outputSeries c⟩`. -/
def pairing (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) : R :=
  ∑ c ∈ range d, ∑ o, h c o * outputSeries ν C p c o

/-- `e_ρ · h_c`. -/
def outDot (p : Port R A K O) (h : ℕ → O → R) (ρ : K) (c : ℕ) : R := ∑ o, p.output ρ o * h c o

/-- The face's output gradient `ν̂ Σ_c W_c[ρ] h_c`. -/
def gradOutput (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) (ρ : K) (o : O) : R :=
  ν * ∑ c ∈ range d, faceW C p c ρ * h c o

/-- The face's current-read gradient `ν̂ Σ_c (e_ρ·h_c) R_c[x][ρ]`. -/
def gradCurrent (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) (ρ : K) (x : A) : R :=
  ν * ∑ c ∈ range d, outDot p h ρ c * faceR C p c x ρ

/-- The face's earlier-read gradient `ν̂ Σ_c (e_ρ·h_c) L_c[y][ρ]`. -/
def gradEarlier (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) (ρ : K) (y : A) : R :=
  ν * ∑ c ∈ range d, outDot p h ρ c * faceL C p c y ρ

/-- The face's energy `ν̂² S`. -/
def energy (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) : R := ν ^ 2 * (sumSquares d C : R)

/-! ## 2. The rows are the comparison's coefficients -/

omit [DecidableEq A] [DecidableEq K] [DecidableEq O] in
/-- The comparison in rank form: `Φ = ν̂ Σ_c Σ_ρ W_c[ρ] (e_ρ·h_c)`. -/
theorem pairing_eq (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) :
    pairing ν d C p h = ν * ∑ c ∈ range d, ∑ ρ, faceW C p c ρ * outDot p h ρ c := by
  simp only [pairing, outputSeries, outDot, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun o _ => ?_
  ring

/-- Move the output `e_(ρ₀)[o₀]` by `t`. -/
def Port.shiftOutput (p : Port R A K O) (ρ₀ : K) (o₀ : O) (t : R) : Port R A K O :=
  { p with output := fun ρ o => p.output ρ o + if ρ = ρ₀ ∧ o = o₀ then t else 0 }

/-- Move the current read `a_(ρ₀)[x₀]` by `t`. -/
def Port.shiftCurrent (p : Port R A K O) (ρ₀ : K) (x₀ : A) (t : R) : Port R A K O :=
  { p with current := fun ρ x => p.current ρ x + if ρ = ρ₀ ∧ x = x₀ then t else 0 }

/-- Move the earlier read `b_(ρ₀)[y₀]` by `t`. -/
def Port.shiftEarlier (p : Port R A K O) (ρ₀ : K) (y₀ : A) (t : R) : Port R A K O :=
  { p with earlier := fun ρ y => p.earlier ρ y + if ρ = ρ₀ ∧ y = y₀ then t else 0 }

omit [Fintype K] [Fintype O] [DecidableEq O] in
theorem faceW_shiftCurrent (C : ℕ → A → A → ℕ) (p : Port R A K O) (ρ₀ : K) (x₀ : A) (t : R) (c : ℕ) (ρ : K) :
    faceW C (p.shiftCurrent ρ₀ x₀ t) c ρ = faceW C p c ρ + if ρ = ρ₀ then t * faceR C p c x₀ ρ₀ else 0 := by
  have hterm : ∀ x y, (C c x y : R) * (p.current ρ x + if ρ = ρ₀ ∧ x = x₀ then t else 0) * p.earlier ρ y =
      (C c x y : R) * p.current ρ x * p.earlier ρ y +
        if ρ = ρ₀ ∧ x = x₀ then t * ((C c x y : R) * p.earlier ρ y) else 0 := by
    intro x y
    split_ifs <;> ring
  simp only [faceW, faceR, Port.shiftCurrent, hterm, Finset.sum_add_distrib]
  congr 1
  by_cases hρ : ρ = ρ₀
  · subst hρ
    simp only [true_and, if_true]
    rw [Finset.sum_eq_single x₀]
    · simp [Finset.mul_sum]
    · intro x _ hx
      simp [hx]
    · simp
  · simp [hρ]

omit [Fintype K] [Fintype O] [DecidableEq O] in
theorem faceW_shiftEarlier (C : ℕ → A → A → ℕ) (p : Port R A K O) (ρ₀ : K) (y₀ : A) (t : R) (c : ℕ) (ρ : K) :
    faceW C (p.shiftEarlier ρ₀ y₀ t) c ρ = faceW C p c ρ + if ρ = ρ₀ then t * faceL C p c y₀ ρ₀ else 0 := by
  have hterm : ∀ x y, (C c x y : R) * p.current ρ x * (p.earlier ρ y + if ρ = ρ₀ ∧ y = y₀ then t else 0) =
      (C c x y : R) * p.current ρ x * p.earlier ρ y +
        if ρ = ρ₀ ∧ y = y₀ then t * ((C c x y : R) * p.current ρ x) else 0 := by
    intro x y
    split_ifs <;> ring
  simp only [faceW, faceL, Port.shiftEarlier, hterm, Finset.sum_add_distrib]
  congr 1
  by_cases hρ : ρ = ρ₀
  · subst hρ
    simp [Finset.mul_sum]
  · simp [hρ]

omit [DecidableEq A] in
/-- **Moving an output moves the comparison by the face's output gradient**, exactly. -/
theorem pairing_shiftOutput (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R)
    (ρ₀ : K) (o₀ : O) (t : R) :
    pairing ν d C (p.shiftOutput ρ₀ o₀ t) h = pairing ν d C p h + t * gradOutput ν d C p h ρ₀ o₀ := by
  have hW : ∀ c ρ, faceW C (p.shiftOutput ρ₀ o₀ t) c ρ = faceW C p c ρ := fun _ _ => rfl
  have hD : ∀ ρ c, outDot (p.shiftOutput ρ₀ o₀ t) h ρ c =
      outDot p h ρ c + if ρ = ρ₀ then t * h c o₀ else 0 := by
    intro ρ c
    simp only [outDot, Port.shiftOutput, add_mul, Finset.sum_add_distrib]
    congr 1
    by_cases hρ : ρ = ρ₀
    · simp [hρ]
    · simp [hρ]
  rw [pairing_eq, pairing_eq, gradOutput]
  simp only [hW, hD, mul_add, Finset.sum_add_distrib, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

omit [DecidableEq O] in
/-- **Moving a current read moves the comparison by the face's current-read gradient**, exactly. -/
theorem pairing_shiftCurrent (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R)
    (ρ₀ : K) (x₀ : A) (t : R) :
    pairing ν d C (p.shiftCurrent ρ₀ x₀ t) h = pairing ν d C p h + t * gradCurrent ν d C p h ρ₀ x₀ := by
  have hD : ∀ ρ c, outDot (p.shiftCurrent ρ₀ x₀ t) h ρ c = outDot p h ρ c := fun _ _ => rfl
  have hR : ∀ c, faceR C (p.shiftCurrent ρ₀ x₀ t) c x₀ ρ₀ = faceR C p c x₀ ρ₀ := fun _ => rfl
  rw [pairing_eq, pairing_eq, gradCurrent]
  simp only [hD, faceW_shiftCurrent, add_mul, Finset.sum_add_distrib, mul_add, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

omit [DecidableEq O] in
/-- **Moving an earlier read moves the comparison by the face's earlier-read gradient**, exactly. -/
theorem pairing_shiftEarlier (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R)
    (ρ₀ : K) (y₀ : A) (t : R) :
    pairing ν d C (p.shiftEarlier ρ₀ y₀ t) h = pairing ν d C p h + t * gradEarlier ν d C p h ρ₀ y₀ := by
  have hD : ∀ ρ c, outDot (p.shiftEarlier ρ₀ y₀ t) h ρ c = outDot p h ρ c := fun _ _ => rfl
  rw [pairing_eq, pairing_eq, gradEarlier]
  simp only [hD, faceW_shiftEarlier, add_mul, Finset.sum_add_distrib, mul_add, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

omit [DecidableEq A] [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
/-- **A phase with no population adds nothing**: the output gradient is its sum over the populated phases, as the
Rust's skip of `p.population == 0` assumes. -/
theorem gradOutput_eq_populated (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R)
    (ρ : K) (o : O) :
    gradOutput ν d C p h ρ o =
      ν * ∑ c ∈ (range d).filter (fun c => phasePopulation C c ≠ 0), faceW C p c ρ * h c o := by
  rw [gradOutput, Finset.sum_filter]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with hc
  · rfl
  · have h0 : ∀ x y, C c x y = 0 := by
      intro x y
      have hsum : ∑ x, ∑ y, C c x y = 0 := not_not.mp hc
      exact (Finset.sum_eq_zero_iff.mp ((Finset.sum_eq_zero_iff.mp hsum) x (mem_univ _))) y (mem_univ _)
    simp [faceW, h0]

/-! ## 3. Each equals the sum over occupied bindings -/

/-- A phase's occupied slots `(x, y)`, `C[c, x, y] ≠ 0`. -/
def slots (C : ℕ → A → A → ℕ) (c : ℕ) : Finset (A × A) := univ.filter fun s => C c s.1 s.2 ≠ 0

/-- The oracle's output gradient: `Σ_c (Σ_occupied C ν̂ a_ρ[x] b_ρ[y]) h_c`. -/
def wholeOutput (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) (ρ : K) (o : O) : R :=
  ∑ c ∈ range d, (∑ s ∈ slots C c, (C c s.1 s.2 : R) * ν * p.current ρ s.1 * p.earlier ρ s.2) * h c o

/-- The oracle's current-read gradient: `Σ_c (e_ρ·h_c) Σ_(occupied, x) C ν̂ b_ρ[y]`. -/
def wholeCurrent (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) (ρ : K) (x : A) : R :=
  ∑ c ∈ range d, outDot p h ρ c *
    ∑ s ∈ slots C c, if s.1 = x then (C c s.1 s.2 : R) * ν * p.earlier ρ s.2 else 0

/-- The oracle's earlier-read gradient: `Σ_c (e_ρ·h_c) Σ_(occupied, y) C ν̂ a_ρ[x]`. -/
def wholeEarlier (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) (ρ : K) (y : A) : R :=
  ∑ c ∈ range d, outDot p h ρ c *
    ∑ s ∈ slots C c, if s.2 = y then (C c s.1 s.2 : R) * ν * p.current ρ s.1 else 0

/-- The oracle's energy: the squares of the occupied normalized values `C ν̂`. -/
def wholeEnergy (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) : R :=
  ∑ c ∈ range d, ∑ s ∈ slots C c, ((C c s.1 s.2 : R) * ν) ^ 2

omit [DecidableEq A] in
/-- A sum over a phase's occupied slots of terms that carry the count as a factor is the sum over every slot. -/
theorem sum_slots (C : ℕ → A → A → ℕ) (c : ℕ) (f : A × A → R) (hf : ∀ s, C c s.1 s.2 = 0 → f s = 0) :
    ∑ s ∈ slots C c, f s = ∑ x, ∑ y, f (x, y) := by
  rw [slots, Finset.sum_filter, ← Fintype.sum_prod_type']
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs with hs
  · rfl
  · exact (hf s (not_not.mp hs)).symm

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] [DecidableEq A] in
theorem gradOutput_eq_whole (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R)
    (ρ : K) (o : O) : gradOutput ν d C p h ρ o = wholeOutput ν d C p h ρ o := by
  rw [gradOutput, wholeOutput, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_slots C c _ (fun s hs => by simp [hs]), faceW]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

omit [Fintype K] [DecidableEq K] [DecidableEq O] in
theorem gradCurrent_eq_whole (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R)
    (ρ : K) (x : A) : gradCurrent ν d C p h ρ x = wholeCurrent ν d C p h ρ x := by
  rw [gradCurrent, wholeCurrent, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_slots C c _ (fun s hs => by simp [hs]), Finset.sum_eq_single x]
  · dsimp only
    simp only [if_true, faceR, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  · intro x' _ hx'
    simp [hx']
  · simp

omit [Fintype K] [DecidableEq K] [DecidableEq O] in
theorem gradEarlier_eq_whole (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R)
    (ρ : K) (y : A) : gradEarlier ν d C p h ρ y = wholeEarlier ν d C p h ρ y := by
  rw [gradEarlier, wholeEarlier, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_slots C c _ (fun s hs => by simp [hs])]
  dsimp only
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, faceL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

omit [DecidableEq A] in
theorem energy_eq_whole (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) : energy ν d C = wholeEnergy ν d C := by
  rw [energy, wholeEnergy, sumSquares]
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sum_slots C c _ (fun s hs => by simp [hs]), Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring

omit [Fintype K] [DecidableEq K] [DecidableEq O] in
/-- **`whole_pair_gradient`**: the face's three rank gradients and its energy, read from its rows, equal the whole
table's sums over the occupied bindings at value `C ν̂`. -/
theorem whole_pair_gradient (ν : R) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) (h : ℕ → O → R) :
    (∀ ρ o, gradOutput ν d C p h ρ o = wholeOutput ν d C p h ρ o) ∧
      (∀ ρ x, gradCurrent ν d C p h ρ x = wholeCurrent ν d C p h ρ x) ∧
      (∀ ρ y, gradEarlier ν d C p h ρ y = wholeEarlier ν d C p h ρ y) ∧
      energy ν d C = wholeEnergy ν d C :=
  ⟨gradOutput_eq_whole ν d C p h, gradCurrent_eq_whole ν d C p h, gradEarlier_eq_whole ν d C p h,
    energy_eq_whole ν d C⟩

/-! ## 4. A binding moves each series by its own term -/

/-- `k` counts added at `(c₀, x₀, y₀)` (the build's `add`); `k = 1` is a binding. -/
def addCounts (C : ℕ → A → A → ℕ) (c₀ : ℕ) (x₀ y₀ : A) (k : ℕ) : ℕ → A → A → ℕ :=
  fun c x y => C c x y + if c = c₀ ∧ x = x₀ ∧ y = y₀ then k else 0

/-- One binding, in the form `HNN/Encoding.pair_read_counts_bind` reads. -/
abbrev bindCounts (C : ℕ → A → A → ℕ) (c₀ : ℕ) (x₀ y₀ : A) : ℕ → A → A → ℕ := addCounts C c₀ x₀ y₀ 1

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
theorem faceW_add (C : ℕ → A → A → ℕ) (p : Port R A K O) (c₀ : ℕ) (x₀ y₀ : A) (k : ℕ) (c : ℕ) (ρ : K) :
    faceW (addCounts C c₀ x₀ y₀ k) p c ρ =
      faceW C p c ρ + if c = c₀ then (k : R) * p.current ρ x₀ * p.earlier ρ y₀ else 0 := by
  simp only [faceW, addCounts, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  by_cases hc : c = c₀
  · simp [hc, ite_and]
  · simp [hc]

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
theorem faceR_add (C : ℕ → A → A → ℕ) (p : Port R A K O) (c₀ : ℕ) (x₀ y₀ : A) (k : ℕ) (c : ℕ) (x : A) (ρ : K) :
    faceR (addCounts C c₀ x₀ y₀ k) p c x ρ =
      faceR C p c x ρ + if c = c₀ ∧ x = x₀ then (k : R) * p.earlier ρ y₀ else 0 := by
  simp only [faceR, addCounts, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  by_cases hc : c = c₀ ∧ x = x₀
  · obtain ⟨rfl, rfl⟩ := hc
    simp
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg (fun h => hc ⟨h.1, h.2.1⟩)]
    simp

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
theorem faceL_add (C : ℕ → A → A → ℕ) (p : Port R A K O) (c₀ : ℕ) (x₀ y₀ : A) (k : ℕ) (c : ℕ) (y : A) (ρ : K) :
    faceL (addCounts C c₀ x₀ y₀ k) p c y ρ =
      faceL C p c y ρ + if c = c₀ ∧ y = y₀ then (k : R) * p.current ρ x₀ else 0 := by
  simp only [faceL, addCounts, Nat.cast_add, add_mul, Finset.sum_add_distrib]
  congr 1
  by_cases hc : c = c₀ ∧ y = y₀
  · obtain ⟨rfl, rfl⟩ := hc
    simp
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [if_neg (fun h => hc ⟨h.1, h.2.2⟩)]
    simp

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
theorem faceW_bind (C : ℕ → A → A → ℕ) (p : Port R A K O) (c₀ : ℕ) (x₀ y₀ : A) (c : ℕ) (ρ : K) :
    faceW (bindCounts C c₀ x₀ y₀) p c ρ =
      faceW C p c ρ + if c = c₀ then p.current ρ x₀ * p.earlier ρ y₀ else 0 := by
  rw [faceW_add]
  simp

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
theorem faceR_bind (C : ℕ → A → A → ℕ) (p : Port R A K O) (c₀ : ℕ) (x₀ y₀ : A) (c : ℕ) (x : A) (ρ : K) :
    faceR (bindCounts C c₀ x₀ y₀) p c x ρ = faceR C p c x ρ + if c = c₀ ∧ x = x₀ then p.earlier ρ y₀ else 0 := by
  rw [faceR_add]
  simp

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
theorem faceL_bind (C : ℕ → A → A → ℕ) (p : Port R A K O) (c₀ : ℕ) (x₀ y₀ : A) (c : ℕ) (y : A) (ρ : K) :
    faceL (bindCounts C c₀ x₀ y₀) p c y ρ = faceL C p c y ρ + if c = c₀ ∧ y = y₀ then p.current ρ x₀ else 0 := by
  rw [faceL_add]
  simp

end Ring

theorem phasePopulation_bind (C : ℕ → A → A → ℕ) (c₀ : ℕ) (x₀ y₀ : A) (c : ℕ) :
    phasePopulation (bindCounts C c₀ x₀ y₀) c = phasePopulation C c + if c = c₀ then 1 else 0 := by
  simp only [phasePopulation, addCounts, Finset.sum_add_distrib]
  congr 1
  by_cases hc : c = c₀
  · simp [hc, ite_and]
  · simp [hc]

/-- The binding adds one to the pair population of `HNN/IndexedOpen`, below the period. -/
theorem pairPopulation_bind (d : ℕ) (C : ℕ → A → A → ℕ) {c₀ : ℕ} (hc : c₀ < d) (x₀ y₀ : A) :
    pairPopulation d (bindCounts C c₀ x₀ y₀) = pairPopulation d C + 1 := by
  have := fun c => phasePopulation_bind C c₀ x₀ y₀ c
  simp only [phasePopulation] at this
  simp only [pairPopulation, this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range, hc, if_true]

/-- **The sum of squares moves by `2 C_old + 1`**, `C_old` the count before the binding. -/
theorem sumSquares_bind (d : ℕ) (C : ℕ → A → A → ℕ) {c₀ : ℕ} (hc : c₀ < d) (x₀ y₀ : A) :
    sumSquares d (bindCounts C c₀ x₀ y₀) = sumSquares d C + (2 * C c₀ x₀ y₀ + 1) := by
  have key : ∀ c x y, (bindCounts C c₀ x₀ y₀ c x y) ^ 2 =
      C c x y ^ 2 + if c = c₀ ∧ x = x₀ ∧ y = y₀ then 2 * C c₀ x₀ y₀ + 1 else 0 := by
    intro c x y
    simp only [bindCounts, addCounts]
    split_ifs with h
    · obtain ⟨rfl, rfl, rfl⟩ := h
      ring
    · simp
  simp only [sumSquares, key, Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single c₀]
  · simp [ite_and]
  · intro c _ hc'
    simp [hc']
  · intro h
    exact absurd (Finset.mem_range.mpr hc) h

omit [DecidableEq A] in
theorem mem_occupied {d : ℕ} {C : ℕ → A → A → ℕ} {s : ℕ × A × A} :
    s ∈ occupied d C ↔ s.1 < d ∧ C s.1 s.2.1 s.2.2 ≠ 0 := by
  simp [occupied]

/-- The binding's slot joins the occupied set (where it already stood, the set is unchanged). -/
theorem occupied_bind (d : ℕ) (C : ℕ → A → A → ℕ) {c₀ : ℕ} (hc : c₀ < d) (x₀ y₀ : A) :
    occupied d (bindCounts C c₀ x₀ y₀) = insert (c₀, x₀, y₀) (occupied d C) := by
  ext ⟨c, x, y⟩
  simp only [mem_occupied, Finset.mem_insert, Prod.mk.injEq, bindCounts, addCounts]
  by_cases h : c = c₀ ∧ x = x₀ ∧ y = y₀
  · obtain ⟨rfl, rfl, rfl⟩ := h
    simp [hc]
  · rw [if_neg h, add_zero]
    simp only [h, false_or]

/-- **The occupied count moves by one exactly when the slot was empty.** -/
theorem occupied_card_bind (d : ℕ) (C : ℕ → A → A → ℕ) {c₀ : ℕ} (hc : c₀ < d) (x₀ y₀ : A) :
    (occupied d (bindCounts C c₀ x₀ y₀)).card = (occupied d C).card + if C c₀ x₀ y₀ = 0 then 1 else 0 := by
  rw [occupied_bind d C hc x₀ y₀]
  split_ifs with h0
  · exact Finset.card_insert_of_notMem (by simp [mem_occupied, h0])
  · rw [Finset.insert_eq_of_mem (by simp [mem_occupied, hc, h0]), add_zero]

omit [Fintype K] [DecidableEq K] [Fintype O] [DecidableEq O] in
/-- **The binding laws together**: one count at `(c₀, x₀, y₀)`, `c₀ < d`, moves `W`, `R`, `L`, `n` and `S` by
`a[x₀] b[y₀]`, `b[y₀]`, `a[x₀]`, one and `2 C_old + 1`, and the occupied count by one exactly when `C_old = 0`. -/
theorem bind_laws {R : Type*} [CommRing R] (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port R A K O) {c₀ : ℕ} (hc : c₀ < d)
    (x₀ y₀ : A) :
    (∀ ρ, faceW (bindCounts C c₀ x₀ y₀) p c₀ ρ = faceW C p c₀ ρ + p.current ρ x₀ * p.earlier ρ y₀) ∧
      (∀ ρ, faceR (bindCounts C c₀ x₀ y₀) p c₀ x₀ ρ = faceR C p c₀ x₀ ρ + p.earlier ρ y₀) ∧
      (∀ ρ, faceL (bindCounts C c₀ x₀ y₀) p c₀ y₀ ρ = faceL C p c₀ y₀ ρ + p.current ρ x₀) ∧
      phasePopulation (bindCounts C c₀ x₀ y₀) c₀ = phasePopulation C c₀ + 1 ∧
      sumSquares d (bindCounts C c₀ x₀ y₀) = sumSquares d C + (2 * C c₀ x₀ y₀ + 1) ∧
      (occupied d (bindCounts C c₀ x₀ y₀)).card = (occupied d C).card + if C c₀ x₀ y₀ = 0 then 1 else 0 := by
  refine ⟨fun ρ => by simp [faceW_bind], fun ρ => by simp [faceR_bind], fun ρ => by simp [faceL_bind],
    by simp [phasePopulation_bind], sumSquares_bind d C hc x₀ y₀, occupied_card_bind d C hc x₀ y₀⟩

/-! ## 5. Joined to the pair read -/

section Join

variable {S : Type*} [AddCommGroup S] [Module ℚ S]

/-- The port's bilinear form: a pair table `T` read as `Σ_ρ (a_ρᵀ T b_ρ) e_ρ`. -/
def portForm (p : Port ℚ A K O) : (A × A → ℚ) →ₗ[ℚ] (O → ℚ) where
  toFun T := fun o => ∑ ρ, (∑ x, ∑ y, T (x, y) * p.current ρ x * p.earlier ρ y) * p.output ρ o
  map_add' T T' := by
    funext o
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r T := by
    funext o
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ρ _ => Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring

omit [DecidableEq A] [DecidableEq K] [Fintype O] [DecidableEq O] in
/-- **The port reads a phase's counts as the face's output row** at `ν̂ = 1`. -/
theorem portForm_counts (C : ℕ → A → A → ℕ) (p : Port ℚ A K O) (c : ℕ) :
    portForm p (fun s => (C c s.1 s.2 : ℚ)) = outputSeries 1 C p c := by
  funext o
  simp [portForm, outputSeries, faceW]

omit [DecidableEq K] [Fintype O] [DecidableEq O] in
/-- The port's read of one binding is its own term `Σ_ρ a_ρ[x₀] b_ρ[y₀] e_ρ`. -/
theorem portForm_single (p : Port ℚ A K O) (x₀ y₀ : A) :
    portForm p (Pi.single (x₀, y₀) (1 : ℚ)) = fun o => ∑ ρ, p.current ρ x₀ * p.earlier ρ y₀ * p.output ρ o := by
  funext o
  simp only [portForm, LinearMap.coe_mk, AddHom.coe_mk]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  congr 1
  rw [Finset.sum_eq_single x₀, Finset.sum_eq_single y₀]
  · simp
  · intro y _ hy
    simp [Prod.ext_iff, hy]
  · simp
  · intro x _ hx
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [Prod.ext_iff, hx]
  · simp

omit [DecidableEq K] [Fintype O] [DecidableEq O] in
/-- **The pair read of the counts is the face's rows carried back through the ring.** -/
theorem pairRead_eq_face (P : (Module.End ℚ S)ˣ) (I : (O → ℚ) →ₗ[ℚ] S) (p : Port ℚ A K O) (d : ℕ)
    (C : ℕ → A → A → ℕ) :
    pairRead P I (portForm p) d (fun c x y => (C c x y : ℚ)) =
      ∑ c ∈ range d, back P c (I (outputSeries 1 C p c)) := by
  unfold pairRead
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← portForm_counts]
  have hT : (fun s : A × A => (C c s.1 s.2 : ℚ)) = ∑ x, ∑ y, (C c x y : ℚ) • Pi.single (x, y) (1 : ℚ) := by
    funext s
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single s.1, Finset.sum_eq_single s.2]
    · simp
    · intro y _ hy
      simp [Prod.ext_iff, Ne.symm hy]
    · simp
    · intro x _ hx
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [Prod.ext_iff, Ne.symm hx]
    · simp
  rw [hT]
  simp only [map_sum, map_smul]

omit [DecidableEq K] [Fintype O] [DecidableEq O] in
/-- **The binding's step on the pair read is its own term**, carried back from its phase:
`HNN/Encoding.pair_read_counts_bind` read through the port's form. -/
theorem pairRead_bind_face (P : (Module.End ℚ S)ˣ) (I : (O → ℚ) →ₗ[ℚ] S) (p : Port ℚ A K O) {d : ℕ}
    (C : ℕ → A → A → ℕ) {c₀ : ℕ} (hc : c₀ < d) (x₀ y₀ : A) :
    pairRead P I (portForm p) d (fun c x y => (bindCounts C c₀ x₀ y₀ c x y : ℚ)) =
      pairRead P I (portForm p) d (fun c x y => (C c x y : ℚ)) +
        back P c₀ (I (fun o => ∑ ρ, p.current ρ x₀ * p.earlier ρ y₀ * p.output ρ o)) := by
  rw [← portForm_single]
  exact Encoding.pair_read_counts_bind P I (portForm p) C hc x₀ y₀

end Join

/-! ## 6. Over `ℝ`, each row entry is the comparison's derivative -/

section Real

variable (ν : ℝ) (d : ℕ) (C : ℕ → A → A → ℕ) (p : Port ℝ A K O) (h : ℕ → O → ℝ)

omit [DecidableEq A] in
theorem hasDerivAt_shiftOutput (ρ₀ : K) (o₀ : O) (t : ℝ) :
    HasDerivAt (fun s => pairing ν d C (p.shiftOutput ρ₀ o₀ s) h) (gradOutput ν d C p h ρ₀ o₀) t := by
  simp only [pairing_shiftOutput]
  simpa using ((hasDerivAt_id t).mul_const (gradOutput ν d C p h ρ₀ o₀)).const_add (pairing ν d C p h)

omit [DecidableEq O] in
theorem hasDerivAt_shiftCurrent (ρ₀ : K) (x₀ : A) (t : ℝ) :
    HasDerivAt (fun s => pairing ν d C (p.shiftCurrent ρ₀ x₀ s) h) (gradCurrent ν d C p h ρ₀ x₀) t := by
  simp only [pairing_shiftCurrent]
  simpa using ((hasDerivAt_id t).mul_const (gradCurrent ν d C p h ρ₀ x₀)).const_add (pairing ν d C p h)

omit [DecidableEq O] in
theorem hasDerivAt_shiftEarlier (ρ₀ : K) (y₀ : A) (t : ℝ) :
    HasDerivAt (fun s => pairing ν d C (p.shiftEarlier ρ₀ y₀ s) h) (gradEarlier ν d C p h ρ₀ y₀) t := by
  simp only [pairing_shiftEarlier]
  simpa using ((hasDerivAt_id t).mul_const (gradEarlier ν d C p h ρ₀ y₀)).const_add (pairing ν d C p h)

end Real

end Holonics.HNN.ResidentPairFace
