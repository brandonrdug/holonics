import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.ZMod.Basic
import Holonics.Aeon.Clock.CarryWord
import Holonics.Holon.Complex

/-!
# The Harper chain: a ring chain with uniform cell holonomy is the almost-Mathieu operator

[definition] Source: #410's box "A library constitution equal to the Harper/almost-Mathieu
operator, with gap labels `N = s + tα` read from `CarryWord` and an edge receiver whose channel
count is `t`", item 3 of §4 of
`research/records/2026-10-05_THE_GHOST_LIVES_IN_THE_GAP_THE_JOINTS_OF_THE_LENS.md`, whose joint J1
names the missing term: "a constitution of the library (a ring chain with declared cell holonomy,
or the carry word's operator below) shown equal to the Harper/almost-Mathieu operator, with its
gap-labelling face `N = s + tα` read from `Aeon/Clock/CarryWord` and its edge receiver". The join
was first named in §9 item 3 of
`2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS`
("a rotation hears a fractal spectrum there, if a constitution is shown to equal the operator").
Owners extended: `Aeon/Clock/CarryWord` (`helixReading`, `carry`, `sum_carry`,
`sum_carry_eq_windings`), `Aeon/Clock/Winding` (`windings`, `openPhase`, `split_unique`) and
`Holon/Complex` (`IsWalk`, `walkTransport`: a cell given as a closed walk, read by the product of
its transports, whose connection incidence reads `hol − 1` there, `cell_curvature`). Atlas rows
read: `gap.label-chern-edge`, `pump.thouless-integer`, `cell.chern-winding`,
`rotation.three-distance`, `holonomy.cell-face`, `curvature.discrete-da-squared`,
`holonomy.ring-step-period` and `wave.density-long-wave-reading`.

**The constitution.** The sites are `ℤ × M`: a chain of rings along `n ∈ ℤ`, each ring read by
`m ∈ M` (`M = ℤ` for the plane, `M = ZMod L` for a cylinder of rings of `L` sites). A site has four
bonds (`Bond`). Along the chain a bond's transport is `1`; around the ring at column `n` it is the
turn `e^(2πiαn)` (`ringPhase`, the Landau gauge), and the reversed bond carries its inverse
(`transport`). The hopping operator `hop` sums, over the four bonds out of a site, the bond's
transport times the value at its head.

What is proved.

1. [proved-derived; formal-checked] **The cell holonomy is uniform.** The unit cell at `(n, m)` is a
   closed walk of four bonds (`cell`, `cell_isWalk`), and its transport is `e^(2πiα)` at every
   cell (`cell_holonomy`, in the owner's `walkTransport`). A reversed bond ends where the bond
   starts (`head_reverseEdge`) and carries the conjugate transport (`transport_reverseEdge`): the
   constitution is self-adjoint bond by bond.
2. [proved-standard; formal-checked] **Harper's equation.** For `ψ(n, m) = χ(m) φ(n)` with a ring
   character `χ(m + 1) = e^(iθ) χ(m)`, `(hop ψ)(n, m) = χ(m) (φ(n + 1) + φ(n − 1) +
   2cos(2παn + θ) φ(n))`: the almost-Mathieu operator at coupling one (`hop_ringBloch`; the
   operators `unitHopping`, `harperPotential`, `almostMathieu`). On the plane `χ(m) = e^(imθ)`
   (`hop_bloch`); on the cylinder `χ(m) = e^(2πikm/L)` and `θ = 2πk/L` (`hop_cylinder`, through
   Mathlib's `ZMod.toCircle`). [proved-derived; formal-checked] The potential reads the helix of
   `CarryWord` through its open phase alone: `2κ cos(2παn + 2πρ) =
   2κ cos(2π openPhase(helixReading α ρ n))` (`harperPotential_eq_openPhase`), so the potential
   sits on the circle and the carry word counts the windings it does not see.
3. [proved-standard; formal-checked] **The Bloch matrix at `α = p/q`.** The potential is
   `q`-periodic (`harperPotential_periodic`). On functions with `φ(n + q) = e^(ik) φ(n)`
   (`IsBloch`) the operator with unit hopping and any potential `v` acts on the cell `0, …, q − 1`
   as the `q × q` matrix `blochMatrix q v k`: `v` on the diagonal, `1` beside it, `e^(ik)` in the
   corner `(q − 1, 0)` and `e^(−ik)` in `(0, q − 1)` (`blochMatrix_mulVec`); at `q = 2` the two
   hoppings add (`blochMatrix_two_zero_one`). It is Hermitian (`blochMatrix_isHermitian`). With a
   `q`-periodic potential a Bloch function solves the equation on all of `ℤ` iff its cell is an
   eigenvector (`bloch_eigen_iff`, through `unitHopping_isBloch` and `IsBloch.eq_zero_of_cell`),
   and every cell vector extends to a Bloch function (`blochExtend_isBloch`, `blochExtend_cell`).
   Harper's matrix is `harperBloch p q θ k` (`harperBloch_isHermitian`, `hop_eq_harperBloch`,
   `harper_eigen_iff`).
4. [proved-standard; formal-checked] **Chambers' relation.** The transfer matrix
   `[[E − v_n, −1], [1, 0]]` (`transfer`) carries `(φ(n), φ(n − 1))` to `(φ(n + 1), φ(n))` along a
   solution, and their product over `j` columns (`monodromy`) carries `(φ(0), φ(−1))` to
   `(φ(j), φ(j − 1))` (`monodromy_mulVec`) with determinant one (`det_monodromy`). Its trace over one
   period is `Δ(E)` (`discriminant`), independent of `k`. A `2 × 2` matrix of determinant one with
   eigenvalue `μ` has trace `μ + μ⁻¹` (`trace_eq_of_eigen`), so for every `q ≥ 1` a nonzero Bloch
   solution at energy `E` has `Δ(E) = 2cos k` (`discriminant_eq_two_cos_of_bloch`) and every
   eigenvalue of `H(k)` is a root of `Δ(E) − 2cos k` (`discriminant_eq_two_cos_of_det`). Every root
   is an eigenvalue: the transfer over one period then has the eigenvalue `e^(ik)`, and the orbit of
   its eigenvector over the cell (`monodromy_succ_mulVec`) is an eigenvector of `H(k)`
   (`det_eq_zero_of_discriminant`). With a `q`-periodic potential, `E` is an eigenvalue of `H(k)`
   iff `Δ(E) = 2cos k` (`det_eq_zero_iff_discriminant`; for Harper, `harper_det_eq_zero_iff`). At
   `q = 2` and `q = 3` the polynomials agree: `det(E − H(k)) = Δ(E) − 2cos k` (`chambers_two`,
   `chambers_three`). Here `k` is the Bloch phase across one period, the corner entries' `e^(±ik)`;
   with a phase `κ` a site, `k = qκ` and the relation reads `Δ(E) − 2cos(qκ)`.
5. [proved-standard; formal-checked] **Gap labels (TKNN).** For coprime `p, q` and every `r ∈ ℤ`
   there is one `t ∈ ℤ` with `−q < 2t ≤ q` and `r ≡ tp (mod q)` (`IsGapLabel`, `exists_gapLabel`,
   `IsGapLabel.unique`, `existsUnique_gapLabel`), and with `s = (r − tp)/q` (`gapWhole`),
   `r = sq + tp` (`IsGapLabel.tknn`) and `r/q = s + t·(p/q)` (`IsGapLabel.density`): the gap's
   density `N = r/q` is `s + tα`. Witnesses: at `α = 1/3` the gaps `r = 1, 2` have `t = 1, −1` and
   `s = 0, 1` (`gapLabel_witness_third`); at `α = 2/5` the gap `r = 1` has `t = −2`, `s = 1`
   (`gapLabel_witness_two_fifths`).
6. [proved-derived; formal-checked] **The label read from the carry word.** For any real `α` and
   integers `s, t` with `N = s + tα ∈ [0, 1)`, `s = −windings(tα)` and `N = openPhase(tα)`
   (`label_split`, from the owner's `split_unique`), for every sign of `t`; on a TKNN label with
   `0 ≤ r < q` this is `IsGapLabel.split`. The windings are the carry word's from intercept `0`:
   for `t = k ≥ 0` the carries of the first `k` ticks (`windings_eq_sum_carry`, the owner's
   `sum_carry_eq_windings`), so `s = −Σ_(n<k) carry(α, 0, n)`
   (`IsGapLabel.whole_eq_neg_sum_carry`); for `t = −k < 0` the carries of the `k` ticks before
   tick `0` (`windings_neg_eq_sum_carry`, the owner's `sum_carry`), so
   `s = Σ_(i<k) carry(α, 0, −k + i)` (`IsGapLabel.whole_eq_sum_carry_before`). The label's whole
   part is the epoch count of the carry word over the `|t|` ticks between tick `0` and tick `t`,
   with the sign of `−t`; its slope part is the count of ticks; and the gap's density is the open
   phase the helix reads at tick `t`. Witnesses: at `α = 1/3`,
   `carry(1/3, 0, 0) = 0`, `carry(1/3, 0, −1) = 1`, `openPhase(1/3) = 1/3` and
   `openPhase(−1/3) = 2/3` (`carry_witness_third`); at `α = 2/5`,
   `carry(2/5, 0, −2) + carry(2/5, 0, −1) = 1` and `openPhase(−4/5) = 1/5`
   (`carry_witness_two_fifths`).

What is not claimed.

- Chambers' polynomial identity `det(E − H(k)) = Δ(E) − 2cos k` for general `q`: it is proved at
  `q = 2` and `q = 3`; for every `q` the two polynomials have the same roots (item 4), but their
  multiplicities, and so the identity of the two monic polynomials of degree `q`, are not
  written.
- The spectrum's form: the Cantor spectrum at irrational `α` (Avila–Jitomirskaya, the Ten Martini
  problem), and that the gap with label `t` is open (Avila, You and Zhou away from critical
  coupling).
- The integrated density of states as a spectral count: that `N = r/q` is the share of the
  spectrum below the `r`-th gap (each of the `q` bands of `H(θ, k)` carrying `1/q`) is not proved;
  item 5 is the Diophantine face of the label, not its spectral reading.
- The integer the gap carries: the Hall conductance `σ = t e²/h` and the Chern number of the filled
  bands (TKNN), `t = ∂N/∂α` (Středa), the edge receiver whose channel count is `t` (Hatsugai), and
  the Thouless pump of J2 (`pump.thouless-integer`). The box stays part done.

The computational object is the helical pair interaction read on the ring chain: each ring bond is
a pair contact whose transport is the turn `e^(2πiαn)` and each chain bond the identity, so the
pair leaves the turn `α` round every cell; the rate-`α` clock's helix gives the potential its open
phase and the carry word its windings. Of the winding guide's six general objects this touches the
helix (circle + carry: the potential reads the open phase, the label's whole part counts the
carries), the pair (the lock `p/q` at its coprime address; the label's slope is the residue of `r`
over `p` modulo `q`, centred), the cell holonomy (the uniform `e^(2πiα)` of every cell, read by the
owner's walk transport), faces and placement (the density face `N = s + tα` and its open phase) and
the tube (the chain of `q` columns and its transfer matrix round one period). The tower thread
stays attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Physics.HarperChain

open Complex (exp I)
open Real (pi)
open scoped Matrix
open Holonics.HolonCore (IsWalk walkTransport)
open Holonics.Aeon.Clock.Winding (windings openPhase split_unique)
open Holonics.Aeon.Clock.CarryWord (carry helixReading helixReading_eq sum_carry
  sum_carry_eq_windings)

/-! ## 1. The operators -/

/-- [definition] **Unit hopping with potential `v`** on the chain:
`(Hφ)(n) = φ(n + 1) + φ(n − 1) + v(n) φ(n)`. -/
def unitHopping (v : ℤ → ℝ) (φ : ℤ → ℂ) (n : ℤ) : ℂ := φ (n + 1) + φ (n - 1) + (v n : ℂ) * φ n

/-- [definition] **The almost-Mathieu potential** of coupling `κ`, frequency `α` and phase `θ`:
`2κ cos(2παn + θ)`. -/
def harperPotential (κ α θ : ℝ) (n : ℤ) : ℝ := 2 * κ * Real.cos (2 * pi * α * n + θ)

/-- [definition] **The almost-Mathieu operator**; at `κ = 1` it is Harper's. -/
def almostMathieu (κ α θ : ℝ) : (ℤ → ℂ) → ℤ → ℂ := unitHopping (harperPotential κ α θ)

/-- [proved-standard; formal-checked] Conjugation turns a real phase backwards. -/
theorem star_exp_real_mul_I (x : ℝ) : star (exp (x * I)) = exp (-(x * I)) := by
  rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-- [proved-standard; formal-checked] A turn and its inverse sum to twice the cosine. -/
theorem exp_add_exp_neg (k : ℝ) : exp (k * I) + exp (-(k * I)) = ((2 * Real.cos k : ℝ) : ℂ) := by
  push_cast
  rw [Complex.two_cos, neg_mul]

/-- [proved-standard; formal-checked] Two turns forwards and their inverses sum to twice the
cosine of the summed angle. -/
theorem phase_add_conj (x θ : ℝ) :
    exp (x * I) * exp (θ * I) + exp (-(x * I)) * exp (-(θ * I)) = (2 * Real.cos (x + θ) : ℝ) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  push_cast
  rw [Complex.two_cos]
  congr 1 <;> ring_nf

/-- [proved-derived; formal-checked] **The potential reads the helix's open phase.** With the phase
`θ = 2πρ`, the potential at column `n` is `2κ cos(2π openPhase(helixReading α ρ n))`: the whole
windings of the rate-`α` clock, which the carry word counts, do not enter it. -/
theorem harperPotential_eq_openPhase (κ α ρ : ℝ) (n : ℤ) :
    harperPotential κ α (2 * pi * ρ) n =
      2 * κ * Real.cos (2 * pi * openPhase (helixReading α ρ n)) := by
  rw [openPhase, Int.fract, helixReading_eq, mul_sub,
    show 2 * pi * (⌊(n : ℝ) * α + ρ⌋ : ℝ) = (⌊(n : ℝ) * α + ρ⌋ : ℝ) * (2 * pi) by ring,
    Real.cos_sub_int_mul_two_pi, harperPotential]
  congr 2
  ring

/-! ## 2. The ring chain, its constitution and its cell holonomy -/

/-- [definition] **The four bonds out of a site** of the ring chain: along the chain (`east`,
`west`) and around the ring (`north`, `south`). -/
inductive Bond
  | east
  | north
  | west
  | south
  deriving DecidableEq

/-- [definition] The reversed bond. -/
def Bond.reverse : Bond → Bond
  | .east => .west
  | .north => .south
  | .west => .east
  | .south => .north

section Lattice

variable {M : Type*} [AddGroupWithOne M]

/-- [definition] The site a bond leaves. -/
def tail (e : (ℤ × M) × Bond) : ℤ × M := e.1

/-- [definition] The site a bond reaches. -/
def head : (ℤ × M) × Bond → ℤ × M
  | (x, .east) => (x.1 + 1, x.2)
  | (x, .north) => (x.1, x.2 + 1)
  | (x, .west) => (x.1 - 1, x.2)
  | (x, .south) => (x.1, x.2 - 1)

/-- [definition] The bond traversed backwards: it leaves the head along the reversed direction. -/
def reverseEdge (e : (ℤ × M) × Bond) : (ℤ × M) × Bond := (head e, e.2.reverse)

/-- [proved-derived; formal-checked] A reversed bond ends where the bond starts. -/
theorem head_reverseEdge (e : (ℤ × M) × Bond) : head (reverseEdge e) = tail e := by
  obtain ⟨⟨n, m⟩, b⟩ := e
  cases b <;> simp [reverseEdge, head, tail, Bond.reverse]

/-- [definition] **The ring transport at column `n`**: the turn `e^(2πiαn)` (Landau gauge). -/
def ringPhase (α : ℝ) (n : ℤ) : ℂˣ :=
  Units.mk0 (exp ((2 * pi * α * n : ℝ) * I)) (Complex.exp_ne_zero _)

/-- [proved-derived; formal-checked] The ring transport's value. -/
theorem ringPhase_val (α : ℝ) (n : ℤ) :
    (ringPhase α n : ℂ) = exp ((2 * pi * α * n : ℝ) * I) := rfl

/-- [proved-derived; formal-checked] The inverse ring transport turns backwards. -/
theorem ringPhase_inv_val (α : ℝ) (n : ℤ) :
    ((ringPhase α n)⁻¹ : ℂˣ) = exp (-((2 * pi * α * n : ℝ) * I)) := by
  rw [Units.val_inv_eq_inv_val, ringPhase_val, Complex.exp_neg]

/-- [definition] **The constitution's transports**: `1` along the chain, the ring transport of the
bond's column around the ring, its inverse backwards. -/
def transport (α : ℝ) : (ℤ × M) × Bond → ℂˣ
  | (_, .east) => 1
  | (x, .north) => ringPhase α x.1
  | (_, .west) => 1
  | (x, .south) => (ringPhase α x.1)⁻¹

/-- [proved-derived; formal-checked] **The constitution is self-adjoint bond by bond**: a reversed
bond carries the conjugate transport. -/
theorem transport_reverseEdge (α : ℝ) (e : (ℤ × M) × Bond) :
    (transport α (reverseEdge e) : ℂ) = star (transport α e : ℂ) := by
  obtain ⟨⟨n, m⟩, b⟩ := e
  cases b <;> simp only [reverseEdge, head, transport, Bond.reverse, Units.val_one, star_one,
    ringPhase_inv_val, ringPhase_val, star_exp_real_mul_I]
  rw [Complex.star_def, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-- [definition] **The hopping operator** of the ring chain: over the four bonds out of a site,
the bond's transport times the value at its head. -/
def hop (α : ℝ) (ψ : ℤ × M → ℂ) (x : ℤ × M) : ℂ :=
  (transport α (x, .east) : ℂ) * ψ (head (x, .east)) +
    (transport α (x, .north) : ℂ) * ψ (head (x, .north)) +
    (transport α (x, .west) : ℂ) * ψ (head (x, .west)) +
    (transport α (x, .south) : ℂ) * ψ (head (x, .south))

/-- [proved-derived; formal-checked] The hopping operator written out. -/
theorem hop_apply (α : ℝ) (ψ : ℤ × M → ℂ) (n : ℤ) (m : M) :
    hop α ψ (n, m) = ψ (n + 1, m) + ψ (n - 1, m) + exp ((2 * pi * α * n : ℝ) * I) * ψ (n, m + 1) +
      exp (-((2 * pi * α * n : ℝ) * I)) * ψ (n, m - 1) := by
  simp only [hop, transport, head, Units.val_one, one_mul, ringPhase_val, ringPhase_inv_val]
  ring

/-- [definition] **The unit cell** at `(n, m)` as a walk of four bonds: east, north, west,
south. -/
def cell (n : ℤ) (m : M) : List ((ℤ × M) × Bond) :=
  [((n, m), .east), ((n + 1, m), .north), ((n + 1, m + 1), .west), ((n, m + 1), .south)]

/-- [proved-derived; formal-checked] The unit cell is a closed walk at its corner. -/
theorem cell_isWalk (n : ℤ) (m : M) : IsWalk tail head (n, m) (n, m) (cell n m) := by
  simp [cell, IsWalk, tail, head]

/-- [proved-derived; formal-checked] **Every unit cell has holonomy `e^(2πiα)`**: the ordered
product of the four transports round it (the owner's `walkTransport`) does not depend on the
cell. -/
theorem cell_holonomy (α : ℝ) (n : ℤ) (m : M) :
    walkTransport (transport α) (cell n m) = exp ((2 * pi * α : ℝ) * I) := by
  simp only [cell, walkTransport, transport, Units.val_one, one_mul, mul_one, ringPhase_val,
    ringPhase_inv_val]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- [proved-standard; formal-checked] **Harper's equation.** On `ψ(n, m) = χ(m) φ(n)` with a ring
character `χ(m + 1) = e^(iθ) χ(m)`, the ring chain acts as `χ(m)` times the almost-Mathieu
operator at coupling one and phase `θ`. -/
theorem hop_ringBloch (α θ : ℝ) (χ : M → ℂ) (hχ : ∀ m, χ (m + 1) = exp (θ * I) * χ m)
    (φ : ℤ → ℂ) (n : ℤ) (m : M) :
    hop α (fun x => χ x.2 * φ x.1) (n, m) = χ m * almostMathieu 1 α θ φ n := by
  have hm : χ (m - 1) = exp (-(θ * I)) * χ m := by
    have h := hχ (m - 1)
    rw [sub_add_cancel] at h
    rw [h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
  rw [hop_apply]
  dsimp only
  rw [hχ, hm, almostMathieu, unitHopping, harperPotential]
  have key := phase_add_conj (2 * pi * α * n) θ
  push_cast at key ⊢
  linear_combination (χ m * φ n) * key

end Lattice

/-- [proved-standard; formal-checked] **Harper's equation on the plane**: `ψ(n, m) = e^(imθ) φ(n)`.
-/
theorem hop_bloch (α θ : ℝ) (φ : ℤ → ℂ) (n m : ℤ) :
    hop α (fun x : ℤ × ℤ => exp ((x.2 * θ : ℝ) * I) * φ x.1) (n, m) =
      exp ((m * θ : ℝ) * I) * almostMathieu 1 α θ φ n := by
  refine hop_ringBloch α θ (fun m : ℤ => exp ((m * θ : ℝ) * I)) (fun m => ?_) φ n m
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- [proved-standard; formal-checked] **Harper's equation on a cylinder of `L`-site rings**: the
ring character `e^(2πikm/L)` gives the phase `θ = 2πk/L`. -/
theorem hop_cylinder (L : ℕ) [NeZero L] (α : ℝ) (k : ℤ) (φ : ℤ → ℂ) (n : ℤ) (m : ZMod L) :
    hop α (fun x : ℤ × ZMod L => (ZMod.toCircle ((k : ZMod L) * x.2) : ℂ) * φ x.1) (n, m) =
      (ZMod.toCircle ((k : ZMod L) * m) : ℂ) * almostMathieu 1 α (2 * pi * k / L) φ n := by
  refine hop_ringBloch α _ (fun m : ZMod L => (ZMod.toCircle ((k : ZMod L) * m) : ℂ))
    (fun m => ?_) φ n m
  rw [mul_add, mul_one, AddChar.map_add_eq_mul, Circle.coe_mul, ZMod.toCircle_intCast, mul_comm]
  congr 2
  push_cast
  ring

/-! ## 3. The Bloch matrix at a rational cell holonomy -/

/-- [proved-standard; formal-checked] **At `α = p/q` the potential is `q`-periodic.** -/
theorem harperPotential_periodic (κ θ : ℝ) {p : ℤ} {q : ℕ} (hq : 0 < q) (n : ℤ) :
    harperPotential κ ((p : ℝ) / q) θ (n + q) = harperPotential κ ((p : ℝ) / q) θ n := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have h : 2 * pi * ((p : ℝ) / q) * ((n + q : ℤ) : ℝ) + θ =
      2 * pi * ((p : ℝ) / q) * (n : ℝ) + θ + p * (2 * pi) := by
    push_cast
    field_simp
    ring
  rw [harperPotential, harperPotential, h, Real.cos_add_int_mul_two_pi]

/-- [definition] **A Bloch function** of period `q` and phase `k`: `φ(n + q) = e^(ik) φ(n)`. -/
def IsBloch (q : ℕ) (k : ℝ) (φ : ℤ → ℂ) : Prop := ∀ n, φ (n + q) = exp (k * I) * φ n

/-- [definition] **The Bloch matrix** `H(k)` of unit hopping with potential `v` on a cell of `q`
columns: `v` on the diagonal, `1` beside it, `e^(ik)` in the corner `(q − 1, 0)` and `e^(−ik)` in
`(0, q − 1)`. -/
def blochMatrix (q : ℕ) (v : ℤ → ℝ) (k : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.of fun i j =>
    ((if i = j then (v (i : ℕ) : ℂ) else 0) + (if (i : ℕ) + 1 = j then 1 else 0) +
      (if (j : ℕ) + 1 = i then 1 else 0) +
      (if (i : ℕ) + 1 = q ∧ (j : ℕ) = 0 then exp (k * I) else 0)) +
      (if (j : ℕ) + 1 = q ∧ (i : ℕ) = 0 then exp (-(k * I)) else 0)

/-- [proved-standard; formal-checked] **At `q = 2` the two hoppings add**: `H(k)₀₁ = 1 + e^(−ik)`. -/
theorem blochMatrix_two_zero_one (v : ℤ → ℝ) (k : ℝ) :
    blochMatrix 2 v k 0 1 = 1 + exp (-(k * I)) := by
  simp [blochMatrix]

/-- [proved-standard; formal-checked] **The Bloch matrix is Hermitian.** -/
theorem blochMatrix_isHermitian (q : ℕ) (v : ℤ → ℝ) (k : ℝ) : (blochMatrix q v k).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [blochMatrix, Matrix.of_apply, star_add, apply_ite star, star_zero, star_one,
    Complex.star_def, Complex.conj_ofReal]
  have e1 : starRingEnd ℂ (exp (k * I)) = exp (-(k * I)) := star_exp_real_mul_I k
  have e2 : starRingEnd ℂ (exp (-(k * I))) = exp (k * I) := by
    rw [← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]; ring_nf
  rw [e1, e2]
  by_cases h : i = j
  · subst h; ring
  · rw [if_neg (Ne.symm h), if_neg h]; ring

/-- [proved-standard; formal-checked] A sum over the cell picks the column a condition names. -/
theorem sum_ite_val_eq {q : ℕ} (a : ℕ) (f : ℕ → ℂ) :
    ∑ l : Fin q, (if a = (l : ℕ) then f l else 0) = if a < q then f a else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨a, h⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro hab
      exact hb (Fin.ext hab.symm)
    · simp
  · refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg]
    intro hal
    exact h (hal ▸ l.isLt)

/-- [proved-standard; formal-checked] **The operator reduces to the Bloch matrix**: on a Bloch
function the matrix acting on the cell `0, …, q − 1` is unit hopping read at the cell's columns. -/
theorem blochMatrix_mulVec {q : ℕ} (v : ℤ → ℝ) {k : ℝ} {φ : ℤ → ℂ} (hφ : IsBloch q k φ)
    (j : Fin q) :
    (blochMatrix q v k *ᵥ fun l : Fin q => φ ((l : ℕ) : ℤ)) j = unitHopping v φ ((j : ℕ) : ℤ) := by
  simp only [Matrix.mulVec, dotProduct, blochMatrix, Matrix.of_apply, add_mul, ite_mul, zero_mul,
    one_mul, Finset.sum_add_distrib]
  have hj := j.isLt
  have s1 : (∑ x : Fin q, if j = x then (v ((j : ℕ) : ℤ) : ℂ) * φ ((x : ℕ) : ℤ) else 0) =
      (v ((j : ℕ) : ℤ) : ℂ) * φ ((j : ℕ) : ℤ) := by
    rw [Finset.sum_ite_eq]; simp
  have s2 : (∑ x : Fin q, if (j : ℕ) + 1 = x then φ ((x : ℕ) : ℤ) else 0) =
      if (j : ℕ) + 1 < q then φ ((j : ℕ) + 1) else 0 := by
    rw [sum_ite_val_eq ((j : ℕ) + 1) (fun x : ℕ => φ (x : ℤ))]
    push_cast
    rfl
  have s3 : (∑ x : Fin q, if (x : ℕ) + 1 = j then φ ((x : ℕ) : ℤ) else 0) =
      if (j : ℕ) = 0 then 0 else φ ((j : ℕ) - 1) := by
    by_cases h0 : (j : ℕ) = 0
    · rw [if_pos h0]
      refine Finset.sum_eq_zero fun l _ => ?_
      rw [if_neg]
      omega
    · rw [if_neg h0]
      have hc : ∀ x : Fin q, ((x : ℕ) + 1 = j) ↔ ((j : ℕ) - 1 = x) := fun x => by omega
      simp only [hc]
      rw [sum_ite_val_eq ((j : ℕ) - 1) (fun x : ℕ => φ (x : ℤ)), if_pos (by omega)]
      congr 1
      omega
  have s4 : (∑ x : Fin q, if (j : ℕ) + 1 = q ∧ (x : ℕ) = 0 then exp (k * I) * φ ((x : ℕ) : ℤ)
      else 0) = if (j : ℕ) + 1 = q then exp (k * I) * φ 0 else 0 := by
    by_cases h1 : (j : ℕ) + 1 = q
    · simp only [h1, true_and, if_true]
      have hc : ∀ x : Fin q, ((x : ℕ) = 0) ↔ (0 = (x : ℕ)) := fun x => eq_comm
      simp only [hc]
      rw [sum_ite_val_eq 0 (fun x : ℕ => exp (k * I) * φ (x : ℤ)), if_pos (by omega)]
      simp
    · simp [h1]
  have s5 : (∑ x : Fin q, if (x : ℕ) + 1 = q ∧ (j : ℕ) = 0 then exp (-(k * I)) * φ ((x : ℕ) : ℤ)
      else 0) = if (j : ℕ) = 0 then exp (-(k * I)) * φ ((q : ℤ) - 1) else 0 := by
    by_cases h0 : (j : ℕ) = 0
    · simp only [h0, and_true, if_true]
      have hc : ∀ x : Fin q, ((x : ℕ) + 1 = q) ↔ (q - 1 = (x : ℕ)) := fun x => by omega
      simp only [hc]
      rw [sum_ite_val_eq (q - 1) (fun x : ℕ => exp (-(k * I)) * φ (x : ℤ)), if_pos (by omega)]
      congr 2
      omega
    · simp [h0]
  rw [s1, s2, s3, s4, s5, unitHopping]
  have hup : (if (j : ℕ) + 1 < q then φ ((j : ℕ) + 1) else 0) +
      (if (j : ℕ) + 1 = q then exp (k * I) * φ 0 else 0) = φ (((j : ℕ) : ℤ) + 1) := by
    by_cases h1 : (j : ℕ) + 1 = q
    · rw [if_neg (by omega), if_pos h1, zero_add, ← hφ 0, zero_add]
      congr 1
      omega
    · rw [if_pos (by omega), if_neg h1, add_zero]
  have hdown : (if (j : ℕ) = 0 then 0 else φ ((j : ℕ) - 1)) +
      (if (j : ℕ) = 0 then exp (-(k * I)) * φ ((q : ℤ) - 1) else 0) = φ (((j : ℕ) : ℤ) - 1) := by
    by_cases h0 : (j : ℕ) = 0
    · rw [if_pos h0, if_pos h0, zero_add, h0]
      have h := hφ (-1)
      rw [neg_add_eq_sub] at h
      rw [h, ← mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, one_mul]
      simp
    · rw [if_neg h0, if_neg h0, add_zero]
  linear_combination hup + hdown

/-- [proved-standard; formal-checked] A Bloch function vanishing at `r` vanishes at every
`r + qj`. -/
theorem IsBloch.add_mul_period {q : ℕ} {k : ℝ} {ψ : ℤ → ℂ} (hψ : IsBloch q k ψ) {r : ℤ}
    (hr : ψ r = 0) (j : ℤ) : ψ (r + q * j) = 0 := by
  induction j using Int.induction_on with
  | zero => simpa using hr
  | succ j ih =>
    rw [show r + (q : ℤ) * (j + 1) = r + q * j + q by ring, hψ, ih, mul_zero]
  | pred j ih =>
    have h := hψ (r + q * (-(j : ℤ) - 1))
    rw [show r + (q : ℤ) * (-(j : ℤ) - 1) + q = r + q * (-(j : ℤ)) by ring, ih] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (Complex.exp_ne_zero _)

/-- [proved-standard; formal-checked] **A Bloch function is fixed by its cell**: vanishing on
`0, …, q − 1` it vanishes on `ℤ`. -/
theorem IsBloch.eq_zero_of_cell {q : ℕ} (hq : 0 < q) {k : ℝ} {ψ : ℤ → ℂ} (hψ : IsBloch q k ψ)
    (h0 : ∀ j : Fin q, ψ ((j : ℕ) : ℤ) = 0) (n : ℤ) : ψ n = 0 := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  have hlt := Int.emod_lt_of_pos n hq'
  have hge := Int.emod_nonneg n hq'.ne'
  have hr : ψ (n % q) = 0 := by
    have := h0 ⟨(n % q).toNat, by omega⟩
    simpa [Int.toNat_of_nonneg (Int.emod_nonneg n hq'.ne')] using this
  have h := hψ.add_mul_period hr (n / q)
  rwa [Int.emod_add_mul_ediv] at h

/-- [proved-standard; formal-checked] Bloch functions of one phase are closed under difference. -/
theorem IsBloch.sub {q : ℕ} {k : ℝ} {φ ψ : ℤ → ℂ} (hφ : IsBloch q k φ) (hψ : IsBloch q k ψ) :
    IsBloch q k (φ - ψ) := fun n => by simp only [Pi.sub_apply, hφ n, hψ n]; ring

/-- [proved-standard; formal-checked] Bloch functions of one phase are closed under scaling. -/
theorem IsBloch.const_mul {q : ℕ} {k : ℝ} {φ : ℤ → ℂ} (hφ : IsBloch q k φ) (E : ℂ) :
    IsBloch q k (fun n => E * φ n) := fun n => by simp only [hφ n]; ring

/-- [proved-standard; formal-checked] With a `q`-periodic potential, unit hopping keeps the Bloch
phase. -/
theorem unitHopping_isBloch {q : ℕ} {v : ℤ → ℝ} (hv : ∀ n, v (n + q) = v n) {k : ℝ} {φ : ℤ → ℂ}
    (hφ : IsBloch q k φ) : IsBloch q k (unitHopping v φ) := fun n => by
  simp only [unitHopping]
  rw [show n + q + 1 = (n + 1) + q by ring, show n + q - 1 = (n - 1) + q by ring, hφ, hφ, hφ, hv]
  ring

/-- [proved-standard; formal-checked] **The eigenproblem reduces to the cell**: with a `q`-periodic
potential, a Bloch function solves `Hφ = Eφ` on `ℤ` iff its cell is an eigenvector of `H(k)`. -/
theorem bloch_eigen_iff {q : ℕ} (hq : 0 < q) {v : ℤ → ℝ} (hv : ∀ n, v (n + q) = v n) {k : ℝ}
    {φ : ℤ → ℂ} (hφ : IsBloch q k φ) (E : ℂ) :
    (∀ n, unitHopping v φ n = E * φ n) ↔
      blochMatrix q v k *ᵥ (fun l : Fin q => φ ((l : ℕ) : ℤ)) =
        E • fun l : Fin q => φ ((l : ℕ) : ℤ) := by
  constructor
  · intro h
    funext j
    rw [blochMatrix_mulVec v hφ j, h]
    rfl
  · intro h n
    have hB := (unitHopping_isBloch hv hφ).sub (hφ.const_mul E)
    have h0 : ∀ j : Fin q, (unitHopping v φ - fun n => E * φ n) ((j : ℕ) : ℤ) = 0 := by
      intro j
      have hj := congrFun h j
      rw [blochMatrix_mulVec v hφ j] at hj
      simp only [Pi.sub_apply, hj, Pi.smul_apply, smul_eq_mul, sub_self]
    exact sub_eq_zero.mp (hB.eq_zero_of_cell hq h0 n)

/-- [definition] **The Bloch extension** of a cell vector `u`: `φ(n) = e^(ik⌊n/q⌋) u(n mod q)`. -/
def blochExtend (q : ℕ) (k : ℝ) (u : Fin q → ℂ) (n : ℤ) : ℂ :=
  if h : 0 < q then
    exp ((k * (n / q : ℤ) : ℝ) * I) *
      u ⟨(n % q).toNat, by
        have := Int.emod_lt_of_pos n (show (0 : ℤ) < q by exact_mod_cast h)
        omega⟩
  else 0

/-- [proved-standard; formal-checked] The Bloch extension is a Bloch function. -/
theorem blochExtend_isBloch (q : ℕ) (k : ℝ) (u : Fin q → ℂ) : IsBloch q k (blochExtend q k u) := by
  intro n
  by_cases hq : 0 < q
  · have hq' : (q : ℤ) ≠ 0 := by exact_mod_cast hq.ne'
    have hd : (n + q) / q = n / q + 1 := by
      simpa using Int.add_mul_ediv_right n 1 hq'
    simp only [blochExtend, dif_pos hq, Int.add_emod_right, hd]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · simp [blochExtend, dif_neg hq]

/-- [proved-standard; formal-checked] The Bloch extension restricts to the cell vector. -/
theorem blochExtend_cell {q : ℕ} (k : ℝ) (u : Fin q → ℂ) (j : Fin q) :
    blochExtend q k u ((j : ℕ) : ℤ) = u j := by
  have hq : 0 < q := lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hj : ((j : ℕ) : ℤ) / q = 0 := Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast j.isLt)
  have hm : ((j : ℕ) : ℤ) % q = (j : ℕ) := Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  simp only [blochExtend, dif_pos hq, hj]
  simp [hm]

/-- [definition] **Harper's Bloch matrix** `H(θ, k)` at the cell holonomy `p/q`. -/
def harperBloch (p : ℤ) (q : ℕ) (θ k : ℝ) : Matrix (Fin q) (Fin q) ℂ :=
  blochMatrix q (harperPotential 1 ((p : ℝ) / q) θ) k

/-- [proved-standard; formal-checked] Harper's Bloch matrix is Hermitian. -/
theorem harperBloch_isHermitian (p : ℤ) (q : ℕ) (θ k : ℝ) : (harperBloch p q θ k).IsHermitian :=
  blochMatrix_isHermitian _ _ _

/-- [proved-standard; formal-checked] **The ring chain at `α = p/q` is Harper's Bloch matrix**: on
`ψ(n, m) = e^(imθ) φ(n)` with `φ` Bloch of phase `k`, the hopping operator at the cell's sites is
`e^(imθ)` times `H(θ, k)` acting on the cell. -/
theorem hop_eq_harperBloch {p : ℤ} {q : ℕ} (θ k : ℝ) {φ : ℤ → ℂ} (hφ : IsBloch q k φ) (m : ℤ)
    (j : Fin q) :
    hop ((p : ℝ) / q) (fun x : ℤ × ℤ => exp ((x.2 * θ : ℝ) * I) * φ x.1) (((j : ℕ) : ℤ), m) =
      exp ((m * θ : ℝ) * I) * (harperBloch p q θ k *ᵥ fun l : Fin q => φ ((l : ℕ) : ℤ)) j := by
  rw [hop_bloch, harperBloch, blochMatrix_mulVec _ hφ]
  rfl

/-- [proved-standard; formal-checked] **Harper's eigenproblem at `α = p/q` reduces to `H(θ, k)`.** -/
theorem harper_eigen_iff {p : ℤ} {q : ℕ} (hq : 0 < q) (θ k : ℝ) {φ : ℤ → ℂ} (hφ : IsBloch q k φ)
    (E : ℂ) :
    (∀ n, almostMathieu 1 ((p : ℝ) / q) θ φ n = E * φ n) ↔
      harperBloch p q θ k *ᵥ (fun l : Fin q => φ ((l : ℕ) : ℤ)) =
        E • fun l : Fin q => φ ((l : ℕ) : ℤ) :=
  bloch_eigen_iff hq (harperPotential_periodic 1 θ hq) hφ E

/-! ## 4. The transfer matrix and Chambers' relation -/

/-- [definition] **The transfer matrix** `[[a, −1], [1, 0]]` of one column, with `a = E − v(n)`
at energy `E`. -/
def transfer (a : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![a, -1; 1, 0]

/-- [definition] **The transfer over `j` columns**: `T_(j−1) ⋯ T_0`. -/
def monodromy (v : ℤ → ℝ) (E : ℂ) : ℕ → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | j + 1 => transfer (E - v j) * monodromy v E j

/-- [definition] **The discriminant** `Δ(E)`: the trace of the transfer over one period. -/
def discriminant (v : ℤ → ℝ) (q : ℕ) (E : ℂ) : ℂ := (monodromy v E q).trace

/-- [proved-standard; formal-checked] A transfer matrix has determinant one. -/
theorem det_transfer (a : ℂ) : (transfer a).det = 1 := by
  simp [transfer, Matrix.det_fin_two]

/-- [proved-standard; formal-checked] The transfer over `j` columns has determinant one. -/
theorem det_monodromy (v : ℤ → ℝ) (E : ℂ) (j : ℕ) : (monodromy v E j).det = 1 := by
  induction j with
  | zero => simp [monodromy]
  | succ j ih => rw [monodromy, Matrix.det_mul, det_transfer, ih, one_mul]

/-- [proved-standard; formal-checked] **The transfer carries a solution**: along `Hφ = Eφ` it takes
`(φ(0), φ(−1))` to `(φ(j), φ(j − 1))`. -/
theorem monodromy_mulVec {v : ℤ → ℝ} {E : ℂ} {φ : ℤ → ℂ} (hE : ∀ n, unitHopping v φ n = E * φ n)
    (j : ℕ) : monodromy v E j *ᵥ ![φ 0, φ (-1)] = ![φ j, φ ((j : ℤ) - 1)] := by
  induction j with
  | zero => simp [monodromy]
  | succ j ih =>
    rw [monodromy, ← Matrix.mulVec_mulVec, ih]
    have h := hE j
    simp only [unitHopping] at h
    ext i
    fin_cases i
    · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination -h
    · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **A `2 × 2` matrix of determinant one with eigenvalue `μ` has
trace `μ + μ⁻¹`.** -/
theorem trace_eq_of_eigen (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) {μ : ℂ} {w : Fin 2 → ℂ}
    (hw : w ≠ 0) (h : A *ᵥ w = μ • w) : A.trace = μ + μ⁻¹ := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  rw [Matrix.det_fin_two] at hA
  rw [Matrix.trace_fin_two]
  have key : A 0 0 * A 1 1 - A 0 1 * A 1 0 - μ * (A 0 0 + A 1 1) + μ ^ 2 = 0 := by
    by_cases hx : w 0 = 0
    · have hy : w 1 ≠ 0 := by
        intro hy; apply hw; ext i; fin_cases i <;> simp [hx, hy]
      apply (mul_eq_zero.mp _).resolve_left hy
      linear_combination (A 0 0 - μ) * h1 - A 1 0 * h0
    · apply (mul_eq_zero.mp _).resolve_left hx
      linear_combination (A 1 1 - μ) * h0 - A 0 1 * h1
  have hμ : μ ≠ 0 := by
    rintro rfl
    rw [hA] at key
    simp at key
  have h2 : μ * (A 0 0 + A 1 1) = μ ^ 2 + 1 := by linear_combination hA - key
  apply mul_left_cancel₀ hμ
  rw [mul_add μ μ, mul_inv_cancel₀ hμ]
  linear_combination h2

/-- [proved-standard; formal-checked] **A Bloch solution fixes the discriminant**: for every
`q ≥ 1`, a nonzero Bloch function of phase `k` solving `Hφ = Eφ` has `Δ(E) = 2cos k`. -/
theorem discriminant_eq_two_cos_of_bloch {q : ℕ} (hq : 0 < q) {v : ℤ → ℝ} {k : ℝ} {E : ℂ}
    {φ : ℤ → ℂ} (hφ : IsBloch q k φ) (hE : ∀ n, unitHopping v φ n = E * φ n)
    (hne : ∃ n, φ n ≠ 0) : discriminant v q E = ((2 * Real.cos k : ℝ) : ℂ) := by
  have hw : ![φ 0, φ (-1)] ≠ 0 := by
    intro hw0
    obtain ⟨n, hn⟩ := hne
    apply hn
    refine hφ.eq_zero_of_cell hq (fun j => ?_) n
    have h := monodromy_mulVec hE (j : ℕ)
    rw [hw0, Matrix.mulVec_zero] at h
    exact (congrFun h 0).symm
  have hM : monodromy v E q *ᵥ ![φ 0, φ (-1)] = exp (k * I) • ![φ 0, φ (-1)] := by
    rw [monodromy_mulVec hE q]
    have h0 := hφ 0
    have h1 := hφ (-1)
    rw [zero_add] at h0
    rw [neg_add_eq_sub] at h1
    ext i
    fin_cases i
    · simp [h0]
    · simp [h1]
  rw [discriminant, trace_eq_of_eigen _ (det_monodromy v E q) hw hM, ← Complex.exp_neg,
    exp_add_exp_neg]

/-- [proved-standard; formal-checked] **Every eigenvalue of `H(k)` is a root of
`Δ(E) − 2cos k`**, for every `q ≥ 1` and every `q`-periodic potential. -/
theorem discriminant_eq_two_cos_of_det {q : ℕ} (hq : 0 < q) {v : ℤ → ℝ} (hv : ∀ n, v (n + q) = v n)
    (k : ℝ) {E : ℂ} (hdet : (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det = 0) :
    discriminant v q E = ((2 * Real.cos k : ℝ) : ℂ) := by
  obtain ⟨u, hu, hEu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hφ := blochExtend_isBloch q k u
  have hcell : (fun l : Fin q => blochExtend q k u ((l : ℕ) : ℤ)) = u :=
    funext (blochExtend_cell k u)
  have hHu : blochMatrix q v k *ᵥ u = E • u := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hEu
    exact hEu.symm
  refine discriminant_eq_two_cos_of_bloch hq hφ ((bloch_eigen_iff hq hv hφ E).mpr ?_) ?_
  · rw [hcell]; exact hHu
  · by_contra hall
    push Not at hall
    apply hu
    funext j
    rw [← blochExtend_cell k u j, hall]
    rfl

/-- [proved-standard; formal-checked] One more column of the transfer: the upper entry steps by
the recursion, the lower entry takes the upper one. -/
theorem monodromy_succ_mulVec (v : ℤ → ℝ) (E : ℂ) (w : Fin 2 → ℂ) (j : ℕ) :
    (monodromy v E (j + 1) *ᵥ w) 0 =
        (E - v j) * (monodromy v E j *ᵥ w) 0 - (monodromy v E j *ᵥ w) 1 ∧
      (monodromy v E (j + 1) *ᵥ w) 1 = (monodromy v E j *ᵥ w) 0 := by
  rw [monodromy, ← Matrix.mulVec_mulVec]
  constructor
  · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **Every root of `Δ(E) − 2cos k` is an eigenvalue of
`H(k)`**, for every `q ≥ 1` and every potential: the transfer over one period has the eigenvalue
`e^(ik)`, and its eigenvector's orbit over the cell is an eigenvector of `H(k)`. -/
theorem det_eq_zero_of_discriminant {q : ℕ} (hq : 0 < q) (v : ℤ → ℝ) (k : ℝ) {E : ℂ}
    (hΔ : discriminant v q E = ((2 * Real.cos k : ℝ) : ℂ)) :
    (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det = 0 := by
  have hμ : exp (k * I) * exp (-(k * I)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hdetM : (monodromy v E q - exp (k * I) • (1 : Matrix (Fin 2) (Fin 2) ℂ)).det = 0 := by
    have hd := det_monodromy v E q
    rw [Matrix.det_fin_two] at hd
    have ht := hΔ
    rw [discriminant, Matrix.trace_fin_two, ← exp_add_exp_neg] at ht
    rw [Matrix.det_fin_two]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, sub_zero]
    linear_combination hd - exp (k * I) * ht - hμ
  obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdetM
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMw
  set a : ℕ → ℂ := fun j => (monodromy v E j *ᵥ w) 0 with ha
  set b : ℕ → ℂ := fun j => (monodromy v E j *ᵥ w) 1 with hb
  have ha0 : a 0 = w 0 := by simp [ha, monodromy]
  have hb0 : b 0 = w 1 := by simp [hb, monodromy]
  have haq : a q = exp (k * I) * w 0 := by simp only [ha, hMw]; simp
  have hbq : b q = exp (k * I) * w 1 := by simp only [hb, hMw]; simp
  have hstep : ∀ j : ℕ, a (j + 1) = (E - v j) * a j - b j ∧ b (j + 1) = a j :=
    fun j => monodromy_succ_mulVec v E w j
  set u : Fin q → ℂ := fun j => a j with hu
  have hφ := blochExtend_isBloch q k u
  have hcell : (fun l : Fin q => blochExtend q k u ((l : ℕ) : ℤ)) = u := funext (blochExtend_cell k u)
  have hφa : ∀ j : ℕ, j < q → blochExtend q k u (j : ℤ) = a j := fun j hj =>
    blochExtend_cell k u ⟨j, hj⟩
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨u, ?_, ?_⟩
  · intro hu0
    apply hw
    have h0 : a 0 = 0 := congrFun hu0 ⟨0, hq⟩
    have h1 : a (q - 1) = 0 := congrFun hu0 ⟨q - 1, by omega⟩
    have hbq' : b q = 0 := by
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      rw [(hstep q').2]
      simpa using h1
    rw [hbq] at hbq'
    have hw1 : w 1 = 0 := (mul_eq_zero.mp hbq').resolve_left (Complex.exp_ne_zero _)
    ext i
    fin_cases i
    · simpa [ha0] using h0
    · simpa using hw1
  · rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
    funext j
    have hmv := blochMatrix_mulVec v hφ j
    rw [hcell] at hmv
    rw [hmv, unitHopping, Pi.smul_apply, smul_eq_mul, hφa j j.isLt]
    have hj := j.isLt
    have hup : blochExtend q k u (((j : ℕ) : ℤ) + 1) = a ((j : ℕ) + 1) := by
      by_cases h1 : (j : ℕ) + 1 = q
      · rw [show ((j : ℕ) : ℤ) + 1 = 0 + q by omega, hφ, show (0 : ℤ) = ((0 : ℕ) : ℤ) by rfl,
          hφa 0 hq, h1, haq, ha0]
      · rw [show ((j : ℕ) : ℤ) + 1 = (((j : ℕ) + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hφa _ (by omega)
    have hdown : blochExtend q k u (((j : ℕ) : ℤ) - 1) = b j := by
      by_cases h0 : (j : ℕ) = 0
      · have h := hφ (-1)
        rw [show (-1 : ℤ) + q = ((q - 1 : ℕ) : ℤ) by omega, hφa _ (by omega)] at h
        have hb' : b q = a (q - 1) := by
          obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
          simpa using (hstep q').2
        rw [← hb', hbq] at h
        rw [h0, show ((0 : ℕ) : ℤ) - 1 = -1 by norm_num, hb0]
        exact ((mul_right_injective₀ (Complex.exp_ne_zero (k * I))) h).symm
      · obtain ⟨j', hj'⟩ : ∃ j', (j : ℕ) = j' + 1 := ⟨(j : ℕ) - 1, by omega⟩
        rw [hj', (hstep j').2, show (((j' + 1 : ℕ) : ℤ)) - 1 = (j' : ℤ) by push_cast; ring]
        exact hφa _ (by omega)
    rw [hup, hdown, (hstep j).1]
    ring

/-- [proved-standard; formal-checked] **Chambers' zero set for every `q ≥ 1`**: with a `q`-periodic
potential, `E` is an eigenvalue of `H(k)` iff `Δ(E) = 2cos k`. -/
theorem det_eq_zero_iff_discriminant {q : ℕ} (hq : 0 < q) {v : ℤ → ℝ} (hv : ∀ n, v (n + q) = v n)
    (k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin q) (Fin q) ℂ) - blochMatrix q v k).det = 0 ↔
      discriminant v q E = ((2 * Real.cos k : ℝ) : ℂ) :=
  ⟨discriminant_eq_two_cos_of_det hq hv k, det_eq_zero_of_discriminant hq v k⟩

/-- [proved-standard; formal-checked] **Chambers' zero set for Harper's matrix**: at `α = p/q`,
`E` is an eigenvalue of `H(θ, k)` iff `Δ(E) = 2cos k`. -/
theorem harper_det_eq_zero_iff {p : ℤ} {q : ℕ} (hq : 0 < q) (θ k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin q) (Fin q) ℂ) - harperBloch p q θ k).det = 0 ↔
      discriminant (harperPotential 1 ((p : ℝ) / q) θ) q E = ((2 * Real.cos k : ℝ) : ℂ) :=
  det_eq_zero_iff_discriminant hq (harperPotential_periodic 1 θ hq) k E

/-- [proved-standard; formal-checked] **Chambers' relation at `q = 2`**:
`det(E − H(k)) = Δ(E) − 2cos k`. -/
theorem chambers_two (v : ℤ → ℝ) (k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin 2) (Fin 2) ℂ) - blochMatrix 2 v k).det =
      discriminant v 2 E - ((2 * Real.cos k : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two, ← exp_add_exp_neg]
  have he : exp (-(k * I)) * exp (k * I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  simp [blochMatrix, discriminant, monodromy, transfer, Matrix.trace_fin_two]
  linear_combination (-1 : ℂ) * he

/-- [proved-standard; formal-checked] **Chambers' relation at `q = 3`**:
`det(E − H(k)) = Δ(E) − 2cos k`. -/
theorem chambers_three (v : ℤ → ℝ) (k : ℝ) (E : ℂ) :
    (E • (1 : Matrix (Fin 3) (Fin 3) ℂ) - blochMatrix 3 v k).det =
      discriminant v 3 E - ((2 * Real.cos k : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three, ← exp_add_exp_neg]
  have he : exp (-(k * I)) * exp (k * I) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  simp [blochMatrix, discriminant, monodromy, transfer]
  linear_combination (-(E - (v 1 : ℂ))) * he

/-! ## 5. Gap labels: the TKNN Diophantine equation -/

/-- [definition] **`t` labels the gap `r` of the lock `p/q`**: `−q/2 < t ≤ q/2` and
`r ≡ tp (mod q)`. -/
def IsGapLabel (p : ℤ) (q : ℕ) (r t : ℤ) : Prop :=
  -(q : ℤ) < 2 * t ∧ 2 * t ≤ q ∧ r ≡ t * p [ZMOD q]

/-- [proved-standard; formal-checked] **The label is unique** for coprime `p, q`. -/
theorem IsGapLabel.unique {p : ℤ} {q : ℕ} (hcop : IsCoprime (q : ℤ) p) {r t t' : ℤ}
    (ht : IsGapLabel p q r t) (ht' : IsGapLabel p q r t') : t = t' := by
  obtain ⟨h1, h2, h3⟩ := ht
  obtain ⟨h1', h2', h3'⟩ := ht'
  have hd : (q : ℤ) ∣ (t' - t) * p := by
    have := (h3.symm.trans h3')
    rw [Int.modEq_iff_dvd] at this
    rw [sub_mul]
    exact this
  have hd' := hcop.dvd_of_dvd_mul_right hd
  have h0 := Int.eq_zero_of_abs_lt_dvd hd' (by rw [abs_lt]; constructor <;> omega)
  omega

/-- [proved-standard; formal-checked] **Every gap has a label** for coprime `p, q`: the residue of
`r` over `p` modulo `q`, centred. -/
theorem exists_gapLabel {p : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) p) (r : ℤ) :
    ∃ t, IsGapLabel p q r t := by
  have hq' : (0 : ℤ) < q := by exact_mod_cast hq
  obtain ⟨a, b, hab⟩ := hcop
  have hlt := Int.emod_lt_of_pos (r * b) hq'
  have hge := Int.emod_nonneg (r * b) hq'.ne'
  have hdiv := Int.emod_add_mul_ediv (r * b) q
  have hmod : ∀ c : ℤ, r ≡ ((r * b) % q - c * q) * p [ZMOD q] := by
    intro c
    rw [Int.modEq_iff_dvd]
    refine ⟨-(r * a) - ((r * b) / q + c) * p, ?_⟩
    have ht : (r * b) % q = r * b - q * ((r * b) / q) := by linarith
    rw [ht]
    linear_combination r * hab
  by_cases h : 2 * ((r * b) % q) ≤ q
  · exact ⟨(r * b) % q, by omega, h, by simpa using hmod 0⟩
  · exact ⟨(r * b) % q - q, by omega, by omega, by simpa using hmod 1⟩

/-- [proved-standard; formal-checked] **TKNN**: for coprime `p, q` every gap `r` has exactly one
label `t` with `−q < 2t ≤ q`. -/
theorem existsUnique_gapLabel {p : ℤ} {q : ℕ} (hq : 0 < q) (hcop : IsCoprime (q : ℤ) p) (r : ℤ) :
    ∃! t, IsGapLabel p q r t := by
  obtain ⟨t, ht⟩ := exists_gapLabel hq hcop r
  exact ⟨t, ht, fun t' ht' => ht'.unique hcop ht⟩

/-- [definition] **The label's whole part** `s = (r − tp)/q`. -/
def gapWhole (p : ℤ) (q : ℕ) (r t : ℤ) : ℤ := (r - t * p) / q

/-- [proved-standard; formal-checked] **The TKNN equation** `r = sq + tp`. -/
theorem IsGapLabel.tknn {p : ℤ} {q : ℕ} {r t : ℤ} (ht : IsGapLabel p q r t) :
    r = gapWhole p q r t * q + t * p := by
  have hd : (q : ℤ) ∣ r - t * p := (Int.modEq_iff_dvd.mp ht.2.2.symm)
  rw [gapWhole, Int.ediv_mul_cancel hd]
  ring

/-- [proved-standard; formal-checked] **The gap's density is `N = r/q = s + tα`** at `α = p/q`. -/
theorem IsGapLabel.density {p : ℤ} {q : ℕ} (hq : 0 < q) {r t : ℤ} (ht : IsGapLabel p q r t) :
    (r : ℝ) / q = gapWhole p q r t + t * ((p : ℝ) / q) := by
  have hq' : (q : ℝ) ≠ 0 := by positivity
  have h := congrArg (fun z : ℤ => (z : ℝ)) ht.tknn
  push_cast at h
  rw [h]
  field_simp

/-- [proved-standard; formal-checked] Witness: at `α = 1/3` the gaps `r = 1, 2` have labels
`t = 1, −1` and whole parts `s = 0, 1`. -/
theorem gapLabel_witness_third :
    IsGapLabel 1 3 1 1 ∧ IsGapLabel 1 3 2 (-1) ∧ gapWhole 1 3 1 1 = 0 ∧ gapWhole 1 3 2 (-1) = 1 := by
  refine ⟨⟨by norm_num, by norm_num, by decide⟩, ⟨by norm_num, by norm_num, by decide⟩, by decide,
    by decide⟩

/-- [proved-standard; formal-checked] Witness: at `α = 2/5` the gap `r = 1` has label `t = −2` and
whole part `s = 1`. -/
theorem gapLabel_witness_two_fifths : IsGapLabel 2 5 1 (-2) ∧ gapWhole 2 5 1 (-2) = 1 :=
  ⟨⟨by norm_num, by norm_num, by decide⟩, by decide⟩

/-! ## 6. The label read from the carry word -/

/-- [proved-derived; formal-checked] **A density `N = s + tα` in `[0, 1)` is a split of the helix
reading `tα`**: `s = −windings(tα)` and `N = openPhase(tα)`, for every sign of `t`. -/
theorem label_split {α N : ℝ} {s t : ℤ} (hN : N = s + t * α) (h0 : 0 ≤ N) (h1 : N < 1) :
    s = -windings ((t : ℝ) * α) ∧ N = openPhase ((t : ℝ) * α) := by
  have h := split_unique (t := (t : ℝ) * α) (-s) N (by push_cast; linarith) h0 h1
  exact ⟨by omega, h.2⟩

/-- [proved-derived; formal-checked] **The windings of `kα`, `k ≥ 0`, are the carries of the
first `k` ticks** from intercept `0`. -/
theorem windings_eq_sum_carry (α : ℝ) (k : ℕ) :
    windings ((k : ℤ) * α : ℝ) = ∑ i ∈ Finset.range k, carry α 0 i := by
  rw [sum_carry_eq_windings]
  rfl

/-- [proved-derived; formal-checked] **The windings of `−kα` are minus the carries of the `k` ticks
before tick `0`.** -/
theorem windings_neg_eq_sum_carry (α : ℝ) (k : ℕ) :
    -windings ((-(k : ℤ) : ℤ) * α : ℝ) = ∑ i ∈ Finset.range k, carry α 0 (-(k : ℤ) + i) := by
  rw [sum_carry, neg_add_cancel, helixReading_eq, helixReading_eq]
  simp [windings]

/-- [proved-derived; formal-checked] **A TKNN label splits the helix reading**: for `0 ≤ r < q`,
`s = −windings(t p/q)` and `r/q = openPhase(t p/q)`. -/
theorem IsGapLabel.split {p : ℤ} {q : ℕ} (hq : 0 < q) {r t : ℤ} (ht : IsGapLabel p q r t)
    (hr0 : 0 ≤ r) (hrq : r < q) :
    gapWhole p q r t = -windings ((t : ℝ) * ((p : ℝ) / q)) ∧
      (r : ℝ) / q = openPhase ((t : ℝ) * ((p : ℝ) / q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  refine label_split (ht.density hq) (div_nonneg (by exact_mod_cast hr0) hq'.le) ?_
  rw [div_lt_one hq']
  exact_mod_cast hrq

/-- [proved-derived; formal-checked] **For `t = k ≥ 0` the whole part is minus the carries of the
first `k` ticks** of the rate-`p/q` carry word from intercept `0`. -/
theorem IsGapLabel.whole_eq_neg_sum_carry {p : ℤ} {q : ℕ} (hq : 0 < q) {r t : ℤ}
    (ht : IsGapLabel p q r t) (hr0 : 0 ≤ r) (hrq : r < q) {k : ℕ} (hk : t = k) :
    gapWhole p q r t = -∑ i ∈ Finset.range k, carry ((p : ℝ) / q) 0 i := by
  rw [(ht.split hq hr0 hrq).1, ← windings_eq_sum_carry, hk]

/-- [proved-derived; formal-checked] **For `t = −k < 0` the whole part is the carries of the `k`
ticks before tick `0`.** -/
theorem IsGapLabel.whole_eq_sum_carry_before {p : ℤ} {q : ℕ} (hq : 0 < q) {r t : ℤ}
    (ht : IsGapLabel p q r t) (hr0 : 0 ≤ r) (hrq : r < q) {k : ℕ} (hk : t = -k) :
    gapWhole p q r t = ∑ i ∈ Finset.range k, carry ((p : ℝ) / q) 0 (-(k : ℤ) + i) := by
  rw [(ht.split hq hr0 hrq).1, ← windings_neg_eq_sum_carry, hk]

/-- [proved-derived; formal-checked] Witness at `α = 1/3`: the gap `r = 1` reads no carry over one
tick and the open phase `1/3`; the gap `r = 2` reads one carry over the tick before `0` and the open
phase `2/3`. -/
theorem carry_witness_third :
    carry (1 / 3) 0 0 = 0 ∧ carry (1 / 3) 0 (-1) = 1 ∧ openPhase (1 / 3 : ℝ) = 1 / 3 ∧
      openPhase (-(1 / 3) : ℝ) = 2 / 3 := by
  have h1 := gapLabel_witness_third.1.whole_eq_neg_sum_carry (by norm_num) (by norm_num)
    (by norm_num) (k := 1) rfl
  have h2 := gapLabel_witness_third.2.1.whole_eq_sum_carry_before (by norm_num) (by norm_num)
    (by norm_num) (k := 1) rfl
  have h3 := (gapLabel_witness_third.1.split (by norm_num) (by norm_num) (by norm_num)).2
  have h4 := (gapLabel_witness_third.2.1.split (by norm_num) (by norm_num) (by norm_num)).2
  rw [gapLabel_witness_third.2.2.1] at h1
  rw [gapLabel_witness_third.2.2.2] at h2
  norm_num at h1 h2 h3 h4
  refine ⟨by linarith, h2.symm, h3.symm, ?_⟩
  norm_num at h4 ⊢
  exact h4.symm

/-- [proved-derived; formal-checked] Witness at `α = 2/5`: the gap `r = 1` (label `t = −2`) reads
one carry over the two ticks before `0` and the open phase `1/5`. -/
theorem carry_witness_two_fifths :
    carry (2 / 5) 0 (-2) + carry (2 / 5) 0 (-1) = 1 ∧
      openPhase (-(4 / 5) : ℝ) = 1 / 5 := by
  have h1 := gapLabel_witness_two_fifths.1.whole_eq_sum_carry_before (by norm_num) (by norm_num)
    (by norm_num) (k := 2) rfl
  have h2 := (gapLabel_witness_two_fifths.1.split (by norm_num) (by norm_num) (by norm_num)).2
  rw [gapLabel_witness_two_fifths.2] at h1
  norm_num [Finset.sum_range_succ] at h1 h2
  exact ⟨by linarith, h2.symm⟩

end Holonics.Physics.HarperChain
