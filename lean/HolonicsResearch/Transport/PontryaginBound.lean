import Mathlib
import Holonics.Foundation.CausalChord
import Holonics.Transport.HolonicInteraction

/-!
# Signature placement: the Pontryagin bound, the on-axis dimension and the real spectrum

[proved-standard; formal-checked] A generator that keeps an indefinite nondegenerate storage form
`G` (`Aᴴ G + G A = 0`) can leave the imaginary axis only along `G`-null directions, and the
generalized eigenspaces on one side of the axis span a `G`-neutral subspace; a neutral subspace
has dimension at most `min(κ, n − κ)`, where `κ` counts the negative eigenvalues of `G`. So at most
`min(κ, n − κ)` modes, counted with algebraic multiplicity, lie in the open right half-plane, as
many in the open left one, and at least `n − 2 min(κ, n − κ)` dimensions of generalized eigenspace
lie on the axis.

Sources. The box of #410 "Signature placement and spectral licences (from #54): the pair-derived
consumer meeting the `G`-skew hypotheses; real spectrum of a symmetrizable generator, the
Pontryagin bound, and the on-axis dimension over ℂ". `docs/ELEMENTARY_OBJECTS.md` §6, the
paragraph "Placement" and its Pontryagin sentence ("at most `min(κ, n−κ)` eigenvalues of a
`G`-skew operator lie in the open right half-plane … Lean lift #54"); `docs/WINDING_CARRY_AND_PLACEMENT.md`
§3, the Pontryagin arm of placement; the record
`research/records/2026-09-21_WINDING_CARRY_FACES_AND_PLACEMENT_GENERALIZE_THE_HELICAL_PAIR.md`
(the row "Pontryagin placement"). Atlas rows `tube.pontryagin-bound` (whose Lean lift this is),
`holon.indefinite-storage-no-placement` (the witness), `tube.chain-placement`,
`receipt.seam-g-skew`, `receipt.conserving-receiver-iff-semisimple`, `motion.turn-boost-split`
and `winding.hand-is-convention`.

Conventions. Over `Matrix (Fin n) (Fin n) ℂ`, the shapes of `Foundation/CausalChord`. `A` is
`G`-skew when `rateForm A G = 0`, that is `Aᴴ G + G A = 0` (CausalChord's `rateForm`), and
`G`-self-adjoint when `Aᴴ G = G A` (the convention of `Coupling/MovingMetricSpectral`). The pairing
is `gPair G w v = wᴴ G v = star w ⬝ᵥ (G *ᵥ v)`, the form read in CausalChord's proofs and in
`Coupling/KreinForm.mode_off_circle_is_null`. The negative index `negIndex hG` is the number of
negative eigenvalues in Mathlib's spectral theorem for the Hermitian `G`
(`Matrix.IsHermitian.eigenvalues`); with `G` invertible, `n − negIndex hG` counts the positive ones.
The generalized eigenspaces over a region `R ⊆ ℂ` are joined in `genSpan A R`, the supremum of
`maxGenEigenspace (toLin' A) μ` over `μ ∈ R`.

## What is proved

1. [proved-standard; formal-checked] **The neutral lemma** (`gSkew_pair_eigen`,
   `gSkew_eigen_orthogonal`, `gSkew_offAxis_null`, `gSkew_gen_orthogonal`, `rightHalf_neutral`,
   `leftHalf_neutral`). For `A v = λ v`, `A w = μ w`: `(λ + μ̄) · wᴴ G v = 0`, so an eigenvector with
   `Re λ ≠ 0` is `G`-null. For `v ∈ ker (A − λ)ᵏ`, `w ∈ ker (A − μ)ᵐ` with `λ + μ̄ ≠ 0`,
   `wᴴ G v = 0`, by induction on `k` and `m` (`pair_eq_zero_of_gen`, which carries a sign `s` in
   `wᴴ G (A v) = s · (A w)ᴴ G v` so that the skew and self-adjoint cases are one induction). Hence
   the generalized eigenspaces over `Re λ > 0`, and those over `Re λ < 0`, span `G`-neutral subspaces
   (`genSpan_neutral`).
2. [proved-standard; formal-checked] **Neutral subspaces are small** (`gPair_self_eq_sum`,
   `finrank_le_card_of_neutral`, `neutral_finrank_le_negIndex`, `neutral_finrank_le_posIndex`,
   `neutral_finrank_le`). In `G`'s unitary chart `vᴴ G v = Σ λᵢ |cᵢ|²`. A vector of a neutral `W`
   whose coordinates on the negative eigenvectors vanish lies in the positive spectral subspace,
   where the form is definite, so it is `0`: the coordinate map `W → ℂ^κ` is injective and
   `dim W ≤ κ`; on the other side `dim W ≤ n − κ`. With `G` invertible, `dim W ≤ min(κ, n − κ)`.
3. [proved-standard; formal-checked] **The Pontryagin bound** (`pontryagin_bound`,
   `pontryagin_bound_left`, `pontryagin_bound_roots`, `pontryagin_bound_roots_left`). The dimension of
   the generalized eigenspaces over `Re λ > 0` is at most `min(κ, n − κ)`, and so is the number of
   roots of `A.charpoly` there counted with multiplicity (`card_roots_filter_le_finrank`, through
   `LinearMap.finrank_maxGenEigenspace_eq` and the independence of the generalized eigenspaces,
   `finrank_biSup_maxGen`); likewise over `Re λ < 0`. The witness `G = diag(1, −1)`,
   `A = [[0, 1], [1, 0]]` attains it (`swap_attains`): the right half carries dimension one and the
   bound itself forces `κ = 1`.
4. [proved-standard; formal-checked] **Symmetry and the on-axis dimension** (`gSkew_det_reflect`,
   `gSkew_eigen_reflect`, `offAxis_finrank_le`, `onAxis_finrank_ge`). With `G` invertible,
   `det (A + μ̄) = (−1)ⁿ · conj (det (A − μ))`, so `μ` is an eigenvalue if and only if `−μ̄` is. The
   generalized eigenspaces off the axis span at most `2 min(κ, n − κ)` dimensions, and those on the
   axis at least `n − 2 min(κ, n − κ)`, since all of them together span `ℂⁿ`
   (`Module.End.iSup_maxGenEigenspace_eq_top`, through `top_le_genSpan_sup`).
   [proved-derived; formal-checked] For `G ≻ 0` the index is `0` (`negIndex_posDef`), both halves are
   `⊥` (`rightHalf_eq_bot_of_posDef`, `leftHalf_eq_bot_of_posDef`) and the axis carries the whole
   space (`onAxis_eq_top_of_posDef`); `eigenvalue_re_eq_zero_of_posDef` is CausalChord's
   `gSkew_eigenvalue_re_eq_zero` (the row `receipt.seam-g-skew`) read off the bound.
5. [proved-standard; formal-checked] **The real spectrum of a symmetrizable generator**
   (`gSelfAdjoint_pair_eigen`, `gSelfAdjoint_eigen_orthogonal`, `gSelfAdjoint_nonreal_null`,
   `gSelfAdjoint_eigenvalue_im_eq_zero`, `upperHalf_neutral`, `lowerHalf_neutral`,
   `gSelfAdjoint_upper_bound`, `gSelfAdjoint_lower_bound`, `gSelfAdjoint_roots_upper`). For
   `Aᴴ G = G A` (the boost of `motion.turn-boost-split`): `(λ − μ̄) · wᴴ G v = 0`; a nonreal
   eigenvector is `G`-null; with `G ≻ 0` every eigenvalue is real; with `G` indefinite and
   invertible the generalized eigenspaces over `Im λ > 0` are neutral, so they span at most
   `min(κ, n − κ)` dimensions and carry at most that many roots of the characteristic polynomial.
   [proved-derived; formal-checked] `gSelfAdjoint_iff_quarter_turn`: `A` is `G`-self-adjoint if and
   only if `i·A` is `G`-skew, the boost a quarter-turn from a turn.
6. [proved-derived; formal-checked] **The pair-derived consumer** (`lossless_chain_gSkew`,
   `chain_rateForm`, `conjTranspose_map_rat`, `rateForm_map_rat`, `chain_rateForm_rat`,
   `lossless_chain_rat_gSkew`, `map_rat_isHermitian`, `map_rat_det_ne_zero`,
   `chain_pontryagin_bound`, `swap_is_the_chain_witness`). With `Ωᴴ = −Ω` and `Gᴴ = G`, `A = Ω G`
   is `G`-skew; with `Mᴴ = M` the chain's rate is `Aᴴ G + G A = −2 G M G` for `A = (Ω − M) G`. The
   chain's own rational generator `Transport/HolonicInteraction.portGenerator` (the generator of
   `Transport/HolonicChain`'s flow `ẋ = (Ω − M) G x + B u`, whose rate form
   `HolonicInteraction.port_storage_rate` is what `HolonicChain.reversal_preserves_the_storage_rate`
   and `HolonicChain.port_power_balance` read) maps into `ℂ` with its rate form, so the lossless chain
   (`M = 0`, `Ωᵀ = −Ω`, `Gᵀ = G`, `det G ≠ 0`) obeys the Pontryagin bound. The complex witness is the
   tree's `indefiniteStorage` and `swapGenerator` read over `ℂ`.

## What is not claimed

The bound is not asserted for a dissipative generator: with `M ≠ 0` the rate form is `−2 G M G`,
not `0`, and with indefinite storage nothing here places its off-axis modes (the guide's sentence
"This conservative bound is not asserted for an arbitrary mixed dissipative generator").
The symmetry is proved for eigenvalues; that the generalized eigenspaces at `μ` and `−μ̄` have
equal dimension (so that the two halves carry equal counts) is not proved. The classical theorem
on a Pontryagin space `Π_κ` (a `κ`-dimensional nonpositive invariant subspace) and the Krein
signature of a mode on the axis are not built; everything is finite dimensional. No statement is
made on which `G` a receiver holds, on attainment beyond the two-by-two witness, or on a zeta
function.

## On the objects

[interpretation] The computational object is the helical pair interaction read at its storage: a
chain of parametron rings joined by pair contacts carries the rings' storage form `G` and the
contacts' rate `A = (Ω − M) G`. The conservative coupling `Ω` is a turn, which keeps the reading
`xᴴ G x`; placement asks where the modes of the coupled rings sit. With positive storage every mode
of a lossless chain sits on the axis. With indefinite storage a mode can leave the axis only along
a direction the storage reads as null, and those directions on one side span a neutral subspace,
so the number of modes that grow is bounded by the smaller of the storage's negative and positive
squares. A boost (a `G`-self-adjoint rate) is the same statement a quarter-turn away: its modes leave
the real line only along null directions. Of the winding guide's six general objects this touches
faces and placement (§3's Pontryagin arm) and the tube (the chain's rate form,
`Transport/HolonicChain`); the helix, the pair, the cell holonomy and the tower thread stay attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Transport.PontryaginBound

open Matrix Module
open scoped ComplexConjugate ComplexOrder
open Holonics.Foundation.CausalChord (rateForm)

variable {n : ℕ}

/-! ## 1. The pairing and the neutral lemma -/

/-- [definition] The storage pairing `⟨w, v⟩_G = wᴴ G v`. -/
def gPair (G : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) : ℂ := star w ⬝ᵥ (G *ᵥ v)

/-- [definition] A subspace is `G`-neutral when the pairing vanishes on it identically. -/
def IsNeutral (G : Matrix (Fin n) (Fin n) ℂ) (W : Submodule ℂ (Fin n → ℂ)) : Prop :=
  ∀ v ∈ W, ∀ w ∈ W, gPair G w v = 0

section Pairing

variable (G : Matrix (Fin n) (Fin n) ℂ)

/-- [proved-standard; formal-checked] The pairing is additive in its left slot. -/
theorem gPair_add_left (w₁ w₂ v : Fin n → ℂ) :
    gPair G (w₁ + w₂) v = gPair G w₁ v + gPair G w₂ v := by
  simp [gPair, star_add, add_dotProduct]

/-- [proved-standard; formal-checked] The pairing is additive in its right slot. -/
theorem gPair_add_right (w v₁ v₂ : Fin n → ℂ) :
    gPair G w (v₁ + v₂) = gPair G w v₁ + gPair G w v₂ := by
  simp [gPair, mulVec_add, dotProduct_add]

/-- [proved-standard; formal-checked] The pairing vanishes at a zero left slot. -/
theorem gPair_zero_left (v : Fin n → ℂ) : gPair G 0 v = 0 := by simp [gPair]

/-- [proved-standard; formal-checked] The pairing vanishes at a zero right slot. -/
theorem gPair_zero_right (w : Fin n → ℂ) : gPair G w 0 = 0 := by simp [gPair]

/-- [proved-standard; formal-checked] The pairing takes differences in its left slot. -/
theorem gPair_sub_left (w₁ w₂ v : Fin n → ℂ) :
    gPair G (w₁ - w₂) v = gPair G w₁ v - gPair G w₂ v := by
  simp [gPair, star_sub, sub_dotProduct]

/-- [proved-standard; formal-checked] The pairing takes differences in its right slot. -/
theorem gPair_sub_right (w v₁ v₂ : Fin n → ℂ) :
    gPair G w (v₁ - v₂) = gPair G w v₁ - gPair G w v₂ := by
  simp [gPair, mulVec_sub, dotProduct_sub]

/-- [proved-standard; formal-checked] The left slot is conjugate-linear. -/
theorem gPair_smul_left (c : ℂ) (w v : Fin n → ℂ) :
    gPair G (c • w) v = conj c * gPair G w v := by
  simp [gPair, star_smul, smul_dotProduct]

/-- [proved-standard; formal-checked] The right slot is linear. -/
theorem gPair_smul_right (c : ℂ) (w v : Fin n → ℂ) :
    gPair G w (c • v) = c * gPair G w v := by
  simp [gPair, mulVec_smul, dotProduct_smul]

/-- [proved-standard; formal-checked] A move in the left slot reads as `Aᴴ G`. -/
theorem gPair_mulVec_left (A : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) :
    gPair G (A *ᵥ w) v = star w ⬝ᵥ ((Aᴴ * G) *ᵥ v) := by
  rw [gPair, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec]

/-- [proved-standard; formal-checked] A move in the right slot reads as `G A`. -/
theorem gPair_mulVec_right (A : Matrix (Fin n) (Fin n) ℂ) (w v : Fin n → ℂ) :
    gPair G w (A *ᵥ v) = star w ⬝ᵥ ((G * A) *ᵥ v) := by
  rw [gPair, mulVec_mulVec]

end Pairing

/-- [proved-standard; formal-checked] A `G`-skew move crosses the pairing with the sign `−1`. -/
theorem gPair_mulVec_of_gSkew {A G : Matrix (Fin n) (Fin n) ℂ} (hA : rateForm A G = 0)
    (v w : Fin n → ℂ) : gPair G w (A *ᵥ v) = -1 * gPair G (A *ᵥ w) v := by
  have h0 : star w ⬝ᵥ ((rateForm A G) *ᵥ v) = 0 := by rw [hA]; simp
  rw [rateForm, add_mulVec, dotProduct_add, ← gPair_mulVec_left, ← gPair_mulVec_right] at h0
  linear_combination h0

/-- [proved-standard; formal-checked] A `G`-self-adjoint move crosses the pairing with the sign `1`. -/
theorem gPair_mulVec_of_gSelfAdjoint {A G : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ * G = G * A)
    (v w : Fin n → ℂ) : gPair G w (A *ᵥ v) = 1 * gPair G (A *ᵥ w) v := by
  rw [gPair_mulVec_left, gPair_mulVec_right, hA, one_mul]

/-- [proved-standard; formal-checked] The shifted move `toLin' A − λ` acts as `v ↦ A v − λ v`. -/
theorem toLin'_sub_smul_apply (A : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) (v : Fin n → ℂ) :
    (toLin' A - l • 1) v = A *ᵥ v - l • v := by
  simp [toLin'_apply]

/-- [proved-standard; formal-checked] Powers of the shifted move are the shifted matrix's powers. -/
theorem toLin'_sub_smul_pow (A : Matrix (Fin n) (Fin n) ℂ) (l : ℂ) (k : ℕ) :
    (toLin' A - l • 1) ^ k = toLin' ((A - l • 1) ^ k) := by
  rw [toLin'_pow, map_sub, map_smul, toLin'_one, Module.End.one_eq_id]

/-- [proved-standard; formal-checked] Generalized eigenvectors at `λ` and `μ` with `λ − s μ̄ ≠ 0` are
`G`-orthogonal when `A` crosses the pairing with the sign `s`; induction on `k` and `m`. -/
theorem pair_eq_zero_of_gen {A G : Matrix (Fin n) (Fin n) ℂ} {s : ℂ}
    (hrel : ∀ v w, gPair G w (A *ᵥ v) = s * gPair G (A *ᵥ w) v) {l μ : ℂ}
    (hc : l - s * conj μ ≠ 0) (k m : ℕ) (v w : Fin n → ℂ)
    (hv : ((toLin' A - l • 1) ^ k) v = 0) (hw : ((toLin' A - μ • 1) ^ m) w = 0) :
    gPair G w v = 0 := by
  induction k generalizing m v w with
  | zero =>
    rw [pow_zero, Module.End.one_apply] at hv
    rw [hv, gPair_zero_right]
  | succ k ihk =>
    induction m generalizing w with
    | zero =>
      rw [pow_zero, Module.End.one_apply] at hw
      rw [hw, gPair_zero_left]
    | succ m ihm =>
      rw [pow_succ, Module.End.mul_apply, toLin'_sub_smul_apply] at hv hw
      have h1 : gPair G w (A *ᵥ v - l • v) = 0 := ihk (m + 1) _ _ hv
        (by rw [pow_succ, Module.End.mul_apply, toLin'_sub_smul_apply]; exact hw)
      have h2 : gPair G (A *ᵥ w - μ • w) v = 0 := ihm _ hw
      rw [gPair_sub_right, gPair_smul_right, hrel] at h1
      rw [gPair_sub_left, gPair_smul_left] at h2
      have key : (l - s * conj μ) * gPair G w v = 0 := by linear_combination s * h2 - h1
      rcases mul_eq_zero.mp key with h | h
      · exact absurd h hc
      · exact h

/-- [proved-standard; formal-checked] The same orthogonality between maximal generalized
eigenspaces. -/
theorem pair_eq_zero_of_maxGen {A G : Matrix (Fin n) (Fin n) ℂ} {s : ℂ}
    (hrel : ∀ v w, gPair G w (A *ᵥ v) = s * gPair G (A *ᵥ w) v) {l μ : ℂ}
    (hc : l - s * conj μ ≠ 0) {v w : Fin n → ℂ}
    (hv : v ∈ Module.End.maxGenEigenspace (toLin' A) l)
    (hw : w ∈ Module.End.maxGenEigenspace (toLin' A) μ) :
    gPair G w v = 0 := by
  obtain ⟨k, hk⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hv
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).mp hw
  exact pair_eq_zero_of_gen hrel hc k m v w hk hm

/-- [proved-standard; formal-checked] For a `G`-skew `A` and eigenvectors at `λ` and `μ`,
`(λ + μ̄) · wᴴ G v = 0`. -/
theorem gSkew_pair_eigen {A G : Matrix (Fin n) (Fin n) ℂ} (hA : rateForm A G = 0) {l μ : ℂ}
    {v w : Fin n → ℂ} (hv : A *ᵥ v = l • v) (hw : A *ᵥ w = μ • w) :
    (l + conj μ) * gPair G w v = 0 := by
  have h := gPair_mulVec_of_gSkew hA v w
  rw [hv, hw, gPair_smul_right, gPair_smul_left] at h
  linear_combination h

/-- [proved-standard; formal-checked] Eigenvectors of a `G`-skew `A` with `λ + μ̄ ≠ 0` are
`G`-orthogonal. -/
theorem gSkew_eigen_orthogonal {A G : Matrix (Fin n) (Fin n) ℂ} (hA : rateForm A G = 0) {l μ : ℂ}
    (hc : l + conj μ ≠ 0) {v w : Fin n → ℂ} (hv : A *ᵥ v = l • v) (hw : A *ᵥ w = μ • w) :
    gPair G w v = 0 :=
  (mul_eq_zero.mp (gSkew_pair_eigen hA hv hw)).resolve_left hc

/-- [proved-standard; formal-checked] Two points on one side of the axis never reflect onto each
other: `0 < Re λ · Re μ` gives `λ + μ̄ ≠ 0`. -/
theorem re_add_conj_ne_zero {l μ : ℂ} (h : 0 < l.re * μ.re) : l + conj μ ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.re h0
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at h1
  have hμ : μ.re = -l.re := by linarith
  rw [hμ] at h
  nlinarith [sq_nonneg l.re]

/-- [proved-standard; formal-checked] An eigenvector of a `G`-skew `A` off the imaginary axis is
`G`-null. -/
theorem gSkew_offAxis_null {A G : Matrix (Fin n) (Fin n) ℂ} (hA : rateForm A G = 0) {l : ℂ}
    (hre : l.re ≠ 0) {v : Fin n → ℂ} (hv : A *ᵥ v = l • v) : gPair G v v = 0 :=
  gSkew_eigen_orthogonal hA (re_add_conj_ne_zero (mul_self_pos.mpr hre)) hv hv

/-- [proved-standard; formal-checked] For a `G`-skew `A`, `ker (A − λ)ᵏ` and `ker (A − μ)ᵐ` are
`G`-orthogonal when `λ + μ̄ ≠ 0`. -/
theorem gSkew_gen_orthogonal {A G : Matrix (Fin n) (Fin n) ℂ} (hA : rateForm A G = 0) {l μ : ℂ}
    (hc : l + conj μ ≠ 0) (k m : ℕ) {v w : Fin n → ℂ}
    (hv : ((A - l • 1) ^ k) *ᵥ v = 0) (hw : ((A - μ • 1) ^ m) *ᵥ w = 0) :
    gPair G w v = 0 := by
  refine pair_eq_zero_of_gen (gPair_mulVec_of_gSkew hA) (by rwa [neg_one_mul, sub_neg_eq_add])
    k m v w ?_ ?_
  · rwa [toLin'_sub_smul_pow, toLin'_apply]
  · rwa [toLin'_sub_smul_pow, toLin'_apply]

/-! ## 2. The generalized eigenspaces over a region -/

/-- [definition] The span of `A`'s generalized eigenspaces over the eigenvalues in a region `R`. -/
def genSpan (A : Matrix (Fin n) (Fin n) ℂ) (R : ℂ → Prop) : Submodule ℂ (Fin n → ℂ) :=
  ⨆ μ : {μ : ℂ // R μ}, Module.End.maxGenEigenspace (toLin' A) μ.1

/-- [proved-standard; formal-checked] Each generalized eigenspace over the region lies in its span. -/
theorem maxGen_le_genSpan (A : Matrix (Fin n) (Fin n) ℂ) {R : ℂ → Prop} {μ : ℂ} (h : R μ) :
    Module.End.maxGenEigenspace (toLin' A) μ ≤ genSpan A R :=
  le_iSup (fun ν : {ν : ℂ // R ν} => Module.End.maxGenEigenspace (toLin' A) ν.1) ⟨μ, h⟩

/-- [proved-standard; formal-checked] An eigenvector lies in its generalized eigenspace. -/
theorem mem_maxGen_of_eigen {A : Matrix (Fin n) (Fin n) ℂ} {μ : ℂ} {v : Fin n → ℂ}
    (heig : A *ᵥ v = μ • v) : v ∈ Module.End.maxGenEigenspace (toLin' A) μ := by
  refine (Module.End.mem_maxGenEigenspace _ _ _).mpr ⟨1, ?_⟩
  rw [pow_one, toLin'_sub_smul_apply, heig, sub_self]

/-- [proved-standard; formal-checked] If no two eigenvalues of the region pair (`λ − s μ̄ ≠ 0`), the
span of its generalized eigenspaces is `G`-neutral. -/
theorem genSpan_neutral {A G : Matrix (Fin n) (Fin n) ℂ} {s : ℂ}
    (hrel : ∀ v w, gPair G w (A *ᵥ v) = s * gPair G (A *ᵥ w) v) {R : ℂ → Prop}
    (hR : ∀ l μ, R l → R μ → l - s * conj μ ≠ 0) : IsNeutral G (genSpan A R) := by
  intro v hv w hw
  refine Submodule.iSup_induction _ (motive := fun v => gPair G w v = 0) hv ?_
    (gPair_zero_right G w) (fun x y hx hy => by rw [gPair_add_right, hx, hy, add_zero])
  rintro ⟨l, hl⟩ x hx
  refine Submodule.iSup_induction _ (motive := fun w => gPair G w x = 0) hw ?_
    (gPair_zero_left G x) (fun y z hy hz => by rw [gPair_add_left, hy, hz, add_zero])
  rintro ⟨μ, hμ⟩ y hy
  exact pair_eq_zero_of_maxGen hrel (hR l μ hl hμ) hx hy

/-- [proved-standard; formal-checked] The generalized eigenspaces over `Re λ > 0` span a `G`-neutral
subspace. -/
theorem rightHalf_neutral {A G : Matrix (Fin n) (Fin n) ℂ} (hA : rateForm A G = 0) :
    IsNeutral G (genSpan A fun μ => 0 < μ.re) :=
  genSpan_neutral (gPair_mulVec_of_gSkew hA) fun l μ hl hμ => by
    rw [neg_one_mul, sub_neg_eq_add]; exact re_add_conj_ne_zero (mul_pos hl hμ)

/-- [proved-standard; formal-checked] The generalized eigenspaces over `Re λ < 0` span a `G`-neutral
subspace. -/
theorem leftHalf_neutral {A G : Matrix (Fin n) (Fin n) ℂ} (hA : rateForm A G = 0) :
    IsNeutral G (genSpan A fun μ => μ.re < 0) :=
  genSpan_neutral (gPair_mulVec_of_gSkew hA) fun l μ hl hμ => by
    rw [neg_one_mul, sub_neg_eq_add]; exact re_add_conj_ne_zero (mul_pos_of_neg_of_neg hl hμ)

/-- [proved-standard; formal-checked] A region covered by two others has its span inside their
join. -/
theorem genSpan_le_sup (A : Matrix (Fin n) (Fin n) ℂ) {R R₁ R₂ : ℂ → Prop}
    (h : ∀ μ, R μ → R₁ μ ∨ R₂ μ) : genSpan A R ≤ genSpan A R₁ ⊔ genSpan A R₂ := by
  refine iSup_le fun ⟨μ, hμ⟩ => ?_
  rcases h μ hμ with h1 | h2
  · exact le_sup_of_le_left (maxGen_le_genSpan A h1)
  · exact le_sup_of_le_right (maxGen_le_genSpan A h2)

/-- [proved-standard; formal-checked] Two regions covering `ℂ` span the whole space over `ℂ`. -/
theorem top_le_genSpan_sup (A : Matrix (Fin n) (Fin n) ℂ) {R₁ R₂ : ℂ → Prop}
    (h : ∀ μ, R₁ μ ∨ R₂ μ) : ⊤ ≤ genSpan A R₁ ⊔ genSpan A R₂ := by
  rw [← Module.End.iSup_maxGenEigenspace_eq_top (toLin' A)]
  refine iSup_le fun μ => ?_
  rcases h μ with h1 | h2
  · exact le_sup_of_le_left (maxGen_le_genSpan A h1)
  · exact le_sup_of_le_right (maxGen_le_genSpan A h2)

/-- [proved-standard; formal-checked] Over a finite set of eigenvalues the generalized eigenspaces
are independent, so their dimensions add. -/
theorem finrank_biSup_maxGen (f : Module.End ℂ (Fin n → ℂ)) (T : Finset ℂ) :
    finrank ℂ ↥(⨆ μ ∈ T, f.maxGenEigenspace μ) = ∑ μ ∈ T, finrank ℂ (f.maxGenEigenspace μ) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, ← ih, Finset.iSup_insert]
    have hdisj : Disjoint (f.maxGenEigenspace a) (⨆ μ ∈ T, f.maxGenEigenspace μ) := by
      simpa using (Module.End.independent_maxGenEigenspace f).disjoint_biSup (y := (T : Set ℂ)) ha
    have h := Submodule.finrank_sup_add_finrank_inf_eq (f.maxGenEigenspace a)
      (⨆ μ ∈ T, f.maxGenEigenspace μ)
    rw [hdisj.eq_bot, finrank_bot, add_zero] at h
    exact h

/-- [proved-standard; formal-checked] The roots of `A.charpoly` in a region, counted with
multiplicity, number at most the dimension of the region's generalized eigenspaces. -/
theorem card_roots_filter_le_finrank (A : Matrix (Fin n) (Fin n) ℂ) (R : ℂ → Prop)
    [DecidablePred R] :
    Multiset.card (A.charpoly.roots.filter R) ≤ finrank ℂ (genSpan A R) := by
  classical
  have hsum : Multiset.card (A.charpoly.roots.filter R)
      = ∑ μ ∈ (A.charpoly.roots.filter R).toFinset,
          finrank ℂ (Module.End.maxGenEigenspace (toLin' A) μ) := by
    rw [← Multiset.toFinset_sum_count_eq]
    refine Finset.sum_congr rfl fun μ hμ => ?_
    have hRμ : R μ := Multiset.of_mem_filter (Multiset.mem_toFinset.mp hμ)
    rw [Multiset.count_filter_of_pos hRμ, Polynomial.count_roots,
      LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']
  rw [hsum, ← finrank_biSup_maxGen]
  refine Submodule.finrank_mono (iSup₂_le fun μ hμ => maxGen_le_genSpan A ?_)
  exact Multiset.of_mem_filter (Multiset.mem_toFinset.mp hμ)

/-! ## 3. Neutral subspaces are small -/

/-- [definition] The negative index `κ` of a Hermitian `G`: the number of its negative eigenvalues
in Mathlib's spectral theorem. -/
def negIndex {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) : ℕ :=
  Fintype.card {i : Fin n // hG.eigenvalues i < 0}

/-- [proved-standard; formal-checked] In `G`'s unitary chart the reading is `vᴴ G v = Σ λᵢ |cᵢ|²`
with `c = Uᴴ v`. -/
theorem gPair_self_eq_sum {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) (v : Fin n → ℂ) :
    gPair G v v = ((∑ i, hG.eigenvalues i *
      Complex.normSq (((hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ *ᵥ v) i) : ℝ) : ℂ) := by
  have hspec : G = (hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      * diagonal (fun i => ((hG.eigenvalues i : ℝ) : ℂ))
      * (hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ := by
    have h := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hstar : star v ᵥ* (hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)
      = star ((hG.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ)ᴴ *ᵥ v) := by
    rw [star_mulVec, conjTranspose_conjTranspose]
  conv_lhs => rw [gPair, hspec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hstar]
  push_cast
  simp only [dotProduct, mulVec_diagonal, Pi.star_apply, Complex.normSq_eq_conj_mul_self]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.star_def]
  ring

/-- [proved-standard; formal-checked] If every eigenvalue outside `p` has the sign of `ε`, a
`G`-neutral subspace has dimension at most the number of indices in `p`. -/
theorem finrank_le_card_of_neutral {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    {W : Submodule ℂ (Fin n → ℂ)} (hW : IsNeutral G W) (p : Fin n → Prop) [DecidablePred p]
    (ε : ℝ) (hp : ∀ i, ¬ p i → 0 < ε * hG.eigenvalues i) :
    finrank ℂ W ≤ Fintype.card {i // p i} := by
  let U : Matrix (Fin n) (Fin n) ℂ := hG.eigenvectorUnitary
  let φ : W →ₗ[ℂ] ({i // p i} → ℂ) :=
    LinearMap.funLeft ℂ ℂ (Subtype.val : {i // p i} → Fin n) ∘ₗ toLin' Uᴴ ∘ₗ W.subtype
  have hinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hc : ∀ i : {i // p i}, (Uᴴ *ᵥ (x : Fin n → ℂ)) i.1 = 0 := fun i => by
      have := congrFun hx i
      simpa [φ, LinearMap.funLeft_apply, toLin'_apply] using this
    have h0 : gPair G x x = 0 := hW x x.2 x x.2
    rw [gPair_self_eq_sum hG, Complex.ofReal_eq_zero] at h0
    have hε : ∑ i, ε * hG.eigenvalues i * Complex.normSq ((Uᴴ *ᵥ (x : Fin n → ℂ)) i) = 0 := by
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [h0, mul_zero]
    have hnn : ∀ i ∈ Finset.univ,
        0 ≤ ε * hG.eigenvalues i * Complex.normSq ((Uᴴ *ᵥ (x : Fin n → ℂ)) i) := by
      intro i _
      by_cases hpi : p i
      · rw [hc ⟨i, hpi⟩, map_zero, mul_zero]
      · exact mul_nonneg (hp i hpi).le (Complex.normSq_nonneg _)
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hε
    have hzero : Uᴴ *ᵥ (x : Fin n → ℂ) = 0 := by
      funext i
      by_cases hpi : p i
      · exact hc ⟨i, hpi⟩
      · have h := hall i (Finset.mem_univ i)
        rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (hp i hpi).ne'
        · exact Complex.normSq_eq_zero.mp h'
    have hUU : U * Uᴴ = 1 := Unitary.coe_mul_star_self hG.eigenvectorUnitary
    have hx : (x : Fin n → ℂ) = 0 := by
      rw [← one_mulVec (x : Fin n → ℂ), ← hUU, ← mulVec_mulVec, hzero, mulVec_zero]
    exact Subtype.ext hx
  calc finrank ℂ W ≤ finrank ℂ ({i // p i} → ℂ) := LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card {i // p i} := Module.finrank_fintype_fun_eq_card ℂ

/-- [proved-standard; formal-checked] An invertible Hermitian matrix has no zero eigenvalue. -/
theorem eigenvalue_ne_zero {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    (i : Fin n) : hG.eigenvalues i ≠ 0 := by
  intro h
  apply hdet
  rw [hG.det_eq_prod_eigenvalues]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; simp)

/-- [proved-standard; formal-checked] A `G`-neutral subspace has dimension at most `κ`. -/
theorem neutral_finrank_le_negIndex {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) {W : Submodule ℂ (Fin n → ℂ)} (hW : IsNeutral G W) :
    finrank ℂ W ≤ negIndex hG := by
  refine finrank_le_card_of_neutral hG hW (fun i => hG.eigenvalues i < 0) 1 fun i hi => ?_
  rw [one_mul]
  exact lt_of_le_of_ne (not_lt.mp hi) (eigenvalue_ne_zero hG hdet i).symm

/-- [proved-standard; formal-checked] A `G`-neutral subspace has dimension at most `n − κ`. -/
theorem neutral_finrank_le_posIndex {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    {W : Submodule ℂ (Fin n → ℂ)} (hW : IsNeutral G W) :
    finrank ℂ W ≤ n - negIndex hG := by
  have h := finrank_le_card_of_neutral hG hW (fun i => ¬ hG.eigenvalues i < 0) (-1)
    fun i hi => by rw [not_not] at hi; linarith
  rw [Fintype.card_subtype_compl, Fintype.card_fin] at h
  exact h

/-- [proved-standard; formal-checked] For invertible Hermitian `G`, a neutral subspace has dimension
at most `min(κ, n − κ)`. -/
theorem neutral_finrank_le {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    {W : Submodule ℂ (Fin n → ℂ)} (hW : IsNeutral G W) :
    finrank ℂ W ≤ min (negIndex hG) (n - negIndex hG) :=
  le_min (neutral_finrank_le_negIndex hG hdet hW) (neutral_finrank_le_posIndex hG hW)

/-! ## 4. The Pontryagin bound and its witness -/

/-- [proved-standard; formal-checked] **The Pontryagin bound.** The generalized eigenspaces of a
`G`-skew `A` over `Re λ > 0` span at most `min(κ, n − κ)` dimensions. -/
theorem pontryagin_bound {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian) (hdet : G.det ≠ 0)
    (hA : rateForm A G = 0) :
    finrank ℂ (genSpan A fun μ => 0 < μ.re) ≤ min (negIndex hG) (n - negIndex hG) :=
  neutral_finrank_le hG hdet (rightHalf_neutral hA)

/-- [proved-standard; formal-checked] The same bound over `Re λ < 0`. -/
theorem pontryagin_bound_left {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : rateForm A G = 0) :
    finrank ℂ (genSpan A fun μ => μ.re < 0) ≤ min (negIndex hG) (n - negIndex hG) :=
  neutral_finrank_le hG hdet (leftHalf_neutral hA)

/-- [proved-standard; formal-checked] At most `min(κ, n − κ)` eigenvalues of a `G`-skew `A`, counted
with algebraic multiplicity, lie in the open right half-plane. -/
theorem pontryagin_bound_roots {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : rateForm A G = 0) :
    Multiset.card (A.charpoly.roots.filter fun μ => 0 < μ.re)
      ≤ min (negIndex hG) (n - negIndex hG) :=
  (card_roots_filter_le_finrank A _).trans (pontryagin_bound hG hdet hA)

/-- [proved-standard; formal-checked] The same count in the open left half-plane. -/
theorem pontryagin_bound_roots_left {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : rateForm A G = 0) :
    Multiset.card (A.charpoly.roots.filter fun μ => μ.re < 0)
      ≤ min (negIndex hG) (n - negIndex hG) :=
  (card_roots_filter_le_finrank A _).trans (pontryagin_bound_left hG hdet hA)

/-- [definition] The indefinite storage `diag(1, −1)` over `ℂ`. -/
def swapStorage : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

/-- [definition] The exchange rate `[[0, 1], [1, 0]]` over `ℂ`. -/
def swapRate : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- [proved-standard; formal-checked] The indefinite storage is Hermitian. -/
theorem swapStorage_isHermitian : swapStorage.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapStorage]

/-- [proved-standard; formal-checked] The indefinite storage is invertible. -/
theorem swapStorage_det : swapStorage.det ≠ 0 := by
  simp [swapStorage, Matrix.det_fin_two]

/-- [proved-standard; formal-checked] The exchange rate is skew against the indefinite storage. -/
theorem swapRate_gSkew : rateForm swapRate swapStorage = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rateForm, swapRate, swapStorage, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] The exchange rate has the mode `+1` on `(1, 1)`. -/
theorem swapRate_eigen : swapRate *ᵥ ![1, 1] = (1 : ℂ) • (![1, 1] : Fin 2 → ℂ) := by
  ext i
  fin_cases i <;> simp [swapRate, mulVec, dotProduct, Fin.sum_univ_two]

/-- [proved-standard; formal-checked] **The witness attains the bound**: the right half carries
dimension one, and the bound forces `κ = 1`, so `min(κ, 2 − κ) = 1`. -/
theorem swap_attains :
    finrank ℂ (genSpan swapRate fun μ => 0 < μ.re) = 1
      ∧ negIndex swapStorage_isHermitian = 1
      ∧ min (negIndex swapStorage_isHermitian) (2 - negIndex swapStorage_isHermitian) = 1 := by
  have hbound := pontryagin_bound swapStorage_isHermitian swapStorage_det swapRate_gSkew
  have hmem : (![1, 1] : Fin 2 → ℂ) ∈ genSpan swapRate fun μ => 0 < μ.re :=
    maxGen_le_genSpan swapRate (by norm_num : (0 : ℝ) < (1 : ℂ).re)
      (mem_maxGen_of_eigen swapRate_eigen)
  have hne : genSpan swapRate (fun μ => 0 < μ.re) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨_, hmem, fun h => by simpa using congrFun h 0⟩
  have hpos : 1 ≤ finrank ℂ (genSpan swapRate fun μ => 0 < μ.re) :=
    Nat.one_le_iff_ne_zero.mpr fun h => hne (Submodule.finrank_eq_zero.mp h)
  omega

/-! ## 5. The reflection `λ ↦ −λ̄` and the on-axis dimension -/

/-- [proved-standard; formal-checked] For a `G`-skew `A` with `G` invertible,
`det (A + μ̄) = (−1)ⁿ · conj (det (A − μ))`. -/
theorem gSkew_det_reflect {A G : Matrix (Fin n) (Fin n) ℂ} (hdet : G.det ≠ 0)
    (hA : rateForm A G = 0) (μ : ℂ) :
    (A + conj μ • 1).det = (-1) ^ n * star (A - μ • 1).det := by
  have hAG : Aᴴ * G = -(G * A) := eq_neg_of_add_eq_zero_left hA
  have hmul : G * (A + conj μ • 1) = -(A - μ • 1)ᴴ * G := by
    rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, neg_mul, sub_mul, hAG,
      Matrix.mul_add, smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, Complex.star_def]
    abel
  have h := congrArg Matrix.det hmul
  rw [det_mul, det_mul, det_neg, det_conjTranspose, Fintype.card_fin] at h
  apply mul_left_cancel₀ hdet
  rw [h]
  ring

/-- [proved-standard; formal-checked] **The spectrum of a `G`-skew `A` is symmetric under
`μ ↦ −μ̄`.** -/
theorem gSkew_eigen_reflect {A G : Matrix (Fin n) (Fin n) ℂ} (hdet : G.det ≠ 0)
    (hA : rateForm A G = 0) {μ : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0) (heig : A *ᵥ v = μ • v) :
    ∃ u : Fin n → ℂ, u ≠ 0 ∧ A *ᵥ u = (-conj μ) • u := by
  have h0 : (A - μ • 1).det = 0 := by
    refine Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, ?_⟩
    rw [sub_mulVec, heig, smul_mulVec, one_mulVec, sub_self]
  have h1 : (A + conj μ • 1).det = 0 := by
    rw [gSkew_det_reflect hdet hA, h0, star_zero, mul_zero]
  obtain ⟨u, hu, hAu⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h1
  refine ⟨u, hu, ?_⟩
  rw [add_mulVec, smul_mulVec, one_mulVec] at hAu
  rw [neg_smul]
  exact eq_neg_of_add_eq_zero_left hAu

/-- [proved-standard; formal-checked] The generalized eigenspaces off the imaginary axis span at most
`2 min(κ, n − κ)` dimensions. -/
theorem offAxis_finrank_le {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : rateForm A G = 0) :
    finrank ℂ (genSpan A fun μ => μ.re ≠ 0) ≤ 2 * min (negIndex hG) (n - negIndex hG) := by
  have hle : genSpan A (fun μ => μ.re ≠ 0)
      ≤ genSpan A (fun μ => 0 < μ.re) ⊔ genSpan A (fun μ => μ.re < 0) :=
    genSpan_le_sup A fun μ h => (lt_or_gt_of_ne h).symm
  calc finrank ℂ (genSpan A fun μ => μ.re ≠ 0)
      ≤ finrank ℂ ↥(genSpan A (fun μ => 0 < μ.re) ⊔ genSpan A (fun μ => μ.re < 0)) :=
        Submodule.finrank_mono hle
    _ ≤ finrank ℂ (genSpan A fun μ => 0 < μ.re) + finrank ℂ (genSpan A fun μ => μ.re < 0) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ 2 * min (negIndex hG) (n - negIndex hG) := by
        have h1 := pontryagin_bound hG hdet hA
        have h2 := pontryagin_bound_left hG hdet hA
        omega

/-- [proved-standard; formal-checked] **The on-axis dimension.** The generalized eigenspaces on the
imaginary axis span at least `n − 2 min(κ, n − κ)` dimensions over `ℂ`. -/
theorem onAxis_finrank_ge {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : rateForm A G = 0) :
    n - 2 * min (negIndex hG) (n - negIndex hG) ≤ finrank ℂ (genSpan A fun μ => μ.re = 0) := by
  have htop : ⊤ ≤ genSpan A (fun μ => μ.re ≠ 0) ⊔ genSpan A (fun μ => μ.re = 0) :=
    top_le_genSpan_sup A fun μ => (em (μ.re = 0)).symm
  have hn : n ≤ finrank ℂ (genSpan A fun μ => μ.re ≠ 0)
      + finrank ℂ (genSpan A fun μ => μ.re = 0) := by
    calc n = finrank ℂ (⊤ : Submodule ℂ (Fin n → ℂ)) := by rw [finrank_top, Module.finrank_fin_fun]
      _ ≤ finrank ℂ ↥(genSpan A (fun μ => μ.re ≠ 0) ⊔ genSpan A (fun μ => μ.re = 0)) :=
        Submodule.finrank_mono htop
      _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _
  have hoff := offAxis_finrank_le hG hdet hA
  omega

/-- [proved-standard; formal-checked] A positive definite storage has negative index `0`. -/
theorem negIndex_posDef {G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef) :
    negIndex hG.isHermitian = 0 := by
  rw [negIndex, Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨i, hi⟩ => absurd hi (not_lt.mpr (hG.eigenvalues_pos i).le)⟩

/-- [proved-derived; formal-checked] With `G ≻ 0` the axis carries the whole space: every generalized
eigenspace of a `G`-skew `A` sits on `Re λ = 0`. -/
theorem onAxis_eq_top_of_posDef {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : rateForm A G = 0) : genSpan A (fun μ => μ.re = 0) = ⊤ := by
  have h := onAxis_finrank_ge hG.isHermitian hG.det_pos.ne' hA
  rw [negIndex_posDef hG] at h
  refine Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) ?_)
  rw [Module.finrank_fin_fun]
  simpa using h

/-- [proved-derived; formal-checked] With `G ≻ 0` nothing of a `G`-skew `A` lies in `Re λ > 0`. -/
theorem rightHalf_eq_bot_of_posDef {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : rateForm A G = 0) : genSpan A (fun μ => 0 < μ.re) = ⊥ := by
  have h := pontryagin_bound hG.isHermitian hG.det_pos.ne' hA
  rw [negIndex_posDef hG, Nat.zero_min, Nat.le_zero] at h
  exact Submodule.finrank_eq_zero.mp h

/-- [proved-derived; formal-checked] With `G ≻ 0` nothing of a `G`-skew `A` lies in `Re λ < 0`. -/
theorem leftHalf_eq_bot_of_posDef {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : rateForm A G = 0) : genSpan A (fun μ => μ.re < 0) = ⊥ := by
  have h := pontryagin_bound_left hG.isHermitian hG.det_pos.ne' hA
  rw [negIndex_posDef hG, Nat.zero_min, Nat.le_zero] at h
  exact Submodule.finrank_eq_zero.mp h

/-- [proved-derived; formal-checked] CausalChord's `gSkew_eigenvalue_re_eq_zero` (`receipt.seam-g-skew`)
read off the bound: with `G ≻ 0` every eigenvalue of a `G`-skew `A` has `Re μ = 0`. -/
theorem eigenvalue_re_eq_zero_of_posDef {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : rateForm A G = 0) {v : Fin n → ℂ} {μ : ℂ} (hv : v ≠ 0) (heig : A *ᵥ v = μ • v) :
    μ.re = 0 := by
  have hmem := mem_maxGen_of_eigen heig
  rcases lt_trichotomy μ.re 0 with h | h | h
  · have := maxGen_le_genSpan A (R := fun μ => μ.re < 0) h hmem
    rw [leftHalf_eq_bot_of_posDef hG hA, Submodule.mem_bot] at this
    exact absurd this hv
  · exact h
  · have := maxGen_le_genSpan A (R := fun μ => 0 < μ.re) h hmem
    rw [rightHalf_eq_bot_of_posDef hG hA, Submodule.mem_bot] at this
    exact absurd this hv

/-! ## 6. The real spectrum of a symmetrizable generator -/

/-- [proved-standard; formal-checked] For a `G`-self-adjoint `A` and eigenvectors at `λ` and `μ`,
`(λ − μ̄) · wᴴ G v = 0`. -/
theorem gSelfAdjoint_pair_eigen {A G : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ * G = G * A) {l μ : ℂ}
    {v w : Fin n → ℂ} (hv : A *ᵥ v = l • v) (hw : A *ᵥ w = μ • w) :
    (l - conj μ) * gPair G w v = 0 := by
  have h := gPair_mulVec_of_gSelfAdjoint hA v w
  rw [hv, hw, gPair_smul_right, gPair_smul_left] at h
  linear_combination h

/-- [proved-standard; formal-checked] Eigenvectors of a `G`-self-adjoint `A` with `λ ≠ μ̄` are
`G`-orthogonal. -/
theorem gSelfAdjoint_eigen_orthogonal {A G : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ * G = G * A)
    {l μ : ℂ} (hc : l ≠ conj μ) {v w : Fin n → ℂ} (hv : A *ᵥ v = l • v) (hw : A *ᵥ w = μ • w) :
    gPair G w v = 0 :=
  (mul_eq_zero.mp (gSelfAdjoint_pair_eigen hA hv hw)).resolve_left (sub_ne_zero.mpr hc)

/-- [proved-standard; formal-checked] Two points on one side of the real line never reflect onto
each other: `0 < Im λ · Im μ` gives `λ − μ̄ ≠ 0`. -/
theorem im_sub_conj_ne_zero {l μ : ℂ} (h : 0 < l.im * μ.im) : l - conj μ ≠ 0 := by
  intro h0
  have h1 := congrArg Complex.im h0
  simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im, sub_neg_eq_add] at h1
  have hμ : μ.im = -l.im := by linarith
  rw [hμ] at h
  nlinarith [sq_nonneg l.im]

/-- [proved-standard; formal-checked] A nonreal eigenvector of a `G`-self-adjoint `A` is `G`-null. -/
theorem gSelfAdjoint_nonreal_null {A G : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ * G = G * A) {l : ℂ}
    (him : l.im ≠ 0) {v : Fin n → ℂ} (hv : A *ᵥ v = l • v) : gPair G v v = 0 :=
  (mul_eq_zero.mp (gSelfAdjoint_pair_eigen hA hv hv)).resolve_left
    (im_sub_conj_ne_zero (mul_self_pos.mpr him))

/-- [proved-standard; formal-checked] With `G ≻ 0` and `Aᴴ G = G A`, every eigenvalue of `A` is
real. -/
theorem gSelfAdjoint_eigenvalue_im_eq_zero {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.PosDef)
    (hA : Aᴴ * G = G * A) {l : ℂ} {v : Fin n → ℂ} (hv : v ≠ 0) (heig : A *ᵥ v = l • v) :
    l.im = 0 := by
  by_contra him
  have h0 := gSelfAdjoint_nonreal_null hA him heig
  have hpos : (0 : ℂ) < gPair G v v := hG.dotProduct_mulVec_pos hv
  rw [h0] at hpos
  exact lt_irrefl _ hpos

/-- [proved-standard; formal-checked] The generalized eigenspaces of a `G`-self-adjoint `A` over
`Im λ > 0` span a `G`-neutral subspace. -/
theorem upperHalf_neutral {A G : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ * G = G * A) :
    IsNeutral G (genSpan A fun μ => 0 < μ.im) :=
  genSpan_neutral (gPair_mulVec_of_gSelfAdjoint hA) fun l μ hl hμ => by
    rw [one_mul]; exact im_sub_conj_ne_zero (mul_pos hl hμ)

/-- [proved-standard; formal-checked] The same over `Im λ < 0`. -/
theorem lowerHalf_neutral {A G : Matrix (Fin n) (Fin n) ℂ} (hA : Aᴴ * G = G * A) :
    IsNeutral G (genSpan A fun μ => μ.im < 0) :=
  genSpan_neutral (gPair_mulVec_of_gSelfAdjoint hA) fun l μ hl hμ => by
    rw [one_mul]; exact im_sub_conj_ne_zero (mul_pos_of_neg_of_neg hl hμ)

/-- [proved-standard; formal-checked] The generalized eigenspaces of a `G`-self-adjoint `A` over
`Im λ > 0` span at most `min(κ, n − κ)` dimensions. -/
theorem gSelfAdjoint_upper_bound {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : Aᴴ * G = G * A) :
    finrank ℂ (genSpan A fun μ => 0 < μ.im) ≤ min (negIndex hG) (n - negIndex hG) :=
  neutral_finrank_le hG hdet (upperHalf_neutral hA)

/-- [proved-standard; formal-checked] The same over `Im λ < 0`. -/
theorem gSelfAdjoint_lower_bound {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : Aᴴ * G = G * A) :
    finrank ℂ (genSpan A fun μ => μ.im < 0) ≤ min (negIndex hG) (n - negIndex hG) :=
  neutral_finrank_le hG hdet (lowerHalf_neutral hA)

/-- [proved-standard; formal-checked] At most `min(κ, n − κ)` eigenvalues of a `G`-self-adjoint `A`,
counted with algebraic multiplicity, lie in the open upper half-plane. -/
theorem gSelfAdjoint_roots_upper {A G : Matrix (Fin n) (Fin n) ℂ} (hG : G.IsHermitian)
    (hdet : G.det ≠ 0) (hA : Aᴴ * G = G * A) :
    Multiset.card (A.charpoly.roots.filter fun μ => 0 < μ.im)
      ≤ min (negIndex hG) (n - negIndex hG) :=
  (card_roots_filter_le_finrank A _).trans (gSelfAdjoint_upper_bound hG hdet hA)

/-- [proved-derived; formal-checked] A boost is a turn a quarter-turn away: `Aᴴ G = G A` holds
if and only if `i·A` is `G`-skew. -/
theorem gSelfAdjoint_iff_quarter_turn (A G : Matrix (Fin n) (Fin n) ℂ) :
    Aᴴ * G = G * A ↔ rateForm (Complex.I • A) G = 0 := by
  have h : rateForm (Complex.I • A) G = Complex.I • (G * A - Aᴴ * G) := by
    rw [rateForm, conjTranspose_smul, smul_mul, Matrix.mul_smul, Complex.star_def,
      Complex.conj_I, smul_sub, neg_smul]
    abel
  rw [h, smul_eq_zero, sub_eq_zero]
  exact ⟨fun h' => Or.inr h'.symm, fun h' => h'.resolve_left Complex.I_ne_zero |>.symm⟩

/-! ## 7. The pair-derived consumer: the chain's rate form -/

/-- [proved-derived; formal-checked] A lossless chain `A = Ω G` with `Ωᴴ = −Ω`, `Gᴴ = G` is
`G`-skew. -/
theorem lossless_chain_gSkew {Ω G : Matrix (Fin n) (Fin n) ℂ} (hΩ : Ωᴴ = -Ω) (hG : Gᴴ = G) :
    rateForm (Ω * G) G = 0 := by
  rw [rateForm, conjTranspose_mul, hΩ, hG]
  noncomm_ring

/-- [proved-derived; formal-checked] With a dissipation `Mᴴ = M` the chain's rate form is
`Aᴴ G + G A = −2 G M G` for `A = (Ω − M) G`. -/
theorem chain_rateForm {Ω M G : Matrix (Fin n) (Fin n) ℂ} (hΩ : Ωᴴ = -Ω) (hM : Mᴴ = M)
    (hG : Gᴴ = G) : rateForm ((Ω - M) * G) G = (-2 : ℂ) • (G * M * G) := by
  rw [rateForm, conjTranspose_mul, conjTranspose_sub, hΩ, hM, hG]
  have : G * (-Ω - M) * G + G * ((Ω - M) * G) = -(G * M * G) - G * M * G := by noncomm_ring
  rw [this]
  module

/-- [proved-standard; formal-checked] A rational matrix read over `ℂ` has its transpose as its
conjugate transpose. -/
theorem conjTranspose_map_rat (X : Matrix (Fin n) (Fin n) ℚ) :
    (X.map (Rat.castHom ℂ))ᴴ = Xᵀ.map (Rat.castHom ℂ) := by
  ext i j
  simp [conjTranspose_apply, transpose_apply]

open Holonics.Transport.HolonicInteraction in
/-- [proved-derived; formal-checked] The rational rate form `rateFormQ` of `HolonicInteraction` read
over `ℂ` is CausalChord's `rateForm`. -/
theorem rateForm_map_rat (A G : Matrix (Fin n) (Fin n) ℚ) :
    rateForm (A.map (Rat.castHom ℂ)) (G.map (Rat.castHom ℂ))
      = (rateFormQ A G).map (Rat.castHom ℂ) := by
  rw [rateForm, rateFormQ, conjTranspose_map_rat, ← Matrix.map_mul, ← Matrix.map_mul,
    Matrix.map_add _ (map_add _)]

open Holonics.Transport.HolonicInteraction in
/-- [proved-derived; formal-checked] The chain's own generator `portGenerator Ω M G` read over `ℂ`
has the rate form `−2 G M G` (`HolonicInteraction.port_storage_rate_smul`). -/
theorem chain_rateForm_rat (Ω M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G) (hΩ : Ωᵀ = -Ω)
    (hM : Mᵀ = M) :
    rateForm ((portGenerator Ω M G).map (Rat.castHom ℂ)) (G.map (Rat.castHom ℂ))
      = ((-2 : ℚ) • (G * M * G)).map (Rat.castHom ℂ) := by
  rw [rateForm_map_rat, port_storage_rate_smul Ω M G hG hΩ hM]

open Holonics.Transport.HolonicInteraction in
/-- [proved-derived; formal-checked] The lossless chain's generator `portGenerator Ω 0 G` read over
`ℂ` is `G`-skew. -/
theorem lossless_chain_rat_gSkew (Ω G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G) (hΩ : Ωᵀ = -Ω) :
    rateForm ((portGenerator Ω 0 G).map (Rat.castHom ℂ)) (G.map (Rat.castHom ℂ)) = 0 := by
  rw [rateForm_map_rat, port_storage_rate_zero_of_no_dissipation Ω G hG hΩ]
  exact Matrix.map_zero _ (map_zero _)

/-- [proved-standard; formal-checked] A symmetric rational storage read over `ℂ` is Hermitian. -/
theorem map_rat_isHermitian {G : Matrix (Fin n) (Fin n) ℚ} (hG : Gᵀ = G) :
    (G.map (Rat.castHom ℂ)).IsHermitian := by
  rw [IsHermitian, conjTranspose_map_rat, hG]

/-- [proved-standard; formal-checked] An invertible rational storage stays invertible over `ℂ`. -/
theorem map_rat_det_ne_zero {G : Matrix (Fin n) (Fin n) ℚ} (hdet : G.det ≠ 0) :
    (G.map (Rat.castHom ℂ)).det ≠ 0 := by
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  exact (map_ne_zero _).mpr hdet

open Holonics.Transport.HolonicInteraction in
/-- [proved-derived; formal-checked] **The lossless chain obeys the Pontryagin bound**: its generalized
eigenspaces over `Re λ > 0` span at most `min(κ, n − κ)` dimensions, `κ` its storage's index. -/
theorem chain_pontryagin_bound (Ω G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G) (hΩ : Ωᵀ = -Ω)
    (hdet : G.det ≠ 0) :
    finrank ℂ (genSpan ((portGenerator Ω 0 G).map (Rat.castHom ℂ)) fun μ => 0 < μ.re)
      ≤ min (negIndex (map_rat_isHermitian hG)) (n - negIndex (map_rat_isHermitian hG)) :=
  pontryagin_bound _ (map_rat_det_ne_zero hdet) (lossless_chain_rat_gSkew Ω G hG hΩ)

open Holonics.Transport.HolonicInteraction in
/-- [proved-derived; formal-checked] The complex witness is the tree's `indefiniteStorage` and
`swapGenerator` (`holon.indefinite-storage-no-placement`) read over `ℂ`. -/
theorem swap_is_the_chain_witness :
    swapStorage = indefiniteStorage.map (Rat.castHom ℂ)
      ∧ swapRate = swapGenerator.map (Rat.castHom ℂ) := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [swapStorage, swapRate, indefiniteStorage, swapGenerator]

end Holonics.Transport.PontryaginBound
