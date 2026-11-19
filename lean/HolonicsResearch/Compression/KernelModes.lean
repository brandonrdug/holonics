import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Kernel modes: conduct runs through derived modes, an action closes or separates, context factors modulo silence

[definition] Formal obligations #410, the box "`quotient.kernel-mode-reduction`, `quotient.contextual-factorization`
(participation classes, context)". The two atlas rows (`docs/atlas/information.tsv`) had as their only owners the
retired host files `crates/holonics/src/exact_linear/kernel_modes.rs` and `exact_linear/contextual.rs`, read at
`d329cb541^` ([history](https://github.com/brandonrdug/holonics/tree/551d6c5d/crates/holonics/src/exact_linear)).
This file states what those files computed and refused, over any field `K` (`ℚ` in the witnesses). The rows they use:
`norm.attention-class-exact` (the pair (mass, current) is the compositional carrier,
`Computation/AttentionModeCompression`), `compression.kernel` and `info.preimage-fibre` (the quotient keeps its whole
fibre), `compression.cokernel` and `compression.cokernel-two-term` (an obstruction is a coholon annihilating the
image). The factorization is also the row `linalg.rank-factorization-rebase` (`A = CR`, a host row). In the winding
guide's §6 the same square is Kalman's minimal realization: `D E = ρ`, `E_next T = U E`
(`Foundation/ReceiverHistoryCompression`); THE_MACHINE's row "Continuing compression" reads it as `D E = ρ`,
`E_next T_g = U_g E`, "otherwise keep the separating direction".

Owners named and not imported (this file proves the finite matrix forms from Mathlib alone): the kernel quotient is the
coarsest retention, and a face is reached exactly when every cocycle vanishes on it (`Compression/Core/FaceMap`:
`kernelQuotient_is_coarsest_retention`, `reachable_iff_cocycles_vanish`); the cocycle reading of the cokernel
(`Objects/Pairing.annihilates_range_iff_mem_dualAnnihilator`, `mem_range_iff_coholon_cocycles_vanish`); the column
Fredholm alternative over `ℚ` (`Transport/EditRigidity.mem_range_iff_annihilators_vanish`); an additive generator
descends to the joint quotient exactly when it preserves the blind subgroup
(`Foundation/JointReceiverDescent.joint_generator_descends_iff`); a quotient places two occurrences in one fibre
(`Foundation/ReceiverQuotient.quotient_eq_places_both_in_one_fibre`).

Conventions. A kernel `K₀ : Matrix m n K` reads `n` sources at `m` receivers; `D : Matrix m r K` is the decoder and
`E : Matrix r n K` the encoder through `r` modes. The Rust solved `X S = Y` with observations as columns; the system
`D X = Y` below is its transpose, and its obstruction `vᵀ D = 0`, `vᵀ Y ≠ 0` is the Rust's `source_null` read on the
transposed side. The atlas row writes the closing square `U E = E T` with `T` the source action; here, as in the Rust
code, the source action is `U` and the modal action `T`, with `E U = T E`.

[proved-standard; formal-checked] What is proved, classical (items 1 to 3).

1. **Factoring a reading through another** (`exists_comp_eq_iff_ker_le`): `g = t ∘ f` for some linear `t` exactly
   when `ker f ≤ ker g`. Its matrix forms: `T E = Y` is solvable exactly when `E v = 0` forces `Y v = 0`
   (`exists_mul_left_eq_iff`), and `D X = Y` exactly when `vᵀ D = 0` forces `vᵀ Y = 0`
   (`exists_mul_right_eq_iff`, the Fredholm alternative over a field).
2. **Rank factorization.** With `K₀ = D E`, `D`'s columns independent and `E`'s rows independent:
   `ker K₀ = ker E` (`ker_eq_ker_encoder`), `range K₀ = range D` (`range_eq_range_decoder`), and the count of modes
   is the rank (`rank_eq_card_modes`). Independent rows are an encoder onto its modes (`mulVec_surjective_of_rows`,
   `rows_of_mulVec_surjective`), which cancels on the right (`cancel_right_of_rows`). Every matrix has such a
   factorization through `rank K₀` modes (`exists_rankFactorization`), and two factorizations through one count of
   modes differ by an invertible modal basis (`rankFactorization_unique_up_to_rebase`): the modes are derived from
   the kernel, and nothing beyond a modal frame is chosen.
3. **The system's alternative** (`solvable_xor_obstructed`): exactly one of "`D X = Y` has a solution" and "some `v`
   has `vᵀ D = 0` and `vᵀ Y ≠ 0`" holds; the solutions are a particular solution plus the free directions `D Z = 0`
   (`solutions_eq_particular_add_free`).

[proved-derived; formal-checked] What is proved, read on the house's objects (items 4 to 8; a classical step among
them carries its own tag).

4. **Conduct runs through the modes.** `K₀ x = D (E x)` (`conduct_through_modes`), and two sources share a mode
   summary exactly when they share every conduct (`summary_eq_iff_conduct_eq`): the summary is the quotient by the
   kernel and holds no source-event sequence. A conduct normalized by any receiving covector is the same for two
   sources with one summary (`normalized_eq_of_summary_eq`). A source family is a mass `w` and a weighted current
   `J`; its summary is `(E w, E J)` (`summary`), and its reading at receiver `i` is the decoded current over the
   decoded mass (`summaryRead`). That reading is the normalized conduct `(K₀ J)ᵢ / (K₀ w)ᵢ` (`normalizedConduct`,
   `summaryRead_eq_normalizedConduct`), the same for two families with one summary
   (`normalizedConduct_eq_of_summary_eq`), and the mass times it returns the current where the mass is nonzero
   (`mass_smul_summaryRead`). The summary of a weighted family of families is the weighted sum of their summaries
   (`summary_sum`): mass and current are contracted, and the division comes after. A change of the value frame acts
   on the reading from the right (`summaryRead_value_transport`).
5. **Participation classes**, the box's words: a score constant on the classes of `π` factors through the class
   encoder (`classEncoder`, `classKernel_factor`), whose summary is the class mass and the class current
   (`classEncoder_mulVec`, `classEncoder_mul`). Read through it, item 4 is `norm.attention-class-exact` over any
   field; the classes are one factorization, and the derived modes of item 2 number the rank.
6. **An action closes on the modes or returns its separating fibre.** For a source action `U`, a modal `T` with
   `E U = T E` exists exactly when `ker E ≤ ker (E U)` (`closes_iff_ker_le`), and exactly one of "it closes" and
   "some `v` has `E v = 0` and `E (U v) ≠ 0`" holds (`closes_xor_separates`). With independent rows the modal action
   is unique (`modalAction_unique`), and the summary and the conduct are carried by it
   (`summary_after_action`, `conduct_after_action`).
7. **Rebase.** For invertible `B`, `E′ = B E`, `D′ = D B⁻¹`, `M′ = B M` keep `D′ E′ = D E` (`rebase_decoder_mul`,
   `rebase_factor`) and `D′ M′ = D M` (`rebase_summary`), so every reading is unchanged (`rebase_summaryRead`); the
   pair is again a rank factorization (`rebase_cols`, `rebase_rows`), and a closed action's `T` becomes `B T B⁻¹`
   (`rebase_action`).
8. **Contextual factorization.** For occurrences read by a source `S`, a context `C` and a return `Y`: a decoder `g`
   with `Y = g ∘ (S, C)` exists exactly when `ker S ⊓ ker C ≤ ker Y` (`lift_iff`), and otherwise an occurrence
   combination `p` with `S p = 0`, `C p = 0`, `Y p ≠ 0` is returned; exactly one holds (`lift_xor_obstruction`). On a
   source-null occurrence the return is the decoder read on the context alone (`contrast_reads_context`, the Rust's
   `contrast_map`). The silent context is `N = C(ker S ⊓ ker Y)` (`silentContext`). Every decoder kills `(0, N)`
   (`decoder_kills_silentContext`) and so factors through the quotient `C → C ⧸ N`
   (`decoder_factors_through_silentQuotient`); when a decoder exists, one reads the context modulo `N`
   (`lift_through_silentQuotient`, the Rust's `returned_map` on `lifted_source`). The quotient kills `N` and nothing
   else (`silentQuotient_ker`), and on the source-null occurrences the quotient context and the return are silent
   together (`silent_kernel`), so they have one rank there (`finrank_map_eq_of_inf_ker_eq`, `demonstrated_rank_eq`:
   the Rust's `demonstrated_context_rank` check `rank(q C K) = rank(Y K)`, `K` spanning `ker S`).

[proved-derived; formal-checked] Witnesses over `ℚ`. The kernel `[[1,1,0],[0,0,1],[1,1,1]]` has rank two and the
factorization through the encoder `[[1,1,0],[0,0,1]]` (`witness_factor`, `witness_decoder_cols`,
`witness_encoder_rows`, `witness_rank`). The action `diag(2,2,3)` closes with `T = diag(2,3)` (`witness_closes`);
`diag(1,2,1)` returns the direction `(1,−1,0)`, which the encoder erases and the action exposes as `(−1,0)`
(`witness_separates`), so it does not close (`witness_does_not_close`). The system `K₀ X = (2,1,3)ᵀ` has the
particular solution `(1,1,1)ᵀ` and the free direction `(1,−1,0)ᵀ` (`witness_consistent`); `K₀ X = (2,1,4)ᵀ` is
obstructed by `v = (1,1,−1)`, which reads `−1` on it (`witness_obstructed`, `witness_no_solution`). For contexts, the
Rust's two tests: a source `[1,1]` and a context `[2,2]` leave the combination `(1,−1)` that the return `[1,−1]`
reads (`witness_context_obstructed`); a source `[1,1,1]`, a context `[[1,−1,0],[0,0,1],[0,0,0]]` and a return
`[1,−1,0]` lift (`witness_context_lifts`), and the silent context holds `(0,1,0)` and not the unobserved third
context direction `(0,0,1)`, which the quotient keeps (`witness_silentContext`).

[definition] What is not claimed.
- The Rust's certified arithmetic widths and work counts (`ExactWork`), its frame identity checks (`ForeignFrame`;
  here a frame is an explicit argument), its refusal of negative entries (`NegativeMass`) and its positive-mass gate
  (`NoPositiveMass`). The statements here hold over every field with no sign condition, and a reading needs only a
  nonzero mass; the nonnegativity in the atlas row's conditions belongs to the Rust's chart.
- Attention normalization beyond the ratio of item 4: no softmax and no score read from a query (the class factoring
  of item 5 takes the score as given; `norm.attention-class-exact` owns the attention reading over `ℝ`).
- The Rust's `descend_context_generator` (`q T = U q` on the context, or the columns `q T n` on a basis of `N`) is the
  closing alternative of item 6 read with the encoder `q`; its defect columns are not stated apart. The phase-rechart
  test (a frame change of the context transports the quotient) is not stated.
- `N` is not shown to be the largest context subspace that every decoder kills, and no decoder of the affine family
  is selected: a particular solution is a coordinate representative, never a cause.

The computational object is the helical pair interaction read on a linear chart: a receiver is paired with a source
through the modes, the decoder placing each receiver's face on the modes and the encoder placing each source in them,
and an obstruction is a coholon paired against a target, the pair's cokernel side. Of the winding guide's six general
objects this touches faces and placement (a receiver's face is decoded from the modes, and a rebase moves the modal
frame while every face stays), the pair (the obstruction `v` with `vᵀ D = 0`, `vᵀ Y ≠ 0`) and the tower thread (a
system's solutions are unique, plural as an affine family, or obstructed, the three outcomes of a gluing, and the
silent quotient is a restriction of the context). The helix, cell holonomy and the tube stay attached: a closed modal
action `T` is one step of a clocked transport on the modes, and a rebase conjugates it.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.Compression.KernelModes

open Matrix

/-! ## Factoring a reading through another -/

section Factor

variable {K : Type*} [Field K] {V W Z : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W]
  [Module K W] [AddCommGroup Z] [Module K Z]

/-- [proved-standard; formal-checked] A linear reading `g` factors through `f` exactly when `f`'s kernel lies in
`g`'s. -/
theorem exists_comp_eq_iff_ker_le (f : V →ₗ[K] W) (g : V →ₗ[K] Z) :
    (∃ t : W →ₗ[K] Z, t ∘ₗ f = g) ↔ LinearMap.ker f ≤ LinearMap.ker g := by
  constructor
  · rintro ⟨t, rfl⟩ x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [LinearMap.comp_apply, hx, map_zero]
  · intro h
    obtain ⟨t, ht⟩ := LinearMap.exists_extend
      ((LinearMap.ker f).liftQ g h ∘ₗ f.quotKerEquivRange.symm.toLinearMap)
    refine ⟨t, LinearMap.ext fun x => ?_⟩
    have he : f.quotKerEquivRange.symm ⟨f x, LinearMap.mem_range_self f x⟩ =
        Submodule.Quotient.mk x := by
      rw [LinearEquiv.symm_apply_eq]
      ext
      rw [LinearMap.quotKerEquivRange_apply_mk]
    have hx := LinearMap.congr_fun ht ⟨f x, LinearMap.mem_range_self f x⟩
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, he,
      Submodule.liftQ_apply] at hx
    rw [LinearMap.comp_apply, ← hx]
    rfl

end Factor

section Matrices

variable {K : Type*} [Field K]
variable {m n r s : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s]

omit [Fintype s] [DecidableEq s] [Fintype m] [DecidableEq m] in
/-- [proved-standard; formal-checked] **Left factorization.** `T E = Y` has a solution exactly when every source
the encoder erases is erased by `Y`. -/
theorem exists_mul_left_eq_iff (E : Matrix r n K) (Y : Matrix s n K) :
    (∃ T : Matrix s r K, T * E = Y) ↔ ∀ v : n → K, E *ᵥ v = 0 → Y *ᵥ v = 0 := by
  have key : (∃ T : Matrix s r K, T * E = Y) ↔
      ∃ t : (r → K) →ₗ[K] (s → K), t ∘ₗ E.mulVecLin = Y.mulVecLin := by
    constructor
    · rintro ⟨T, rfl⟩
      exact ⟨T.mulVecLin, (Matrix.mulVecLin_mul T E).symm⟩
    · rintro ⟨t, ht⟩
      refine ⟨LinearMap.toMatrix' t, ?_⟩
      have h := congrArg LinearMap.toMatrix' ht
      rwa [LinearMap.toMatrix'_comp, ← Matrix.toLin'_apply', ← Matrix.toLin'_apply',
        LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at h
  rw [key, exists_comp_eq_iff_ker_le]
  constructor
  · intro h v hv
    have hk := h (LinearMap.mem_ker.mpr (by rwa [Matrix.mulVecLin_apply]))
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk
  · intro h v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    exact h v hv

omit [Fintype n] [DecidableEq n] [Fintype s] [DecidableEq s] in
/-- [proved-standard; formal-checked] **The Fredholm alternative over a field.** `D X = Y` has a solution exactly
when every covector annihilating `D` annihilates `Y`. -/
theorem exists_mul_right_eq_iff (D : Matrix m r K) (Y : Matrix m s K) :
    (∃ X : Matrix r s K, D * X = Y) ↔ ∀ v : m → K, v ᵥ* D = 0 → v ᵥ* Y = 0 := by
  have h := exists_mul_left_eq_iff Dᵀ Yᵀ
  simp only [Matrix.mulVec_transpose] at h
  rw [← h]
  constructor
  · rintro ⟨X, rfl⟩
    exact ⟨Xᵀ, by rw [Matrix.transpose_mul]⟩
  · rintro ⟨T, hT⟩
    refine ⟨Tᵀ, ?_⟩
    rw [← Matrix.transpose_transpose (D * Tᵀ), Matrix.transpose_mul, Matrix.transpose_transpose,
      hT, Matrix.transpose_transpose]

end Matrices

/-! ## Kernel modes: a rank factorization -/

section Modes

variable {K : Type*} [Field K]
variable {m n r : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-standard; formal-checked] Independent rows make the encoder onto its modes. -/
theorem mulVec_surjective_of_rows {E : Matrix r n K} (hE : LinearIndependent K E.row) :
    Function.Surjective E.mulVec := by
  have h1 : Module.finrank K (LinearMap.range E.mulVecLin) = Module.finrank K (r → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    exact hE.rank_matrix
  have h2 := Submodule.eq_top_of_finrank_eq h1
  intro y
  obtain ⟨x, hx⟩ := LinearMap.range_eq_top.mp h2 y
  exact ⟨x, hx⟩

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] An encoder onto its modes has independent rows. -/
theorem rows_of_mulVec_surjective {E : Matrix r n K} (h : Function.Surjective E.mulVec) :
    LinearIndependent K E.row := by
  rw [← Matrix.vecMul_injective_iff]
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp h
  intro v w hvw
  have h' := congrArg (fun u => u ᵥ* B) hvw
  simpa only [Matrix.vecMul_vecMul, hB, Matrix.vecMul_one] using h'

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] An encoder with independent rows cancels on the right. -/
theorem cancel_right_of_rows {s : Type*} {E : Matrix r n K} (hE : LinearIndependent K E.row)
    {A A' : Matrix s r K} (h : A * E = A' * E) : A = A' := by
  obtain ⟨B, hB⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp (mulVec_surjective_of_rows hE)
  rw [← Matrix.mul_one A, ← Matrix.mul_one A', ← hB, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h]

variable (K₀ : Matrix m n K) (D : Matrix m r K) (E : Matrix r n K)

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-standard; formal-checked] Through a decoder with independent columns, the kernel erases exactly what
the encoder erases. -/
theorem ker_eq_ker_encoder (hDE : D * E = K₀) (hD : LinearIndependent K D.col) :
    LinearMap.ker K₀.mulVecLin = LinearMap.ker E.mulVecLin := by
  have hinj : Function.Injective D.mulVec := Matrix.mulVec_injective_iff.mpr hD
  ext x
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← hDE, ← Matrix.mulVec_mulVec]
  constructor
  · intro h
    apply hinj
    rw [h, Matrix.mulVec_zero]
  · intro h
    rw [h, Matrix.mulVec_zero]

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-standard; formal-checked] Through an encoder with independent rows, the kernel reaches exactly what the
decoder reaches. -/
theorem range_eq_range_decoder (hDE : D * E = K₀) (hE : LinearIndependent K E.row) :
    LinearMap.range K₀.mulVecLin = LinearMap.range D.mulVecLin := by
  have hs : Function.Surjective E.mulVecLin := by
    rw [Matrix.coe_mulVecLin]
    exact mulVec_surjective_of_rows hE
  rw [← hDE, Matrix.mulVecLin_mul, LinearMap.range_comp, LinearMap.range_eq_top.mpr hs,
    Submodule.map_top]

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-standard; formal-checked] The count of modes of a rank factorization is the kernel's rank. -/
theorem rank_eq_card_modes (hDE : D * E = K₀) (hD : LinearIndependent K D.col)
    (hE : LinearIndependent K E.row) : K₀.rank = Fintype.card r := by
  have hinj : Function.Injective D.mulVecLin := by
    rw [Matrix.coe_mulVecLin]
    exact Matrix.mulVec_injective_iff.mpr hD
  rw [Matrix.rank, range_eq_range_decoder K₀ D E hDE hE, LinearMap.finrank_range_of_inj hinj,
    Module.finrank_fintype_fun_eq_card]

omit [DecidableEq r] in
/-- [proved-standard; formal-checked] **Every kernel has a rank factorization** through `rank K₀` modes. -/
theorem exists_rankFactorization :
    ∃ (D : Matrix m (Fin K₀.rank) K) (E : Matrix (Fin K₀.rank) n K),
      D * E = K₀ ∧ LinearIndependent K D.col ∧ LinearIndependent K E.row := by
  let b : Module.Basis (Fin K₀.rank) K (LinearMap.range K₀.mulVecLin) :=
    Module.finBasisOfFinrankEq K _ rfl
  let d : (Fin K₀.rank → K) →ₗ[K] (m → K) :=
    (LinearMap.range K₀.mulVecLin).subtype ∘ₗ b.equivFun.symm.toLinearMap
  let e : (n → K) →ₗ[K] (Fin K₀.rank → K) := b.equivFun.toLinearMap ∘ₗ K₀.mulVecLin.rangeRestrict
  have hde : d ∘ₗ e = K₀.mulVecLin := by
    ext x
    simp [d, e]
  have hd : ∀ x, LinearMap.toMatrix' d *ᵥ x = d x := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  have he : ∀ x, LinearMap.toMatrix' e *ᵥ x = e x := fun x => by
    rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
  refine ⟨LinearMap.toMatrix' d, LinearMap.toMatrix' e, ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hde, ← Matrix.toLin'_apply', LinearMap.toMatrix'_toLin']
  · rw [← Matrix.mulVec_injective_iff]
    intro x y hxy
    rw [hd, hd] at hxy
    exact b.equivFun.symm.injective (Subtype.val_injective hxy)
  · apply rows_of_mulVec_surjective
    intro y
    obtain ⟨z, hz⟩ := b.equivFun.surjective y
    obtain ⟨x, hx⟩ := LinearMap.surjective_rangeRestrict K₀.mulVecLin z
    exact ⟨x, by rw [he]; simp [e, hx, hz]⟩

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-derived; formal-checked] **Conduct runs through the modes**: the kernel's conduct of a source is the
decoded mode summary. -/
theorem conduct_through_modes (hDE : D * E = K₀) (x : n → K) : K₀ *ᵥ x = D *ᵥ (E *ᵥ x) := by
  rw [← hDE, Matrix.mulVec_mulVec]

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-derived; formal-checked] **The summary holds nothing beyond the conduct**: two sources share a mode
summary exactly when they share every conduct. -/
theorem summary_eq_iff_conduct_eq (hDE : D * E = K₀) (hD : LinearIndependent K D.col) (x y : n → K) :
    E *ᵥ x = E *ᵥ y ↔ K₀ *ᵥ x = K₀ *ᵥ y := by
  rw [conduct_through_modes K₀ D E hDE, conduct_through_modes K₀ D E hDE]
  exact ⟨fun h => by rw [h], fun h => Matrix.mulVec_injective_iff.mpr hD h⟩

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-derived; formal-checked] A conduct normalized by any receiving covector `ω` is the same for two sources
with one mode summary. -/
theorem normalized_eq_of_summary_eq [Fintype m] (hDE : D * E = K₀) (ω : m → K) {x y : n → K}
    (h : E *ᵥ x = E *ᵥ y) :
    (ω ⬝ᵥ (K₀ *ᵥ x))⁻¹ • (K₀ *ᵥ x) = (ω ⬝ᵥ (K₀ *ᵥ y))⁻¹ • (K₀ *ᵥ y) := by
  rw [conduct_through_modes K₀ D E hDE x, conduct_through_modes K₀ D E hDE y, h]

end Modes

/-! ## The summary of a source family, read after contraction -/

section Summary

variable {K : Type*} [Field K]
variable {m n r d : Type*} [Fintype n] [Fintype r]

/-- [definition] **The mode summary** of a source family with mass `w` and weighted current `J`: both contracted by
the encoder, the mass beside the current. -/
def summary (E : Matrix r n K) (w : n → K) (J : Matrix n d K) : (r → K) × Matrix r d K :=
  (E *ᵥ w, E * J)

/-- [definition] **The reading of a summary** at receiver `i` through the decoder: the decoded current over the
decoded mass. -/
def summaryRead (D : Matrix m r K) (M : (r → K) × Matrix r d K) (i : m) : d → K :=
  ((D *ᵥ M.1) i)⁻¹ • (D * M.2) i

/-- [definition] **The normalized conduct** of a source family at receiver `i`: the kernel's current over its
mass. -/
def normalizedConduct (K₀ : Matrix m n K) (w : n → K) (J : Matrix n d K) (i : m) : d → K :=
  ((K₀ *ᵥ w) i)⁻¹ • (K₀ * J) i

variable (K₀ : Matrix m n K) (D : Matrix m r K) (E : Matrix r n K)

/-- [proved-derived; formal-checked] **A summary reads the normalized conduct**: decoding the contracted mass and
current and dividing after gives the kernel's current over its mass. -/
theorem summaryRead_eq_normalizedConduct (hDE : D * E = K₀) (w : n → K) (J : Matrix n d K) (i : m) :
    summaryRead D (summary E w J) i = normalizedConduct K₀ w J i := by
  simp only [summaryRead, summary, normalizedConduct, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hDE]

/-- [proved-derived; formal-checked] Two source families with one summary have one normalized conduct at every
receiver. -/
theorem normalizedConduct_eq_of_summary_eq (hDE : D * E = K₀) {w w' : n → K} {J J' : Matrix n d K}
    (h : summary E w J = summary E w' J') (i : m) :
    normalizedConduct K₀ w J i = normalizedConduct K₀ w' J' i := by
  rw [← summaryRead_eq_normalizedConduct K₀ D E hDE, h, summaryRead_eq_normalizedConduct K₀ D E hDE]

/-- [proved-derived; formal-checked] Where the mass is nonzero, the mass times the reading returns the kernel's
current: the division loses nothing there. -/
theorem mass_smul_summaryRead (hDE : D * E = K₀) (w : n → K) (J : Matrix n d K) {i : m}
    (hm : (K₀ *ᵥ w) i ≠ 0) : (K₀ *ᵥ w) i • summaryRead D (summary E w J) i = (K₀ * J) i := by
  rw [summaryRead_eq_normalizedConduct K₀ D E hDE, normalizedConduct, smul_smul, mul_inv_cancel₀ hm,
    one_smul]

omit [Fintype r] in
/-- [proved-derived; formal-checked] **Contracted before normalization**: the summary of a weighted family of
source families is the weighted sum of their summaries. -/
theorem summary_sum {ι : Type*} (t : Finset ι) (a : ι → K) (w : ι → n → K) (J : ι → Matrix n d K) :
    summary E (∑ k ∈ t, a k • w k) (∑ k ∈ t, a k • J k) = ∑ k ∈ t, a k • summary E (w k) (J k) := by
  refine Prod.ext ?_ ?_
  · simp [summary, Prod.fst_sum, Matrix.mulVec_sum, Matrix.mulVec_smul]
  · simp [summary, Prod.snd_sum, Matrix.mul_sum, Matrix.mul_smul]

/-- [proved-derived; formal-checked] **The value leg**: a change of the value frame `V` on the summary's currents
acts on the reading from the right, the mass untouched. -/
theorem summaryRead_value_transport {e : Type*} [Fintype d] (V : Matrix d e K) (M : (r → K) × Matrix r d K)
    (i : m) : summaryRead D (M.1, M.2 * V) i = summaryRead D M i ᵥ* V := by
  simp only [summaryRead]
  rw [← Matrix.mul_assoc, Matrix.mul_apply_eq_vecMul (D * M.2) V, Matrix.smul_vecMul]

end Summary

/-! ### Participation classes: one factorization through classes -/

section Classes

variable {K : Type*} [Field K]
variable {m n c d : Type*} [Fintype n] [Fintype c] [DecidableEq c]

/-- [definition] **The class encoder** of a class map `π`: mode `k` reads the sources of class `k`. -/
def classEncoder (π : n → c) : Matrix c n K :=
  Matrix.of fun k i => if π i = k then 1 else 0

omit [Fintype n] in
/-- [proved-standard; formal-checked] A kernel whose score is constant on each class factors through the class
encoder. -/
theorem classKernel_factor (π : n → c) (b : Matrix m c K) :
    b * classEncoder π = Matrix.of fun q i => b q (π i) := by
  ext q i
  simp [classEncoder, Matrix.mul_apply]

omit [Fintype c] in
/-- [proved-standard; formal-checked] The class encoder's mass is the class mass. -/
theorem classEncoder_mulVec (π : n → c) (w : n → K) (k : c) :
    (classEncoder π *ᵥ w) k = ∑ i ∈ Finset.univ.filter (fun i => π i = k), w i := by
  simp [classEncoder, Matrix.mulVec, dotProduct, Finset.sum_filter]

omit [Fintype c] in
/-- [proved-standard; formal-checked] The class encoder's current is the class current. -/
theorem classEncoder_mul (π : n → c) (J : Matrix n d K) (k : c) (j : d) :
    ((classEncoder π : Matrix c n K) * J) k j = ∑ i ∈ Finset.univ.filter (fun i => π i = k), J i j := by
  simp [classEncoder, Matrix.mul_apply, Finset.sum_filter]

end Classes

/-! ## An action closes on the modes or returns its separating fibre -/

section Action

variable {K : Type*} [Field K]
variable {m n r d : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]

/-- [proved-standard; formal-checked] **A source action descends to the modes** (`E U = T E` for some `T`) exactly
when it carries the encoder's kernel into the kernel of `E U`. -/
theorem closes_iff_ker_le (E : Matrix r n K) (U : Matrix n n K) :
    (∃ T : Matrix r r K, E * U = T * E) ↔
      LinearMap.ker E.mulVecLin ≤ LinearMap.ker (E * U).mulVecLin := by
  have h := exists_mul_left_eq_iff E (E * U)
  constructor
  · rintro ⟨T, hT⟩ v hv
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    exact h.mp ⟨T, hT.symm⟩ v hv
  · intro hle
    obtain ⟨T, hT⟩ := h.mpr fun v hv => by
      have hk := hle (show v ∈ LinearMap.ker E.mulVecLin by
        rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply])
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hk
    exact ⟨T, hT.symm⟩

/-- [proved-derived; formal-checked] **An action closes on the modes or returns its separating fibre**, and exactly
one of the two holds: a modal `T` with `E U = T E`, or a source `v` the encoder erases whose image under `U` it
reads. -/
theorem closes_xor_separates (E : Matrix r n K) (U : Matrix n n K) :
    Xor (∃ T : Matrix r r K, E * U = T * E) (∃ v : n → K, E *ᵥ v = 0 ∧ E *ᵥ (U *ᵥ v) ≠ 0) := by
  rw [xor_iff_iff_not]
  have h := exists_mul_left_eq_iff E (E * U)
  simp only [not_exists, not_and, not_not, Matrix.mulVec_mulVec]
  rw [← h]
  exact ⟨fun ⟨T, hT⟩ => ⟨T, hT.symm⟩, fun ⟨T, hT⟩ => ⟨T, hT.symm⟩⟩

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] With independent encoder rows, a closed action's modal `T` is unique. -/
theorem modalAction_unique {E : Matrix r n K} (hE : LinearIndependent K E.row) {U : Matrix n n K}
    {T T' : Matrix r r K} (hT : E * U = T * E) (hT' : E * U = T' * E) : T = T' :=
  cancel_right_of_rows hE (hT.symm.trans hT')

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-derived; formal-checked] **The summary runs on the modes**: the summary of the acted family is the modal
action on the summary. -/
theorem summary_after_action {E : Matrix r n K} {U : Matrix n n K} {T : Matrix r r K} (hT : E * U = T * E)
    (w : n → K) (J : Matrix n d K) :
    summary E (U *ᵥ w) (U * J) = (T *ᵥ (summary E w J).1, T * (summary E w J).2) := by
  simp only [summary, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hT]

omit [DecidableEq n] [DecidableEq r] in
/-- [proved-derived; formal-checked] The conduct of the acted source is decoded from the modal action on the
summary. -/
theorem conduct_after_action {K₀ : Matrix m n K} {D : Matrix m r K} {E : Matrix r n K} {U : Matrix n n K}
    {T : Matrix r r K} (hDE : D * E = K₀) (hT : E * U = T * E) (x : n → K) :
    K₀ *ᵥ (U *ᵥ x) = D *ᵥ (T *ᵥ (E *ᵥ x)) := by
  rw [conduct_through_modes K₀ D E hDE, Matrix.mulVec_mulVec x E U, hT, ← Matrix.mulVec_mulVec]

end Action

/-! ## Rebase: a change of modal frame -/

section Rebase

variable {K : Type*} [Field K]
variable {m n r d : Type*} [Fintype n] [Fintype r] [DecidableEq n] [DecidableEq r]
variable (D : Matrix m r K) (E : Matrix r n K) {B : Matrix r r K}

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] The rebased decoder undoes the modal basis: `(D B⁻¹) B = D`. -/
theorem rebase_decoder_mul (hB : IsUnit B) : D * B⁻¹ * B = D := by
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB), Matrix.mul_one]

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] **Rebase keeps the factorization**: `D′ E′ = D E` with `E′ = B E`,
`D′ = D B⁻¹`. -/
theorem rebase_factor (hB : IsUnit B) : (D * B⁻¹) * (B * E) = D * E := by
  rw [← Matrix.mul_assoc, rebase_decoder_mul D hB]

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] **Rebase keeps the decoded summary**: `D′ M′ = D M` with `M′ = B M`. -/
theorem rebase_summary (hB : IsUnit B) (M : Matrix r d K) : (D * B⁻¹) * (B * M) = D * M := by
  rw [← Matrix.mul_assoc, rebase_decoder_mul D hB]

omit [Fintype n] [DecidableEq n] in
/-- [proved-derived; formal-checked] Every reading of a summary is unchanged by a rebase of its modal frame. -/
theorem rebase_summaryRead (hB : IsUnit B) (M : (r → K) × Matrix r d K) (i : m) :
    summaryRead (D * B⁻¹) (B *ᵥ M.1, B * M.2) i = summaryRead D M i := by
  simp only [summaryRead, Matrix.mulVec_mulVec, rebase_decoder_mul D hB, rebase_summary D hB]

omit [DecidableEq n] in
/-- [proved-derived; formal-checked] **A closed action is carried by conjugation**: if `E U = T E`, then
`E′ U = (B T B⁻¹) E′`. -/
theorem rebase_action (hB : IsUnit B) {U : Matrix n n K} {T : Matrix r r K} (hT : E * U = T * E) :
    (B * E) * U = (B * T * B⁻¹) * (B * E) := by
  have hinv : B⁻¹ * B = 1 := Matrix.nonsing_inv_mul B ((Matrix.isUnit_iff_isUnit_det B).mp hB)
  calc (B * E) * U = B * (T * E) := by rw [Matrix.mul_assoc, hT]
    _ = (B * T * B⁻¹) * (B * E) := by
      rw [Matrix.mul_assoc (B * T), ← Matrix.mul_assoc B⁻¹, hinv, Matrix.one_mul, Matrix.mul_assoc]

omit [Fintype n] [DecidableEq n] in
/-- [proved-standard; formal-checked] The rebased decoder keeps independent columns. -/
theorem rebase_cols (hB : IsUnit B) (hD : LinearIndependent K D.col) : LinearIndependent K (D * B⁻¹).col := by
  rw [← Matrix.mulVec_injective_iff] at hD ⊢
  have hBi : Function.Injective (B⁻¹).mulVec :=
    Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.mpr hB)
  intro x y h
  have h' : D *ᵥ (B⁻¹ *ᵥ x) = D *ᵥ (B⁻¹ *ᵥ y) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    exact h
  exact hBi (hD h')

omit [DecidableEq n] in
/-- [proved-standard; formal-checked] The rebased encoder keeps independent rows. -/
theorem rebase_rows (hB : IsUnit B) (hE : LinearIndependent K E.row) : LinearIndependent K (B * E).row := by
  apply rows_of_mulVec_surjective
  intro y
  obtain ⟨z, hz⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr hB y
  obtain ⟨x, hx⟩ := mulVec_surjective_of_rows hE z
  exact ⟨x, by rw [← Matrix.mulVec_mulVec, hx, hz]⟩

/-- [proved-standard; formal-checked] **The modes are derived**: two rank factorizations of one kernel through one
count of modes differ by an invertible modal basis, `E′ = B E` and `D′ = D B⁻¹`. -/
theorem rankFactorization_unique_up_to_rebase {K₀ : Matrix m n K} {D D' : Matrix m r K}
    {E E' : Matrix r n K} (hDE : D * E = K₀) (hD : LinearIndependent K D.col)
    (hE : LinearIndependent K E.row) (hDE' : D' * E' = K₀) (hD' : LinearIndependent K D'.col)
    (hE' : LinearIndependent K E'.row) :
    ∃ B : Matrix r r K, IsUnit B ∧ E' = B * E ∧ D' = D * B⁻¹ := by
  have hker := (ker_eq_ker_encoder K₀ D E hDE hD).symm.trans (ker_eq_ker_encoder K₀ D' E' hDE' hD')
  have hmem : ∀ v : n → K, E *ᵥ v = 0 ↔ E' *ᵥ v = 0 := fun v => by
    have hv := SetLike.ext_iff.mp hker v
    rwa [LinearMap.mem_ker, LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply] at hv
  obtain ⟨B, hB⟩ := (exists_mul_left_eq_iff E E').mpr fun v hv => (hmem v).mp hv
  obtain ⟨B', hB'⟩ := (exists_mul_left_eq_iff E' E).mpr fun v hv => (hmem v).mpr hv
  have h1 : B' * B = 1 := cancel_right_of_rows hE (by rw [Matrix.mul_assoc, hB, hB', Matrix.one_mul])
  have h2 : B * B' = 1 := cancel_right_of_rows hE' (by rw [Matrix.mul_assoc, hB', hB, Matrix.one_mul])
  have h3 : D' * B = D := cancel_right_of_rows hE (by rw [Matrix.mul_assoc, hB, hDE', hDE])
  refine ⟨B, ⟨⟨B, B', h2, h1⟩, rfl⟩, hB.symm, ?_⟩
  rw [Matrix.inv_eq_left_inv h1, ← h3, Matrix.mul_assoc, h2, Matrix.mul_one]

end Rebase

/-! ## Contextual factorization -/

section System

variable {K : Type*} [Field K]
variable {m r s : Type*} [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]

/-- [proved-standard; formal-checked] **The system's alternative**: `D X = Y` has a solution, or a covector `v` with
`vᵀ D = 0` reads `Y`, and exactly one of the two holds. -/
theorem solvable_xor_obstructed (D : Matrix m r K) (Y : Matrix m s K) :
    Xor (∃ X : Matrix r s K, D * X = Y) (∃ v : m → K, v ᵥ* D = 0 ∧ v ᵥ* Y ≠ 0) := by
  rw [xor_iff_iff_not, exists_mul_right_eq_iff]
  simp only [not_exists, not_and, not_not]

omit [Fintype m] [DecidableEq m] [DecidableEq r] in
/-- [proved-standard; formal-checked] **The affine family**: once `D X₀ = Y`, the solutions are exactly `X₀ + Z`
with `D Z = 0`. -/
theorem solutions_eq_particular_add_free (D : Matrix m r K) {Y : Matrix m s K} {X₀ : Matrix r s K}
    (h₀ : D * X₀ = Y) (X : Matrix r s K) : D * X = Y ↔ ∃ Z : Matrix r s K, D * Z = 0 ∧ X = X₀ + Z := by
  constructor
  · intro h
    exact ⟨X - X₀, by rw [Matrix.mul_sub, h, h₀, sub_self], by abel⟩
  · rintro ⟨Z, hZ, rfl⟩
    rw [Matrix.mul_add, h₀, hZ, add_zero]

end System

section Context

variable {K : Type*} [Field K] {P A C W : Type*} [AddCommGroup P] [Module K P] [AddCommGroup A]
  [Module K A] [AddCommGroup C] [Module K C] [AddCommGroup W] [Module K W]
variable (S : P →ₗ[K] A) (Ctx : P →ₗ[K] C) (Y : P →ₗ[K] W)

/-- [proved-standard; formal-checked] **A lift exists** (a decoder reading the return from the source and the
context) exactly when every occurrence combination silent to both is silent to the return. -/
theorem lift_iff :
    (∃ g : A × C →ₗ[K] W, g ∘ₗ S.prod Ctx = Y) ↔
      LinearMap.ker S ⊓ LinearMap.ker Ctx ≤ LinearMap.ker Y := by
  rw [exists_comp_eq_iff_ker_le, LinearMap.ker_prod]

/-- [proved-derived; formal-checked] **A lift or its obstruction**: a decoder through source and context exists, or
an occurrence combination silent to both is read by the return, and exactly one of the two holds. -/
theorem lift_xor_obstruction :
    Xor (∃ g : A × C →ₗ[K] W, g ∘ₗ S.prod Ctx = Y) (∃ p : P, S p = 0 ∧ Ctx p = 0 ∧ Y p ≠ 0) := by
  rw [xor_iff_iff_not, lift_iff]
  simp only [not_exists, not_and, not_not]
  constructor
  · intro h p hS hC
    exact LinearMap.mem_ker.mp
      (h (Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hS, LinearMap.mem_ker.mpr hC⟩))
  · intro h p hp
    obtain ⟨hS, hC⟩ := Submodule.mem_inf.mp hp
    exact LinearMap.mem_ker.mpr (h p (LinearMap.mem_ker.mp hS) (LinearMap.mem_ker.mp hC))

/-- [definition] **The silent context** `N = C(ker S ⊓ ker Y)`: the context carried by the occurrence combinations
that neither the source nor the return reads. -/
def silentContext : Submodule K C :=
  (LinearMap.ker S ⊓ LinearMap.ker Y).map Ctx

/-- [proved-derived; formal-checked] Every decoder through source and context reads nothing on the silent context. -/
theorem decoder_kills_silentContext (g : A × C →ₗ[K] W) (hg : g ∘ₗ S.prod Ctx = Y) {c : C}
    (hc : c ∈ silentContext S Ctx Y) : g (0, c) = 0 := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hc
  obtain ⟨hS, hY⟩ := Submodule.mem_inf.mp hp
  rw [LinearMap.mem_ker] at hS hY
  have hgp : g (S p, Ctx p) = Y p := LinearMap.congr_fun hg p
  rw [hS] at hgp
  rw [hgp, hY]

/-- [proved-derived; formal-checked] **The contrast reads the context**: on a source-null occurrence the return is
the decoder read on the context alone. -/
theorem contrast_reads_context (g : A × C →ₗ[K] W) (hg : g ∘ₗ S.prod Ctx = Y) {p : P} (hp : S p = 0) :
    Y p = g (0, Ctx p) := by
  have hgp : g (S p, Ctx p) = Y p := LinearMap.congr_fun hg p
  rw [hp] at hgp
  exact hgp.symm

/-- [proved-derived; formal-checked] **Every decoder factors through the silent quotient** `C → C ⧸ N`. -/
theorem decoder_factors_through_silentQuotient (g : A × C →ₗ[K] W) (hg : g ∘ₗ S.prod Ctx = Y) :
    ∃ g' : A × (C ⧸ silentContext S Ctx Y) →ₗ[K] W,
      g' ∘ₗ LinearMap.prodMap LinearMap.id (silentContext S Ctx Y).mkQ = g := by
  rw [exists_comp_eq_iff_ker_le, LinearMap.ker_prodMap, LinearMap.ker_id, Submodule.ker_mkQ]
  rintro ⟨a, c⟩ hac
  obtain ⟨ha, hc⟩ := Submodule.mem_prod.mp hac
  rw [Submodule.mem_bot] at ha
  simp only at ha hc
  subst ha
  exact LinearMap.mem_ker.mpr (decoder_kills_silentContext S Ctx Y g hg hc)

/-- [proved-derived; formal-checked] **The lift reads the context modulo its silent part**: when a decoder exists,
one reads the source and the context's class in `C ⧸ N`. -/
theorem lift_through_silentQuotient (h : LinearMap.ker S ⊓ LinearMap.ker Ctx ≤ LinearMap.ker Y) :
    ∃ g' : A × (C ⧸ silentContext S Ctx Y) →ₗ[K] W,
      g' ∘ₗ S.prod ((silentContext S Ctx Y).mkQ ∘ₗ Ctx) = Y := by
  obtain ⟨g, hg⟩ := (lift_iff S Ctx Y).mpr h
  obtain ⟨g', hg'⟩ := decoder_factors_through_silentQuotient S Ctx Y g hg
  refine ⟨g', LinearMap.ext fun p => ?_⟩
  have h1 : g (S p, Ctx p) = Y p := LinearMap.congr_fun hg p
  have h2 : g' (S p, (silentContext S Ctx Y).mkQ (Ctx p)) = g (S p, Ctx p) :=
    LinearMap.congr_fun hg' (S p, Ctx p)
  exact h2.trans h1

/-- [proved-standard; formal-checked] The silent quotient kills the silent context and nothing else: no unobserved
context direction is dropped. -/
theorem silentQuotient_ker :
    LinearMap.ker (silentContext S Ctx Y).mkQ = silentContext S Ctx Y :=
  Submodule.ker_mkQ _

/-- [proved-derived; formal-checked] **Silent together**: on the source-null occurrences, the context read modulo
`N` vanishes exactly where the return does. -/
theorem silent_kernel (h : LinearMap.ker S ⊓ LinearMap.ker Ctx ≤ LinearMap.ker Y) :
    LinearMap.ker S ⊓ LinearMap.ker ((silentContext S Ctx Y).mkQ ∘ₗ Ctx) =
      LinearMap.ker S ⊓ LinearMap.ker Y := by
  ext p
  simp only [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  constructor
  · rintro ⟨hS, hN⟩
    refine ⟨hS, ?_⟩
    obtain ⟨w, hw, hwp⟩ := Submodule.mem_map.mp hN
    obtain ⟨hwS, hwY⟩ := Submodule.mem_inf.mp hw
    rw [LinearMap.mem_ker] at hwS hwY
    have hd : p - w ∈ LinearMap.ker S ⊓ LinearMap.ker Ctx :=
      Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr (by rw [map_sub, hS, hwS, sub_zero]),
        LinearMap.mem_ker.mpr (by rw [map_sub, hwp, sub_self])⟩
    have hY := LinearMap.mem_ker.mp (h hd)
    rwa [map_sub, hwY, sub_zero] at hY
  · rintro ⟨hS, hY⟩
    exact ⟨hS, Submodule.mem_map.mpr
      ⟨p, Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hS, LinearMap.mem_ker.mpr hY⟩, rfl⟩⟩

omit [AddCommGroup A] [Module K A] [AddCommGroup C] [Module K C] [AddCommGroup W] [Module K W] in
/-- [proved-standard; formal-checked] Two readings that vanish at the same places of a subspace map it onto images of
one dimension. -/
theorem finrank_map_eq_of_inf_ker_eq [FiniteDimensional K P] {W₁ W₂ : Type*} [AddCommGroup W₁] [Module K W₁]
    [AddCommGroup W₂] [Module K W₂] (p : Submodule K P) (f₁ : P →ₗ[K] W₁) (f₂ : P →ₗ[K] W₂)
    (h : p ⊓ LinearMap.ker f₁ = p ⊓ LinearMap.ker f₂) :
    Module.finrank K (p.map f₁) = Module.finrank K (p.map f₂) := by
  have e₁ := LinearMap.finrank_range_add_finrank_ker (f₁.domRestrict p)
  have e₂ := LinearMap.finrank_range_add_finrank_ker (f₂.domRestrict p)
  rw [LinearMap.range_domRestrict, LinearMap.ker_domRestrict] at e₁ e₂
  have hk : Submodule.comap p.subtype (LinearMap.ker f₁) = Submodule.comap p.subtype (LinearMap.ker f₂) := by
    ext x
    have hx := SetLike.ext_iff.mp h (x : P)
    simp only [Submodule.mem_inf, x.2, true_and] at hx
    simpa only [Submodule.mem_comap, Submodule.subtype_apply] using hx
  rw [hk] at e₁
  omega

/-- [proved-derived; formal-checked] **The demonstrated context rank**: on the source-null occurrences, the context
read modulo `N` and the return have one rank (the Rust's `rank(q C K) = rank(Y K)`). -/
theorem demonstrated_rank_eq [FiniteDimensional K P]
    (h : LinearMap.ker S ⊓ LinearMap.ker Ctx ≤ LinearMap.ker Y) :
    Module.finrank K ((LinearMap.ker S).map Y) =
      Module.finrank K ((LinearMap.ker S).map ((silentContext S Ctx Y).mkQ ∘ₗ Ctx)) :=
  finrank_map_eq_of_inf_ker_eq _ _ _ (silent_kernel S Ctx Y h).symm

end Context

/-! ## Witnesses over `ℚ` -/

section Witness

/-- [definition] The witness kernel: three receivers reading three sources, the third receiver the sum of the
first two. -/
def kernel3 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 1, 0; 0, 0, 1; 1, 1, 1]

/-- [definition] Its decoder through two modes. -/
def decoder3 : Matrix (Fin 3) (Fin 2) ℚ := !![1, 0; 0, 1; 1, 1]

/-- [definition] Its encoder onto two modes: the first mode reads the first two sources together, the second the
third. -/
def encoder3 : Matrix (Fin 2) (Fin 3) ℚ := !![1, 1, 0; 0, 0, 1]

/-- [proved-derived; formal-checked] **Witness**: the kernel factors through its two modes. -/
theorem witness_factor : decoder3 * encoder3 = kernel3 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [decoder3, encoder3, kernel3, Matrix.mul_apply, Fin.sum_univ_two]

/-- [proved-derived; formal-checked] **Witness**: the decoder's two columns are independent. -/
theorem witness_decoder_cols : LinearIndependent ℚ decoder3.col := by
  rw [← Matrix.mulVec_injective_iff]
  intro x y h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [decoder3, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  funext i
  fin_cases i
  · exact h0
  · exact h1

/-- [proved-derived; formal-checked] **Witness**: the encoder's two rows are independent. -/
theorem witness_encoder_rows : LinearIndependent ℚ encoder3.row := by
  rw [← Matrix.vecMul_injective_iff]
  intro x y h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp [encoder3, Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h0 h2
  funext i
  fin_cases i
  · exact h0
  · exact h2

/-- [proved-derived; formal-checked] **Witness**: the kernel has rank two, read from its factorization. -/
theorem witness_rank : kernel3.rank = 2 := by
  rw [rank_eq_card_modes kernel3 decoder3 encoder3 witness_factor witness_decoder_cols witness_encoder_rows,
    Fintype.card_fin]

/-- [definition] A source action scaling the first two sources by `2` and the third by `3`. -/
def scale3 : Matrix (Fin 3) (Fin 3) ℚ := !![2, 0, 0; 0, 2, 0; 0, 0, 3]

/-- [definition] Its modal action. -/
def scaleModes : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, 3]

/-- [proved-derived; formal-checked] **Witness**: the scaling closes on the modes, `E U = T E`. -/
theorem witness_closes : encoder3 * scale3 = scaleModes * encoder3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [encoder3, scale3, scaleModes, Matrix.mul_apply, Fin.sum_univ_succ]

/-- [definition] A source action that scales the second source alone. -/
def separating3 : Matrix (Fin 3) (Fin 3) ℚ := !![1, 0, 0; 0, 2, 0; 0, 0, 1]

/-- [definition] The direction the encoder erases: the first source against the second. -/
def separatingDirection : Fin 3 → ℚ := ![1, -1, 0]

/-- [proved-derived; formal-checked] **Witness**: the encoder erases `(1, −1, 0)` and reads its image under the
action as `(−1, 0)`. -/
theorem witness_separates :
    encoder3 *ᵥ separatingDirection = 0 ∧
      encoder3 *ᵥ (separating3 *ᵥ separatingDirection) = ![-1, 0] := by
  constructor
  · funext i
    fin_cases i <;> simp [encoder3, separatingDirection, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · funext i
    fin_cases i <;>
      norm_num [encoder3, separating3, separatingDirection, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

/-- [proved-derived; formal-checked] **Witness**: so that action does not close on the modes. -/
theorem witness_does_not_close : ¬ ∃ T : Matrix (Fin 2) (Fin 2) ℚ, encoder3 * separating3 = T * encoder3 := by
  have hx := closes_xor_separates encoder3 separating3
  rw [xor_iff_iff_not] at hx
  rw [hx, not_not]
  refine ⟨separatingDirection, witness_separates.1, ?_⟩
  rw [witness_separates.2]
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-- [definition] A target the kernel reaches. -/
def target3 : Matrix (Fin 3) (Fin 1) ℚ := !![2; 1; 3]

/-- [definition] A particular solution for it. -/
def particular3 : Matrix (Fin 3) (Fin 1) ℚ := !![1; 1; 1]

/-- [definition] A free direction of the kernel. -/
def free3 : Matrix (Fin 3) (Fin 1) ℚ := !![1; -1; 0]

/-- [proved-derived; formal-checked] **Witness**: a consistent system with its particular solution, a free direction,
and a second member of its affine family. -/
theorem witness_consistent :
    kernel3 * particular3 = target3 ∧ kernel3 * free3 = 0 ∧ kernel3 * (particular3 + free3) = target3 := by
  have h1 : kernel3 * particular3 = target3 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [kernel3, particular3, target3, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num
  have h2 : kernel3 * free3 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [kernel3, free3, Matrix.mul_apply, Fin.sum_univ_succ]
  exact ⟨h1, h2, (solutions_eq_particular_add_free kernel3 h1 _).mpr ⟨free3, h2, rfl⟩⟩

/-- [definition] A target the kernel does not reach. -/
def obstructed3 : Matrix (Fin 3) (Fin 1) ℚ := !![2; 1; 4]

/-- [definition] Its obstruction: the third receiver against the first two. -/
def obstruction3 : Fin 3 → ℚ := ![1, 1, -1]

/-- [proved-derived; formal-checked] **Witness**: `v = (1, 1, −1)` annihilates the kernel and reads `−1` on the
target. -/
theorem witness_obstructed : obstruction3 ᵥ* kernel3 = 0 ∧ obstruction3 ᵥ* obstructed3 = ![-1] := by
  constructor
  · funext j
    fin_cases j <;> simp [kernel3, obstruction3, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  · funext j
    fin_cases j
    simp [obstructed3, obstruction3, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
    norm_num

/-- [proved-derived; formal-checked] **Witness**: so the obstructed system has no solution. -/
theorem witness_no_solution : ¬ ∃ X : Matrix (Fin 3) (Fin 1) ℚ, kernel3 * X = obstructed3 := by
  have hx := solvable_xor_obstructed kernel3 obstructed3
  rw [xor_iff_iff_not] at hx
  rw [hx, not_not]
  refine ⟨obstruction3, witness_obstructed.1, ?_⟩
  rw [witness_obstructed.2]
  intro h
  have h0 := congrFun h 0
  norm_num at h0

/-- [definition] The Rust's first context test: a source reading both occurrences together. -/
def ctxSource2 : Matrix (Fin 1) (Fin 2) ℚ := !![1, 1]

/-- [definition] A context reading them together too. -/
def ctxContext2 : Matrix (Fin 1) (Fin 2) ℚ := !![2, 2]

/-- [definition] A return reading their difference. -/
def ctxReturn2 : Matrix (Fin 1) (Fin 2) ℚ := !![1, -1]

/-- [proved-derived; formal-checked] **Witness**: the combination `(1, −1)` is silent to source and context and read
by the return, so no decoder exists. -/
theorem witness_context_obstructed :
    ¬ ∃ g : (Fin 1 → ℚ) × (Fin 1 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ),
      g ∘ₗ ctxSource2.mulVecLin.prod ctxContext2.mulVecLin = ctxReturn2.mulVecLin := by
  have hx := lift_xor_obstruction ctxSource2.mulVecLin ctxContext2.mulVecLin ctxReturn2.mulVecLin
  rw [xor_iff_iff_not] at hx
  rw [hx, not_not]
  refine ⟨![1, -1], ?_, ?_, ?_⟩
  · funext i
    fin_cases i
    simp [ctxSource2, Matrix.mulVec, dotProduct]
  · funext i
    fin_cases i
    simp [ctxContext2, Matrix.mulVec, dotProduct]
  · intro h
    have h0 := congrFun h 0
    simp [ctxReturn2, Matrix.mulVec, dotProduct] at h0

/-- [definition] The Rust's second context test: a source reading three occurrences together. -/
def ctxSource3 : Matrix (Fin 1) (Fin 3) ℚ := !![1, 1, 1]

/-- [definition] A context reading the first two apart, the third, and a third direction no occurrence reaches. -/
def ctxContext3 : Matrix (Fin 3) (Fin 3) ℚ := !![1, -1, 0; 0, 0, 1; 0, 0, 0]

/-- [definition] A return reading the first two apart. -/
def ctxReturn3 : Matrix (Fin 1) (Fin 3) ℚ := !![1, -1, 0]

/-- [proved-derived; formal-checked] **Witness**: the second test lifts, since every occurrence combination the
context does not read is one the return does not read. -/
theorem witness_context_lifts :
    LinearMap.ker ctxSource3.mulVecLin ⊓ LinearMap.ker ctxContext3.mulVecLin ≤
      LinearMap.ker ctxReturn3.mulVecLin := by
  intro p hp
  obtain ⟨_, hC⟩ := Submodule.mem_inf.mp hp
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hC ⊢
  have h0 := congrFun hC 0
  funext i
  fin_cases i
  simpa [ctxContext3, ctxReturn3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h0

/-- [proved-derived; formal-checked] **Witness**: its silent context holds `(0, 1, 0)` and not the unobserved third
context direction `(0, 0, 1)`, which the quotient keeps. -/
theorem witness_silentContext :
    ![0, 1, 0] ∈ silentContext ctxSource3.mulVecLin ctxContext3.mulVecLin ctxReturn3.mulVecLin ∧
      ![0, 0, 1] ∉ silentContext ctxSource3.mulVecLin ctxContext3.mulVecLin ctxReturn3.mulVecLin := by
  constructor
  · refine Submodule.mem_map.mpr ⟨![-1 / 2, -1 / 2, 1], Submodule.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext i
      fin_cases i
      simp [ctxSource3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      norm_num
    · rw [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      funext i
      fin_cases i
      simp [ctxReturn3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · rw [Matrix.mulVecLin_apply]
      funext i
      fin_cases i <;> simp [ctxContext3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  · intro h
    obtain ⟨p, _, hp⟩ := Submodule.mem_map.mp h
    rw [Matrix.mulVecLin_apply] at hp
    have h2 := congrFun hp 2
    simp [ctxContext3, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h2

end Witness

end Holonics.Compression.KernelModes
