# The Pontryagin bound places a skew generator's modes, a reversed carrier passes the trace faces, a revolute joint moves at its Cayley rate, left to right is the opposite group, and the carry tower is the b-adic tower, in Lean

November 19, 05:35 UTC. The ninth formalization pass over #410, its tenth set, after [the
ninth](2026-11-19_THE_SIEVE_TOWER_IS_A_LAW_OF_ANY_MULTIPLICATIVE_RECURRENCE_ONE_CHART_CERTIFIES_AN_IRREDUCIBLE_CURVE_FRICTION_PRICES_A_HELD_MODE_A_SOLVED_CHARTS_BITS_FOLLOW_THE_HADAMARD_BOUND_AND_FRAME_DRAGGING_IS_A_FLUX_IN_LEAN.md)
(#1019). Five new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #54, #408, #73.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Transport/PontryaginBound` | For `G` nondegenerate Hermitian with `κ` negative squares and `A` `G`-skew (`AᴴG + GA = 0`), generalized eigenspaces whose eigenvalues have `λ + μ̄ ≠ 0` are `G`-orthogonal (`pair_eq_zero_of_gen`, `gSkew_gen_orthogonal`), so the span over `Re λ > 0` is `G`-neutral (`rightHalf_neutral`), and a neutral subspace has dimension at most `min(κ, n − κ)` (`neutral_finrank_le`): at most `min(κ, n − κ)` eigenvalues counted with algebraic multiplicity lie in each open half-plane (`pontryagin_bound_roots`, `pontryagin_bound_roots_left`), attained by `diag(1, −1)`, `[[0, 1], [1, 0]]` (`swap_attains`); the spectrum is symmetric under `λ ↦ −λ̄` (`gSkew_eigen_reflect`), the modes on the imaginary axis span at least `n − 2 min(κ, n − κ)` over ℂ, all of it for `G ≻ 0` (`onAxis_finrank_ge`, `onAxis_eq_top_of_posDef`); a `G`-self-adjoint generator has real spectrum for `G ≻ 0` and at most `min(κ, n − κ)` eigenvalues in the upper half-plane otherwise, the quarter-turn `i` carrying one statement to the other (`gSelfAdjoint_eigenvalue_im_eq_zero`, `gSelfAdjoint_roots_upper`, `gSelfAdjoint_iff_quarter_turn`); the lossless chain `ΩG` is `G`-skew and obeys the bound, while a dissipation adds the rate form `−2GMG` (`lossless_chain_gSkew`, `chain_pontryagin_bound`, `chain_rateForm`). | #410's box "Signature placement and spectral licences (from #54)"; `docs/ELEMENTARY_OBJECTS.md` §6 and the winding guide §3 | `tube.pontryagin-bound` (now formal-checked), `tube.g-skew-on-axis` (new), `tube.g-self-adjoint-real-spectrum` (new), `tube.lossless-chain-g-skew` (new), `receipt.seam-g-skew` |
| `Transport/TraceFacesGeneral` | A unit carrier conserves the determinant, the trace sequence, the transfer determinant and the characteristic polynomial of any material, singular and reset included (`carry_conserves_*`), and the owner's three theorems follow (`recovers_carried_*`); a carrier that is not invertible passes the faces between a material factored through it and the reversed product: `det(1 − T·AB) = det(1 − T·BA)` and `tr((AB)^(k+1)) = tr((BA)^(k+1))` for any sizes, `X^|n| χ(AB) = X^|m| χ(BA)` (`transfer_determinant_mul_comm`, `trace_pow_mul_comm`, `charpoly_mul_comm_rect`), and a reset `E² = E` gives `E P E` the faces of `P E` (`reset_compression_charpoly`), while the determinant and the zeroth trace read the sizes and a singular intertwiner conserves nothing (`rect_det_differs`, `singular_intertwiner_breaks_trace`); Newton's identities hold division-free on every commutative ring, in the transfer polynomial's coefficients and in the characteristic polynomial's (`newton_transfer`, `newton_charpoly`, `two_site_newton`), and the traces decide the characteristic polynomial where `1, …, n` cancel, over every ℚ-algebra and every domain of characteristic zero, but not in `ZMod p` at size `p`, where the zero and the identity share every trace (`charpoly_eq_of_trace_eq`, `charpoly_eq_of_trace_eq_charZero`, `zmod_charpolys_differ`); block products for sites of any sizes, with the owner's two-by-two theorems as their case (`transfer_determinant_blockDiagonal'`, `charpoly_blockDiagonal'`, `trace_pow_blockDiagonal'`), and the Kronecker composite's trace sequence (`trace_pow_kronecker`). | #410's boxes "Trace faces of arbitrary material" and "The certified wake, and the turn traces' Newton identities"; `Transport/NavigatorTraceFaces` | `trace.reversed-carrier` (new), `trace.newton-identities` (new), `trace.phase-carriage-conserves-faces`, `trace.det-one-minus-tm`, `navigator.trace-faces`, `aeon.zeta-log-derivative` |
| `Transport/SerialChainJacobian` | A proper rotation recharts the hat map, `R[u]×Rᵀ = [Ru]×`, a reflection reverses the cross product, and the skew part reads the axis, `R vee(R − Rᵀ) = vee(R − Rᵀ)`, parallel to every fixed vector off the identity and zero at a half-turn (`proper_conj_crossMat`, `reflectionZ_reverses`, `proper_skew_axis`, `proper_skew_axis_parallel`, `halfTurnX_skew_zero`), beside `Geometry/Motion`'s covariance and axis; the Cayley rotation about any axis `u` is proper, satisfies `(1 − t[u]×)C = 1 + t[u]×`, composes by half-angle addition `C(s)C(t) = C((s + t)/(1 − (u·u)st))` and moves at `C′ = ω[u]×C`, `ω = 2/(1 + (u·u)t²)`, the same in body and space, with `θ = 2 arctan t` and `C = 1 + sin θ K + (1 − cos θ)K²` on a unit axis (`cayleyRot_proper`, `cayleyRot_mul`, `hasDerivAt_cayleyRot`, `cayleyRot_body_rate`, `cayleyRot_angle`), the owner's `z` chart its case (`cayleyRot_z`), and the group law with `C′(0) = 2[u]×` forcing that rate (`cayley_rate_of_group_law`); a chain's spatial column is `Ad` of its prefix applied to the joint's twist, a Cayley joint's `[P(ωu)]×` about the moved pivot (`chain_spatial_column`, `cayley_chain_column`, `revolute_chain_point_rate`); and the prototype's `spatial_jacobian` loop is `zipWith rechart` over the serial prefixes, rechart composing contravariantly (`rechart_compose`, `spatialColumns_eq_zipWith`). | #410's boxes "The serial-chain Jacobian (#408)" and "Pair/frame and port realization (#408)" (its first clause); `Transport/SerialScrewChain`; the prototype's `serial.rs` at `13f8c734` | `chain.cayley-rate` (new), `chain.spatial-column-ad` (new), `motion.proper-skew-axis` (new), `screw.adjoint-rechart` (now formal-checked), `chain.jacobian-columns`, `chain.wrench-pullback`, `chain.cayley-z-chart`, `frame.cayley-rotations` |
| `Transport/MoveConventions` | Left-to-right composition is the opposite group: "`f`, then `g`" is `g * f = unop(op f * op g)`, a left-to-right word is the right-to-left product of its reverse, and the maps of a type under "then" are `(Function.End α)ᵐᵒᵖ` (`op_followedBy`, `followedByWord_eq_prod_reverse`, `thenEndEquivOp`); the serial owner's charts form a monoid whose application is an injective map into that opposite monoid and whose column matrix `[[L, t], [0, 1]]` multiplies right to left, `H(f then g) = H g · H f`, so its `configuration` is the column product of the reversed word and its `serialConfiguration` of the word as written (`applyHom_injective`, `homogeneous_compose`, `homogeneous_configuration`, `homogeneous_serialConfiguration`); the cell's triangle holonomy in the opposite group is that of the reversed word (`triangleHolonomy_op`, `regauge_op`); the noncommuting triangle of two translations and a quarter turn reads the carry `2e₂` left to right and none right to left (`triangle_readings_differ`); the cochain sum is the holonomy on a commutative carrier and its first order along `exp(t aₑ)` in a Banach algebra, while the second order adds `[a, b] + [a, c] + [b, c]`, and on the Heisenberg steps a cell with cochain sum `0` has holonomy `1 + [a, b]/2 ≠ 1` (`additive_triangleHolonomy`, `holonomy_first_order`, `holonomy_second_order`, `heisenberg_cell_holonomy_ne_one`); a based point closes iff `(M − 1)x + t = 0`, the frame iff `M = 1, t = 0`, a turn closes its pivot and no frame, and the translation decides closure only when `M = 1`, all points or none (`point_closes_iff`, `frame_closes_iff`, `turn_closes_pivot_not_frame`, `translation_is_not_the_test`, `flat_closes_all_or_none`, `unique_closing_point`). | #410's box "Move-composition conventions for cell realization"; the winding guide §4; `Transport/CellHolonomy`, `Transport/SerialScrewChain`, `Geometry/Motion` | `holonomy.composition-convention` (now formal-checked), `holonomy.first-order-cochain` (new), `holonomy.point-frame-closure` (new), `winding.burgers-step` |
| `Foundation/CarryTower` | A word of `n` digits in base `b ≥ 1` is a face of `ZMod (bⁿ)` (`chartEquiv`), its adder, defined place by place with carries that are bits, is that ring's addition with the top carry `⌊(value w + value w′)/bⁿ⌋` released (`carry_le_one`, `value_addCarry`, `topCarry_eq`, `chartEquiv_addCarry`), and truncation is `padicTower b`'s restriction, commuting with the adder and the product (`wordFace_truncate`, `truncate_addCarry`, `truncate_mulCarry`), so the carry charts and the `b`-adic tower migrate into each other and share their sections (`chartMigration`, `sectionEquivPadicTower`); the sections are the digit streams, `ℤ_[p]` at a prime with digit `k` of `α` read as `(toZModPow (k+1) α).val / pᵏ mod p` (`streamEquiv`, `streamEquivPadic`, `streamEquivPadic_symm_apply`); a level-`m` face has `b^(n − m)` lifts at level `n` and the tower is plural for `b ≥ 2` (`fibre_card`, `restrict_not_injective`, `carryTower_plural`); the faces over one face form a tower whose sections are its observation fibre (`aboveSectionEquiv`); Hensel level by level: `f(A + t pⁿ) ≡ f(A) + t pⁿ f′(A)`, a root with `f′ ≠ 0` at level one lifts uniquely (`taylor_step`, `hensel_lift`), the roots form a sub-tower whose sections are the roots in `ℤ_[p]`, and a simple root modulo `pᵏ` is the face of exactly one of them, its tail in the unique arm (`rootSectionEquiv`, `hensel_thread_unique`, `hensel_padic_root_unique`, `henselThread_gluing`), with `X²`, `X² − 2` and `X² + 1` at `p = 2` (lifting twice, or not at all: obstructed) and `X² + 1` at `p = 5` (two threads: plural) inhabiting every arm of `GluingResult`. | #410's box "The carry tower"; the winding guide §6; packet 8 of the record of September 21 | `tower.carry-chart-tower` (new), `tower.above-face-tail` (new), `tower.hensel-thread` (now formal-checked), `tower.padic-plural`, `radix.closing-edge` |

The boxes these answer, by their opening words: "Signature placement and spectral licences"; "Trace faces of arbitrary
material"; "The serial-chain Jacobian (#408)"; "Move-composition conventions for cell realization"; "The carry tower".
Two are part done (§3): "Pair/frame and port realization (#408)", whose proper-rotation recharting and axis extraction
are stated, and "The certified wake, and the turn traces' Newton identities", whose Newton identities are stated.

One more box was found answered: "β joined to the membrane faces" is `Objects/Membrane` (#948, November 17), which
proves the face of a bounding membrane gauge-free, the linear globe's `β` that face and the elimination of an interior
`Λ_DN` (`membraneFace_gauge`, `linearGlobe_boundary_is_membrane_face`, `interior_elimination`); it is ticked with that
pointer.

## 2. What the pass corrected

1. **The Pontryagin bound needs no indefinite storage, counts with multiplicity, and its spectral symmetry is a
   theorem.** Atlas `tube.pontryagin-bound` read "G indefinite … at most min(κ, n − κ) eigenvalues" and "Lean lift owed
   (#54)": the bound holds for every nondegenerate Hermitian `G` (the definite case gives 0, `receipt.seam-g-skew`) and
   counts eigenvalues with algebraic multiplicity. `ELEMENTARY_OBJECTS` §6 tagged the symmetry `λ ↦ −λ̄`
   `[interpretation]` together with its `ξ(s) = ξ(1 − s)` reading; the symmetry is proved-standard and only the zeta
   reading is an interpretation, and the guide now separates them. The box's "symmetrizable generator" classically means
   `A = DS` with `D` positive diagonal and `S` symmetric, a case of the `G`-self-adjoint generator with `G ≻ 0` that is
   stated (`agent-inferred`). The off-axis bound does not follow from the symmetry but from the bound on each half; the
   symmetry adds that the halves are equal as sets of eigenvalues. The rate-form identity the chain reads lives in
   `Transport/HolonicInteraction` (`port_storage_rate`), not in `Transport/HolonicChain`.
2. **The owner's scope was unit material, and the traces decide where the integers cancel.** `NavigatorTraceFaces`'s
   scope read "invertible carriers", but every theorem there also takes unit material, since `phaseTransport` lives in a
   group; singular and reset material was outside it even under an invertible carrier, as the box's "unit-valued
   material" says. "The traces determine the coefficients only where `1, …, n` are units" is too strong: the condition
   is that they cancel, and over ℤ, where 2 is no unit, the traces still decide. Newton's identities were already held
   as one power-series identity (`aeon.zeta-log-derivative`, `Zeta.transferDet_derivative`); what was missing was their
   coefficient and characteristic-polynomial forms and the condition. "The certified wake" of the merged box has no
   source anywhere in the tree, so that half stays owed with its words.
3. **The rotation covariance was already held, the pair-rate form was already proved, and the rate `2/(1 + t²)` assumes
   a unit axis.** `SerialScrewChain`'s scope and `docs/FORMAL_FRAMEWORK.md` held "general proper-rotation cross-product
   covariance" as the remainder for #62, while `Geometry/Motion` already proved it with the axis (`proper_mulVec_cross`,
   `proper_has_axis`, atlas `motion.chasles-screw`); both now say so. The box "Pair/frame and port realization" listed
   the pair-rate form `C*J*DJC` as owed, and its congruence is
   `Transport/HelicalPairInteraction.faceForm_pairRatePort_congruence` (atlas `pair.rate-port-congruence`): what stays
   owed is its consumer, the native decoder `C(q)`. The serial box's angular rate `2/(1 + t²)` holds for the prototype's
   unit hinge axes; for an axis `u` the square-root-free rate is `2/(1 + (u·u)t²)`.
4. **"Translation alone is not the test" holds only for a turning holonomy, and the guide named no owner of the
   left-to-right order.** For `R = I` the translation decides closure, every point or none (`flat_closes_all_or_none`);
   the winding guide §4 and atlas `winding.burgers-step` now say so. The box named `Geometry/Motion` and
   `Transport/CellHolonomy` as owners, while the left-to-right composition is
   `Transport/SerialScrewChain.AffineMap3.compose` and Motion's `move_comp` composes right to left; the conventions in
   the tree stood side by side with no cross-reference (`Chronology.transportWord` acts right to left,
   `TransportWord.parallelTransport` lets the rightmost letter act first, `SerialScrewChain.configuration` composes left
   to right while `serialConfiguration` lets the rightmost act first, and `CellHolonomy`'s word follows the boundary
   while acting `g₂₀` first). The guide, `CellHolonomy`'s scope and the atlas now name them. Motion's `(1 − M)O = b` and
   the guide's `(R − I)x + t = 0` are one equation. The brief's two-by-two witness "where exp is a polynomial" holds for
   each step and not for their sum, which squares to `1`; it is proved by commutation, and the Heisenberg pair carries
   the polynomial case. `SerialScrewChain` ("finite exact affine charts", "exact matrices") and
   `Foundation/TransportWord` ("exact translation", "exact sum") called values exact; they now read rational, or
   nothing.
5. **The box's `IwasawaTower.padicTower` does not exist, the tower needs no prime, and the guide's Hensel owner states
   no lifting condition.** The name comes from packet 8 of the record of September 21; `padicTower` stands in
   `Foundation/PadicTower` (namespace `ContinuingTower`), and `IwasawaTower` only cites `padicSectionEquiv`. Its
   definition takes no primality, so `padicTower b` is the `b`-adic tower of every base; its docstring now says so. The
   winding guide §6 cited `Foundation/ContinuingTower` for "uniquely when the required lifting condition holds", where
   that module proves existence under surjective restriction and no lifting condition; the guide now names `CarryTower`
   for the thread and `ContinuingTower` for existence.
6. **The winding guide gave the Pontryagin bound's Lean lift to #54 while no module stated it.** §3 now names
   `PontryaginBound` and its theorems, and `ELEMENTARY_OBJECTS` §6 reads the bound as formal-checked.
7. **β's join to the membrane faces was read as open after it was proved.** `ELEMENTARY_OBJECTS` §7 closed on "Open: the
   join of `β` to the membrane's faces, and the Λ_DN join" while `Objects/Membrane` (#948) states the first and the
   elimination; the guide now names the owner, and what stays owed is `Λ_DN` read along a tube's stations and a tower's
   levels (#410's box "The `Λ_DN` join").

## 3. What each statement stands on, and what is left

- **The Pontryagin bound**: equal dimensions of the paired generalized eigenspaces at `μ` and `−μ̄`, the
  invariant-subspace theorem and the Krein signature of the modes on the axis, and the placement of a dissipative chain
  with indefinite storage (atlas `tube.chain-placement`, whose owner is still not located) are not stated.
- **The trace faces**: coupled sites, the Kronecker composite's transfer determinant and products over infinitely many
  sites are not stated, and "the certified wake" waits for a source that defines it.
- **The serial chain**: the exponential of a twist, the product at `(u·u)st = 1` and the lifted winding (the prototype's
  extra turns), the prismatic and screw rows beyond the general column, the wrench pullback `τ = JᵀW`, and the HNN
  consumer's configuration, rate, storage and current chart maps (found nowhere in the tree) are not stated.
- **The conventions**: no logarithm of a holonomy and no general Baker–Campbell–Hausdorff series; the linearization that
  identifies a nonabelian holonomy's fields with `Foundation/HodgeReceiver`'s cochains is not built.
- **The carry tower**: addition of digit streams with their unending carry, a digit recurrence for multiplication, the
  general condition `|f(a)| < |f′(a)|²` with Newton's quadratic convergence, and the thread count of `X²` at `p = 2`
  (its finite lifts plural, its one thread that of `0`) are not stated.

## 4. Receipt

- Workers on disjoint owner paths, at most three at a time, wrote the five modules; the lead re-checked each single file (exit 0, no warnings), corrected one witness sentence in the conventions module (a matrix squaring to `1` has an unending exponential series, not "no polynomial"), repointed the owed sentences, found the membrane box answered, and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the five modules and the five `Holonics` modules whose docstrings changed (`Transport/NavigatorTraceFaces`, `Transport/SerialScrewChain`, `Transport/CellHolonomy`, `Foundation/TransportWord`, `Foundation/PadicTower`) read `Build completed successfully (8755 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, every tracked research module, since the census reads unrooted=0) read `Build completed successfully (10596 jobs)`, exit 0; `Holonics` read `Build completed successfully (9166 jobs)`, exit 0. The warnings printed are other modules' (unused variables, universe notes), none in a changed file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
