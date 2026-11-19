# A congruence's rate is a boost and a turn and focuses within n over its expansion, a circulant's inertia is read by its windings, and an action closes on a kernel's modes or returns its separating direction, in Lean

November 19, 06:58 UTC. The twelfth formalization pass over #410, its thirteenth set, after [the
twelfth](2026-11-19_A_RING_PATHS_LOG_RATIO_IS_ITS_LIFTS_ENTROPY_READING_AND_ITS_MEAN_CARRY_IS_THE_CURRENT_AN_INTERCONNECTION_CARRIES_ITS_STEP_ITS_RESTRICTION_AND_JOINT_RECEPTION_AND_A_RETENTION_COUNTS_ITS_ACTIVE_GRAM_MODES_IN_LEAN.md)
(#1023). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #73, #145.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Physics/Spacetime/Raychaudhuri` | A congruence's rate `B = J′J⁻¹` splits uniquely as `(θ/n)·1 + σ + ω` (expansion, symmetric traceless shear, antisymmetric rotation), with `tr(B²) = θ²/n + ⟨σ, σ⟩ − ⟨ω, ω⟩` (`split_eq`, `split_unique`, `trace_mul_self`), and the rotation and symmetric part are `Geometry/Motion`'s turn and boost at the comoving metric (`rotation_eq_turn`, `symPart_eq_boost`); in any complete normed `ℝ`-algebra `J″ = −RJ` gives the Riccati law `B′ = −B² − R` (`riccati`), whose trace on real matrices is Raychaudhuri's equation `θ′ = −θ²/n − ⟨σ, σ⟩ + ⟨ω, ω⟩ − tr R` (`matrix_riccati`, `raychaudhuri`), and for a symmetric tide its antisymmetric part is `ω′ = −(Sω + ωS)` and its traceless part the shear's law (`rotation_law`, `rotation_rate_zero`, `shear_law`); a rotation-free congruence with `tr R ≥ 0` and `θ < 0` on `[0, T]` has `T < n/|θ(0)|`, from the deviation equation directly, and `θ(t) = nθ₀/(n + θ₀t)` shows the bound cannot be lowered (`inv_expansion_ge`, `caustic_within`, `no_negative_expansion_past_caustic`, `caustic_of_deviation`, `caustic_sharp`); a tensor with the curvature symmetries and vanishing `η`-trace has symmetric traceless electric and magnetic parts, and a tide equal to `E` leaves Raychaudhuri's rate as at `R = 0` (`electric_symm`, `electric_traceless`, `magnetic_traceless`, `magnetic_symm`, `raychaudhuriRate_electric`); over ℚ with `n = 3` the field-theory passage's `CongruenceLedger.returnedExpansionRate` is `raychaudhuriRate` with its slots filled (`ledger_eq_raychaudhuriRate`, `tidal_trace_reads_sector`) | #410's box "Curvature's strain and rotation" (part); the Swing record of September 28, §5.6 and §9; `Geometry/Motion`, `Geometry/Deviation`, `Physics/HolonicFieldTheoryPassage.CongruenceLedger`, `Physics/Spacetime/StressEnergy` | `coupling.congruence-kinematic-split`, `coupling.raychaudhuri-riccati`, `coupling.focusing-caustic`, `coupling.weyl-electric-magnetic` (new), `coupling.deviation-focus`, `coupling.holonic-field-theory-passage`, `coupling.holonic-focusing-sectors` |
| `Mathematics/CirculantInertia` | For any additive character `ψ` of `ℤ/n` into a commutative ring, the first-row circulant `circ c` has the colour `v_k(j) = ψ(jk)` as an eigenvector with eigenvalue its symbol at `ψ(k)`, `f(x) = Σ_j c_j x^j`, and for any `ω` with `ωⁿ = 1` the same holds for `v_k(j) = ω^(jk)` (`circ_mulVec_colour`, `circ_mulVec_pow`; Mathlib's `circulant`, the transpose, reads colour `k` at `f(ω^(−k))`, `circulant_mulVec_colour`); the Fourier transform diagonalizes it, `det(x − C) = ∏_k (x − f(ψ(k)))` (`dft_circ`, `charpoly_circ`); a real symmetric row reads `λ_k = c₀ + Σ_(0<2m<n) c_m β_(mk) + [2 ∣ n] c_(n/2) (−1)^k` with `β_m = 2cos(2πm/n)`, an integer combination of star values for integer `c` (`eval_symbol_symm`, `eigen_openHalf`, `eval_symbol_int_symm`); the cycle adjacency has `λ_k = β_k`, negative exactly for `n < 4k < 3n`, null exactly at `4k = n` or `3n`, so a null passage exists iff `4 ∣ n`, and RingSpectrum's cycle Laplacian is `circ(2e₀ − c)` with squared gap `2 − β_k` (`eval_symbol_cycleAdj`, `beta_neg_iff`, `beta_eq_zero_iff`, `exists_beta_eq_zero_iff`, `cycleLaplacian_eq_circ`, `gapSq_eq_two_sub_beta`); for a rational symbol, colour `k` is null iff `Φ_(n/gcd(k, n))` divides it, one polynomial division with its quotient as witness (`aeval_eq_zero_iff_cyclotomic_dvd`, `eq_cyclotomic_mul_divByMonic`, `eval_symbol_eq_zero_iff`); negation exchanges the positive and negative classes and keeps the null class, inertia `(p, z, q) ↦ (q, z, p)` (`inertia_neg`, `partition_neg`, `inertia_eigen_neg`); at `n = 8` the cycle reads inertia `(3, 2, 3)` and `Φ₄ ∣ X + X⁷` (`inertia_cycle_eight`, `cyclotomic_four_dvd_cycle_eight`) | #410's box "`winding.circulant-inertia`, `winding.cyclotomic-null-test`, `winding.hand-is-convention`"; the retired `crates/holonics/src/geometry/winding_inertia.rs` (removed at `d329cb541`); `Mathematics/OnePlaneRing`, `Mathematics/RingSpectrum` | `winding.circulant-inertia`, `winding.cyclotomic-null-test`, `winding.hand-is-convention` |
| `Compression/KernelModes` | Over any field, a linear reading factors through another exactly when its kernel contains the other's, with the matrix forms `T E = Y` and the Fredholm alternative for `D X = Y` (`exists_comp_eq_iff_ker_le`, `exists_mul_left_eq_iff`, `exists_mul_right_eq_iff`); every kernel has a rank factorization `K₀ = D E` through `rank K₀` modes, with `ker K₀ = ker E`, `range K₀ = range D`, unique up to an invertible modal basis (`exists_rankFactorization`, `ker_eq_ker_encoder`, `range_eq_range_decoder`, `rank_eq_card_modes`, `rankFactorization_unique_up_to_rebase`); conduct runs through the modes, two sources share a summary exactly when they share every conduct, and the summary `(E w, E J)` of a family read at a receiver is its normalized conduct `(K₀J)ᵢ/(K₀w)ᵢ`, contracted before the division (`conduct_through_modes`, `summary_eq_iff_conduct_eq`, `summaryRead_eq_normalizedConduct`, `summary_sum`), with a score constant on participation classes factoring through the class encoder (`classKernel_factor`); a source action `U` closes on the modes, `E U = T E`, exactly when `ker E ≤ ker(E U)`, and otherwise a direction the encoder erases and the action exposes is returned, exactly one of the two (`closes_iff_ker_le`, `closes_xor_separates`, `modalAction_unique`); a rebase keeps every reading and conjugates `T` (`rebase_summaryRead`, `rebase_action`); `D X = Y` is solvable or obstructed by a `v` with `vᵀD = 0`, `vᵀY ≠ 0`, its solutions a particular one plus the free directions (`solvable_xor_obstructed`, `solutions_eq_particular_add_free`); a return `Y` lifts through a source and a context exactly when `ker S ⊓ ker C ≤ ker Y`, else an occurrence combination is returned, and every decoder factors through the context modulo its silent part `N = C(ker S ⊓ ker Y)`, with the host's rank check (`lift_iff`, `lift_xor_obstruction`, `decoder_factors_through_silentQuotient`, `lift_through_silentQuotient`, `demonstrated_rank_eq`); witnesses over ℚ for each alternative and the host's two context tests | #410's box "`quotient.kernel-mode-reduction`, `quotient.contextual-factorization`"; the retired `crates/holonics/src/exact_linear/{kernel_modes,contextual}.rs` (removed at `d329cb541`); `Compression/Core/FaceMap`, `Objects/Pairing`, `Computation/AttentionModeCompression` | `quotient.kernel-mode-reduction`, `quotient.contextual-factorization`, `linalg.rank-factorization-rebase` |

The boxes these answer, by their opening words: "Curvature's strain and rotation" (part done: Petrov's classification
and the deviation equation from a metric's connection are left); "`winding.circulant-inertia`";
"`quotient.kernel-mode-reduction`".

## 2. What the pass corrected

1. **The magnetic part is no rotation.** The box ("Curvature's strain and rotation: the Weyl tensor's electric/magnetic
   split"), `docs/ELEMENTARY_OBJECTS.md` ("tidal curvature and frame dragging are the Weyl tensor's strain and rotation
   parts") and the Swing record's §5.6 ("frame dragging a rotation field") pair the magnetic part with rotation. `H` is
   symmetric and traceless like `E` (`magnetic_symm`, `magnetic_traceless`), so in Motion's split it is a boost-type
   part, not a turn: what turns is a gyroscope or a congruence that `H` drives, and in this module the turn is the
   congruence's `ω`. The reading that stands: the electric part is the tide and the magnetic part is gravitomagnetism,
   which drives rotation. The ledger's slots `shearSquare` and `vorticitySquare` did not say their convention; their
   coefficients match the full contractions `σ_abσ^ab = ⟨σ, σ⟩`, which `ledger_eq_raychaudhuriRate` fixes (under the
   half convention `σ² = ½σ_abσ^ab` the rate reads `−2σ² + 2ω²`).
2. **The negative band is between a quarter and three quarters of a turn, and the hand fixes the split only up to its
   own exchange.** `winding.circulant-inertia` read "`λ_k = β_k < 0 ⇔` step exceeds a quarter turn"; with `0 ≤ k < n`
   the band is `n < 4k < 3n`, and "exceeds a quarter turn" holds only for the shorter turn (the owner's star table ran
   `m = 0..n/2`). Its "integer combination" needs an integer row; the owner first scaled the row to an integral symbol.
   The eigenvector identity needs `ωⁿ = 1` only, primitivity entering for the null test and for distinct colours, and
   the row's `circ` is the first-row circulant, Mathlib's transpose. `winding.hand-is-convention` was graded
   `definition` while the swap of inertia under negation is a theorem (`inertia_neg`), and its "the split (p, z, q) is
   frame-free" says more than the hand: invariance under every change of frame is Sylvester's law. The rows now say so.
3. **The closing square's letters swap between sources, and the masses' sign was the host's gate.** The atlas row and
   the host docstring wrote `U E = E T` with `T` the source action, THE_MACHINE and HOLON.md write `E_next T = U E`, and
   the host code solved `E U = T E` with `U` the source action; the module follows the code and its Conventions
   paragraph maps the three, and the row now names which letter acts on the sources. The row's "nonnegative source
   action masses" was the host chart's refusal (`NegativeMass`, `NoPositiveMass`), not a hypothesis of the law: every
   statement holds over any field and a reading needs a nonzero mass only. The host `factor_receiver` said "Solve D self
   = target" while solving the left form `X S = Y`, and the contextual row's "free row directions" mixed the two sides;
   the module states the transpose. The box's "participation classes" names no object of either row; it is read as the
   class factorization of `norm.attention-class-exact`, and the derived modes are no classes: they are a rank
   factorization, unique only up to a rebase. The rows' "runs exactly through" and "factor exactly through" now read
   "runs through" and "factor through".

## 3. What each statement stands on, and what is left

- `Physics/Spacetime/Raychaudhuri` stands on Mathlib's `hasFDerivAt_ringInverse` and its matrix `linftyOp` norm (local
  instances a later user must switch on), on `Geometry/Motion`'s `turn` and `boost`, and on the owner's
  `CongruenceLedger`. The deviation equation `J″ = −RJ`, the tide `R_ij = R_(i a j b) u^a u^b` and its symmetry are
  hypotheses, not derived from a Lorentzian metric's connection; no tensor with the Weyl symmetries is built from a
  metric; the rotation's staying zero along the congruence needs uniqueness for its linear law, and the focusing
  statements take `ω = 0` on `[0, T]`; the null (Sachs) form, accelerated congruences, Jacobi's formula `θ = (log det
  J)′` and a caustic as a point are not stated. Petrov's classification (the eigenvalue types of `E + iH`) is the box's
  part left, so the box stays owed and part done. The ledger's docstring ("A geometric realization must supply these
  from a Lorentzian metric, connection, and congruence") is left as it stands, since `Physics/HolonicFieldTheoryPassage`
  sits under `Framework/Information` and an edit there rebuilds most of the library; the atlas rows and this record
  carry the join.
- `Mathematics/CirculantInertia` stands on the colours and the Fourier transform of `Mathematics/OnePlaneRing`
  (`dft_comp_add`, `dft`) and RingSpectrum's `cycleLaplacian` and `gapSq`, and on Mathlib's `ZMod.stdAddChar`,
  `IsPrimitiveRoot` and cyclotomic polynomials. Not stated: the owner's Sturm refinement of a nonzero eigenvalue's sign
  on `det(xI − C)` (Faddeev–LeVerrier; the chain itself is `Mathematics/Sturm`); Niven's rational star values as the
  roots of `D_n(x) − 2` (the separate row `winding.niven-star-values`); circulants over other fields; and Sylvester's
  law of inertia.
- `Compression/KernelModes` stands on Mathlib's matrix rank, `toLin'` and nonsingular inverse alone, and names without
  importing the owners it meets (`Compression/Core/FaceMap`, `Objects/Pairing`, `Transport/EditRigidity`,
  `Foundation/JointReceiverDescent`, `Foundation/ReceiverQuotient`, `Foundation/ReceiverHistoryCompression`). Not
  stated: the host's certified widths, work counts and frame checks; softmax or a score read from a query
  (`norm.attention-class-exact` owns the attention reading over ℝ); the context generator's defect columns apart from
  `closes_xor_separates` read with the quotient as the encoder; the phase-rechart test; that `N` is the largest subspace
  every decoder kills; and the receipt's dimension counts `n − rank`, `m − rank` of `linalg.rank-factorization-rebase`.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the owed sentences of `docs/ELEMENTARY_OBJECTS.md` (the Weyl tensor's parts), `docs/THE_MACHINE.md`, `docs/HOLON.md`, `docs/HNN_FORMULA.md` and `docs/HOLONIC_NOTATION.md` to the new modules, and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3512 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, every tracked research module, since the census reads unrooted=0) read `Build completed successfully (10605 jobs)`, exit 0; `Holonics` read `Build completed successfully (9166 jobs)`, exit 0. The warnings printed are other modules' (unused simp arguments, unused variables, universe notes), none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
