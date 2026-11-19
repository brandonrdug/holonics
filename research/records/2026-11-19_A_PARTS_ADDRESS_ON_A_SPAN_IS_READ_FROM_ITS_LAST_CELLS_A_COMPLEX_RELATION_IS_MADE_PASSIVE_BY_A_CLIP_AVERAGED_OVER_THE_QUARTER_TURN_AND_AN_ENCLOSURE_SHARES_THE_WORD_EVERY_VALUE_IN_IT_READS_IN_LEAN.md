# A part's address on a span is read from its last cells, a complex relation is made passive by a clip averaged over the quarter-turn, and an enclosure shares the word every value in it reads, in Lean

November 19, 08:25 UTC. The fifteenth formalization pass over #410, its sixteenth set, after [the
fifteenth](2026-11-19_THE_INNOVATION_TOWARD_A_TARGETS_CODE_FACE_DESCENDS_THE_SCORED_FACE_A_FLOORED_MIXTURE_RETURNS_A_DORMANT_MEMBER_AT_K_PLUS_LOG_M_BITS_AND_A_PAIR_DEPOSITS_CERTIFIED_STEP_KEEPS_THREE_QUARTERS_OF_ITS_LINES_DECREASE_IN_LEAN.md)
(#1026). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Compression/Landmark/SpanSuffix` | A part's located address on a span is the match `(j, ℓ)`, `1 ≤ ℓ ≤ j < |span|`, `ℓ ≤ |part|`, with the part's last `ℓ` cells equal to `span[j−ℓ, j)`, largest in the order `(ℓ, j)`: a match, the longest, the latest among the longest, and the one pair with these properties (`located_isMatch`, `located_longest`, `located_latest`, `located_eq_some_iff`); nothing is located exactly when the part is empty or its last cell does not occur in `span.dropLast`, and a located length is at most `|span| − 1` (`located_eq_none_iff_getLast`, `located_length_le`); the last `|span| − 1` cells locate alike, so two parts that share them read alike after every future, a `ReceiverHistoryCompression` of the house (`located_retained_suffix`, `future_equivalent`, `retainedSuffixCompression`); the occurrence continues as `(j + 1, L + 1)` while the next cell is the span's, and at a break relocates from the retained suffix and the new cell (`located_concat_of_continues`, `located_concat_retained`); the incremental reader `(suffix, received, address)` reads `located` at every prefix, and its count is never read (`read_eq`, `read_address_eq_located_suffix`, `foldl_received_unread`); the owner's restore and snapshot tests replay by `decide` (`witness_latest_among_longest`, `witness_rust_snapshot`) | #410's box "`SpanReading`'s retained suffix is future-equivalent"; the retired `compression/landmark/context/spans.rs` (`fbb9dee61^`); `Foundation/ReceiverHistoryCompression` | `context.span-located` |
| `Holon/ReactionProjection` | For a complex structure `J` (`Jᵀ J = 1`, `J J = −1`, such as `realify (i·1)`, `realifyI`) the average `R̄ = ½(R + JᵀRJ)` is positive semidefinite with `R` and commutes with `J`, and when `Jᵀ (sym L) J = sym L` (true for every realification, `realify_commute`, `realify_symPartK_invariant`) `⟨e, (L − R̄)e⟩ = ½⟨e, (L − R)e⟩ + ½⟨Je, (L − R)Je⟩`, so the averaged congruence clip of a complex relation is passive (`average_psd`, `average_commute`, `averaging_identity`, `average_passive`, `averaged_clip_passive`); `|E_ij| ≤ ε` on `m` indices gives `|⟨e, Ee⟩| ≤ mε|e|²`, so removing the grain-rounded average plus `n u·1` from `realify W` keeps it passive and removes a positive semidefinite part (`quad_abs_le_of_entry`, `grain_passive`, `passive_complex_at_grain`, `passive_complex_at_grain_removed_psd`); by Gershgorin some natural shift makes `W − τ·1` passive, the least `τ*` keeps the skew part, is `0` only on a passive relation, is at most `⌈c⌉₊` for every bound `c` of the form and leaves a witness above `τ* − 1`, and equals `⌈λ_max(sym W)⌉₊`, at a grain `⌈λ_max/u⌉₊` (`gershgorin_quad`, `leastShift_passive`, `shift_keeps_skew`, `leastShift_eq_zero_iff`, `leastShift_le_ceil`, `leastShift_active`, `leastShift_eq_ceil_lamMax`, `grainShift_eq_ceil`); for `S = [[0, 1], [1, 0]]` every `P_t` diagonalizes to `diag(2, −2)` while the clip's removed part has trace `(t² + t⁻²)/2`, unbounded, against the shift's `1·1` (`clip_removed_unbounded`, `clip_vs_shift_witness`) | #410's box "The complex-passivity averaging argument, grain correction and scalar-shift comparison of Rust `holon::reaction`"; the retired `holon/reaction.rs` (`2d34b819`, the same file as `d8dd2455e^`); `Holon/Reaction`, `Holon/Deposition`, `Holon/Cayley` | `holon.reaction-passive-projection` (new), `holon.minimal-certified-shift`, `deposition.certified-congruence-clip` |
| `Mathematics/ConstantNavigators` | For `x > 0`, `z = (x − 1)/(x + 1)` has `|z| < 1` and `log x = 2 Σ z^(2k+1)/(2k+1)` from Mathlib's series, and the tail after `N` terms is at most `2|z|^(2N+1)/((2N+1)(1 − z²))`, the partial sums lower ends for `x ≥ 1` (`hasSum_log_atanh`, `abs_log_sub_logPartial_le`, `log_mem_enclosure`); on `1 ≤ x ≤ 2` the width is `9/(4(2N+1)3^(2N+1))`, four terms give `53056/76545 ≤ log 2 ≤ 53056/76545 + 1/78732`, and every `x > 0` is `2^k y` with `1 ≤ y < 2`, read within `(|k| + 1)` unit widths (`log_unit_enclosure`, `log_two_enclosure`, `unit_reduction`, `abs_log_sub_reduced_le`); at `|x| ≤ 1` `exp x` lies in `[P − r, P + r]` with `r = |x|^n (n+1)/(n! n)` from `Real.exp_bound`, the first `2N` terms of `exp(ix)` split into the cosine's and sine's alternating partial sums, and `cis x` lies in the box of their enclosures (`exp_mem_enclosure`, `cis_partial`, `norm_cis_sub_partial_le`, `cis_mem_box`); the rational loop `commonWord` at a declared depth emits only digits that every value of the enclosure reads at the same place, the head and partial denominators of `GenContFract.of x`, and stops only where the ends' next digits part or both end (`commonWord_digit`, `commonWord_partDen`, `commonWord_maximal`); by `decide +kernel`, `[355/113 ± 10⁻⁶]` shares `[3; 7]` and π's twenty-place enclosure shares nineteen digits `[3; 7, 15, 1, 292, …]` (`commonWord_around_355_113`, `commonWord_pi`, `pi_cfDigit`) | #410's box "`series.log-atanh`, `series.log-atanh-exp`, `series.common-continued-fraction`, `analytic.certified-capture`, `analytic.euler-maclaurin-eta`", its first three rows; the retired `geometry/exact_analysis/{elementary, constants}.rs` (`d329cb541^`); Mathlib's `Real.hasSum_log_sub_log_of_abs_lt_one`, `Real.exp_bound`, `Complex.exp_bound`, `GenContFract.IntFractPair.stream`, `Real.pi_gt_d20` | `series.log-atanh`, `series.log-atanh-exp`, `series.common-continued-fraction` |

The boxes these answer, by their opening words: "`SpanReading`'s retained suffix is future-equivalent"; "The
complex-passivity averaging argument"; "`series.log-atanh`, `series.log-atanh-exp`, `series.common-continued-fraction`"
(part).

## 2. What the pass corrected

1. **The suffix alone is the future-sufficient state.** The box counts the received count and the located address in the
   retained state; `located` never reads the count, and the address is itself `located` of the retained suffix, so the
   two are carried beside the suffix, not needed by it. The atlas row's set `{ℓ ≥ 1 : part[n−ℓ, n) = span[j−ℓ, j), j <
   |span|}` left `ℓ ≤ j` and `ℓ ≤ n` implicit and bound `j` inside a maximum over `ℓ`; the law is a maximum over pairs
   in the order `(ℓ, j)`, and the row now says so, with the grade `formal-checked`. `docs/RECEIVER_HOLARCHY.md` listed
   `context::spans` among the retired line's catered layers with no law carried forward; the copy stage stays retired,
   and the located span's law is now listed among the laws the line stated, kept in Lean as mathematics.
2. **A passive relation is fixed by the owner's guard, not by the formula.** `docs/HNN_FORMULA.md` said of the grain
   correction "A passive relation is fixed"; the retired `passive_complex_at_grain` returned a relation with no positive
   inertia unchanged before it projected, and the formula `L − (round(R̄) + n u·1)` alone removes the shift `n u·1` from
   a passive relation (`grain_removed_of_passive`). The guide now says so, the scalar shift's bound reads `τ* =
   ⌈λ_max(herm W)/u⌉₊`, so the shift removes less than `λ_max₊ + u`, and its three laws, marked `agent-inferred` and
   `measured` and "owed in Lean (#62)", now point to the module; the clip's growth on learned blocks stays a
   measurement.
3. **Two π enclosures read only `[3; 7]`.** `[355/113 − 10⁻⁶, 355/113 + 10⁻⁶]` and `[3.14159, 3.1416]` each hold the
   convergent `355/113 = [3; 7, 16] = [3; 7, 15, 1]`, so their ends part at the third digit (`15` below, `16` above,
   `ends_part_around_355_113`); an enclosure that excludes it, Mathlib's twenty-place one, reads nineteen digits. The
   atlas row `series.log-atanh` wrote the tail as `2 z^(2N+1)/…`, which needs `|z|` for `0 < x < 1`, where `z < 0`;
   `series.common-continued-fraction` restricted the law to a positive interval, which it does not need, and said the
   enclosure "certifies exactly" its prefix, a use of "exact" the precision law retires; the rows now read `|z|`, any
   sign and "certifies". The loop follows the owner where an end lands on the shared floor: the digit is emitted, since
   every value of the enclosure reads it, and the word stops. `series.log-atanh-exp` named "exp, sin, cos of a
   rational"; the enclosures are proved at `|x| ≤ 1`, and a ratio beyond it is reached by halving, whose identities are
   proved while the propagation of the enclosures through it is not, which the row's scope now says.

## 3. What each statement stands on, and what is left

- `Compression/Landmark/SpanSuffix` stands on Mathlib's `List.rtake` and `List.argmax` and on
  `Foundation/ReceiverHistoryCompression.quotientEqForcesEverySuccessorFace`. Not stated: the two-port reading's place
  in the receivers (`receiver::population::admitted`), the span's closing letter, a minimal quotient (two cells that
  occur nowhere in the span are read alike), that the Rust `locate` loop computes `located`, and any cost of relocation.
- `Holon/ReactionProjection` stands on `Holon/Reaction.realify`, `Holon/Deposition.{symPartK, quad_symPartK, quad_congr,
  congruenceClip_nonpos}` and `Holon/Cayley.{lamMax, shift_passive_iff}`. Not stated: the skew-Hermitian rounding at the
  grain, the inertia bisection's algorithm and its rational certificates, the Rust's interleaved coordinates and
  `BigInt` arithmetic, that its Hermitian rounding of complex entries is the entrywise rounding of the realification (at
  a tie `round(−x) ≠ −round(x)`; both are within `u/2`, which is all `grain_passive` reads), and the optimality of
  either projection. `Holon/Deposition`'s docstring is unchanged, since editing it would rebuild most of the library.
- `Mathematics/ConstantNavigators` stands on Mathlib alone. Not stated: `analytic.certified-capture` and
  `analytic.euler-maclaurin-eta`, which keep #410's box part done; the rounding of each enclosure out to a bit grain;
  the propagation of enclosures through squaring, doubling and `k log 2 + log y` as interval arithmetic (the identities
  and one width bound are proved); the sharper alternating remainders of the sine and cosine; and the Farey reading of
  the word as a statement on Farey intervals and their mediants.

## 4. Receipt

- Workers on disjoint owner paths, three at a time, wrote the three modules; the lead re-checked each single file (exit 0, no warnings), repointed the guides (`docs/RECEIVER_HOLARCHY.md` lists the located span among the laws the retired line stated; `docs/HNN_FORMULA.md`'s reaction section, whose three laws were marked `agent-inferred` and `measured` and "owed in Lean (#62)", now points to `Holon/ReactionProjection`, and its retired enclosure owner to `Mathematics/ConstantNavigators`; `docs/HELICAL_GEOMETRY.md`'s row for π and `e` names the new module), and wrote the atlas rows and this record. Each worker ran `#print axioms` on its main theorems: a subset of `propext`, `Classical.choice`, `Quot.sound`. The continued-fraction witnesses use `decide +kernel`, a kernel reduction that adds no axiom.
- Gate 4: `bash tools/lean_check.sh` on the three modules read `Build completed successfully (3376 jobs)`, exit 0; the research library's root closure (`+HolonicsResearch`, every tracked research module, since the census reads unrooted=0) read `Build completed successfully (10614 jobs)`, exit 0; `Holonics` read `Build completed successfully (9166 jobs)`, exit 0. The messages printed are other modules' (axiom reports, unused simp arguments, unused variables), none in a new file. Run on a four-core cloud host; a Lean check reads nothing the PC holds (CLAUDE.md, rule 4).
- Gate 1's text checks: `link_check.py atlas` and `links` report broken=0, `records_index.py` passes (8 passed), and `lean_census.py` reports unbuilt=0 and unrooted=0.
- No `sorry`, `axiom` or `native_decide`.
