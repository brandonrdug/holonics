# The resonator returns its wave and the comparison reaches its material

**Date:** 2026-09-26. **Campaign:** rebuild steps 4–5, Decision 38, #73 and #76; formal scope #62.
**Status:** implemented; the fixed loaded family loses its predictive comparison.

## The missing term

The campaign-2 resonator received the junction wave but returned none of it to the field. Its
port work was recorded as an interconnection defect, and no comparison covector reached its
material. The corrected campaign-2 receipt stated this explicitly. Decision 38 joins that
consumer rather than adding another isolated resonator.

The law and its order live in [THE_REBUILD](../../docs/plans/THE_REBUILD.md#decision-38-the-resonator-loads-the-ring-and-receives-its-covector).
The existing element produces a wave; the resonator receives it and returns a wave to the next
junction. The adjoint reverses the same stages. The material family consists of four scalar
amplitudes on immutable capacity, stiffness, dissipation and pump bases, with phase certification
before publication. A declaration may admit signed stiffness. Pump work remains explicit;
positive storage and dissipation alone do not establish passivity of an active word.

Brandon's egg discussion was re-read from the direct Claude Code messages of September 24–26.
Its operational intent is already in the [light/change record](2026-09-24_THE_LIGHT_IS_THE_CHANGE_AND_EXPRESSION_COLLAPSES_ONTO_FINITELY_MANY_CRITICAL_CLASSES.md)
and the [audited egg/shadow record](2026-09-26_THE_SHADOW_IS_THE_RECEIVERS_KERNEL_AND_THE_EGG_IS_TWO_RINGS_IN_RELATIVE_MOTION.md):
interior and boundary exchange, the neck transports, and current silence does not imply future
extinction. The loaded port implements the first connection. Campaign 3 must still supply the
future receiver family and mode release; the scalar family is not an arbitrary shape model.

## Laws and consuming calls

| Law | Lean owner | Runtime consumer |
|---|---|---|
| Element followed by resonator, with internal port power cancelled | `HNN/Ring.loaded_word_stage_balance` | `hnn::word::Word::tick` |
| Executed balance, including state and returned-wave splits | `HNN/Ring.loaded_tick_executed_interconnection_balance` | `hnn::ring::ResonatorOperands::step`, `hnn::word::{FieldBalance,WordBalance}` |
| Input/state adjoint and material variation | `HNN/Ring.{loaded_tick_adjoint_pairing,loaded_material_rate_tangent,loaded_tick_material_variation}` | `hnn::port::Word::pull_back`, `hnn::reference::compose` |
| Gain family and material commit work | `HNN/Ring.{loaded_gain_family_increment,loaded_gains_preserve_storage_dissipation,ring_material_commit_work}` | `hnn::constitution` gain deposition, `hnn::word::PowerForm::deposition_work` |
| Grain-score plateau and smooth-score pairing | `HNN/Ratio.{quantized_score_has_grain_plateau,odometer_covector_descends}` | `hnn::ratio::{Face,RatioCovector}`; explanatory scope corrected |

The exact inverse derivative and the executed chart covector have separate scopes. This change
does not discharge the counterfactual word-sensitivity bound or the concrete diamond bridge.
These remain explicit in #62. The deposition receipt's relative growth certificate covers
contact Gram forms only (`contact_growth`, `contact_product`). A uniform bound for loaded
capacity and signed, phase-selected stiffness is also owed; exact end-state material work is
already included in the word balance and does not substitute for that bound.

The card runs the resonator inside its forward and reverse word kernels. The same-hop contact
transit and loaded ring stage commute: they read the frozen junction outputs and write disjoint
contact/arrival and ring/state regions. Both finish before the next junction. The standalone
resonator kernel remains a component parity check, not the live field connection. Deposition and
exact face completion retain their host owners.

## Predeclared measurement

The existing `hnn_exposure` notebook accepts `resonator source` or `resonator none`. The loaded
case declares source ring 0, using its unit parametron's C/K forms and the campaign's initial
passive rate D=I/4, without a pump. All scalar amplitudes start at 1. No family search is performed.
The source ring is the smallest ring whose returned wave reaches the second receiving epoch of
the existing field. Its initial material has a self-delimiting description charged before the
first deposit; final scalar amplitudes are a receipt.

A `2⁵`-window development pilot measures the cost. The full passage is admitted only when its
projection fits ten minutes per realization. A refusal or timeout remains incomplete evidence.
The standing cut is reused development material; the separate evaluation partition is untouched.

## Verification and result

The independent scalar fixture has `h=1`, `Y=2`, `C=I`, `K=D=0`: a unit drive gives
`ω=2/5`, `u′=2/5`, `w′=4/5`, `s′=3/5`. Its wave energy `9/50` and mode energy `16/50`
sum to the opening `1/2`; the capacity-gain directional derivative is `16/25`.
The integration fixtures also cover a nonzero source-opening remainder, multiple ticks,
non-diagonal forms, `h=2`, `Y=4`, pump phases, signed stiffness, deferred comparisons, and an
actual returned gain deposit that changes the next receiving face. A late carrier refusal keeps
the predecessor constitution, tree, charts, ledger and staged handle on both host and card.

The host and card pilots read `32=2⁵` windows. Their exposure times were respectively
`2091=3·17·41` and `1973` ms. The exact linear projections to `3074=2·29·53` windows were
`200866 rem 22 over 32` and `189531 rem 10 over 32` ms, both below the declared ten-minute
limit. These projections admitted the full runs; they were not completion evidence.

### Full development passage

The host read all `6148=2²·29·53` cells, with `3074=2·29·53` compares and deposits.
The scored tail contains `1190=2·5·7·17` cells. Each `ε` below is its own unresolved fibre
`0 ≤ ε < 1/16`; the [aggregate receipt](2026-09-26_LOADED_RESONATOR_RECEIPT.json) retains the
exact enclosing endpoints. Lower code is better.

| Receiving face | Development code | Scored tail code |
|---|---|---|
| Default HNN | `18049 + 15/16 + ε` | `3671 + 9/16 + ε` |
| Loaded source ring | `18050 + 7/16 + ε` | `3671 + 14/16 + ε` |
| Loaded minus default | `0 + 8/16 + ε` | `0 + 4/16 + ε` |
| Tree alone, shared by both | `18067 + 2/16 + ε` | `3677 + 12/16 + ε` |

The loaded case is strictly worse on both parts, even before paying for its material. The
initial material code uses `889=7·127` bits; the default's two empty declaration counts use
2 bits, so the increment is 887 bits. Field plus initial material costs 2326 bits for the loaded
case and 1439 for the default. The default's score and learned constitution remain the earlier
Decision 37 result; its total description now includes these two empty counts.

The final scalar amplitudes are `(g_C,g_K,g_D,g_P)=(1,1,273/256,1)`, with
`273/256=(3·7·13)/2⁸`. Thus the executed dissipation is `(3²·7²·13²)/2¹⁸` times the identity.
The final constitution's learned carriers occupy `4833768=2³·3·31·73·89` bits. Every one of the 3074 loaded word balances closes;
the summed internal port defect is zero. Material work at the commits is included. The maximum
state-coordinate width is 31 bits; this excludes intermediate arithmetic and the separately
reported residual carriers. The carrier census excludes immutable declarations (charged in the
model description) and recomputable caches; it is not an allocation or whole-process memory reading.

The loaded operator and its learning consumer are retained because they close the missing
physical and adjoint connection. The measured source-ring declaration remains an explicit
notebook option. It is not adopted as the default predictive model, and there is no gain or grain
sweep after seeing this result. The next construction is campaign 3's admitted-future mode
restriction, as specified in THE_REBUILD.

### Verification receipt

- `cargo check --workspace --all-targets` passes.
- Host suite: 827 tests and 14 doctests pass.
- CUDA suite: 41 tests pass, including ignored device tests, alone under the repository GPU lock.
- `bash tools/lean_check.sh Holonics HolonicsResearch`: 10230 jobs pass. The added laws use only
  the standard printed axioms; no `sorry`, custom axiom or `native_decide` was added.
- The expression atlas has 2616 unique rows, each with eight fields; `git diff --check` passes.
- Rust formatting is checked on changed files. The workspace-wide formatting check also reports
  pre-existing differences in untouched files; those are left out of this repair.

The loaded host/card protocol receipts agree exactly over 3301 lines, including the complete
constitution curve, source moments, code enclosures, balances, release residuals and final gains.
Exterior timings and device traffic are separate readings. The full exposures took 384041 ms on
the host and 333854 ms on the card, respectively `124 rem 2865 over 3074` and
`108 rem 1862 over 3074` ms per window. Both met the declared ten-minute bound. These integer
wall times are measurements, not a scaling guarantee; the short pilots underestimated the cost.
`ExactWork` counts instrumented work and does not claim a complete operation or energy census.

The default card regression also completes all 3074 windows. Its scores, balances, learned
constitution, resident carrier census and counted work equal the previous full Decision 37
receipt at `f4bae3de`. The newly explicit empty material description adds exactly 2 bits to its
cost. Its measured exposure time is 327803 ms (`106 rem 1959 over 3074` ms per window).
The loaded card passage costs 6051 more ms in these two runs. Charging the material increment
once over the whole passage leaves the loaded family above the default by
`887 + 13/16 + ε` bits. The separate evaluation partition remains unspent.
