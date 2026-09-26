# The field-session join has its owner network and named absences

**Date:** September 20, 2026. **Tree:** `1dc61373`. **Status:** source inventory for plan
finalization. It schedules nothing; the [roadmap](../../docs/plans/THE_ROADMAP.md) orders the work
and the [native specification](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#field-session-source-map)
carries the compact map a worker starts from.

**Request:** finalize the plans for #16–#19, #48/#49 and #50 with the information and methodology
networked to each specific implementation, so an implementer meets the existing machinery, its
governing records and the concrete absent object at the place the work is described.

[established-bounded; source-audit] Three read-only inventory passes followed each relation from
its formal statement through host and resident owners, kernels, tests and dated records to the
consuming call. The primary re-inspected the load-bearing absence claims against source at this
tree: the `rows != 1` refusals, the duplicate-destination refusal, the absent enclosure→point
port, `from_exposures`' unset aperture, the saved-session fields, the prepared and unexecuted
shared-source run, the uncalled `receive_condition`, the moment-compression owner, the growing
operation vector, the resident normal factor/solve, and the September 8 cotangent derivation.
Line numbers are entry points at this tree, not stable addresses.

Path abbreviations: **C** = `crates/holonic-engine/src/native_ecology/constitutive_fibre`,
**K** = `crates/holonic-engine/kernels`, **A** = `crates/holonics-hna/src/native`,
**L** = `formal/elementary-holonics/ElementaryHolonics`.

## The consuming calls as they stand

| Call | Present law |
|---|---|
| `A/field_session/shared.rs::prepare_shared` | One row per free destination, built from the **original** source; every condition row is the constant `1+0i`; `shared_extents` returns `(nodes, 1, 6·nodes+1)`; `commit`/`retain_comparison` are refused |
| `A/field_session/shared.rs::shared_request` | One `preview_field_rows`, injective `scatter_components` of the centre window, `ResidentHeldSection::receive`. No re-entry |
| `A/coupled_wave/body/field/section.rs::prepare_rows` | `features = bilinear_features(s,c)`; `reaction = M·features`; `incoming = s + reaction`; `output = reflect_section(incoming)` |
| `…/section.rs::observe_rows` | `input_covectors` → boundary restriction → `reaction + covector` → `prepare_feature_section_material` → `commit_field_reaction`. **Fixed D**; M only |
| `A/coupled_wave/body/field.rs::observe` (single row) | Same return, then `apply_reflection_target(…, DyadicDeposit)`: this path **does** change D |

[established-bounded; source-inspected] The shared-regions realization arrived in `24e74c64`
with no dated record, no README and no executed run. Its only documentation had been the state
file and the owner map. `preview_field_rows`/`observe_field_rows` have no direct test; two ignored
CUDA tests in `shared.rs` are their only exercise.

## #17 — content-dependent participation and its variation

[definition] The law is `T_F[Ψ]=Σ_G a_FG[Ψ] U_(F←G)[Ψ] Ψ_G` with
`δT=Σ a δ(UΨ)+Σ δa UΨ` ([formula](../../docs/HNN_FORMULA.md)). The exact host reference is
`crates/holonic-engine/examples/connected_holonic_field.rs` with its
[experiment](../experiments/connected_holonic_field/README.md): normalized heads, one material
step, log-potential and value pullback, sigmoid gate, phase contact, layer composition `L²`,
iterated refinement `x←λL²x+(1−λ)h`, implicit whole-field solve, and the exact sensitivity
`dB=(dL)L+L(dL)` through `NormalizedKernel::differential`. The
[interface audit](../experiments/hnn_field_architecture/README.md) already records that the
native normalized return is occurrence-keyed and consumes an existing observation.

| Relation | Existing owner | Scope at the section call |
|---|---|---|
| Normalized face, `q−p`, `J_p(q−p)` | `C/field/receiver/normalized.rs::normalized_material_return`; `K/field_normalized_receiver.cuh::{section_field_normalized_receiver,section_normalized_sum_receiver,normalized_compare_faces}`; recorders in `resident_section/surface_passage.rs` | Resident, but **keyed on field-history occurrences and refusing `rows != 1`** on every operand |
| Pullback to both query arguments | `C/field/receiver/normalized/pullback.rs::{pull_back_material_source,pull_back_material_current}`; `K/field_material_pullback.cuh` | Resident, single occurrence; its second argument is the field's own outgoing/internal current, not the exterior condition |
| Multi-row softmax with differential | `K/exact_resident_adjoint.cuh::section_receiver_return` | Resident and multi-row, on the ported-operator pointer-table ABI with a categorical next-index target; only caller `holonic_intelligence/operative_return.rs` |
| Exact normalized kernel | `exponentiated_ratio/transport.rs::NormalizedKernel::{apply,differential,pullback,binary,fit_step}`; `exponentiated_ratio.rs::RatioFamily` | Host exact reference; tests run on CPU |
| Formal | `L/Computation/{HolonicAdjointNormalization,AttentionModeCompression,NormalizationProjectionScope,HolonicArchitectureCharts,MachineLearningChart}.lean` | `face_add_common`, `laplacianReturn`, `sigmoid_is_binary_normalized_exponential`, `normalized_attention_exact`, `weight_normalized` |
| Source⊗condition features | `C/resident/section/bilinear_features.rs::bilinear_features`; `K/exact_resident_section.cu::section_constitutive_bilinear_source` | Resident rows; both operands must be **exact point** sections; width `2(s·k+s+k)` |
| Applied material | `C/field/material_transport/normal/direct/section.rs::{read_applied_section,read_applied_bilinear_section,stage_receive_enclosed_section}`; point forms `direct.rs::{read_applied_bilinear,_identity,_joint}` with `K/normal_applied_condition.cuh` | The enclosure-source form exists only single-row; the section form needs point operands |
| Section ports | `…/direct/section.rs::{from_points,sum_same_shape,restrict_components,flatten_components,scatter_components}`; `…/direct/held_section.rs::ResidentHeldSection` | `scatter_components` refuses a repeated destination |
| Evolving condition | `C/resident/neighborhood.rs::ResidentNeighborhoodAlternative::prepare_following`; `A/coupled_wave/body.rs::receive_condition` | The first is `pub(crate)` on the coupled-wave path and cannot publish; the second is public and **never called by the session** |
| Current re-entry | `C/field/resident_input.rs::advance_current_resident` | Point/occurrence path, one current per advance |
| Diffusion reference | `diffusion.rs::ExactDiffusionLaw`, `sheaf_diffusion.rs::ExactSheafDiffusionLaw` | Host exact, with certified energy balance |

[established-bounded; source-inspected] **Concretely absent for #17:**

1. A **row-sectioned normalized receiver**: grouped `p`, `q−p`, `J_p` over a section of region
   rows, with typed section operands.
2. A **condition covector port**: no adjoint of `section_constitutive_bilinear_source` exists, so
   nothing returns a covector to the condition operand. This is the port the
   [September 8 cotangent record](2026-09-08_AC1_THE_MATERIAL_RETURN_HAS_A_CONTEXT_COTANGENT.md)
   names, with its derived operative tangent response `w=(2I+JG⁻¹J*)⁻¹r`, `δM=wΨ*`, `z=G⁻¹J*w`.
3. A **re-entry port**: `from_points` has no inverse, so the enclosure section returned by
   `preview_field_rows` cannot be the next call's source; the applied-condition kernel has no
   enclosure-source section form.
4. The **condition chart is fixed at founding**: `shared_extents`, `found_bilinear_contact` and
   `found_features` pin one condition coordinate; M's width becomes `s(1+k)+k` for `k` coordinates.
5. The **composition itself**: layer composition, iterated refinement and the `δa` sensitivity
   have exact host owners and no resident section-level caller.

[agent-inferred] Region coupling enters through each row's gathered neighbour currents and its
participation, not through accumulated overlapping outputs; the centre-window scatter stays
injective. Inferred from `prepare_shared`'s incidence chart and the formula's contact comparison.
The device arm of `AccumulationLaw::IntegerAdd` (#13) is therefore not a dependency of #17.

**Governing records.** [Contextual transport precedes production](2026-09-05_CONTEXTUAL_TRANSPORT_PRECEDES_INHERITED_MODEL_PRODUCTION.md);
[normalized receiver](2026-09-08_AC1_THE_NORMALIZED_RECEIVER_RETURNS_ITS_COMPLETE_CURRENT_AND_TWO_METRIC_FACES.md);
[both query arguments](2026-09-08_AC1_THE_MATERIAL_RETURN_REACHES_BOTH_QUERY_ARGUMENTS.md);
[shared normalization owners](2026-09-12_CONTEXTUAL_RECEPTION_AND_NORMALIZATION_REUSE_THEIR_SHARED_NATIVE_OWNERS.md);
[resident context features](2026-09-13_RESIDENT_CONTEXT_FEATURES_RETURN_PREDICTIONS_AND_FACTORS_RELEASE_EXECUTABLE_CODE.md);
[attention, learning and generation share a Holon](2026-09-14_ATTENTION_LEARNING_AND_GENERATION_SHARE_A_COMPUTATIONAL_HOLON.md);
[the field evolves before reception](2026-09-14_THE_CONTINUING_FIELD_EVOLVES_BEFORE_RECEPTION.md);
[joint current survives repeated generation](2026-09-14_THE_JOINT_FIELD_CURRENT_SURVIVES_REPEATED_GENERATION.md);
[partial fields](2026-09-15_PARTIAL_FIELDS_FORM_JOINT_PATTERNS_THROUGH_THEIR_RECEIVERS.md).

**Tests to extend.** `field::receiver::normalized::tests`, `…::normalized::pullback::tests`,
`resident::section::bilinear_features::tests`, `normal::direct::section::tests`,
`operative::source::tests::reflection_section_shares_internal_source_and_fixed_d_pullback`,
`exponentiated_ratio::transport::tests` (the CPU reference for both variation terms),
`holonics_hna::native::field_session::shared::tests`.

## #19 — changed incidence through forward and adjoint

| Relation | Existing owner | Scope |
|---|---|---|
| New contact deposit | `C/field/junction/operative.rs::{NativeContactRealization,NativeOperativeContactBirth,NativeOperativeContactStaging,stage_operative_contacts}` | Resident staging under the borrowed field |
| Forward and adjoint through D | `C/field/junction/operative/source/reflection_target.rs::{compare_target,compare_received_target,input_covector,material_covector,apply_reflection_target}`; `K/field_reflection_target.cuh` | **Single row.** `apply_reflection_target` is the changed-incidence commit |
| Causal contact propagation | `C/field/junction/operative/propagation.rs::propagate_causal_contacts`; `K/field_causal_contact_{propagation,pullback}.cuh` | Only caller is `operative/map_source/tests.rs` |
| Condition contact | `C/resident/condition_contact.rs::{prepare_contact,commit_contact,ConditionContactMetric}` | The session founds the standing once and never advances it |
| Formal | `L/Physics/ConstitutiveModulation.lean::{coupledResponse_finite_change,tangent_cancellation_does_not_close_finite_response}`; `L/Transport/ChangingReceiver.lean::{passage_transformer_exists_iff,changing_history_exact,moving_receiver_rate}` | Formal-only |

[established-bounded; source-inspected] **Concretely absent for #19:** a section-scale D update.
`observe_rows` is fixed-D by construction (`reflection.rs::input_covectors`); there is no multi-row
`section_field_reflection_target`/`_input_cotangent`; `propagate_causal_contacts` and
`condition_contact::{prepare_contact,commit_contact}` have no session caller.
`coupled_wave::tests::boundary::changing_operative_material_conditions_the_same_hnn_source` was
recorded open by `24e74c64`. Governing records: the September 8 operative-contact series
([staging](2026-09-08_AC1_OPERATIVE_CONTACTS_STAGE_THEIR_COMPLETE_MAP_AND_CURRENT_ON_DEVICE.md),
[deposit](2026-09-08_AC1_THE_DEPOSIT_IS_A_NEW_COEFFICIENT_AND_ITS_DEFECT_REMAINS_A_COMPARISON.md),
[paired return](2026-09-08_AC1_THE_PAIRED_RETURN_CHANGES_CONTACTS_AND_THE_NEXT_CURRENT.md)).

## #16 — a complete source episode through the session

| Relation | Existing owner | Scope |
|---|---|---|
| Corpus and exposure | [Conversation data](../../docs/CONVERSATION_DATA.md); `applications/conversation-data/{conversation_data,providers,exposure}.py`; private `.local/datasets/athena-alpha-exposure-source-context-2026-09-06.jsonl` | 36,920 families; 34,046 development / 1,121 evaluation / 1,753 deferred at the September 4 cut; relation kinds `provider-parent`, `later-human-after-agent`, `comparison-request`, `tool-result-of`, `tool-result-candidate`, `parent-candidate` |
| Reader | `crates/holonics-hna/src/alpha/exposure.rs::{ExposureReader,ExposureCursor,ExposureOccurrence::{validate,development_parts,shared_visible_parts,shared_prior_parent}}` | Validation happens only through the reader; `development_parts` is the only partition gate; `shared_prior_parent` errs on any tool or candidate link |
| Bridge | `A/field_session.rs::FieldSectionRequest::from_exposures` | Called only by tests; uses `shared_visible_parts`; sets `partial: None`, `output_symbols: None` |
| Session | `A/field_session.rs::{FieldSessionSpec,NativeFieldSession::{request,observe,checkpoint},NativeFieldSavedSession}`; `A/field_session/shared.rs::{shared_request,observe_source}`; `stream.rs::pump_field`; Workbench `hna field-session` | Session wire v1/v2; field rest pending kinds 1–3 |
| Episode and assessment | [Evaluation](../../docs/ATHENA_EVALUATION.md); `research/experiments/native_performance_benchmark/{episode,quality}.py` | `input.json`/`assessment.json`; `quality.py` has field profiles for the three-symbol pattern chart only |
| Prepared run | `research/experiments/athena_field/shared/prepare.py`; private `.local/evaluations/athena-shared-source-2026-09-15/{spec,manifest,development,validation,expected}` | 16 symbols, offsets `[-2..2]`, 153,418-nibble section; **inputs only, never executed** |
| Baselines | `athena_field/{README,session/README,pattern/README}.md` | Pattern chart: 77,522 µs generation / 641,746.5 µs update medians, 129 features, 26,447,972 bytes native sections |

[established-bounded; source-inspected] **Concretely absent for #16:**

1. **No exposure→field-session driver.** Every `ExposureReader` consumer feeds the wave or
   normal-material paths.
2. **No request/response aperture** in `from_exposures`: with `partial` unset every position is
   free, which is whole-text reconstruction, not a held request with a generated response. It
   also bypasses the development gate, the author role and `validate()`.
3. **No producing comparison in the shared chart**: `prepare_shared` refuses
   `commit`/`retain_comparison`, so a recorded comparison cannot be retained, saved and applied
   after reopen; `observe_source` needs request and target in one call.
4. **No `ExposureCursor` in `NativeFieldSavedSession`**, so source position and trained state
   cannot be committed together ([conversation data](../../docs/CONVERSATION_DATA.md#athena-alpha-causal-exposure)).
5. **No baseline at the shared chart**, and the non-joint extent back-fill defaults to
   `section_symbols`.
6. `quality.py` has no conversation/repository episode family; `assessment.json` has no
   programmatic consumer.

Governing records: [AC0 exposure](2026-09-06_AC0_THE_CONVERSATIONS_ENTER_AS_SEPARATE_OCCURRENCES_AND_THE_COLD_CURSOR_RESTARTS.md);
[byte clock is not cultivation](2026-09-09_THE_BYTE_CLOCK_AND_OCCURRENCE_EXPANSION_ARE_NOT_GENERATOR_CULTIVATION.md);
[field session](2026-09-15_THE_FIELD_MODEL_GENERATES_CONTEXTUAL_TEXT_THROUGH_THE_PUBLIC_SESSION.md);
[evaluation kit](2026-09-15_ATHENA_EVALUATION_HISTORY_AND_SHARED_CONSEQUENCE_KIT.md).

## #18 — normal statistics beyond the dense chart

[established-bounded; source-inspected] `C/field/material_transport/normal/layout.rs::NormalLayout::for_sources`
states the cost: a dense Gram of `2·sources²` moment values at 18 words each and an LDL over
`2·sources` components. The pattern chart has 129 sources and 12 targets; the prepared shared
spec has 181 and 90; `k` participation coordinates give `s(1+k)+k`. The factor and solve are
already resident (`K/field_normal_material.cuh::{field_enclosed_factor,field_enclosed_solve}`).

| Candidate realization | Owner | Residency | Connected to the session's material |
|---|---|---|---|
| Factored moment `C=BᵀHB` | `factored_moment/{types,sparse}.rs::{FactoredMomentSection,SparseQuadraticMomentSection,FactoredConstitutiveSpine}` | Host exact | No |
| Local factor atoms | `derived_factor_cover.rs::DerivedFactorCover` | Host exact | No |
| Modal reduction `K=DE`, `UE=ET` | `exact_linear/kernel_modes.rs::{KernelModeReduction,compile_source_action,rebase}`; `exact_linear/contextual.rs::factor_receiver` | Host exact | No |
| Generated gather/apply/scatter | `crates/holonic-mount/src/section_layout.rs::SectionLayout`; `section_layout_adoption.rs` | Generator with device launch requirements | Only the enclosure scatter is declared |
| Shared-drive mode | `C/field/internal_mode.rs::condense_shared_drive_mode` | **Resident** | Adjacent, unused by the session |
| Formal | `L/Physics/AccumulatedNormalResponse.lean`; `L/Foundation/NavigatorModeQuotient.lean` | Reference | The Lean model is the dense rank-one update |

**Concretely absent for #18:** `NormalSourceChart` has only `Wave` and `Features`; `NormalLayout`
has no factor frame; no factored owner has a resident section adapter. Governing record:
[partial fields](2026-09-15_PARTIAL_FIELDS_FORM_JOINT_PATTERNS_THROUGH_THEIR_RECEIVERS.md)
("dense normal statistics and the operative journal remain explicit costs").

## #48/#49 — continuing reuse of a repeated generator action

[established-bounded; source-inspected] The helical guide's product-current bridge already has
its owner, in moment form. `L/Millennium/HolonicQuadraticMomentCondensation.lean` proves
`quadraticMoment_generatedWord_eq_transportMomentWord` and
`observableMomentReceiverHistoryCompression`;
`receiver_history_compression/observable.rs::ObservableMomentReceiverHistoryCompression::found`
closes a declared quadratic receiver family under exact backward generator action and returns
the basis forms, present receiver factors, descended generator actions and reconstruction kernel.
`ScrewGeometry.pair_quadrance_is_existing_moment_contraction` is its pair specialization. No
Kronecker-sum or symmetric-square matrix operator exists in Rust, and none is needed.

| Relation | Existing owner |
|---|---|
| `E T=U E` or its separator | `exact_linear/contextual.rs::factor_receiver`; `exact_linear/kernel_modes.rs::compile_source_action`; `L/Foundation/{ReceiverHistoryCompression,JointReceiverDescent,NavigatorModeQuotient}.lean`; `L/Transport/{ChangingReceiver,AccumulatedReceiverDefect}.lean` |
| Reduced recurrence of one operator | `exact_linear.rs::ExactRatMatrix::{minimal_polynomial,power_reduced}`; `A/mathematical.rs::MathematicalRequest::Power` |
| Resident compression | `receiver_exact_compression.rs::compress_on_device`; `native_ecology/recurrent_condensation.rs`; `C/field/internal_mode.rs` |
| Phase closure and landmarks | `L/Millennium/{LandmarksAndModuli,Farey,Polarity}.lean`; `winding_inertia.rs`; `relational_geometry::exact_analysis::{winding,constants}`; `arithmetic_phase/affine_orbit.rs` with `L/Mathematics/AffineOrbitDivisor.lean` |
| Cost | `presentation_cost.rs`; `L/Foundation/{ReceiverCodeCost,PresentationCost}.lean` |

**Concretely absent:** `relational_geometry::screw` is consumed only by
`identity_atlas::screw_gram_point`; the pair receiver `S=[[I,−I],[−I,I]]` exists only in Lean; no
phase-closure owner is called from the helical pair; and on the HNN side
`ResidentCoupledConstitutive::append_operation` re-evaluates the whole growing programme, with
`Power` the only request that compiles a repeated action (of a supplied linear matrix). The
owner map records both as open: resident coefficient-recurrence execution and changing
learned-word compilation; dense-to-modal future compression.

## #50 and #12–#15 — resident exact algebra has no HNN consumer today

[established-bounded; source-inspected] The field session's normal factor/solve is already
resident, and the only `exact_linear` eliminations on the HNN path are small fixed-port
`preimage_fibre` calls below `DECLARED_PRIME_IMAGE_CROSSOVER = 48`. Host elimination time is spent
in `holonic_interaction::ContactDissipation::assemble`, `rigidity_receiver` and
`conditioned_static_response`: the deferred structural consumers. The two obstacles are named and
exhibited by test (`section_layout_adoption::GeneratedTileObstacle::{PivotSweepIsBilinear,SharedLocalOperator}`);
no `Z/p` pivot kernel, second gathered operand, per-region operator table, signed-128-bit generated
ring, device `IntegerAdd` arm or typed context ownership exists. These remain real library work
whose consuming call is outside the current HNN order.

## Consequence for the order

[definition; agent-inferred] The absences split by owner path into two engine port sets and one
session set that do not touch each other, followed by the join that consumes all three. Inferred
from the disjoint files named above and the rule that a join consuming several returns is
sequential.

1. **Participation ports** (`K/field_normalized_receiver.cuh`, `C/field/receiver/normalized*`,
   `resident_section/surface_passage.rs`): the row-sectioned normalized receiver and its pullback.
2. **Condition ports** (`C/resident/section/bilinear_features.rs`, `K/normal_applied_condition.cuh`,
   `C/field/material_transport/normal/direct/section.rs`): the bilinear-source adjoint to the
   condition operand, the enclosure-source section form and the re-entry port.
3. **Session and source** (`A/field_session*.rs`, `alpha/exposure.rs`, `athena_field/shared/`):
   the exposure driver with its request/response aperture and gates, the shared chart's
   producing comparison, the cursor in the saved session, and the first executed shared-chart
   baseline with its README.
4. **The join** (`A/coupled_wave/body/field/section.rs`, `A/field_session/shared.rs`, founding
   in `A/field_session.rs`): participation over gathered neighbour currents, refinement by
   re-entry, both variation terms in `observe_rows`, checked against
   `connected_holonic_field` and the `NormalizedKernel` CPU tests. In parallel, the helical pair
   reaches `ObservableMomentReceiverHistoryCompression` and the phase-closure owners.
5. **Episodes** through the public session with held-out inspection and cost; #18 at the measured
   width; #19's section-scale D update; then the repeated refinement word meets the same
   compression owners.
