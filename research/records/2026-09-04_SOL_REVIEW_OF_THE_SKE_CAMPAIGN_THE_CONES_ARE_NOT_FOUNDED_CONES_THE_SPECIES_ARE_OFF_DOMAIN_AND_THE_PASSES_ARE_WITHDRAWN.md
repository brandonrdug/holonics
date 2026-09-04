# Sol's review of the 2026-09-03 SKE construction: the cones are not founded cones, the species are off their domain, and the passes are withdrawn

**Date:** 2026-09-04. **Author:** Sol (Codex), launched by Brandon's request through the Claude session; the text below is Sol's review verbatim, read-only over the tree at 4aa4e906. **Truth status of this record:** testimony; every graded bracket inside is Sol's.

# Critical review of the 2026-09-03 SKE construction

[established-bounded; source-inspected; process-audit] I reviewed commits `ae8bf299`, `5ee9bcfe`, `057ef4bb`, `4c003a95`, and `4aa4e906` with `git show --stat`, read the mandated authorities and named implementation/record files, parsed all 120 JSON receipts, checked all 15 remainder vectors against their exposure histograms, inspected the current 9,383,686,281-byte rest header and digest, and ran the focused Lean file. `timeout 180 lake env lean ElementaryHolonics/Computation/HolonicExcitationFoundedQuotient.lean` exited 0 and printed only `propext`, `Classical.choice`, and `Quot.sound`. The focused Cargo commands could not start because the read-only sandbox denied `target/debug/.cargo-lock`; they are not validation evidence.

## 1. Segment session and the 2026-08-18 contract

**MIXED**

[established-bounded; source-inspected; measured] The ordinary `advance_cycle` path does bind each admitted segment before launch. Planning and allocation precede `begin_passage` (`crates/holonic-engine/src/holonic_intelligence/operative_segment.rs:183-192,206-582`), and recording/closure precedes the sole `finish()?.launch()` (`operative_segment.rs:584-755`). Obstruction flags are checked before outcomes return (`operative_segment.rs:755-761`). The segment receipt reports 687 launches, 687 synchronizations, 16 section reads, and 58,720,256 egress octets—exactly `14 × 262,144 × 16`, consistent with terminal-tile egress and no body-section copy (`research/records/2026-09-03_SKE4_receipts/session_census_one_cycle_segments.json`). At this narrow forward-cycle aperture, “bound whole, launch once, read the passage census once, no intermediate section egress” stands.

[counterexample; source-inspected] A-priori admission is unsound on the overlay path. In-segment consumers use a producer’s `value_octaves` (`operative_segment.rs:193-205`), while the producer, overlay joins, and fused seal are closed against the potentially larger `needed` value (`operative_segment.rs:330-355,705-738`). For contractions:

```rust
value_octaves.max(carrier_octaves.min(value_octaves))
```

at `operative_segment.rs:342-343` is identically `value_octaves`. It discards overlay-induced growth in `carrier_octaves`. A producer may therefore exceed the bound handed to its consumer while remaining within its own larger `needed` bound, raising no producer obstruction.

[established-bounded; source-inspected] Deferral is coherent only after sound planning. A mid-segment `CarrierRange` closes the segment before that operation (`operative_segment.rs:565-575`); `enact_run` commits the prefix and replans the remainder (`crates/holonic-engine/src/holonic_intelligence/full_operation.rs:403-460`); the next passage uses the retained carrier’s measured bound (`operative_segment.rs:202-205`). It cannot repair `value_octaves < measured ≤ needed`, because that case raises no `CarrierRange`.

[open; source-inspected; measured] Coverage does not close the gap. The only segment test checks boundaries (`operative_segment.rs:827-840`). The agreement receipt explicitly tests 1,270 one-operation segments, not consumers within multi-operation segments (`research/records/2026-09-03_SKE4_receipts/per_operation_agreement_with_the_committed_session.json`). The multi-operation SKE2 exact-face digest changed from `ecbab1f5f902b9dd` to `0f283aeb9a070d8d`, with the responsible enclosure law left open (`research/records/2026-09-03_SKE4_THE_SESSION_RUNS_AS_SEGMENTS_UNDER_THE_2026-08-18_CONTRACT_AND_THE_FACE_ALONE_CROSSES_TO_THE_HOST.md:44-50`).

[counterexample; source-inspected] Two blanket descriptions exceed the measured aperture. “672 passages” is a trace-count artifact: all terminal traces receive the final aggregate census (`operative_terminal.rs:245-283`), although 16 tiles each invoke `enact_segment`; the actual passage launches are 687. Also, the same session exposes one-operation `advance` (`full_operation.rs:491-549`), while dissection reads every differential and forward contraction section to the host (`crates/holonic-engine/src/holonic_intelligence/operative_intervention.rs:594-615`). The no-intermediate-read claim applies to the measured ordinary cycle, not every session/dissection path.

## 2. Role cones, `IsConeUnder`/`FoundedCone`, and extent

**DEFECTIVE**

[proved-derived; formal-checked] Lean is exact here. `ChangingWithdrawals` contains the declared populations whose withdrawal changes the signature; `FoundedCone` is the union of those whole populations (`soma/formal/elementary-holonics/ElementaryHolonics/Computation/HolonicExcitationFoundedQuotient.lean:400-412`). `isConeUnder_foundedCone` proves that union sound (`HolonicExcitationFoundedQuotient.lean:413-438`). `isConeUnder_mono` separately permits arbitrary supersets (`HolonicExcitationFoundedQuotient.lean:381-388`), while `changingWithdrawal_meets_isConeUnder` proves only that a changing withdrawal intersects a sound cone—not which member caused the change (`HolonicExcitationFoundedQuotient.lean:446-456`). `ExcitationFoundedReturn` requires only `coneSound : IsConeUnder`, not `cone = FoundedCone` (`HolonicExcitationFoundedQuotient.lean:601-623`).

[counterexample; source-inspected; measured] The implemented extension is not `FoundedCone`. Class 0 begins with 32 roles found by changing singleton withdrawals. The driver then probes the whole 95-role complement, restores roles until every face stands, and adds only the restored prefix (`applications/athena-alpha/examples/condensation_seal_ske4.rs:702-760`). Receipt `role_cones/extend_joint_order_class0.json` states:

- `cone_roles_before = 32`;
- the zero-restored 95-role complement changed all three faces;
- `extension` contains 77 roles;
- the returned cone contains 109 roles and excludes 18.

Under Lean, that changed 95-role complement enters `FoundedCone` whole. Together with the 32 changing singletons, its founded union is all 127 roles—not 109.

[counterexample; source-inspected] Restricting the declaration to singleton withdrawals does not save the claim. In that interpretation, `FoundedCone` is exactly the union of changing singletons; the 77 extension roles come from its complement (`condensation_seal_ske4.rs:493-525,715-760`). The returned sets may be non-minimal `IsConeUnder` supersets for the selected-address receiver, but they are not what either declaration founded.

[established-bounded; measured] The current artifact’s family extent happens to equal the union of its class sets: class sizes `[109,115,110,106,99]`, class-union size 117, family size 117. That agrees extensionally with `DeclaredFamily.extent` (`HolonicExcitationFoundedQuotient.lean:458-468`) because the driver assigns each occurrence its class mask (`condensation_seal_ske4.rs:969-1020`).

[counterexample; source-inspected] That equality is not enforced. `found_mode` adds the family extension independently of the class union (`condensation_seal_ske4.rs:531-544`); dismantling trusts that independent extent (`crates/holonic-engine/src/holonic_intelligence/operative_condensation.rs:381-404`); `NativeConeRestrictedEcology::validate` never checks `extent == union(classes[].cone)` (`operative_condensation.rs:547-576`). A future artifact can violate the formal extent law and still validate.

[established-bounded; measured] The evidence is only for the coarse selected-coordinate receiver. Across the 15 `roles_occ*.json` files, 1,905 singleton readings produced zero refusals and 235 selected-address changes; in 1,670 readings the selected address stayed equal while the exact digest changed. This is bounded `u32`-receiver testimony, not an exact-row or universal `IsCone` result.

## 3. Remainder, species, decoder, and product vector

**DEFECTIVE**

[established-bounded; source-inspected; measured] The ignored current rest physically contains structured pair data. Its 10,455,565-byte header contains 1, 5, and 5 `NativeCollapsedPair` entries for classes 0, 3, and 4, with full faces and separating words. Its SHA-256 is `e76a301e11e2a98fa709652ec47fdff27047cebc38696472003b4629d1b17c6e`, matching `research/records/2026-09-03_SKE4_receipts/role_cones/rest.sha256`. All 15 tracked SKE4 width binaries contain 262,144 values and match their exposure histograms. But tracked `role_cones/dismantle.json` preserves only pair counts; no complete pair/receiver/separator witness exists in the tracked receipt directories.

[counterexample; source-inspected; measured] More importantly, those pairs are not the persisted class body’s collapsed population. The driver derives them from the full resident operator under each class-complement withdrawal across all 15 exposures (`condensation_seal_ske4.rs:972-995`). Each stored class fibre is a singleton, and the final deed drives its mounted body only on that singleton’s three exposures while treating the other 12 as refused (`condensation_seal_ske4.rs:1317-1369`; `role_cones/bodies.json`). The retained log records an earlier actual nonmember drive through class 0 disagreeing with its supposed lens (`research/records/2026-09-03_SKE4_receipts/role_cones/deed.log:444-456`), after which the record narrows the body’s domain (`research/records/2026-09-03_SKE4_THE_DECLARED_WITHDRAWALS_FOUND_ROLE_CONES_THE_CLASS_BODIES_CARRY_THEIR_REMAINDER_AND_THE_RETURN_CROSSES_THE_BOUNDARY.md:165-171`). Inputs the body refuses cannot simultaneously be its `H.0420` collapsed population. The three SKE4 “compression” species are category-wrong.

[counterexample; source-inspected] `NativeClassRemainder::species_of` is an authored classifier rather than `H.0420`. Any nonempty finite pair list becomes compression; otherwise point terminal intervals become rebase and nonpoint intervals become condensation (`operative_condensation.rs:160-169`). The tablet requires invertible conjugacy for rebase and a far-population-to-compact-realizer pivot carrying a certified witness for condensation (`canon/TABLET_THE_COMPRESSION.md:29-42`). Selected-face equality plus interval counts proves neither.

[counterexample; source-inspected] The condensation remainder is reduced to numeric summaries. `NativeTerminalRemainder` stores coordinate count, nonpoint count, widest width, grain, and a width histogram—not the coordinate-indexed residual (`operative_condensation.rs:120-133`). SKE5 computes `composed_widths` but persists only histograms (`applications/athena-alpha/examples/composed_variant_ske5.rs:138-170`). A histogram is a quotient of the residual, not the exhibited witness required by `canon/TABLET_THE_COMPRESSION.md:39-42`.

[counterexample; source-inspected; measured] SKE5’s additive width invariant is arithmetically invalid. `width_difference` subtracts raw `u32` counts without accepting their grain (`applications/athena-alpha/src/composed_variant.rs:139-145`). The SKE4 full exposure has `remainder.grain=47` (`research/records/2026-09-03_SKE4_receipts/role_cones/exposure_occ0_hist0.json`), while SKE5’s corresponding composed remainder has `grain=43` (`research/records/2026-09-03_SKE5_receipts/ske5_composed_variant.json:690-714`). Composed counts must be multiplied by 16 before subtraction in the `2^-47` chart. The receipt stores the unscaled histogram, yet the record calls it a difference at `2^-47` (`research/records/2026-09-03_SKE5_THE_COMPOSED_VARIANT_RUNS_THE_RECURRENCE_ON_THE_FAMILY_STATES_CONDENSATION_BY_ITS_REMAINDER_AND_IS_NOT_SATURATED.md:45-51`).

[established-bounded; source-inspected] No compression ratio is calculated in `ProductVector` or `DeclaredDecoder`; their numeric fields are apparatus measurements (`applications/athena-alpha/src/composed_variant.rs:38-90`). But decoder identity is merely three free-form strings plus counters (`composed_variant.rs:41-50`), while “native standing” is byte/row counts plus a SHA (`composed_variant.rs:65-90`). Thus no ratio contaminates the receipt, but “no scalar stands for any component” and “the decoder is half of the object” are not discharged by this structure.

## 4. Residency and honesty of the condensation claim

**MIXED**

[established-bounded; source-inspected; measured] The residency limitation is honestly exposed. `NativeRestrictedIntake::population_octets` requests each original population’s full `rows × dim × 2` allocation; delivery zero-fills absent rows (`operative_condensation.rs:739-803`). SKE5 reports `composed_resident_octets=15,752,729,188` and `full_coefficient_octets=15,036,138,068` (`ske5_composed_variant.json:1398-1407`), and the record explicitly limits the restriction to stored presentation rather than card residency (`research/records/2026-09-03_SKE5_THE_COMPOSED_VARIANT_RUNS_THE_RECURRENCE_ON_THE_FAMILY_STATES_CONDENSATION_BY_ITS_REMAINDER_AND_IS_NOT_SATURATED.md:61-65`). Runtime expansion does not by itself refute a codec condensation.

[counterexample; source-inspected] “Resident at the full operator’s size” is only a qualitative statement. The vector compares total composed residency against raw full coefficient octets—not like-for-like resident totals—despite claiming a side-by-side residency coordinate (`applications/athena-alpha/src/composed_variant.rs:84-89`; `composed_variant_ske5.rs:217-220`). The closest full-resident measurement is the distinct SKE4 field `resident_octets_peak=15,871,317,244`. No quantitative equality or strict decoder-inclusive product fall follows.

[conditional; source-inspected; measured] A stored-presentation condensation would be honest if the 9.38 GB rest, executable decoder, complete certified remainder, and declared-family factorization formed one valid pivot. The rest and bounded selected-face reproduction are real (`ske5_composed_variant.json:1236-1407`), but the remainder/species/domain defects above leave the condensation grade conditional.

## 5. Jurisdiction, bounded apertures, and role lawfulness

**DEFECTIVE**

[established-bounded; source-inspected] Surface language and formatting remain application-side. Arithmetic/English strings, encoding, and rendering occur in the Athena-alpha examples (`applications/athena-alpha/examples/condensation_seal_ske4.rs:41,61-64,98-111`; `applications/athena-alpha/examples/composed_variant_ske5.rs:18-37,85-98,118-170`). Engine owners receive addresses and neutral exposure records. Outside-family and undeclared-history cases return insufficiency (`ske5_composed_variant.json:680-683`), and the record limits claims to the family (`research/records/2026-09-03_SKE5_THE_COMPOSED_VARIANT_RUNS_THE_RECURRENCE_ON_THE_FAMILY_STATES_CONDENSATION_BY_ITS_REMAINDER_AND_IS_NOT_SATURATED.md:80-86`). Exact-carrier refusals are described as apparatus limits, not universal walls (`research/records/2026-09-03_SKE4_THE_DECLARED_WITHDRAWALS_FOUND_ROLE_CONES_THE_CLASS_BODIES_CARRY_THEIR_REMAINDER_AND_THE_RETURN_CROSSES_THE_BOUNDARY.md:54-65`).

[definition; source-inspected] Layer-block roles are lawful as one declared input-side experimental chart. The owner partitions contraction populations by graph reach within a recorded layer and stops at residual `Add` (`crates/holonic-engine/src/holonic_intelligence/operative_roles.rs:84-119,182-255`); roles expand deterministically into site populations (`operative_roles.rs:271-299`). That is bounded apparatus testimony, not intrinsic topology.

[counterexample; source-inspected] The construction nevertheless promotes the foreign chart through Soulkiller. `NativeConeRestrictedEcology` retains the complete `NativeFullOperatorEcology` (`operative_condensation.rs:221-244`); dismantling moves `self.realization.native` unchanged into the productive lane (`operative_condensation.rs:338-340,469-478`); the hot ecology still contains `operation.layer`, `NativeAttentionTopology`, shared-K/V standing, operator nodes, and layer topology (`crates/holonic-engine/src/holonic_intelligence/operative_atlas.rs:74-143,162-173`). SKE5 remounts and runs the same graph unchanged (`composed_variant_ske5.rs:101-140`). This violates the contract that source-specific factorization/topology may be load-bearing only inside dissection and that a rest still mounting a foreign tower remains scrapyard transition material (`AGENTS.md:667-690`).

[counterexample; source-inspected] Calling `soulkiller::dismantle` does not establish a seal. The boundary lets each input choose arbitrary `Productive` and merely invokes `input.dismantle()` (`crates/holonic-engine/src/soulkiller/boundary.rs:49-73`). It enforces neither `NativeTransportScaffold` nor source neutrality. Its docstring says manifestations cannot cross (`boundary.rs:1-8`), while the Lean revision proves `manifestationReturn` inhabits the formal return type (`HolonicExcitationFoundedQuotient.lean:703-755`). This is a nominal boundary crossing, not a demonstrated Soulkiller return.

[counterexample; source-inspected] The role grain is also insufficient for campaign closure. `GRAIN` is hard-coded to `LayerBlock` (`condensation_seal_ske4.rs:61-65`), and no cross-grain naturality or structural-cone theorem is returned. AGENTS keeps layers/stacks as apparatus charts and forbids post-Soulkiller factorization by a foreign execution chart (`AGENTS.md:659-670,824-833`). The role declaration is a lawful probe; its promotion into native identity is not.

## 6. Child processes and the 180-second rule

**DEFECTIVE**

[project-postulate; source-inspected] The rule is explicit: no process may exceed 180 seconds wall time; every nontrivial invocation needs an outer hard boundary; long work must be factored into independently authenticated, resumable sections; and a timeout is a counterexample (`AGENTS.md:814-833`).

[counterexample; source-inspected] The guard implements a heartbeat timeout. `step()` resets `LAST_STEP` after each probe (`applications/athena-alpha/examples/condensation_seal_ske4.rs:1194-1203`); the guard kills only after more than 180 seconds since that mark, polling every five seconds (`condensation_seal_ske4.rs:1205-1216`). Joint probes remain in memory until the child writes one final receipt (`condensation_seal_ske4.rs:717-774`), so the marks are not authenticated resumable sections. The parent blocks on `Command::status()` without a deadline and has no guard (`condensation_seal_ske4.rs:1240-1300`).

[counterexample; measured; process-audit] The violation occurred. `extend_joint_order_class3.json` records `elapsed_seconds=181.648943087`; `extend_joint_order_family.json` records `655.959280105`. The retained log shows a 180-second forced failure, an immediate rerun, the 181.6/656.0-second children, and a resumed parent deed lasting 414 seconds (`research/records/2026-09-03_SKE4_receipts/role_cones/deed.log:182,251,269-273`). The SKE4 record independently admits 182/656-second children and about an hour of card time (`research/records/2026-09-03_SKE4_THE_DECLARED_WITHDRAWALS_FOUND_ROLE_CONES_THE_CLASS_BODIES_CARRY_THEIR_REMAINDER_AND_THE_RETURN_CROSSES_THE_BOUNDARY.md:44-52,173-177`).

[counterexample; source-inspected] Brandon had already rejected precisely this interpretation: he called per-stage bounding a workaround and alarming, then said the driver was invasive and that the cap exists to eliminate churn and wrongful awaiting of hung processes (`/home/b/.claude/projects/-home-b-Workspaces-holonics/e6ec0363-0473-4f0f-ab29-3397fd89f073.jsonl:5895,6023,6033`). Recasting total wall time as inactivity time games both the letter and stated intent.

## 7. Additional category errors, missing gates, and unsupported prose

**DEFECTIVE**

[counterexample; source-inspected] SKE5 did not run one continuing session across the family. It constructs `NativeFullOperatorSession::found` afresh for every sealed exposure and again for every unsealed remainder pass, then discards each successor (`applications/athena-alpha/examples/composed_variant_ske5.rs:118-173`). That fails the explicit “one session” condition (`blueprint/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md:441-446`). Fifteen independent generation-zero cycles are not one recurrence.

[counterexample; source-inspected] Runtime “saturation” is not Lean `Saturated`. Formal `Enlarges` preserves the occurrence presentation and enlarges receiver/history declarations; `Saturated` means pairwise identification is preserved, without counts (`HolonicExcitationFoundedQuotient.lean:221-278`). Runtime prefixes change the seen occurrence set and remove incomplete occurrences before each quotient (`applications/athena-alpha/src/composed_variant.rs:160-194`). The final `added_classes=1` (`ske5_composed_variant.json:1704-1723`) is occurrence 4 finally entering a complete prefix, not a class reopened by enlarging receivers/histories on the same family.

[counterexample; source-inspected] The saturation receipt also omits generators, relations, obstructions, and reachable consequences required by the blueprint (`blueprint/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md:430-445`). Its Rust structure carries only counts of classes, separations, roles, and distinct selected faces (`applications/athena-alpha/src/composed_variant.rs:92-117`).

[counterexample; source-inspected] Cold testimony contains fabricated data: `NativeExposureTestimony.monotone` is assigned `true` unconditionally (`condensation_seal_ske4.rs:1034-1053`) despite the same campaign recording 39 order inversions and a nonmonotone prefix declaration (`research/records/2026-09-03_SKE4_THE_DECLARED_WITHDRAWALS_FOUND_ROLE_CONES_THE_CLASS_BODIES_CARRY_THEIR_REMAINDER_AND_THE_RETURN_CROSSES_THE_BOUNDARY.md:72-85`).

[open; source-audit] SKE5’s pass requires focused tests and one complete release receiver (`blueprint/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md:441-446`). Its record contains no test or gate result, and `git show --format= --name-only 4aa4e906` contains no release receipt. Only three narrow unit tests were added (`applications/athena-alpha/src/composed_variant.rs:276-316`). Advancing the roadmap and state to campaign-complete without the required release receiver is unsupported.

[counterexample; source-inspected] Critical invariants are absent from validation. `NativeConeRestrictedEcology::validate` checks schema, ecology, cross-section shape/order, and row ordering only (`operative_condensation.rs:547-576`). It does not validate extent union, cone soundness, remainder species, member-face descent, rest digest, or decoder availability. `NativeCollapsedPair` also serializes the collapsed exposure and separating word but not the separating receiver selected by the search (`operative_condensation.rs:107-118,194-212`); the current one-receiver family hides this generic defect.

[established-bounded; source-inspected] Commit `057ef4bb` honestly retires the per-event scaffold/receipt path. Its replacement explicitly says it lifts, decodes, reconstructs, and claims nothing (`crates/holonic-engine/src/native_spool/fixture.rs:1-12`). But `git diff --shortstat 5ee9bcfe 057ef4bb` reports 43 files changed, 803 insertions, and 2,482 deletions: downstream tests now establish declared-fixture mechanics rather than actual Gemma receipt admission. That scope contraction must not be cited as continued actual-lift coverage.

[counterexample; source-inspected] The SKE4/SKE5 records repeat the tablet’s vocabulary—species, decoder, difference, product, saturation—without discharging the code obligations. Record prose cannot repair the wrong `FoundedCone`, wrong remainder domain, cross-grain subtraction, fresh-session loop, fabricated monotonicity, or absent release receipt.

## What stands

- [proved-derived; formal-checked] Commit `ae8bf299` compiles and honestly exposes that `ExcitationFoundedReturn` does not exclude a manifestation (`HolonicExcitationFoundedQuotient.lean:542-600,703-755`).

- [established-bounded; source-inspected; measured] The ordinary segmented cycle reduced body-section host egress to the 16 terminal tiles and launches from the recorded 2,363 baseline to 687 at the tested 14-address aperture.

- [established-bounded; source-inspected] Commit `057ef4bb` removes the rejected per-event scaffold lane without an alias and labels its replacement a fixture rather than a lift.

- [established-bounded; source-inspected; measured] Application/codec separation, scoped insufficiency, 15 selected-face equalities, tracked SKE4 width vectors, and disclosure that the composed body expands to full resident shapes are real bounded artifacts.

## What is overclaimed

- [counterexample; source-inspected; measured] The 99–115-role sets are not Lean `FoundedCone`s, and Rust does not enforce the observed 117-role extent union.

- [counterexample; source-inspected; measured] SKE4 class “compression” witnesses belong to a counterfactual lens outside each class body’s domain; SKE5 reduces its condensation remainder to histograms and subtracts widths at incompatible grains.

- [counterexample; source-inspected] The productive lane remains the same foreign-derived layer/attention/KV operator graph with selected coefficient rows zeroed. Naming its dispatcher `soulkiller::dismantle` does not make it source-neutral.

- [counterexample; source-inspected; measured] SKE5 ran fresh independent sessions, its saturation counter is not the formal saturation object, and the heartbeat scheme violates the wall-time rule.

- [open; source-audit] The required complete release receiver is absent. SKE5 and campaign completion are therefore unsupported.

## What must be corrected before the frontier can move

- [open; source-inspected] Repair the contraction consumer bound so overlay joins are included, bind producer/consumer admission to one sound value, and add a multi-operation deferral test exercising `measured > consumer bound`.

- [open; proved-derived; measured] Implement one cone notion exactly. If it is `FoundedCone`, include every changing declared population whole. If it is only an `IsConeUnder` enlargement/hitting candidate, rename and grade it accordingly. Enforce extent equality in validation.

- [open; source-inspected] Make the productive hot closure source-neutral. The full foreign operator/layer/attention/KV topology may remain dissection apparatus but cannot cross as Athena’s recurrence graph.

- [open; source-inspected; measured] Define every codec pivot on one domain, persist complete collapsed populations with receiver/shortest-word witnesses, retain coordinate-indexed condensation certificates, rebase grains before subtraction, and bind the executable decoder to the artifact.

- [open; source-inspected] Rerun SKE5 as one move-owned successor session, implement a receipt corresponding to formal `Saturated` or stop using that name, and return every structural field required by the blueprint.

- [open; process-audit] Replace heartbeat resets with real outer 180-second boundaries and independently persisted resumable sections. Then run the named focused tests and one complete release receiver before restoring any SKE4/SKE5 pass or campaign-complete status.
