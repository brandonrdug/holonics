# The layer is one graph launched once, and the immediate gate returns its falsifiers with the ratchet open

**Date:** 2026-08-19 (construction begun 2026-08-18)
**Kind:** construction return against the resident-passage repair directive: the failure map, the
repair, the one real deed and its inspected artifact, every falsifier with its predicate, the
validation epoch, and the one item that stands open.
**Truth status:** `established-bounded` for every measurement below (each carries its command or its
artifact line); `implemented-exact` for the owners whose focused tests pass; **`open` for the
roadmap's immediate gate as one coherent reading**, because the architecture ratchet is red on the
tree that carries this construction and re-seeding it is not this session's to do; `open` for every
Phoenix master station.
**Authority:** [`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) §"THE PHOENIX REBIRTH…",
[the Phoenix master](../../archive/plans/THE_PHOENIX_REBIRTH_LIFTS_INHERITED_HEXIS_AND_RETURNS_A_NATIVE_EXECUTABLE_ECOLOGY.md),
[the Gemma instance](../../archive/plans/THE_GEMMA_MAP_IS_DISSECTED_CONDENSED_CULTIVATED_AND_REBORN_AS_A_FROZEN_NATIVE_MODEL.md),
[the contract](2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md),
[the audit that withdrew the previous claim](2026-08-18_THE_SECTION_STAYED_BUT_THE_HOST_STILL_OWNED_THE_PASSAGE_AND_NO_PHOENIX_STATION_PASSED.md),
[the validation cadence](2026-08-18_THE_GATE_IS_A_RELEASE_RECEIVER_NOT_AN_INNER_LOOP_AND_REPEATED_VALIDATION_BECAME_THE_BOTTLENECK.md).
**Position boundary:** [`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) does not move.
**Artifact:** `output/the_layer_stays_on_the_card/layer-0-resident-2-tokens-grain-48-terms-14.form`
(5,328 lines) and `output/the_layer_stays_on_the_card/source-runtime-faces-2-tokens.tsv`.

---

## 0. Verdict

**Truth status: established-bounded for the deed; open for the gate as one reading.**

The host semantic dispatch loop the audit convicted — `ResidentBinding → FrontPassage::conduct →
FrontEnactor::enact_in → enact_member`, one launch, one global synchronize and one receipt read per
operation — is gone from production. The whole layer-zero deed, per-layer input predecessor
included, is **compiled once from the binding table, priced whole (semantic and apparatus), admitted
before any allocation, captured into ONE CUDA graph whose 78 edges are the diagram's bonds, launched
once, synchronized once, and read once**; the card accumulates every refusal in a resident census
array; every source binding resolves against authenticated content; the source runtime's face is
returned as a per-port cross-chart defect slot; the signed arithmetic is magnitude-only and checked
against an exact serial reference on the card; and sixteen falsifiers with predicates that can fail
return `PASS` on the real RTX 4080 SUPER, with the serial reference at `2^-96` in parity over all
5,120 terminal coordinates.

**What does not pass, said first:** the directive's completion list includes *"architecture/
no-float/ownership checks pass"*. The no-float check passes (`grep -n "f32\|f64"` over the three
library owners → nothing). The architecture ratchet is **red**: its baseline is emitted from a
detached worktree of `HEAD`, so `resident_section.rs`, `front_passage.rs` and `source_occurrence.rs`
— all uncommitted — carry a zero allowance and every `Vec`, `BTreeMap`, `clone` and `collect` in
them counts. It was read as a design falsifier (§9): no container in the three owners was found
carrying an authored order in place of a transport law. It was **not** re-seeded — re-seeding is the
mechanism the ledger names and it happens at a commit — and it was not documented around: this
record says the gate stands open on it. Therefore no Phoenix station is claimed and the immediate
gate is reported **OPEN on the ratchet**, with everything else it names returned.

## 1. The failure map, as deposited before code

The table below was written before any source edit (`scratchpad/FAILURE_MAP.md`, 2026-08-18) and is
reproduced with what happened.

| present host-owned decision | where it was | required resident replacement | what stands now |
|---|---|---|---|
| `ResidentBinding` as a per-member, per-order host `match` | `front_passage.rs` `enact_member`, called from `FrontEnactor::enact_in` | consume the binding table ONCE at compile into per-occurrence shapes and launches; nothing consulted between nodes | `FrontPassage::compile` → `Plan{shape, bound, producers}`; `realize` records every launch into a graph; the binding is not touched after |
| `FrontPassage::conduct`: cover, price, admit, enact every permutation, compare endpoints, commit | `front_passage.rs:832-980` (audited form) | compile → admit → realize → launch → read | `compile`, `admit`, `realize`, `bind`, `CompiledPassage::launch`, `read_terminal` |
| `FrontEnactor::enact_in` / `impl EnactsInOrder`, `n!` stagings | `front_passage.rs:1090-1139` | independence derived, never replayed | deleted; `interchange::certify_footprints` over read/write address ranges, `Coherence::FootprintDisjoint` |
| `cuCtxSynchronize` + 32-octet scratch read after every operation | `resident_section.rs` `synchronize`, `read_scratch`, `measure`, twelve call sites | one memset node zeroing a resident census array; per-occurrence eight-word slots; one read after the terminal synchronize | `PassageBuilder`, `ResidentPassage::launch`; `TransferCensus{synchronizations: 1}` |
| the shared scratch word — a hidden resource between co-present members | `ResidentSurface::scratch` | per-occurrence slots plus one global word | `SLOT_WORDS = 8`; `Lane{slot, global}` |
| `CoverDecomposition` labelling cells while the launch ignored it; a `DeviceDeclaration` handed in by the driver | `conduct`, `device_declaration()` | the cover built inside the surface from the mounted device's attributes; the passage reads it there | `ResidentSurface::cover()`, `mode()`; no cover parameter exists |
| `ResidentSurface`'s own `#[link(name="cuda")]` census beside `soma/mount` | `resident_section.rs:76-100` | one apparatus census: `mount` | `holonic-engine → mount` (verified with `cargo metadata`: `mount → body, soma-abi`, no cycle); `mount` gained `Event`, stream capture, `Graph`/`GraphExec`/`GraphCensus`, `memset_u32_async`, `launch_on_shared`, `BorrowedContext` |
| work priced per front from measured octaves after the previous front ran; permutations priced `n!` times; residency, staging, census, egress, allocations, synchronizations outside the vector | `predict_deed`, per-front re-price | the WHOLE deed priced from the a-priori octave field before any allocation: `ExactWork` + `ApparatusPrediction`; semantic admitted by a declared `WorkBudget` or exhibited as undeclared; apparatus admitted against the device's free memory | `DeedAdmission{semantic: Option<Admission>, apparatus}`; falsifier 5 |
| `GlobalCouplingBarrier.resident_realization: Option<&str>` | `front_passage.rs` | typed plan and receipt | `CouplingPlan{coupling, kernel, extent, block, predicted}` → `CouplingReceipt{written, measured_octave, measured_width, refused, reach}` |
| file hash only; unchecked symbols; unaddressed container; interventions typed as `Implementation` | `SourceAuthentication`, `resident_layer.rs` | `SourceOccurrence`: symbol grammar resolved in scope, exact JSON spans, header + whole-content digest + regions, assets, `SourceTestimony::Intervention` | `source_occurrence.rs`; falsifier 6 |
| `v << s` on a signed `__int128`; `-v` on the minimum; `b − a` in `int64` | `exact_resident_section.cu:54-68` and elsewhere | unsigned-magnitude shifts with the sign restored under floor/ceiling; a control kernel for the serial reference | `magnitude`, `shift_floor/ceil`, `of_magnitude`, `product_checked`, `dyadic_scale`, `section_arithmetic_control`; falsifiers 2 and 8 |
| two diagrams run in sequence, the first before the second was priced | `found_per_layer_input` + `found_layer` | one deed diagram | `found_deed`: 35 occurrences, 23 fronts |
| falsifiers 13 (`true`), 24 (launch count), 4 (a manual instruction), 1 (old strings) | the driver | predicates that can fail | §6 |

The stop-condition — *"if your proposed repair introduces another operation enum, dispatcher,
scheduler, executor, planner, backend selector, or host callback, stop"* — was checked against the
design before code: the binding table already existed and is consumed once at compile; the deed is a
CUDA graph; the graph's dependency structure is the diagram's bonds; refusals accumulate on the
card; the host receives one return at the terminal.

## 2. What was built, and where the surface shrank

`resident_section.rs` (2,158 → 2,008 lines, ~630 of them tests) lost its extern block, its
per-operation `synchronize`/`refusal_of`/`measure` triple, `clone_section`, `disagreements`, and the
scratch word; it gained the `mount`-bound apparatus occurrence, pure `shape_*` laws, `record_*`
launches into a lane, `PassageBuilder`, `ResidentPassage`, `SlotReading`, and `arithmetic_control`.
`front_passage.rs` (1,418 → 1,511, ~230 of them tests) lost `FrontEnactor`, `impl EnactsInOrder`,
`enact_member`, `CommitHand`, `Standing`, the permutation pricing, and the cover parameter; it gained
whole-deed admission, `ApparatusPrediction`, footprint certificates, typed couplings, the traffic
reading, the mode-checked launch, and the serialized-realization control. `source_occurrence.rs`
(723, ~150 tests) is new. `mount` gained 285 lines of apparatus and no law (`git diff --stat soma/mount/src/`). The kernel is 935 lines
and carries no signed left shift.

**Measured with `cargo run -q -p holonic-architecture-lint`, 2026-08-19, dirty tree:**
`front_passage.rs` `.clone()` 24 · `.collect()` 12 · `.flat_map()` 1 · `.into_iter()` 2 ·
`BTreeMap` 31 · `BTreeSet` 3 · `Vec` 47; `resident_section.rs` `.clone()` 7 · `.collect()` 11 ·
`.into_iter()` 3 · `Vec` 39; `source_occurrence.rs` `.clone()` 20 · `.collect()` 3 · `BTreeMap` 3 ·
`Vec` 21 — all against an allowance of zero, because none of the three is committed. The audited
form's counts cannot be reproduced: those files were never committed and this construction overwrote
them; what departed is enumerated above.

## 3. The apparatus occurrence and the mode

`ResidentSurface::on(readout)` now: `mount::cuda::init`, `Device::count`, `Device::get(0)`, refuses
if the census names a device the readout did not mount (`DeviceDisagrees`), adopts the readout's
context as a `BorrowedContext` (never a second creation), `Module::load_ptx`, resolves the thirteen
kernel symbols (a missing one refuses at mount, not at a launch), builds `DeviceDeclaration` from
`Device::attribute`, builds `HardwareCover::over(Some(declaration))`, derives the launch from device
and kernel attributes, and states its mode:

```text
ModeIdentity { source_law: "holonic_engine::resident_section", abi: "exact-integer-interval-v2",
               kernel: "exact_resident_section",
               device: Some("NVIDIA GeForce RTX 4080 SUPER compute_89 sm80 warp32"),
               arithmetic: "exact-integer", apparatus: "cpu+device0",
               kernel_content: Some("1eb004bc231e7fcd…") }
```

`kernel_content` is new on `ModeIdentity`: the PTX's SHA-256, so two modes with one kernel name and
different laws are two modes. `CompiledPassage::launch(&expected)` refuses `ModeMismatch` without a
deed when the declared mode is not the surface's (falsifier 7: a foreign device, a foreign kernel
content, and a foreign apparatus chart each refused; deed launches unchanged).

The cover **affects the realization** in the one way the doctrine names — placement — and that
placement is checked, not decorative: a cell whose extent does not fill the device chart's grain
(one warp) lands on the CPU chart and the passage returns
`ResourceObstruction::Placement { chart: Cpu }` without a launch
(`front_passage::tests::a_sub_warp_cell_is_a_placement_obstruction_not_a_fallback`); every cell of
the layer landed on `Device(0)` and the receipt says so per front (`cover: CoverReading{device_cells,
cpu_cells: 0, occupied_lanes, idle_lanes}`).

## 4. The deed, measured on the artifact

**Command, closure and clock.** `./target/release/examples/the_layer_stays_on_the_card --tokens
818,18740 --grain 48 --terms 14`, built by `cargo build --release -p holonic-engine --example
the_layer_stays_on_the_card` (1 m 10 s), run 2026-08-19 07:41:31 → 07:47:45 UTC, exit 0, wall
6 m 14 s of which the serial reference is 358.9 s.

**The source occurrence.**
```text
implementation  modeling_gemma4.py  sha256 64ecac478c7d11b9…  transformers 5.8.1
configuration   config.json         sha256 33b10c02df3c2e85…
container       model.safetensors   15,992,595,884 octets · header 281,040 octets sha256 0e2afcbea913d013…
                content sha256 cfbd3d2f1cd71bd4… (9.5 s, taken in a thread beside the mount)
regions         22 identified: every mounted population hashed as it was read; the two entering
                tables and the whole per-layer model projection identified from the header (the
                content digest covers them); the layer's slice hashed under its own name
assets          tokenizer.json, tokenizer_config.json, processor_config.json, chat_template.jinja,
                generation_config.json — each hashed, each declared UNUSED by this aperture
```
**Bindings validated:** 35 operations · **84 symbols resolved with their line numbers** (every one
`Class.method (verbatim source line)`) · **36 configuration fields** compared as exact JSON spans ·
**21 declared shapes** matched to the header · 0 interventions on the base deed (2 on each
matched-sibling deed, on quotient bindings only).

**The diagram and its price, before any allocation:**
```text
5 ports · 35 operations · 35 occurrences · 23 fronts · closed · widest front 4
semantic   additions 188,506,016 · multiplications 189,457,824 · divisions 725,736 ·
           entries written 349,184 · cumulative bits 31,793,152 · peak bits 242 (a bound; 57 measured) ·
           resident entries 81,920 · dependency span 23 · width-weighted 91,642,877,392
apparatus  source maps 749,844,488 octets resident · staged 11,264 · sections 2,793,472 · census 1,152 ·
           deed octets 2,805,888 · allocations 73 · captured launches 70 · deed launches 1 ·
           synchronizations 1 · ingress 11,264 · receipt egress 1,152 · terminal egress 81,920 ·
           graph nodes 71 · graph edges 78 · span 23
admission  semantic: None (no ceiling declared; --work-ceiling absent, said so) ·
           apparatus: 2,805,888 required of 15,695,151,104 free — admitted
```
Two diagrams' six-plus-twenty-three fronts are **twenty-three** fronts as one diagram: the
predecessor's chain lies co-present with the layer's opening fronts. All 35 operations of the two
are present; the count of fronts is the diagram's own layering.

**Bound and launched:**
```text
bound in 0.017 s · graph 71 nodes / 78 edges as the driver holds it (cuGraphGetNodes/Edges) ·
intended (71, 78) · kernel nodes 70 · memset nodes 1 · captured launches 70 (predicted 70)
the deed: wall 0.009 s · CPU ticks 1 · utilization samples [0] (telemetry only)
census across the deed: deed launches 0→1 · captured launches 70→70 · synchronizations 0→1 ·
receipt egress 0→1,152 octets · section egress 0→0 · section read-outs 0→0 · ingress unchanged
the terminal read afterwards: section egress 0→81,920 · read-outs 0→1
global refusal word 0 · every coupling written and unrefused (12) · a-priori bound ≥ measured on
every port · widest slack 15 octaves
```
Nothing was launched between the graph and its terminal synchronize; that is what the census
measures and what a renamed dispatch loop could not pass.

**The physical structure bound, and its bound.** The graph's edge population equals the diagram's
deduplicated bonds plus one edge per occurrence (kernel → census) plus one per entering occurrence
(memset → kernel): `41 + 35 + 2 = 78`. Co-present members carry no edge between them, so the
apparatus is free to overlap them. **What was not observed:** whether the device did overlap them on
this material — no per-kernel timeline was taken. The physical control is falsifier 9: the same
diagram bound as a total order (71 nodes, 96 edges) returns the identical terminal and identical
per-port octaves and widths, and the co-present graph launched a second time returns the identical
terminal.

**The traffic reading**, composed and reported, never routing: resident lanes 122,880; per front
512 to 40,960 lanes occupied, 0 idle, every front one round; `receiver_current` over the diagram's
occurrences and bonds: the earliest section reaches the terminal at chronology 4 along the residual
stream, with 8 later arrivals — the attention, gated-passage and per-layer chains — retained as
deferred (the approach front), 7 reconvergent sites; `traversible_chain` over 22 front-to-front
junctions of lanes, composite `(τ, Γ, T) = (22/21, 1/21, 440/441)`.

**The terminal face:** 2 × 2,560 enclosures at `2^-48`, widest 70,229,731,541 grains ≈ 2.495e-4,
no point enclosures — identical to the widest the audited fixture reported, so the arithmetic
repair moved no coordinate.

## 5. The source/runtime cross-chart defect, as an artifact slot

The exterior realization (`phoenix/source_runtime_face.py`, invoked by the driver, 4.4 s) emits
the source implementation's own values at six ports in two dtypes as exact float64 bit patterns; the
driver decodes each through the exact float mouth and returns, per port and dtype, `chi_gamma`
against the resident enclosure of the same port — inside/outside counts, the worst gap and where,
the first separating coordinate, and how many bf16 quantization fibres (half an ulp either side of
the codeword) meet the enclosure:

```text
port                 dtype  inside  outside  worst gap   first sep.  bf16 fibre meets  widest enclosure
input-rebase         bf16        0    5120   5.670e-1     0            3793            4.370e-13
input-rebase         f32         0    5120   8.273e-6     0               0            4.370e-13
receiver-projection  bf16        0    4096   1.012e0      0            2461            2.771e-12
receiver-projection  f32         0    4096   1.242e-4     0               0            2.771e-12
contact              bf16        0    4096   7.705e-2     0            1805            1.393e-10
contact              f32         0    4096   2.531e-6     0               0            1.393e-10
first-re-entry       bf16        0    5120   6.611e-1     0            2345            8.547e-8
first-re-entry       f32         0    5120   1.603e-4     0               0            8.547e-8
second-re-entry      bf16        0    5120   8.509e-1     0            1752            4.592e-5
second-re-entry      f32       991    4129   1.396e-4     0               0            4.592e-5
layer                bf16        9    5111   9.169e-2     0            1594            2.495e-4
layer                f32      2910    2210   5.513e-6     0               0            2.495e-4
```

Read plainly: the resident deed is an interval realization of the exact formula over the stored
BF16 map at grain `2^-48`; the source runtime rounds every intermediate to its dtype — including the
entering product `embed × 50.5`, which the source's bf16 realization rounds to bf16 while the mouth
carries it exactly, so the two faces already separate at coordinate 0 of the first port. The f32
realization does not round there (its gap at the first port is 8e-6, f32 arithmetic inside the norm),
and it lands inside the terminal enclosure at 2,910 of 5,120 coordinates only because the
propagated remainder has widened the enclosure to 2.5e-4 by then. `chi` is the source's rounding
fibre; the artifact carries it per port and the terminal's 9-of-5,120 reproduces the audit's
figure exactly. It is not dismissed as *"the source rounded"*; it is returned as the cross-chart
defect between the exact-formula chart and the dtype realization, with the quantization fibre.

## 6. Every falsifier, its predicate, and its result

| # | falsifier | predicate (what would fail it) | result |
|---|---|---|---|
| 1 | production cone | structural: the five cone files carry none of eight tokens (`ported_reference`, `PortedOperationKind`, `PortedCarrier`, `PortedProgram`, `ported_reference::realize`, `fn enact(`, `impl EnactsInOrder`, `cuCtxSynchronize`); behavioural: across the deed captured launches unchanged, deed launches +1, synchronizations +1, control launches unchanged | PASS — `[]`; 70→70, 0→1, 0→1, 0→0 |
| 2 | negative interval quotient | on the card, `interval_quotient([-2,-1] lifted by one, [1,2])` returns `[-4, -1]` = `[-2, -1/2]` with refusal 0 | PASS |
| 3 | the card owns the chronology | falsifier 1's behavioural half ∧ every front `FootprintDisjoint` ∧ every cell on `Device(0)` ∧ graph nodes/edges = intended ∧ global refusal 0 | PASS |
| 4 | telemetry never grades | the driver's own text: 19 verdict predicates inspected with string literals removed; none names `samples`, `ticks` or `utilization` | PASS |
| 5 | budget below prediction | `WorkBudget` at price−1 → `ResourceObstruction::Work`; captured launches, deed launches, allocations, resident octets unchanged | PASS — priced 91,642,877,392 vs ceiling 91,642,877,391; 70→70, 1→1, 84→84, 2,809,992→2,809,992 |
| 6 | source mutation refuses | on the `input rebase` binding: fabricated symbol → `SymbolUnresolved`; absent slice → `SliceAbsent`; `rms_norm_eps` declared `1e-05` → `ConfigurationValueDiffers`; shape `[2561]` → `ShapeDiffers`; an intervention on a transport → `InterventionOnSourceLaw` | PASS, all five |
| 7 | mode mismatch | foreign device, foreign kernel content, foreign apparatus chart → `ModeMismatch`; deed launches unchanged | PASS |
| 8 | signed-shift controls | 11 edge cases on the card (signed minimum under shifts 0/−1/40, minimum+1 at −3, ±7 at ±1, −1 at −70, 0 at 60, 5 at 126 refusing, denominator 0 refusing, `[-5,-1]·[3,7]`) against a `BigInt` reference | PASS — 11 of 11 agree |
| 9 | physical concurrent completion | co-present graph (71/78) vs serialized realization (71/96): terminal identical ∧ every port's measured octave and width identical ∧ the co-present graph launched again identical | PASS |
| 10 | source/runtime chi | bf16 face outside at the terminal > 0 ∧ the earliest separating port is before the terminal | PASS — 5,111 of 5,120; first port `input-rebase` |
| 11 | CPU reference poisoning | serial reference at `2^-96` (358.9 s) in parity over 5,120 ∧ the poisoned reference fails parity ∧ the card's re-read bit-identical | PASS — 0 disagree; poisoned 5,120 disagree; identical |
| 12 | hidden card | the driver spawned on itself with `CUDA_VISIBLE_DEVICES=''`: exit 3, `REFUSED: no resident chart — CUDA_ERROR_NO_DEVICE`, no terminal | PASS |
| 13 | both K/V families load-bearing | withdrawing family 0 moves 512 coordinates in each of heads 0–3 and none in 4–7; family 1 the reverse; typed as 2 interventions each | PASS |
| 14 | finer aperture nests | grain `2^-52`, 22 terms: 5,120 of 5,120 nested; widest 2.495e-4 → 1.578e-5 | PASS |
| 15 | remainder load-bearing | the input rebase collapsed to midpoints (typed intervention): 5,120 of 5,120 terminal coordinates moved | PASS |
| 16 | weights mount once; material crosses once | second tokens `[2, 6644]` refilled into the same bound passage: ingress +11,264 = the entering rows, allocations unchanged, populations unchanged, terminal differs at 5,120 | PASS |
| 17–23 | seal, native rest, runtime, adjoint, held-out, matched arms, targeted ablation | not attempted | OPEN by name — later stations |

Sixteen `PASS`, seven `OPEN`, zero `FAIL`, counted from the artifact's `falsifiers:` section.

## 7. The validation epoch, with durations

Owner iteration: `cargo check -p mount` (0.6 s); `cargo check -p holonic-engine --lib` (first
2 m+ after the new dependency and kernels rebuilt, then 16–30 s); `nvcc --ptx` on the changed
kernel alone (~1 s, four times); `cargo test -p holonic-engine --lib -- resident_section
front_passage footprint_tests source_occurrence` (25 tests, ~1 s on the card after a 1 m 30 s
build; repeated three times for stability under parallel threads after a capture-mode collision was
found and fixed: `THREAD_LOCAL`, not `GLOBAL`). Changed-cone: `cargo check -p holonic-engine
--examples` (12.5 s, no errors, pre-existing unused-import warnings in other drivers);
`cargo build --release -p holonic-engine --example the_layer_stays_on_the_card` (1 m 10–22 s, four
times). Real deed: four runs — one refused at compile (the a-priori octave law was too loose once it
was used for admission instead of measured octaves; repaired on the card by self-scaling the contact
brackets and the GELU cube from the material's own octaves, and capping the bound at the word), one
`--no-serial` (exit 0), two complete (6 m 14 s each; the last on the final closure is the artifact).
No `cargo test --workspace`, no `--all-targets`, no bare gate during construction.

## 8. Standing corrections this construction made along the way

- **`hardware_cover.rs` said the engine could not depend on `soma/mount` because of a Cargo cycle.
  That was wrong**: `cargo metadata` shows `mount → body, soma-abi`; the forbidden edge is
  `engine → life`. Corrected in place; the engine now depends on `mount`.
- **`ModeIdentity` gained `kernel_content`**, the PTX digest, so a mode names its law by content.
- **`SourceTestimony::Intervention`** exists; interventions are no longer offered as implementation
  symbols and are admissible only on quotient bindings.
- **`interchange::certify_footprints`** and `Coherence::FootprintDisjoint` /
  `DistinguishingWord::FootprintShared`: independence derived from address footprints before launch.
- **`receiver_current` reads a diagram as its earliest section**: the first arrival at a site is
  caused and later arrivals are deferred; on this layer the residual stream is a four-hop shortcut
  and the transforming chains are the deferred population. Reported under that name.
- **A receiver that declares no semantic ceiling is exhibited as `semantic: None`**, never as
  `2^62`; `--work-ceiling` declares one at runtime.

## 9. What stands open, exactly

1. **The architecture ratchet is red on this tree** (§2). It is a design falsifier and was read as
   one; it is red because the three owners are uncommitted, and it stays red until a commit re-seeds
   the baseline — which this session did not and may not do. Under the directive's completion list,
   the immediate gate is therefore **OPEN**, not returned, and no later Phoenix station is claimed.
2. Whether the device overlapped co-present kernels at runtime was not observed (§4); the serialized
   control is the physical falsifier taken.
3. `output-manifest` and `closure-manifest` were regenerated once with the release reading (§10);
   they are expected to be red again on the next source edit, by their construction.
4. Every Phoenix master station: `open`. Falsifiers 17–23 name why.

## 10. The release reading, in its two scopes

**The one complete gate**, `bash tools/gates.sh`, 2026-08-19 07:56:08 → 08:00:56 UTC, exit 1,
4 m 48 s, after the ledgers were regenerated once (the sixteen new selector and refusal-bit rows
dispositioned `ABI` by hand in `meta/AUTHORED_LEVELS.tsv` and the fifteen departed selector rows
removed, `authored_levels.py --check` then 0 failures; `claim_index.py`, `driver_catalog.py`,
`output_manifest.py`, `closure_manifest.py` each run once):

```text
PASS  tests              2506 passed, 0 failed, 19 ignored over 29 result lines; example targets type-checked
PASS  authored-levels    0 failures; 401 authored numeric levels in DRIVERS
PASS  named-paths        0 failures; 2740 tokens
PASS  line-citations     0 failures; 431 citations
PASS  claim-index        current
FAIL  driver-catalog     DRIFTED — 0 uncatalogued, 0 missing, 249 rows re-measured
PASS  output-manifest    53 recorded, 53 present, 0 departed, 0 moved, 0 unrecorded
PASS  closure-manifest   current: 54 return directories, 18 orphans
PASS  boundary-artifacts 3 bound
PASS  typst              10/10
FAIL  architecture-lint  121 new ownership/materialization occurrences
PASS  document-law       0 failures; 71 absence claims carry command and date
10 passed, 2 failed
```

**The second scope, named and separate.** `driver-catalog` drifted on re-measured rows (the driver
atlas was edited after the catalog was regenerated); the catalog was regenerated — a ledger, no
code, kernel, driver or artifact — and `bash tools/gates.sh driver-catalog` alone returned `PASS`
at 08:01:11. The withdrawn claim record of 2026-08-18 was then bannered as withdrawn, and
`bash tools/gates.sh claim-index named-paths document-law driver-catalog` returned `4 passed`.
**These are not spliced into the complete reading above**: the complete reading is 10 of 12, and
`architecture-lint` is red in both scopes for the reason §2 and §9 give.
