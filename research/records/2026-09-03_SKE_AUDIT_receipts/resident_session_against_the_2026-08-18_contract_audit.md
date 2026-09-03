# resident_session_against_the_2026-08-18_contract_audit

Testimony of one Opus 5 audit sub-agent, 2026-09-03, read-only over the repository and the conversation logs; integrated by the primary session in `../2026-09-03_SKE_AUDIT_THE_COORDINATE_GRAIN_THE_HOST_READOUT_AND_THE_COMPRESSION_LAW_WERE_INJECTIONS_AND_THE_CANON_ALREADY_OWNS_THE_ANSWERS.md`. Every claim below is testimony until cited there.

I'll start by reading the governing contract records and the source in parallel.
I have completed the audit. Here is the report.

---

# Audit: is the HNA session the "renamed instruction loop" the 2026-08-18 contract refused?

**Verdict: yes, and the claim understates it.** The session is structurally the same shape the audit convicted on 2026-08-18, with one addition the earlier form did not have: it also copies the *whole semantic section* to the host after every operation, and takes a semantic decision (the successor projection) from those host words. The 08-18 form read a 32-octet receipt per operation; this one reads the entire carrier. Two details in the claim as stated are wrong in the session's favour and one is wrong against it — detailed in §E.

**Authorship correction up front.** The task attributes the per-operation trace to "Sol/Codex". The git record says otherwise: `baa988a9` (2026-09-02, "Return the Holonic Neural Athena recurrent ecology") and every SKE commit through `eab19f23` carry `Co-Authored-By: Claude Fable 5.1`. The 2026-08-18/19 contract, audit, and Station A–D work carry `Claude Fable 5` / `Claude Opus 5 (1M context)`. The per-operation readout is a Claude injection into a contract a Claude session had written six weeks earlier.

---

## A. The contract's requirements against the session's behaviour, item by item

### A.1 What the contract requires

`research/records/2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md`

- :22–24, the only verbatim Brandon quote in the document: *"the GPU should not be 'used more'; the continuing semantic section must remain owned by the GPU surface. That distinction is what prevents another round of adding CUDA leaves to a CPU machine."*
- :38–40: *"The unit of the correction is one **resident section handle** that enters a semantic operation on the card and leaves it on the card; the CPU never sees a `Vec<Rat>` between two semantic operations."*
- :165–168: *"Operations take handles and return handles plus a `LocalReceipt { launches, work, octave census, width census, refusals }`. **No operation returns a host `Vec<Rat>`.**"*
- :191–195, the complete returned consequence: *"The terminal face copied out once: `T × 2560` intervals; the per-front receipts …; the crossing census with **zero intermediate D→H section transfers**"*.

The audit that occasioned it, `2026-08-18_THE_SECTION_STAYED_BUT_THE_HOST_STILL_OWNED_THE_PASSAGE_AND_NO_PHOENIX_STATION_PASSED.md`:

- :62–68, what makes a loop "renamed": *"`front_passage.rs:71-99` declares the instruction population; `:832-980` loops through fronts on the CPU; `:1003-1071` selects the resident operation by a host `match` … The production-cone gate at `resident_section.rs:1887-1910` searches only for the old spellings. It does not ask whether a replacement enum and dispatch loop own the same decision. The gate passes under renaming and therefore cannot promote the claimed resident passage."*
- :74–85, the convicted census: *"launches 180 / synchronizations 180 / receipt egress 5,760 octets = 180 x 32 / section read-outs 1"* — followed by *"The vectors stay resident; the semantic current does not. The CPU regains control after every local kernel and selects the next semantic variant. This is GPU arithmetic under a host foreman, not a GPU-owned circulation."*
- :172–174, the disposition: *"remove the host semantic dispatch; return one front/deed delta instead of per-kernel host consultation"*.

The repair owner states the same in its own header, `crates/holonic-engine/src/resident_section.rs:1-27`:

```
//! ... the whole passage is bound as one CUDA graph before it is launched, launched once,
//! and read once.
...
//! ... every local operation launched, globally synchronized, read a receipt word back, and
//! only then did the serial chart decide the next operation — 180 launches, 180
//! synchronizations, a renamed instruction loop.
...
//! ... the graph is launched once; refusals accumulate on the card in one census array; and
//! the serial chart receives one census reading and one terminal face. Between the graph
//! launch and the terminal synchronize the serial chart issues nothing — [`TransferCensus`]
//! counts it, so a renamed loop is caught by measurement rather than by a string.
```

`TransferCensus` restates the pass condition as arithmetic (`resident_section.rs:474-478`):

> *"The directive's measurement of a resident passage is this table: between the graph launch and the terminal synchronize the serial chart issues no launch and reads nothing, so `deed_launches` moves by one, `synchronizations` by one, and `captured_launches` … by zero. Section egress moves once, at the declared receiver."*

`section_read_outs` is documented at `resident_section.rs:494-495` as *"How many times a section crossed to the serial chart as a semantic standing."* `read_out` is documented at `surface_mount.rs:387-388` as *"**The terminal receiver's copy.** The one place a section crosses to the serial chart, and it is counted as such."*

The corresponding AGENTS.md clauses:

- `AGENTS.md:763-765`: *"The GPU is the primary resident workhorse. The CPU handles process/apparatus boundaries, durable rest/I/O, narrow exterior codecs, and offline admission audits; **it does not own the hot deed, semantic phase selection, or a fallback implementation.**"*
- `AGENTS.md:771-772`: *"An admitted device hot path must return exact local/delta testimony and must not replay a full host algorithm after every device deed."*
- `AGENTS.md:766-768` (no-float): *"No floating-point operation exists in the production semantic/device-core dependency cone. A float may not determine control flow, index, coefficient, topology, identity, or any integer/bit later committed in a delta even if the float itself disappears before commit."*
- `AGENTS.md:426-429`: *"the strongest lawful resident surface owns the hot deed and returns exact local/delta testimony. On this hardware that surface is the GPU; CUDA is an apparatus chart, not an ontology, and refusal may not fall back to a host semantic replay."*
- `AGENTS.md:330-337`, Brandon 2026-09-03: *"Certifying and reading every operation to the host is not the apparatus's discipline; it is an injection (the renamed instruction loop refused on 2026-08-18)…"*

### A.2 What the session does

| Contract requirement | Session behaviour | Citation |
|---|---|---|
| The passage is **bound whole before launch**; the diagram's bonds are the graph's edges | Every primitive opens a **one-occurrence** passage: `begin_passage(&[vec![]])`. The graph is memset + 1 kernel + 1 census = 3 nodes, 2 edges. There is no diagram in the graph; the diagram is the host `match` in `enact_operation` | `full_operation.rs:592, 679, 727, 835, 888, 936, 996, 1044, 1087, 1144, 1214, 1278`; the host dispatch at `full_operation.rs:345-411` |
| **Launched once, synchronized once** per deed | `ResidentPassage::launch` does `cuGraphLaunch` + `cuStreamSynchronize` + census `cuMemcpyDtoH` — and it is called once **per operation** | `resident_section.rs:1418-1432`; call sites `full_operation.rs:596, 690, 731, 847, 892, 940, 1004, 1048, 1096, 1148, 1221, 1290` |
| **`section_read_outs` moves once**, at the declared receiver; *"zero intermediate D→H section transfers"* | 22 `read_out` call sites; 20 of them are intermediate. Every `execute_*` ends `let intervals = surface.read_out(&successor)?` unconditionally | see §A.3 |
| *"No operation returns a host `Vec<Rat>`"* | Every operation returns `OperationOutcome { …, intervals: Vec<(i64,i64)>, … }` and every step returns `NativeFullOperationEmission { …, intervals: Vec<(i64,i64)> }`. The type is `(i64,i64)` rather than `Rat`, but it is the complete semantic section in host memory between two semantic operations — the exact object the contract's §0 diagram forbade | `full_operation.rs:100-103, 44-52` |
| *"the CPU … does not own … semantic phase selection"* | The successor projection — whether the carrier advances as an enclosure or as a midpoint point-carrier — is decided by a host scan of the copied intervals | `full_operation.rs:568-618`, quoted below |
| *"return one front/deed delta instead of per-kernel host consultation"* | The next operation's admitted octave bound is `slot.max_octave` read from the census after every single operation; there is no a-priori output-octave law in this session | `operative_scalars.rs:107-124` |

### A.3 Every `read_out` call site, and what each is for

```
full_operation.rs:598    project_successor — reads the collapsed successor to assert lo == hi
full_operation.rs:692    execute_lookup       -> OperationOutcome.intervals
full_operation.rs:733    execute_reshape      -> OperationOutcome.intervals
full_operation.rs:787    execute_contract     -> OperationOutcome.intervals
full_operation.rs:849    execute_rms          -> OperationOutcome.intervals
full_operation.rs:894    execute_tanh         -> OperationOutcome.intervals
full_operation.rs:942    execute_gelu         -> OperationOutcome.intervals
full_operation.rs:1006   execute_binary       -> OperationOutcome.intervals
full_operation.rs:1050   execute_scale        -> OperationOutcome.intervals
full_operation.rs:1099   execute_coefficient_scale
full_operation.rs:1150   execute_select
full_operation.rs:1223   execute_contact
full_operation.rs:1292   execute_chronology
full_operation.rs:1338   carrier_intervals    — LEGITIMATE terminal-face read (driver-called)
full_operation.rs:1352   carrier_intervals    — LEGITIMATE, tiled terminal face
operative_terminal.rs:193  execute_tiled_boundary, per tile (32 tiles)
operative_terminal.rs:274  execute_tiled_unary,  per tile (32 tiles × 4 operations)
operative_backward.rs:194  support_of — nonzero_coordinates + widest_interval of a differential
operative_backward.rs:349  return_through(Lookup) — nonzero_coordinates of the embedding differential
operative_intervention.rs:488  tiled_last_row — the terminal row of a tiled carrier
operative_intervention.rs:606  record_site_support — the differential, per contraction population
operative_intervention.rs:615  record_site_support — the forward output, per contraction population
```

Only `full_operation.rs:1338/1352` (`carrier_intervals`) is the terminal-receiver read the contract admits.

### A.4 The successor projection is decided on the host

`crates/holonic-engine/src/holonic_intelligence/full_operation.rs:568-618`:

```rust
    pub(super) fn project_successor(
        &self,
        operation: u32,
        outcome: OperationOutcome<'chart>,
    ) -> Result<(OperationOutcome<'chart>, NativeSuccessorProjection), NativeFullOperationError>
    {
        let nonpoint_coordinates = outcome
            .intervals
            .iter()
            .filter(|(lower, upper)| lower != upper)
            .count();
        if nonpoint_coordinates == 0 {
            return Ok((outcome, NativeSuccessorProjection::Exact));
        }
        let widest_interval = outcome
            .intervals
            .iter()
            .map(|(lower, upper)| lower.abs_diff(*upper))
            .max()
            .unwrap_or(0);
        let surface = self.residence.surface();
        let shape =
            surface.shape_collapse_control(outcome.rows, outcome.width, outcome.bound_octaves)?;
        let successor = surface.fresh_section(outcome.rows, outcome.width, outcome.grain)?;
        let mut builder = surface.begin_passage(&[vec![]])?;
        let lane = builder.open(0, &[])?;
        surface.record_collapse_control(&lane, &outcome.section, &successor)?;
        builder.close(0, &successor, shape.needed)?;
        let reading = builder.finish()?.launch()?;
        let bound_octaves = operation_bound(operation, &reading)?;
        let intervals = surface.read_out(&successor)?;
        if intervals.iter().any(|(lower, upper)| lower != upper) {
            return Err(NativeFullOperationError::Projection);
        }
```

Three separate contract violations in one function:

1. **The branch is host-decided.** `nonpoint_coordinates == 0` is computed by a host scan of a host copy of the device section. This is "semantic phase selection" on the CPU (`AGENTS.md:763-765`).
2. **The two numbers scanned are already device words.** `SlotReading` (`resident_section.rs:997-1017`) carries `max_width` and `nonzero_widths`, and the kernel's own header documents them (`exact_resident_section.cu:1253-1256`): *"`SLOT_WIDTH [6..8]` max over coordinates of `hi - lo` … `SLOT_WIDTH_SUM` add over coordinates of the same width … `SLOT_NONZERO_WIDTHS` add over coordinates of `width != 0`"*. `nonpoint_coordinates` **is** `slot.nonzero_widths`; `widest_interval` **is** `slot.max_width`. Both arrive in the 64-octet census the `launch()` already read. The section copy adds nothing.
3. **It uses the kernel the tree labels unsound as a control.** `record_collapse_control` (`surface_passage.rs:860-883`) records `section_collapse_control`, whose kernel comment is (`exact_resident_section.cu:1214-1215`): *"**A CONTROL, and it is unsound by construction**: every enclosure collapsed to its lower midpoint, the widths dropped. It exists so a driver can show that the propagated remainder is load-bearing."* The declared chart is `MidpointQuotient` / `SealedMidpointQuotient` (`resident_law.rs:437, 557`), and `resident_law.rs:429-435` says so explicitly: *"It is NOT `CollapseControl`, which is the same arithmetic offered as an unsound control at one site; this one is the declared chart of the whole passage and its entailment requires the declaration."*

The on-card fused form exists and is used elsewhere in the same session. `record_midpoint_seal` (`surface_passage.rs:932-960`) + `close_fused` (`resident_section.rs:1267-1280`) record the collapse **and** its census as **one graph node inside the passage**, with no readout and no second passage. `operative_backward.rs:273-278` and `operative_return.rs:231-233, 475-477, 489-491` use exactly that. The kernel documents the fusion as lawful (`exact_resident_section.cu:1414-1432`), including *"the census of a collapsed section measures `lo == hi`, so every width is zero"* — which is why the host re-check at `full_operation.rs:600` is redundant as well.

So the forward path and the backward path in the same file tree do the same arithmetic two different ways: the backward path conformantly (fused, on card, no readout), the forward path as a host branch + second passage + second full readout. SKE1's record claims they are the same (`2026-09-03_SKE1_…:20-21`: *"Every returned differential is sealed to its midpoint under its own census, the declared successor projection the forward already uses"*). Arithmetically yes; as apparatus, no.

### A.5 Passage and readout count for one 1,275-operation cycle

`advance_cycle` (`full_operation.rs:519-566`) runs operations `0 .. len-5` through `advance` → `enact_operation` → `project_successor`, then `advance_terminal`.

Body (1,270 operations): 1 passage + 1 `read_out` each, plus 1 passage + 1 `read_out` for each operation whose kernel widens (`project_successor`). Lookups and carries return point intervals (`2026-09-02_HNA2_…:19`: *"All 5,120 returned coordinates were exact point intervals"*); contractions, RMS, GELU, tanh, contact, chronology and irrational scales do not (HNA2:26 records 21,504 coordinates of which 20,122 point — 1,382 nonpoint, so the projection fires).

Terminal (5 operations): the tied boundary is 262,144 rows over an 8,192-row aligned aperture = **32 tiles**, and each of the five terminal nodes iterates the tiles (`operative_terminal.rs:176-206` and `:243-292`). That is 32 passages + 32 readouts per terminal node, ×5, plus projections.

```
passages per cycle   = 1,270 + nonpoint(≈600) + 160 + terminal-nonpoint(≈100)  ≈ 2,100
section_read_outs    = the same, ≈ 2,100
deed_launches        = the same, ≈ 2,100
synchronizations     = the same, ≈ 2,100
captured_launches    = 2 per passage (kernel + census)  ≈ 4,200
allocations          = ≥ 4 per passage (2 section + census + lineage) ≈ 8,400
```

Against the contract's pass condition (`deed_launches += 1`, `synchronizations += 1`, `section egress once`, asserted as a test at `resident_section/tests_core.rs:503-517` including *"the deed itself reads no section"*), and against the two conformant measurements in the record:

- `2026-08-19_THE_LAYER_IS_ONE_GRAPH_LAUNCHED_ONCE_…:176-179` — a 35-operation layer-zero deed: *"deed launches 0→1 · captured launches 70→70 · synchronizations 0→1 · receipt egress 0→1,152 octets · **section egress 0→0 · section read-outs 0→0** · ingress unchanged / the terminal read afterwards: section egress 0→81,920 · read-outs 0→1"*, and *"Nothing was launched between the graph and its terminal synchronize; that is what the census measures and what a renamed dispatch loop could not pass."*
- `2026-08-19_THE_TOWER_CONDUCTS_LAYER_BY_LAYER_…:88, 94` — the whole 42-layer Gemma tower: *"each layer one graph launched once … PASS — 5 inputs, **43 deed launches each**"*, *"captured launches 5,514 · 43 launches · 43 synchronizations"*.

The same 42-layer body, on the same card, with the same kernels: **43 launches then; ≈2,100 now.**

### A.6 No measured `section_read_outs` exists for this session

I searched every record, blueprint and receipt. The only measured values in the tree are `1` (08-18, the convicted form), `0→0` then `0→1` (08-19, the conformant form). The SKE2 and SKE3 receipts (`research/records/2026-09-03_SKE2_receipts/*.json`, `…SKE3_receipts/*.json`) carry no census field at all. `NativeFullOperationTrace` does carry `census_before`/`census_after` per operation (`full_operation.rs:66-67`), so the number is available and has never been reported. The blueprint's *"`TransferCensus.section_read_outs` measures it at about 1,275 per cycle"* (`blueprint/THE_SOULKILLER_…:59-60`) is a source-derived estimate, not a measurement, and it is low by ~40 %.

### A.7 The structural gate does not catch this — exactly as the 08-18 audit predicted

`production_cone_reaches_the_reference` (`resident_section.rs:1503-1524`) greps for eight forbidden tokens: `ported_reference`, `PortedOperationKind`, `PortedCarrier`, `PortedProgram`, `ported_reference::realize`, `fn enact(`, `impl EnactsInOrder`, `cuCtxSynchronize`. The session's host dispatch is spelled `fn enact_operation(` — not `fn enact(` — and it synchronizes through `Stream::synchronize` (`cuStreamSynchronize`), not `cuCtxSynchronize`. It passes the gate. The owner's own doc-comment anticipated this (`resident_section.rs:1500-1502`): *"The behavioural half is the census: between a graph launch and its terminal synchronize the surface issues no launch, which a renamed loop cannot pass."* The behavioural half was never run against this session.

**A. Conclusion: the session is the renamed instruction loop, in the strict sense the contract defined it — a host `match` selecting one device operation at a time, with a global synchronize and a host consultation between every pair. It is a strictly worse instance than the one convicted on 2026-08-18, because the host consultation is now the whole section rather than a 32-octet receipt, and because the CPU takes a semantic decision (Exact vs Midpoint) from it.**

---

## B. Where the per-operation exact trace and readout came from

### B.1 What Brandon asked

**2026-08-18** — one sentence, quoted verbatim once in the whole tree (`2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD…:22-24`):

> *"the GPU should not be 'used more'; the continuing semantic section must remain owned by the GPU surface. That distinction is what prevents another round of adding CUDA leaves to a CPU machine."*

Nothing about intervals, enclosures, per-coordinate certification, traces, or readouts.

**2026-09-02** — as the HNA blueprint itself records its authority (`blueprint/THE_HOLONIC_NEURAL_ATHENA_…:6-8`):

> *"**Authority:** Brandon's direct correction of 2026-09-02: an operation's consequence is the successor used by the next inference cycle; an exterior response is only another occurrence, not a privileged learning return. The roadmap alone orders the implementation."*

That correction is about **what counts as the consequence of an operation** (the successor ecology, not a second `ReturnedConsequence`/`WorldReturn` event). It is a refutation of a privileged return type. It says nothing about a per-operation host artefact.

### B.2 What the assistant rendered

The triple appears one paragraph later, in the assistant's own formalization (`blueprint/THE_HOLONIC_NEURAL_ATHENA_…:24-26`):

> *"`E_t` is the complete contemporary ecology. `o_t` is the occurrence presented at that step. **The operation returns an emission, an exact trace, and `E_(t+1)`.** The next operation uses `E_(t+1)`. That joining equality is the inference loop."*

and is fixed as an ABI at `:180-185`:

```
Found(Ecology)
Operation { occurrence }
Successor { emission, trace, ecology }
```

The word "trace" here is the Lean-shaped `OperationStep.trace` field of `:48-56` — a *type slot in a formal object*, whose only obligation in the pass conditions is bookkeeping: HNA2's pass condition (`:296-300`) asks that *"chronology and lineage advance even when a selected receiver face is equal"*; HNA3's (`:315-319`) asks that *"a bounded multi-step recurrence … returns every step's occurrence, current, reaction, emission, lineage, and successor"*. Nothing in either requires the trace to contain a copy of the carrier.

The doctrine clause was then written back into `AGENTS.md:590-591`: *"The productive model is the recurrent operation from occurrence and contemporary ecology to emission, exact trace, and successor ecology."*

### B.3 How the formal slot became a device→host copy

Three steps, all in the implementation:

1. **`NativeFullOperationEmission` was given a host-materialized body.** `full_operation.rs:44-52` declares `intervals: Vec<(i64,i64)>` on the emission of *every* operation, not only the terminal one. Since `advance` returns an emission per operation, `read_out` per operation follows by type.
2. **`OperationOutcome` was given the same field.** `full_operation.rs:96-107` — so `enact_operation` (used by the forward cycle **and** by the adjoint's segment replay, `operative_backward.rs:238`) cannot return without a readout.
3. **`project_successor` was written against `outcome.intervals` rather than against the census.** This is the step that turned a reporting artefact into a load-bearing dependency: after `full_operation.rs:568`, the readout cannot be removed without also moving the projection decision.

The consumers confirm the readout was never needed by the recurrence. The application uses only the final emission (`applications/athena-alpha/src/recurrent_operator.rs:142-150, 266-275`); `advance_cycle` drops every intermediate emission and keeps only `step.trace` (`full_operation.rs:539-541`). The per-operation `intervals` are consumed only by three HNA falsifier drivers (`examples/advance_full_native_operator_hna2.rs:47-49, 70-72, 89`; `complete_full_native_recurrence_hna3.rs:85-86`; `recurrent_native_operator_hna2_hna3.rs:77-111`) — one-off checks that "two occurrences differ" and "the emission equals the successor's carrier face."

### B.4 The records then made claims *out of* the injected readout

- `2026-09-02_HNA2_…:19-20`: *"All 5,120 returned coordinates were exact point intervals and the two native carrier rows differed before an application codec or receiver selected anything."*
- `2026-09-02_HNA2_…:25-26`: *"The contraction returned 21,504 coordinates, including 20,122 point intervals."*
- `2026-09-02_HNA2_…:29-30`: *"The contraction crossed as one resident deed and one resident synchronization"* — true of the operation, and precisely the sentence that reads as compliance while the deed count is per-operation.
- `2026-09-02_HNA3_…:13-14`: *"Every node returns its own emission and trace, and the five traces join exactly from generation 1,270 through 1,275."*

These are coordinate-grain statements derived from droplet tracing — the second half of Brandon's 2026-09-03 ruling (`AGENTS.md:330-337`).

**B. Conclusion: Brandon asked for one thing on 08-18 (the GPU owns the continuing section) and one thing on 09-02 (the successor ecology *is* the consequence). Neither asks for a per-operation trace, and neither asks for a readout. The assistant rendered "trace" as a formal field, then rendered the formal field as a host copy of the carrier, then made the projection depend on that copy.**

---

## C. What the census already measures, what a conformant reading would be, and the real obstructions

### C.1 The census already returns everything the host scan computes

`SlotReading` (`resident_section.rs:997-1017`), 16 words per occurrence, read once per passage as `egress_receipt_octets`:

```rust
pub struct SlotReading {
    pub refused: u32,  pub reach: u32,  pub written: bool,  pub inverted: bool,
    pub max_octave: u32,          pub bound_violated: bool,
    pub max_width: u64,           //  == project_successor's `widest_interval`
    pub upstream_flags: u32,  pub upstream_first: Option<usize>,  pub upstream_count: u32,
    pub lineage_inspected: u32,
    pub width_sum: u64,           //  the collapsed population, on card
    pub nonzero_widths: u32,      //  == project_successor's `nonpoint_coordinates`
}
```

Correspondences the source makes exact:

| host computation | device word already read | citations |
|---|---|---|
| `project_successor`'s `nonpoint_coordinates` | `slot.nonzero_widths` | `full_operation.rs:574-578` vs `exact_resident_section.cu:1256, 1367, 1398` |
| `project_successor`'s `widest_interval` | `slot.max_width` | `full_operation.rs:580-584` vs `exact_resident_section.cu:1254` |
| `combine_projections` summing and maxing across 32 tiles | the same words summed/maxed across 32 slots of one passage | `operative_terminal.rs:375-395` |
| `support_of`'s `widest_interval` | `slot.max_width` | `operative_backward.rs:194-203`, `operative_adjoint.rs:201` |
| `operation_bound`'s next-operation bound | `slot.max_octave` — already census-only, no readout | `operative_scalars.rs:115-124` |

The one quantity **not** in the census is `differential_support`'s `nonzero_coordinates` — a count of nonzero *values*, not nonzero widths (`operative_adjoint.rs:191-200`). That is a genuine gap of one commutative census word, not a reason to copy the section.

### C.2 A conformant reading

Per cycle, crossing to the host:

- **the census**, once per passage: `SLOT_WORDS × occurrences × 4` octets. For a whole layer of ~30 occurrences that is 1,920 octets — against the ~30 MB of section the same layer currently copies at 14 rows.
- **the terminal face**, once: `carrier_intervals` (`full_operation.rs:1333-1354`), which is already the contract's admitted receiver (*"The terminal face copied out once"*).
- **the row-mass fold** of each aligned tile — see C.4, an unremoved crossing the census does not count.

`section_read_outs` would be **1** per cycle, matching `2026-08-19_…LAUNCHED_ONCE…:179` and the SKE4 pass condition already written into the blueprint (`blueprint/THE_SOULKILLER_…:264`).

### C.3 A passage can already capture many operations — the session proves it in its own file

`begin_passage(lineage: &[Vec<usize>])` takes an arbitrary occurrence population; `open(index, producers)` places a graph edge per declared predecessor; the schedule control (`Schedule::CoPresent` / `Serialized`) is the interchange falsifier (`surface_passage.rs:14-99`, `resident_section.rs:1090-1101, 1170-1230`). The session already uses it:

- `operative_return.rs:630-690`, `contract_tile_with_overlay`, builds a `1 + 2·count`-occurrence lineage with re-entry joins, and its own doc says the method (`operative_return.rs:627-630`): *"One tile of a contraction beside its overlay atoms, in one passage: the base contraction, one contribution per atom, and the re-entry joins in deposit order. **Every shape and section is founded before the capture opens and every section stays alive until the launch returns.**"*
- `operative_return.rs:453` binds `&[vec![], vec![0], vec![], vec![2]]`; `operative_backward.rs:943` binds three occurrences.

So neither the builder, nor multi-occurrence lineage, nor pre-capture allocation is an obstruction. Allocation before capture is the established pattern; `2026-08-19_…LAUNCHED_ONCE…:170` prices a 35-operation layer at *"allocations 73"* bound in *"0.017 s"*.

### C.4 The real obstructions, with citations

**Obstruction 1 (hard, and it is the reason a contraction is its own passage): the single alignment slot.**

`operative_residence.rs:581-583`:

> *"Align one complete-row tile under the population's device-derived complete frame. **The mutable borrow makes the single alignment pool exclusive until the returned tile is dropped.**"*

Enforced in the type system (`operative_residence.rs:108-114`):

```rust
pub struct NativeAlignedOperatorTile<'residence, 'chart> {
    …
    _exclusive_pool: PhantomData<&'residence mut NativeOperatorResidence<'chart>>,
}
```

and in the addresses: every `align_tile` writes to the one fixed address `self.pool.device_ptr() + self.aligned_offset` (`operative_residence.rs:620-624`; the pool has exactly one `aligned_offset`, `operative_residence.rs:699-753`). Two live tiles would alias. This is an HNA1 memory decision, stated as measured in the blueprint (`blueprint/THE_HOLONIC_NEURAL_ATHENA_…:256-262`): *"The card admitted one 8,192-row aligned slot… together with every packed coefficient the live charge is 15,752,729,188 octets… **A second alignment slot is not admitted.**"* HNA3 names the same limit at the boundary (`2026-09-02_HNA3_THE_COMPLETE_42_LAYER_BODY_…:37`): *"The single aligned pool cannot hold the tied matrix at once."*

This is the trade HNA1 made against Station C: Station C mounted a layer's populations together and released them before the next layer (*"Every layer's stored populations are predicted from the header, admitted, mounted, used by one graph and released before the next layer mounts"*, `2026-08-19_THE_TOWER_CONDUCTS…:79-82`); HNA1 bought whole-model BF16 residency and pays for it with one-tile-at-a-time alignment.

**Consequence:** a layer's ~7 contractions and ~5 gain tiles cannot be in one passage. **But** the ~18 non-contraction operations between them (reshape, select, chronology, contact, GELU, tanh, Hadamard, add, algebraic scale, gain-less RMS) need no tile at all — and today each of those is still its own passage with its own readout. A layer decomposes into ~13 segments, not ~30 passages, without touching the pool.

**Obstruction 2 (the one that would still be there after fixing the pool): the session has no a-priori output-octave law.**

`operative_scalars.rs:107-124` takes the successor's admitted bound from the **measured** census of the predecessor:

```rust
fn exact_bound(reading: &PassageReading) -> Result<u32, u32> {
    if !reading.obstruction.is_empty() { return Err(reading.obstruction.joined_flags()); }
    Ok(reading.slots.last().map(|slot| slot.max_octave.max(1)).unwrap_or(1))
}
```

Inside a captured graph nothing is measured before the launch, so every occurrence's admission must be derived a-priori. Chaining the `shape_*` admissions alone will not survive a layer: `shape_rms_rebase`'s `needed` is `max(2·oct + log2(group) + 1, oct + gain + 1)` (`surface_shapes.rs:611-619`) — the *accumulator* bound — and `shape_contract`'s is `input + entry + ceil_log2(inner) + 1` (`surface_tiled.rs:~131`). Composed naively that exceeds the 126-octave carrier (`resident_section.rs:107, surface_mount.rs:141-143`) within two or three operations.

**The missing law already exists in the tree and this session does not use it.** `ResidentLaw::bound_octaves` gives each law a tight a-priori bound on the *value* rather than the accumulator — for the RMS rebase (`resident_law.rs:1680-1700`):

```rust
        // |y_i| ≤ sqrt(group) · |g_i| for a point section, in the word F + log2(group)/2 + gain + 1;
        // for an interval section the root is at most 1/sqrt(eps) < 2^10, so the word is at most
        // oct + 10 + gain. The larger bounds both.
        (f + (i64::from(ceil_log2(self.group)) + 1) / 2 + gain_value.max(0) + 2)
            .max(first(inputs, 0) + 10 + gain_value.max(0) + 1)
```

and `front_passage.rs:1841-1866` propagates it symbolically over the whole diagram before any allocation, which is how Station C bound 68 operations into one graph and still reported *"the a-priori law held … a-priori ≥ measured on every port · widest slack 15 octaves"* (`2026-08-19_…LAUNCHED_ONCE…:181-183`, `…TOWER_CONDUCTS…:88`).

The HNA session's only import from that owner is `resident_law::decimal_to_rat` (`operative_atlas.rs:22`, `operative_morphology.rs:20`). It uses none of the a-priori machinery. **This, not the alignment pool, is the deepest reason the session is per-operation: without a per-primitive value bound it physically cannot admit occurrence *n+1* until occurrence *n* has run and been measured.**

**Obstruction 3 (real but small): the alignment itself is an uncounted host crossing.**

`align_tile` → `mount_bfloat16_pooled_fixed_frame` (`embedding_fiber.rs:1017-1160`) launches two kernels on the **null stream**, does `cuStreamSynchronize`, then three `cuMemcpyDtoH_v2` — the scratch words and the row-mass low/high arrays (`8 × rows` octets each) — and folds `widest` over `rows` on the host. A null-stream synchronize is illegal during capture, so the alignment must sit outside any passage; and none of it is counted by `TransferCensus` (it goes through the readout's own FFI, not the surface). At 8,192 rows that is 131,072 octets per alignment, ×32 for the tied boundary alone.

**Obstruction 4 (none): the successor projection on the card.** `record_midpoint_seal` + `close_fused` already give a fused on-card collapse-and-census node whose entailment the tree has already argued (`exact_resident_section.cu:1411-1435`), and the backward path already uses it (`operative_backward.rs:273-278`). Moving `project_successor` onto the card is a substitution of an existing owner for another existing owner, plus reading `nonzero_widths`/`max_width` from the reading instead of from a copy. No new design is required.

---

## D. Time attribution

### D.1 Measured numbers in the record

From `research/records/2026-09-03_SKE2_receipts/occ0.json` (14-address occurrence, `7 + 5 =`):

```
first_cycle_milliseconds        1,939      one full 1,275-operation cycle
excitation_milliseconds         3,826      the adjoint return (≈ 2× a cycle)
replay_control elapsed_ms       1,821      one counterfactual forward
cone probes elapsed_ms          1,641 – 1,891   (22 of them)
cone elapsed_ms                44,202      the search
elapsed_seconds                 74.135      one occurrence end to end
```

`2026-09-03_SKE1_…:44-52`: first cycle **2.2 s**; return through the body **3.3 s**; second cycle on the deposited body **7.1 s** (control 3.6 s). `2026-09-03_SKE2_…:108`: *"the SKE1 return deed still crosses all 1,271 operations (2.5 s, 343 deposits…)"*. `2026-09-03_SKE2_…:68`: *"one bounded process per occurrence (73 to 79 s, of which about 45 s is the cone search of 22 probes and 3 controls, each a counterfactual forward of 1.2 to 2 s)"*. SKE3 receipts: 55–77 s per exposure × 15 exposures ≈ 16 minutes of card time.

So ≈ **1.5 ms per operation** at 14 rows, and every SKE deed is a multiple of that: an excitation is two cycles (the segment replay at `operative_backward.rs:238` re-runs `enact_operation` **and** `project_successor` for the whole body), a cone search is 25 cycles.

### D.2 Where the 1.5 ms goes, read off the source

Per non-contraction operation the host issues, in order:

| step | CUDA calls | source |
|---|---|---|
| `fresh_section` | 2 × `cuMemAlloc_v2` | `surface_mount.rs:158-166`, `soma/mount/src/cuda.rs:1567-1578` |
| `begin_passage` | `cuCtxSetCurrent`; 2 × `cuMemAlloc_v2` (census, lineage); 2 × `cuStreamCreate` (origin + 1 lane); 2 × `cuEventCreate`; `cuStreamBeginCapture`; memset node; `cuEventRecord` | `surface_passage.rs:33-99`, `cuda.rs:215-224, 407-416, 253-263` |
| `open` / `record_*` / `close` | `cuStreamWaitEvent`; 2 × `cuModuleGetFunction`; 2 × captured `cuLaunchKernel`; `cuEventRecord` | `surface_passage.rs:126-140`, `resident_section.rs:1242-1265` |
| `finish` | `cuStreamWaitEvent`; `cuStreamEndCapture`; **`cuGraphGetNodes` ×2 + `cuGraphGetEdges` + `cuGraphNodeGetType` per node**; **`cuGraphInstantiateWithFlags`** | `resident_section.rs:1282-1320`, `cuda.rs:469-500, 526-534` |
| `launch` | `cuGraphLaunch`; **`cuStreamSynchronize`** (full drain); `cuMemcpyDtoH_v2` of 64 census octets | `resident_section.rs:1418-1432, 1456-1490` |
| `read_out` | `cuCtxSetCurrent`; **2 × blocking `cuMemcpyDtoH_v2` of the whole carrier into pageable `Vec`s** | `surface_mount.rs:389-404`, `cuda.rs:1668-1677` |
| host projection | 2 full passes over the copied tuples (`filter().count()`, `map().max()`) | `full_operation.rs:574-584` |
| if nonpoint | the whole block again with `record_collapse_control` | `full_operation.rs:586-598` |
| drop | `cuGraphExecDestroy`, `cuGraphDestroy`, 2 × `cuStreamDestroy`, 2 × `cuEventDestroy`, ≥4 × `cuMemFree` | destructors |

Per contraction, additionally: `cuMemcpyHtoD` (16 B seed), 2 × `cuLaunchKernel` on the **null stream** over the whole tile, `cuStreamSynchronize`, 3 × `cuMemcpyDtoH_v2` including `2 × 8 × rows` octets of row mass, and a host fold over `rows` (`embedding_fiber.rs:1044-1160`).

Order-of-magnitude budget for ≈2,100 passages/cycle, from the call counts alone:

- **`cuGraphInstantiateWithFlags` ≈ 2,100 times** for a 3-node graph — a per-passage cost that a captured segment pays once and can then relaunch. Typically tens of µs each: **tens to >100 ms/cycle, entirely avoidable.**
- **≈8,400 `cuMemAlloc_v2` + ≈8,400 `cuMemFree`** — the driver's allocator is a serializing call: **~100–350 ms/cycle.**
- **≈4,200 stream creates + 4,200 event creates** (plus destroys) — **~50–130 ms/cycle**, all of it avoidable by binding once per segment.
- **≈2,100 `cuStreamSynchronize`** — the structural cost is not the call, it is that the card idles between every operation while the host scans intervals. There is no overlap anywhere in a cycle.
- **Section egress**: at 14 rows the body copies ≈0.5–2.4 MB per operation and the terminal five copy `14 × 262,144 × 16 = 58.7 MB` **each** (`operative_terminal.rs:193, 274` per tile, then `stitch_intervals` at `:352-373` concatenating 3.67 M tuples into one fresh host `Vec` per terminal node). Total ≈**1.5 GB/cycle** of blocking pageable D→H, ≈150 ms of pure copy plus per-call latency.
- **Host scanning**: `project_successor` walks up to 3.67 M tuples twice per terminal node, single-threaded.
- **Not avoidable, and the floor SKE4 names**: the exact `i128` contractions (~50 G MAC/cycle at 14 rows) and the BF16→i64 alignment traffic (the whole 15.0 GB coefficient store re-expanded to i64 once per cycle through a 168 MB pool ≈ 75 GB of device traffic). The blueprint's own target is *"a cycle costs what the tiled contraction costs"* (`blueprint/THE_SOULKILLER_…:264-265`).

I cannot apportion these without a profile, and none exists in the record for this session. What the source establishes without measurement is that **every one of the avoidable items scales with the passage count, and the passage count is ≈50× what the same body cost under the contract** (2,100 vs 43).

### D.3 The 2^35 divergence and how the projection answered it

`2026-08-19_THE_TOWER_CONDUCTS_LAYER_BY_LAYER_AND_THE_CERTIFIED_ENCLOSURE_DIVERGES_AT_TWO_TO_THE_THIRTY_FIVE_PER_LAYER.md:36-58` (Station C, Claude Fable 5):

> *"the certified interval enclosure of the *composed* tower diverges: at grain `2^-48` layer 0's widest certified enclosure is `1.904e-4` against the entering grain `3.553e-15` — an amplification of **≈ 2^35.6 per layer**, measured … inside layer 1 the word refuses by name (`CarrierLeft` at the gated-passage Hadamard, the lineage carrying it to every successor) … **No grain and no word carries a certified enclosure of the exact function through two layers.**"*
>
> *"What carries the tower is a **declared quotient chart**: after every occurrence whose enclosure can widen, a `MidpointQuotient` occurrence — quotient species, entailed by its declaration, visible in the diagram — collapses the enclosure to its midpoint for the successors, while the enclosure stays resident in the predecessor's own section as the complete per-entry residual and its collapsed population (widest, summed and nonzero widths) **is censused on the card**."*

Station A/B/C/D are the 2026-08-19 sequence (`…THE_REFUSAL_TRAVELS_ALONG_THE_LINEAGE…`, `…THE_SOURCE_IS_ADMITTED_WHOLE…`, the above, `…THE_SOURCE_IS_DISSECTED_BY_INTERVENTION…`).

The HNA session hit the identical wall at the identical operation and answered it differently (`2026-09-02_HNA3_THE_COMPLETE_42_LAYER_BODY_ADVANCED_TO_THE_TIED_BOUNDARY.md:22-27`):

> *"Direct propagation of every certified interval exhausted the resident word at layer one's gated Hadamard passage, returning refusal flag `0x1`. This is the already-known enclosure amplification, not a missing neural operation. The full session now declares the midpoint receiver projection at each open successor: exact outputs pass unchanged; an open interval returns its nonpoint/widest-width census and its midpoint point-carrier advances. No application status or expected output selects the projection."*

The last sentence is true and is not the issue. The regression is that Station C's answer is **an occurrence inside the graph** whose collapsed population *"is censused on the card"*, and the HNA answer is **a host branch on a host copy**, dispatched to the kernel Station C's own law explicitly disclaims (`resident_law.rs:429-435`). Same arithmetic, opposite apparatus.

### D.4 Was the per-coordinate certified enclosure Brandon's requirement?

**No — it is an apparatus choice by the assistant, and the tree says so.**

- The carrier is introduced in §4 of the contract (`2026-08-18_THE_SECTION_MUST_STAY…:165-167`): *"A `ResidentSection { rows, width, grain }` is an opaque device handle: two `i64` arrays `lo, hi` at one declared dyadic grain `2^{-F}`, so every coordinate is a certified interval."* — and the document's own grade line (`:10`) reads: *"**proposal** for the contract itself, which schedules nothing until the roadmap's named gate returns."* Brandon's contribution to that document is the single sentence at `:22-24`.
- The owner classes the grain and the series aperture as apertures, not law (`resident_section.rs:41-43`): *"`F` and the series aperture ([`SeriesAperture`]) are apparatus apertures the caller declares, and their falsifier is nesting."*
- The `MidpointQuotient` doc calls it *"a quotient **forced by the carrier**"* (`resident_law.rs:430-432`) — i.e. forced by an apparatus choice.
- The standing canon requirement is exactness of arithmetic, not per-coordinate enclosure: `AGENTS.md:766-768` (no-float) and `AGENTS.md:771` (exact local/delta testimony). An exact dyadic point arithmetic with a *group-characteristic* remainder — Brandon's 2026-09-03 grain (`AGENTS.md:330-337`) — satisfies both.

So the chain is: assistant chooses per-coordinate interval enclosures → the composition provably diverges at 2^35.6/layer → the assistant must collapse after every widening occurrence → the HNA session implements the collapse as a host decision → the host decision requires the whole section on the host → the readout becomes structural. Each step follows from the previous; the first step was never asked for.

---

## E. Where the claim as stated is imprecise

1. **"each of the ~1,275 operations… as its own CUDA-graph passage" — an undercount.** The 1,270 body operations are one passage each *plus a second* whenever the operation widens (`full_operation.rs:586-598`), and the terminal five are **32 passages each** (`operative_terminal.rs:176-206, 243-292`), because the tied `262,144 × 2,560` boundary is tiled against the 8,192-row aperture. A cycle is ≈2,100 passages, not ≈1,275.

2. **"`section_read_outs` measures it at about 1,275 per cycle" — never measured, and low.** No record and no receipt in the tree reports a `section_read_outs` for this session; the per-operation `census_before`/`census_after` are carried in the trace (`full_operation.rs:66-67`) and have never been aggregated. The source-derived figure is ≈2,100.

3. **"a full host readout of the carrier" — true, and there is a second class of host crossing the claim omits.** `align_tile` synchronizes the null stream and copies the row-mass arrays to the host on every contraction (`embedding_fiber.rs:1122-1150`), and `TransferCensus` does not count any of it. A conformant session still owes this crossing unless the mass fold moves onto the card.

4. **"decides the midpoint successor projection on the host" — true, and worse than stated.** It also (a) uses the kernel the tree labels *"unsound by construction"* as a control rather than the declared `MidpointQuotient`/`SealedMidpointQuotient` law, and (b) re-reads the collapsed section a second time to assert `lo == hi` (`full_operation.rs:598-601`), a property the fused kernel's own entailment argument already establishes (`exact_resident_section.cu:1428-1431`).

5. **Where the claim is too harsh — the successor projection is not an authored governor.** HNA3's disclaimer holds on inspection: nothing in `project_successor` consults an application status, an expected answer, or a receiver verdict; the branch is `lower != upper` and nothing else. The violation is of the *apparatus* contract (host ownership of the hot deed), not of the purity/jurisdiction bans.

6. **Where the claim is too harsh — this is not the *same* loop as 08-18.** The 08-18 form selected the *semantic variant* from a receipt word between kernels (audit `:83-85`). The HNA form fixes the operation order from the ecology graph in advance (`full_operation.rs:519-566`); the host decides *the projection*, not *which operation runs next*. That difference is real and worth stating precisely — but it does not save the grade, because the contract's own falsifier is behavioural, not semantic: *"between the graph launch and the terminal synchronize the serial chart issues nothing — `TransferCensus` counts it"* (`resident_section.rs:23-27`). By that measure the session fails ≈2,100 times per cycle.

7. **Two further consequences the claim does not name.**
   - The **adjoint return replays the whole forward body through the same path** (`operative_backward.rs:238-241`: `enact_operation` then `project_successor`), so every SKE1/SKE2/SKE3 excitation pays the cost twice, which is exactly the measured `first_cycle 1,939 ms` vs `excitation 3,826 ms`.
   - The **dissection reads two full sections per contraction population** (`operative_intervention.rs:606, 615` in `record_site_support`) — the differential and the forward output — for all 344 populations, and derives `support`, `magnitudes` and `contributions` per coordinate on the host (`operative_intervention.rs:343-377`). That is the coordinate-grain instrument Brandon's 2026-09-03 ruling withdrew (`AGENTS.md:330-337`), and it is the same injection expressed as measurement rather than as apparatus.

---

## Files of record

- `/home/b/Workspaces/holonics/research/records/2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md`
- `/home/b/Workspaces/holonics/research/records/2026-08-18_THE_SECTION_STAYED_BUT_THE_HOST_STILL_OWNED_THE_PASSAGE_AND_NO_PHOENIX_STATION_PASSED.md`
- `/home/b/Workspaces/holonics/research/records/2026-08-19_THE_LAYER_IS_ONE_GRAPH_LAUNCHED_ONCE_AND_THE_IMMEDIATE_GATE_RETURNS_ITS_FALSIFIERS_WITH_THE_RATCHET_OPEN.md`
- `/home/b/Workspaces/holonics/research/records/2026-08-19_THE_TOWER_CONDUCTS_LAYER_BY_LAYER_AND_THE_CERTIFIED_ENCLOSURE_DIVERGES_AT_TWO_TO_THE_THIRTY_FIVE_PER_LAYER.md`
- `/home/b/Workspaces/holonics/research/records/2026-09-02_HNA3_THE_COMPLETE_42_LAYER_BODY_ADVANCED_TO_THE_TIED_BOUNDARY.md`
- `/home/b/Workspaces/holonics/research/records/2026-09-03_SKE2_receipts/occ0.json`
- `/home/b/Workspaces/holonics/blueprint/THE_HOLONIC_NEURAL_ATHENA_IS_ONE_RECURRENT_ECOLOGY_AND_EVERY_OPERATION_ADVANCES_IT.md`
- `/home/b/Workspaces/holonics/blueprint/THE_SOULKILLER_EXCITES_THE_RESIDENT_REALIZATION_AND_RETURNS_THE_RECEIVER_FAMILY_QUOTIENT_AS_CONE_RESTRICTED_ECOLOGIES.md`
- `/home/b/Workspaces/holonics/AGENTS.md` (§Purity boundary 306–348, §Apparatus 757–776, retraction record 170–175, 426–429)
- `/home/b/Workspaces/holonics/crates/holonic-engine/src/resident_section.rs`
- `/home/b/Workspaces/holonics/crates/holonic-engine/src/resident_section/{surface_passage.rs,surface_mount.rs,surface_tiled.rs,surface_shapes.rs,tests_core.rs}`
- `/home/b/Workspaces/holonics/crates/holonic-engine/src/{resident_law.rs,front_passage.rs,embedding_fiber.rs}`
- `/home/b/Workspaces/holonics/crates/holonic-engine/kernels/exact_resident_section.cu`
- `/home/b/Workspaces/holonics/crates/holonic-engine/src/holonic_intelligence/{full_operation.rs,operative_terminal.rs,operative_backward.rs,operative_intervention.rs,operative_adjoint.rs,operative_return.rs,operative_scalars.rs,operative_residence.rs,operative_atlas.rs}`
- `/home/b/Workspaces/holonics/soma/mount/src/cuda.rs`


