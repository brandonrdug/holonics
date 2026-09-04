# Holonic Neural Athena is one recurrent ecology and every operation advances it

**Date:** 2026-09-02
**Status:** COMPLETED. `HNA0--HNA5` passed at their bounded scopes.
**Campaign:** `HNA0--HNA5`.
**Authority:** Brandon's direct correction of 2026-09-02: an operation's consequence is the
successor used by the next inference cycle; an exterior response is only another occurrence, not a
privileged learning return. The roadmap alone orders the implementation.
**Retraction:** This contract replaces
`THE_HOLONIC_NEURAL_ATHENA_VARIANT_RETURNS_QUALITATIVE_CIRCULATION_AND_REAL_WORLD_CULTIVATION.md`
and withdraws its `HNA0--HNA5` grades and its world-verdict/commit construction.

---

## 0. The correction

[definition] A Holonic Neural Athena run is one recurrent sequence of operations on one continuing
ecology:

```text
E_0 --o_0--> E_1 --o_1--> E_2 --o_2--> ...
```

`E_t` is the complete contemporary ecology. `o_t` is the occurrence presented at that step. The
operation returns an emission, an exact trace, and `E_(t+1)`. The next operation uses `E_(t+1)`.
That joining equality is the inference loop.

[definition] No second event called a `ReturnedConsequence`, `WorldReturn`, `CultivationReturn`, or
`ReconstructionReturn` is required to make the step causal. A compiler response, theorem-kernel
diagnostic, sensor reading, user message, tool result, or application-decoded emission may become a
later `o_t`; it enters through the same occurrence port as any other material. Its provenance may be
recorded by an application receiver, but it receives no privileged power to author current,
morphology, success, failure, reward, or learning.

[counterexample; source-inspected] The superseded HNA contract instead required native emission,
an application world, an admission Boolean, a complete world-face family, count-derived current and
storage, a staged candidate, an Eros commit, remount, ablation, and replay before calling the cycle
cultivation. The implementation then converted byte differences into alleged current, repeated one
observation as `eee`, treated exact filesystem readback as a world, and constructed a one-edge
morphology deposit. Those operations are counterexample evidence and carry no HNA grade.

## 1. The formal object

[definition] The primitive HNA object is an operation step, not an inference/return pair. In
Lean-shaped form:

```text
OperationStep(Ecology, Occurrence, Emission, Trace) :=
  predecessor : Ecology
  occurrence  : Occurrence
  emission    : Emission
  trace       : Trace
  successor   : Ecology
  operate     : Ecology -> Occurrence -> Emission x Trace x Ecology
  exact       : operate predecessor occurrence = (emission, trace, successor)
```

[definition] A recurrence is an indexed family of operation steps with exact successor use:

```text
state       : Nat -> Ecology
occurrence  : Nat -> Occurrence
step        : Nat -> OperationStep

step(t).predecessor = state(t)
step(t).occurrence  = occurrence(t)
step(t).successor   = state(t+1)
```

The emission of step `t` may supply all or part of `occurrence(t+1)`. An application may instead or
additionally supply a new occurrence. Both cases use the same `operate`; neither is a feedback mode.

[definition] The ecology contains at least the dependent owners required by the operation:

```text
Ecology E :=
  addressed incidence
  x contemporary carrier/current field
  x local constitutive morphology
  x chronology and occurrence lineage
  x open boundary and obstruction population.
```

This is a dependent causal object, not necessarily a literal Rust product or one flat tensor.

[definition] At a finite local-current chart, one operation has the already-founded neural form

```text
J_(E,g,x)(i,j) = LocalCurrent(E.morphology, g, x, i, j)
x'(i)          = Reaction(E.morphology, g, i, sum_j J_(E,g,x)(i,j))
E'             = Advance(E, occurrence, x')
```

In a declared linear chart, `J = W x`: `W` is a matrix face of the local constitutive morphology,
`x` is the contemporary carrier field, and `J` is the current produced by their operation. An octet
value, adjacent byte difference, state identifier, observation identifier, process status, or
accepted-count ratio is not `J` merely because it can be embedded in the carrier scalar.

[definition] Every operation is a new causal occurrence and therefore advances the ecology's
chronology and lineage. It need not make every coordinate unequal. A static weight projection may
remain equal while activation/current and chronology advance; another operation may change local
morphology as well. Equality at one receiver never erases the successor occurrence.

## 2. Inference, generation, cultivation, and rest are views of one sequence

[definition] The following words do not name different engine modes:

- **inference** is a receiver reading a finite recurrence;
- **generation** is an application reading emissions from successive operations;
- **self-reentry** is an emitted carrier supplying a later occurrence;
- **tool or world interaction** is an application supplying a later occurrence from an exterior
  apparatus;
- **cultivation** is a receiver observing that the morphology projection of the ecology changed
  across one or more ordinary operations; and
- **training/refinement** is a developmental recurrence whose successor ecology is retained or
  rested.

[definition] Resting is optional persistence after any operation:

```text
operate(E_t, o_t) = (..., E_(t+1))
rest(E_(t+1))     = artifact
```

Exact remount establishes storage fidelity only. Source detachment, ablation, withdrawal, replay,
and later behavioral comparison are optional receivers for particular compression, provenance, or
causal-attribution claims. None defines inference, recurrence, or learning in general.

[definition] The ordinary next-token/reprompt loop is the canonical control:

```text
current context occurrence
  -> operate the current ecology
  -> emit the next native face
  -> application renders or selects its exterior face
  -> the resulting occurrence joins the next operation on the successor ecology.
```

The application-side selection or rendering is a codec/apparatus action. It is not a reward, a
teacher signal, a morphology commit, or a second causal law.

## 3. Eros, Athena, and Soulkiller

[definition] **Eros** is the operation/advance law and its repeated composition. It is not a
transaction manager waiting for an exterior verdict.

[definition] **Athena** is one continuing ecology generated by those operations and, when desired,
one rested artifact of a chosen successor. Athena is not identified by a foreign model name,
language, format, task, prompt, compiler, or output surface.

[definition] **Soulkiller** is the one-way construction boundary from a foreign realization to
native operable morphology. Its hot return must contain the actual generic operator complex needed
by `LocalCurrent`, `Reaction`, and `Advance`: local constitutive cross-sections, incidence, carrier
charts, chronology, and receiver projections. A collection of recorded activation pairs keyed as
states and replayed as one generator per example is testimony about a foreign run, not an operable
Athena morphology.

[definition] Foreign weight matrices may enter Soulkiller as exact source-chart testimony. In a
native linear chart they may return as generic constitutive cross-sections whose application to a
carrier is `W x`. Foreign architecture names and execution laws do not enter Athena, but removing
their names does not excuse omitting their mathematical operation.

## 4. Application boundary

[definition] Languages, proof assistants, file formats, sensors, compilers, renderers, and tools are
applications. An application may:

- turn exterior material into a typed occurrence at a declared port;
- render an already-emitted native face;
- supply another ordinary occurrence after an exterior action; and
- record diagnostics and provenance.

It may not author native incidence, select an internal route from an expected answer, reinterpret an
identifier as emitted content, fill a template, reconstruct a stored source snippet, or convert a
pass/fail/status scalar into morphology.

[definition] The engine/application ABI therefore needs ordinary operations, not a privileged
world-return family:

```text
Found(Ecology)
Operation { occurrence }
Successor { emission, trace, ecology }
Rest / Remount                    -- optional storage operations
```

An application-specific `Emission -> Occurrence` adapter may close an autoregressive or tool loop.
It remains outside the native operation and its output enters the next ordinary `Operation`.

## 5. Historical founding source audit (2026-09-02)

[historical] This section records the pre-HNA source that the completed campaign replaced.
It does not describe the current operator or reopen those construction phases. The roadmap and
construction state carry the later SKE extension and current repair.

[counterexample; source-inspected] The pre-HNA Rust scaffold did not instantiate the formal
ecology. `NativeInferenceRequest` supplies an address and receiver but no contemporary carrier
field. The Soulkiller lift makes each complete recorded activation section a state key, makes each
excitation event a generator, and makes the observation the state identifier. Resident conduct then
walks that declared generator table. Its exact incidence contraction is a useful apparatus owner,
but the recorded-transition chart is not the actual local-current/reaction operation of the
inherited neural morphology.

[counterexample; source-inspected] The unadmitted HNA source adds no missing operation. Its
byte-difference current is an authored exterior chart; `conduct_material` does not consume it;
`faces_for` duplicates one process status over all grains; `constitute_world_interaction` makes a
current from counts and ignores carried occurrences when choosing native support; and the deposit
builder authors the successor graph structure. These files remain counterexample material until
removed or rewritten by the ordered construction below.

[established-bounded; source-inspected] The exact activation-section reader, rational/current
arithmetic, CUDA incidence contraction, move-owned ecology carrier, occurrence lineage, tensor
lenses/faces, application process adapters, and rest/remount encoding remain available at their
bounded scopes. At that founding revision they were components; HNA1--HNA5 below subsequently
returned the actual bounded recurrent operation.

## 6. Fixed construction order

[historical] The following is the completed HNA order and its original acceptance conditions.
Its source audits and measurements are dated. Later SKE refinements retain their own scopes;
these old imperatives schedule no new construction.

### HNA0 -- formal recurrent ecology and lifecycle correction

[definition] Add one Lean owner for `OperationStep`, recurrent successor joining, emission as a
receiver of the step, optional morphology projection, and application-produced/self-reentered next
occurrences through one occurrence type. Rebase/naturality must transport the complete operation,
not only its emitted face.

[definition] Supersede the HNA use of `InferenceCirculationReturn.morphologyFixed`,
`CultivationPassage.returnIsLater`, mandatory `morphologyChanged`, and
`ParentedMorphologyCommit`. Retain those old types only for any independently valid specialized
experiment; they do not define HNA.

**Pass HNA0:** [definition] Lean proves exact successor joining across arbitrary finite recurrence;
the next operation consumes the preceding successor; equal emitted faces may retain distinct
operation occurrences; both a fixed-morphology operation and a morphology-changing operation inhabit
the same recurrence; self-reentry and an application-produced occurrence use the same step owner;
the focused and umbrella builds have no `sorry` or new axiom.

[proved-derived; formal-checked] **HNA0 PASSED.** The return is recorded in
[`2026-09-02_HNA0_ONE_OPERATION_RETURNED_ITS_SUCCESSOR_ECOLOGY_AND_THE_NEXT_OPERATION_USES_IT.md`](../../research/records/2026-09-02_HNA0_ONE_OPERATION_RETURNED_ITS_SUCCESSOR_ECOLOGY_AND_THE_NEXT_OPERATION_USES_IT.md).

### HNA1 -- actual native operable morphology

[definition] Replace the activation-example transition archive as the hot Athena body with one
actual Soulkiller return from the available inherited realization into the generic finite
local-current ecology. Preserve exact source coordinates only in cold testimony. The hot return must
contain the complete generic operator sequence required to enact its local constitutive
cross-sections and reactions; no foreign executor or source text is callable.

[established-bounded; source-inspected] The exact full-text residency shape is known. The 719
language tensors contain 15,036,138,068 BF16 octets. Their simultaneous aligned `i64` image would
require 120,289,104,544 octets and cannot exist. HNA1 therefore owns one packed resident coefficient
store plus one reusable aligned tensor/tile pool.

[counterexample; measured] The source-inspected forecast proposed a 16,384-row tile for the widest
10,752-coordinate map. After the readout and resident surface mounted, the card reported
16,448,094,208 octets available; after the complete packed store mounted it reported 1,411,514,368.
The 16,384-row allocation returned `CUDA_ERROR_OUT_OF_MEMORY` and is withdrawn as the realized
aperture.

[established-bounded; measured] The card admitted one 8,192-row aligned slot. The aligned words,
row-mass and score populations, vector workspace, a 512-row / 11,010,048-octet addressed-occurrence
gather region derived from the local causal aperture, and reduction scratch share one
716,578,832-octet allocation. Two certified chronology populations add 12,288 octets; together with
every packed coefficient the live charge is 15,752,729,188 octets. The earlier refused larger
allocation remains counterexample evidence; the final allocator derives 8,192 rows directly and
reported zero allocation retries. A second alignment slot is not admitted.

[definition] Each complete tensor obtains one device-derived exponent/frame at initial mount.
Later tiles reuse that frame through a fixed-frame pooled mount; a tile may not derive its own
exponent. The raw coefficient population crosses to the GPU once. Tensor names and source offsets
remain in cold testimony; hot tensor addresses are native ordinals. Tile alignment is temporary
arithmetic representation and is never morphology identity.

**Pass HNA1:** [definition] every hot operation has declared incidence, carrier domain/codomain,
constitutive cross-section or nonlinear reaction, chronology, and receiver; native execution of a
bounded complete section agrees with the corresponding foreign-world receiver within its explicitly
declared exact or projected chart; changing a recorded activation fixture without changing the
operator morphology cannot change the hot body; no one-generator-per-example transition table is
presented as the model.

[established-bounded; implemented-exact; source-inspected; measured] **HNA1 PASSED.** The hot return
contains 1,275 typed operation nodes over 42 ordered layers and all 719 source-declared coefficient
populations. The configured operation consumes 665; the 54 arrays its own shared-K/V realization
does not reach are explicit obstructions rather than invented operations. All coefficient octets
mounted once, all complete tensor frames returned, and a complete `256 x 2560` matrix section
returned all 256 resident exact scores equal to the independent serial exact chart. The return is
recorded in
[`2026-09-02_HNA1_THE_COMPLETE_TEXT_OPERATOR_BECAME_ONE_RESIDENT_NATIVE_ECOLOGY.md`](../../research/records/2026-09-02_HNA1_THE_COMPLETE_TEXT_OPERATOR_BECAME_ONE_RESIDENT_NATIVE_ECOLOGY.md).

[counterexample; source-inspected] The HNA1 return is the manifestation grade, not a Soulkiller
return: it excites nothing and carries no insufficiency. It is the apparatus the Soulkiller
campaign excites (`SKE0--SKE5`); its residency, exactness, and recurrence claims stand.

### HNA2 -- one native operation advances one ecology

[definition] Implement a move-owned `NativeOperationStep` which consumes the current ecology and one
typed occurrence, enacts `LocalCurrent -> aggregate -> Reaction -> Advance` on the resident
apparatus, and returns the emission, exact trace, and successor ecology together.

**Pass HNA2:** [definition] two distinct admitted carrier occurrences enter the actual constitutive
operation and differ, when the operator distinguishes them, before any receiver/codec; the emitted
face is derived from the operated successor; chronology and lineage advance even when a selected
receiver face is equal; no byte-difference constructor, observation-ID codec, admission count,
candidate, or morphology commit appears in the productive closure.

[established-bounded; implemented-exact; measured] **HNA2 PASSED.** Two ordinary occurrence rows
entered the same resident lookup and remained distinct before any codec. The returned successor then
performed the next lookup, chart reshape, and complete `10,752 x 2,560` constitutive contraction.
Generation advanced `0 -> 4`; the contraction distinguished the two occurrences; and its emitted
face equalled the carrier held by the returned successor. The receipt is
[`2026-09-02_HNA2_ONE_FULL_NATIVE_OPERATION_RETURNED_ITS_SUCCESSOR_ECOLOGY.md`](../../research/records/2026-09-02_HNA2_ONE_FULL_NATIVE_OPERATION_RETURNED_ITS_SUCCESSOR_ECOLOGY.md).

### HNA3 -- recurrent inference and generation

[definition] Compose `NativeOperationStep` repeatedly. The successor ecology returned at step `t`
is moved directly into step `t+1`. A native self-emission or an application adapter may supply the
next occurrence through the same port.

**Pass HNA3:** [definition] a bounded multi-step recurrence on the actual morphology returns every
step's occurrence, current, reaction, emission, lineage, and successor; replacing one successor with
the predecessor or with an independently rebuilt body is detected; an autoregressive
next-token/reprompt application runs without filesystem readback, world-face admission, template
generation, or source-span selection; actual emitted artifacts are inspected.

[established-bounded; implemented-exact; measured] **HNA3 PASSED.** One complete 1,275-operation
cycle returned its final tiled 262,144-coordinate carrier and exact successor. A codec-only
application selected/rendered `The`, appended it to the two-address context, and the same returned
ecology completed a second cycle from generation 1,275 to 2,550. Predecessor and independently
rebuilt generation ordinals were rejected. The two inspected emissions were both `The`; this is
mechanical recurrence evidence, not a qualitative language claim. The receipt is
[`2026-09-02_HNA3_TWO_COMPLETE_NATIVE_CYCLES_USED_ONE_RETURNED_SUCCESSOR_ECOLOGY.md`](../../research/records/2026-09-02_HNA3_TWO_COMPLETE_NATIVE_CYCLES_USED_ONE_RETURNED_SUCCESSOR_ECOLOGY.md).

### HNA4 -- Eros refinement and optional rest

[definition] Run developmental material through the same recurrence. Where the operation's local
law changes the morphology projection, that changed morphology is already part of `E_(t+1)` and is
used by the next operation. Resting or remounting that successor is optional storage, not a semantic
commit.

**Pass HNA4:** [definition] one actual developmental recurrence exhibits its complete successor
ecology and any local morphology difference it produced; the immediately following operation uses
that successor without a second API; a rest/remount control, when requested, returns the same
successor operation; no exterior status, expected answer, target label, loss scalar, or separate
return constructor determines the change. No claim requires source detachment, ablation, or later
held-out behavior unless that narrower claim is explicitly being graded.

[definition] The local law of morphology advance, reconciled with the formal owners on
2026-09-02: `advanceMorphology W o x y` takes the next ordinary occurrence `o` as the comparison at
the emission receiver, returns the differential of the declared receiver through the adjoint of the
local current word, and deposits a factorized overlay on the causal cone of the return. No verdict,
reward, label, status, or caller-supplied factor enters.

[counterexample; source-inspected] The first HNA4 receipt
([`2026-09-02_HNA4_LOCAL_ALIGNMENT_CHANGED_MORPHOLOGY_INSIDE_THE_RECURRENT_OPERATION.md`](../../research/records/2026-09-02_HNA4_LOCAL_ALIGNMENT_CHANGED_MORPHOLOGY_INSIDE_THE_RECURRENT_OPERATION.md))
is withdrawn: its factor was carried on the occurrence, gated by a sign that cannot refuse a
positive scale, and applied as one global scalar
([`the reconciliation`](../../research/records/2026-09-02_THE_HNA4_MORPHOLOGY_FACTOR_IS_OCCURRENCE_CARRIED_AND_THE_FORMAL_OWNERS_REQUIRE_A_CAUSAL_CONE_ADJOINT_RETURN.md)).

[established-bounded; implemented-exact; measured] **HNA4 PASSED at the tied cross-section.** A
continuing occurrence met the retained emitted face; the normalized-exponential differential
returned through the terminal reactions; a rank-5 factorized overlay was deposited on the tied
`262,144 x 2,560` cross-section and the next cycle's contraction applied it. The control without
apertures differs at every emitted word of the second cycle. This was the tied-only HNA4
scope; SKE1 subsequently returned the pullback through the cycle and deposits on 344
cross-sections. Gains, scalars and embedding rows remain outside that deposit scope. The receipt is
[`2026-09-02_HNA4_THE_RETURN_DEPOSITED_A_FACTORIZED_OVERLAY_ON_THE_TIED_CROSS_SECTION_AND_THE_NEXT_CYCLE_APPLIED_IT.md`](../../research/records/2026-09-02_HNA4_THE_RETURN_DEPOSITED_A_FACTORIZED_OVERLAY_ON_THE_TIED_CROSS_SECTION_AND_THE_NEXT_CYCLE_APPLIED_IT.md).

### HNA5 -- application matrix and honest release

[definition] Exercise the same recurrent Athena through text, coding, and mathematics applications
as exterior occurrence/receiver configurations. Compilers, runtimes, and proof kernels may supply
ordinary later occurrences; they never grade or update the ecology implicitly.

**Pass HNA5:** [definition] the same native recurrence runs through every application without a
language- or format-named hot branch; each actual output is inspected at its application receiver;
the recurrence, not an application driver, owns successor formation; the counterexample HNA source
and retracted template/source-lookup paths are absent from the productive closure; focused tests and
one coherent release receiver pass; capability claims are limited to the exact operations and
applications that ran.

[established-bounded; implemented-exact; source-inspected; measured] **HNA5 PASSED. HNA0--HNA5
COMPLETE.** One ecology advanced through the three application cycles at generations
`0 -> 1,275 -> 2,550 -> 3,825`. The inspected faces were ` Explain`, ` i`, and ` :=`; each had one
maximum and no open interval. The codec-only driver contained no operation scheduling or retracted
return-path import, and the hot ecology contained no language/format branch. These faces establish
no qualitative answer capability. The release receipt is
[`2026-09-02_HNA5_ONE_NATIVE_RECURRENCE_CROSSED_THREE_APPLICATIONS_AND_RELEASED_WITHOUT_A_QUALITATIVE_CLAIM.md`](../../research/records/2026-09-02_HNA5_ONE_NATIVE_RECURRENCE_CROSSED_THREE_APPLICATIONS_AND_RELEASED_WITHOUT_A_QUALITATIVE_CLAIM.md).

## 7. Falsifiers

[counterexample] If the next step uses the predecessor rather than the returned successor ecology,
the recurrence is not implemented.

[counterexample] If changing the input occurrence changes only a stored testimony vector or an
application surface after native conduct, the occurrence did not enter the neural operation.

[counterexample] If a driver can replace Athena with an identity/empty stub and still manufacture
the artifact, the driver owns the deed.

[counterexample] If exact serialization, remount, withdrawal, replay, GPU execution, or source
neutrality is the principal evidence for inference or learning, the grade is invalid.

[counterexample] If a process status, kernel verdict, count, loss, score, or expected surface
determines morphology without being part of the declared local operation, an exterior receiver has
become an authored governor.

[counterexample] If a stored source span, activation example, observation identifier, or template
is emitted as though the recurrent ecology formed it, generation is contaminated.
