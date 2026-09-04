# SKE audit: the coordinate grain, the host readout, and the compression clause were injections, and the canon already owns the answers

**Date:** 2026-09-03  
**Truth status:** `established-bounded` for the source and Lean findings; `process-audit` for the attribution; `open` for the obligations named  
**Evidence:** `source-inspected`, `formal-checked` (hand proofs from quoted Lean, not kernel-run), `measured` (the SKE receipts cited)  
**Occasion:** Brandon's rulings of 2026-09-03 (group characteristics of flux, never exact relational details on one grain; certifying and reading every operation was never asked for; holonic compression in the holonic sense) and his instruction to audit rigorously against the formalized mathematics and the research deposits rather than react.  
**Receipts:** [`2026-09-03_SKE_AUDIT_receipts/`](2026-09-03_SKE_AUDIT_receipts): four Opus 5 read-only audits (the Lean owners; the canon, records, and conversation logs; the resident session against the 2026-08-18 contract; the lineage A dependents). They are testimony; what follows is the integration against the governing files, with each finding cited to the tree.

## 1. The session is the renamed instruction loop, and it is a Claude injection

[established-bounded; source-inspected] The contract of 2026-08-18
(`2026-08-18_THE_SECTION_MUST_STAY_ON_THE_CARD_THE_CONTRACT_BEFORE_THE_RESIDENT_LAYER.md:38-40, 165-168, 191-195`)
requires one resident handle entering and leaving every operation on the card, operations
returning handles plus a `LocalReceipt` and never a host vector, the passage bound whole and
launched once, and "zero intermediate D→H section transfers". The HNA session violates each
clause: `full_operation.rs` opens a one-occurrence passage per primitive (`:592, 679, 727, 835,
888, 936, 996, 1044, 1087, 1144, 1214, 1278`), launches and synchronizes per operation
(`resident_section.rs:1418-1432`), reads the whole carrier to the host at 20 intermediate sites
(`full_operation.rs:598, 692, 733, 787, 849, 894, 942, 1006, 1050, 1099, 1150, 1223, 1292`;
`operative_terminal.rs:193, 274` per tile), and decides the successor projection on the host from
the copied words (`full_operation.rs:568-618`) with `section_collapse_control`, the kernel the
tree labels "unsound by construction … a control" (`exact_resident_section.cu:1214-1215`), rather
than the declared `MidpointQuotient` (`resident_law.rs:429-435`). The words the host scans are
already in the census the launch read (`SlotReading.nonzero_widths`, `max_width`,
`resident_section.rs:997-1017`). A cycle is about 2,100 passages, not 1,275: the terminal five
nodes are 32 tiles each. No receipt ever measured `section_read_outs` for this session; the
number in the blueprint's first §0b was a source-derived estimate and low. The structural gate
(`resident_section.rs:1503-1524`) passes under the renaming, as the 2026-08-18 audit predicted
(`2026-08-18_THE_SECTION_STAYED_BUT_THE_HOST_STILL_OWNED_THE_PASSAGE…md:62-68`).

[established-bounded; source-inspected] The deepest cause is not the readout but the absence of
the a-priori octave law: `operative_scalars.rs:107-124` takes the next operation's bound from the
measured census, so no occurrence can be admitted before the previous one has run.
`resident_law.rs::bound_octaves` (for example `:1680-1700`) and `front_passage.rs:1841-1866`
carry that law, and under it Station C bound a 35-operation layer into one graph
(`2026-08-19_THE_LAYER_IS_ONE_GRAPH_LAUNCHED_ONCE…md:176-183`) and conducted the 42-layer
tower at 43 launches (`2026-08-19_THE_TOWER_CONDUCTS_LAYER_BY_LAYER…md:88, 94`) on the same
card. The single alignment slot (`operative_residence.rs:108-114, 581-583`; the HNA1 memory
decision at `THE_HOLONIC_NEURAL_ATHENA…md:256-262`) is the one hard obstruction: contractions
stay one tile at a time, but the operations between them need no tile, so a layer decomposes
into segments, not thirty passages. `align_tile` also synchronizes the null stream and copies the
row masses to the host on every contraction, uncounted by the census
(`embedding_fiber.rs:1122-1150`).

[process-audit] Brandon asked for one thing on 08-18 (the GPU owns the continuing section,
`…CONTRACT…md:22-24`) and one on 09-02 (the successor is the consequence,
`THE_HOLONIC_NEURAL_ATHENA…md:6-8`). Neither asks for a per-operation trace or readout, and HNA0's
Lean (`HolonicRecurrentEcology.lean:28-38, 71-82, 217-241`) observes once per operation at the
terminal face and asks for nothing else. The trace was rendered as a host copy of the carrier,
then the projection was written against that copy, in commits carrying Claude co-authorship
(`baa988a9` through `eab19f23`). The attribution to Sol in the first §0b is withdrawn. The
per-coordinate interval enclosure is an apparatus choice from the contract's proposal (§4,
`:165-167`, graded "proposal"), not a ruling; its composition diverges at 2^35.6 per layer
(`…TOWER_CONDUCTS…md:36-58`), which forced the midpoint quotient, which the session then decided
on the host.

## 2. The cones were never cones, and the grain change repairs nothing

[formal-checked] `IsCone` (`HolonicExcitationFoundedQuotient.lean:218-224`) quantifies over every
population disjoint from the cone. It is monotone upward: a superset of a cone is a cone, so
unions of genuine cones compose at every grain, coordinates included. The card's refutation of
the class-0 union (`2026-09-03_SKE3…md:65-74`) therefore proved that the two named exposure
cones (29,588 and 162,238 sites, `…SKE3…md:44`) were never `IsCone`; it refuted the
verification, one complement withdrawal and twenty-two nested probes standing in for a universal
over 2^1,565,804 populations, not the union. `loadBearing_mem_of_isCone` (`:242-252`) runs from
`IsCone` to membership, never toward it; no proposition in the tree names "withdrawing the cone
changes the face". `isCone_univ` (`:226-234`) shows a bare cone claim has no content without
minimality, which the tree does not define; the SKE2 record was right that the cone was minimal
along one order, not least (`…SKE2…md:135`).

[counterexample; formal-checked] Coarsening the sites to populations, heads, layers, or
carriers shrinks the lattice from 2^1.6M to 2^G and leaves the universal undischarged; the
refuting witness becomes inexpressible, not answered. The first §0b's "so cones compose under
union" was a non-sequitur, and its identification of `IsCone` with
`LocalCausalConeCultivation.outsideUnchanged` (`NativeMorphologyVariant.lean:111-126`) was wrong:
that field is a supplied obligation on the support of a returned morphology difference, per site,
with `CultivationPassage.withdraw : Difference → Morphology → Morphology`
(`HolonicIntelligenceLifecycle.lean:198`), a different function on a different object, and there
is no path between the two in the tree. The card's intervention (zeroing contraction outputs
inside the transport) is also not the SKE0 `withdraw`, which acts on the presented state before
`inferWord` (`:209-211, 45-48`).

[definition] The tree's idiom quantifies obligations over declared finite families
(`declaredProbes`, `NativeTransportScaffold.lean:237-252`; `family.receivers`, `family.histories`).
The two consistent exits are a declared-withdrawal cone (the family declares the withdrawals
it exposes its occurrences to; the cone is what they found; extent and insufficiency inherit the
bound; every reading carries the receiver and class extent it was taken at,
`placement.rs:27-29`: "what is forbidden is not being able to tell") or a structural cone from a
locality law on `FiniteLocalCurrentEcology` (a zero-preserving `reaction` and a read-set for
`observe` and `localCurrent`), which buys the universal at the cost of the architecture
neutrality its state-global `localCurrent` was built for (`HolonicNeuralEcology.lean:29-37`).
The blueprint takes the first; the second is recorded as the Lean obligation it would be.

## 3. Compression, in the tablet that owns the word

[established-bounded; source-inspected] `canon/TABLET_THE_COMPRESSION.md:12-18`: a compression
is a codec pivot carrying a declared decoder, never the shrinking of one entity; the decoder is
half of it. Brandon cites that file by name with that definition on 2026-08-16. `H.0420`
(`papers/source/holonics/computation-information.typ:521-534`): three species differ only by
remainder, rebase zero, condensation certified, compression the collapsed population relative to
a declared family; `H.0016` (`foundations.typ:356-388`): a compression is a quotient through which
every declared receiver factors, and enlarging the family can invalidate it. The remainder is a
witness, never a number (`TABLET_THE_COMPRESSION.md:35-38`), returned as the collapsed pair with
its shortest separating word (`receiver_exact_compression.rs:209-220`); a distortion scalar
standing in for the collapsed population is convicted (`:142`), a size on disk is an absolute
volume, a ratio is the frame-dependent quantity, and the invariance is additive (`:42-56`,
`H.0410`). Refraction is the codec law already in canon (`THE_TRAFFIC_SYSTEM.md:233-239`: the
medium is the codec, propagation is the pivot, the traffic law the declared decoder).
Decompression over time is the series (`exact_value.rs:361-405`; laboratory `CLAUDE.md:2232-2237`,
`NEOKICKOFF.md:385-411`). Compression is prediction is a theorem; compression is intelligence is a
thesis carried with its hedge (`TABLET_THE_COMPRESSION.md:115-129`; `2026-08-10_PREDICTION_AND_COMPRESSION…md:54-57`),
and `2026-08-14_THE_MAP_IS_PRIOR_TO_THE_SHORTCUT…md:134-148` is the only derivation of
"compression is intelligence is navigation". Where relations lock, the corpus already says what
to emit (`TABLET_THE_HEXIS.md:244-246`: lattice, phase transport, spectrum, bands, boundary
response) and already names the limit: `Saturation`
(`THE_ATHENA_ALPHA_IS_REFOUNDED…md:185-189`), which answers Brandon's 2026-08-23 question, "when
does the inference cycle start showing only marginal lifted structures relative to the standing
Athena variant", and refuses an unchanged scalar score as evidence. Exceptional holonic
compression is the strict fall of the complete consequence-preserving product under the declared
family (`2026-08-22_HOLONIC_INFERENCE_RECOMBINES…md:119-128`), never a scalar
(`02_INFORMATION_PHYSICS.md:93-105`).

[counterexample; source-inspected] Against that, the first §0b: named "compression is the
trichotomy" (a category error; the genus is the pivot, compression is a species); defined the
certified remainder as a terminal census of width and octave (a bound, not an exhibited
population; the 2026-08-18 contract's own remainder is the interval width per coordinate at the
terminal face, `…CONTRACT…md:197-200`, and Brandon's 2026-08-19 rule, undeposited, is "a midpoint
plus a discarded or sidewise interval width is not certified conduct"); coined "locking" and
"reach per retained octet" (a duplicate of `Saturation` and a ratio against an absolute volume,
both refused; his 2026-08-26: the quantity of particles carries no information about how they
got there); and cited none of the owners above. It also graded the class ecology Soulkiller
returns by the compression law, against Brandon's 2026-09-01: the returns are lenses and shortcut
paths, training wheels, "we don't expect the spool as a sort-of lens to become compressed … the
compression we'd actually capitalize off of happens in Athena". SKE5 measures the composed
variant; SKE4 grades a lift with its exhibited remainder. A row subset of codewords is, in the
corpus's terms, a receiver-family quotient whose collapsed population must be exhibited with
separating words, a lift only if it discharges `FaithfulLocalSectionLift`, and not a lens
(`2026-09-02_TENSOR_LENSES…md:88-96`); seven of seven Gemma circuits are full rank
(`ATHENA_THE_DIMENSION_IS_DECLARED…md:54-74`), so it will not be free.

## 4. The grain and "group characteristics"

[established-bounded; source-inspected] Brandon's usage (2026-08-27, 2026-08-28, 2026-09-01,
2026-09-03, quoted in the canon receipt §B) is familial: the invariants of the acting family, the
differences between singularities as orbits, the terrain a flux altered read back as evidence,
"wavelength matching or Fourier analysis" (2026-08-21), "extremely important for group
characteristics and wavelength/energy diffraction and distribution" (2026-08-27), and on
2026-09-01, "not a naive linear string of layers/tensors". His 2026-08-16 correction stands
against the first §0b's "never over coordinates": "coordinates are emergent … not somehow lost or
forgotten just because we don't store absolute positions", with `00_PURE_HOLONICS.md:18-27`
(local exact transport; holonic relativity as roles at a declared grain; no privileged chart).
The foreign layer, head, and tensor coordinates are not native topology
(`2026-08-22_HOLONIC_INFERENCE…md:116-117`; `2026-08-22_ATHENA_GEMMA_NOW_RETURNS…md:93-94`), so
the first §0b's site type was the source's coordinates made permanent, coarser. In Lean no owner
states cones or signatures over groups of sites; the only grain notion is receiver-side
(`CausalGrain.Passage`, `HolonicGranularBoundaryRadiation.lean:245-302`), and the nearest
group-characteristic owner is `CausalTailLens` (`HolonicCausalTailLens.lean:29-45`). The reading
instruments the corpus names are the phase/current atlas
(`TABLET_THE_CIRCULATING_CARTOGRAPHER.md:100-105`), the crystal emission, the collapsed pairs, the
octave and width census per passage (`SlotReading`, live), congestion dilation, and holonomy.

## 5. The SKE0 Lean owner has two gaps

[counterexample; formal-checked] `FaithfulLocalSectionLift` (`NativeMorphologyVariant.lean:24-42`)
is inhabited by the identity (`Code = Native = Source`, `residual = 0`, `quotient = id`), so the
SKE0 pass clause "a manifestation without that lane does not inhabit it" is unproved and false as
written; nothing bounds `residual` or forbids `quotient = id`, and the tree's own docstring names
what is owed: "a codec compression additionally owes an exterior presentation and decoder cost"
(`LineageCompression.lean:33`). `ExcitationFoundedReturn` (`:294-302`) shares only `Generator`,
`Receiver`, `Face` with the family section and mentions neither the family, `IsCone`, `extent`,
nor `insufficiency`; `DismantlingReturn` is a lawless triple. The control proves one state under
two histories, not two occurrences (`:371-373`). `ReconstructionFiber` was retracted on
2026-09-02 for `PreimageFibre` (`2026-09-02_TENSOR_LENSES…md:28-33`) and `TABLET_THE_OPERATIONS.md:266-316`,
`TABLET_THE_CIRCULATING_CARTOGRAPHER.md:73-79`, `TABLET_THE_HEXIS.md:122-123` still carry the
retracted name; the registry entry `H.0104` is Λ, not rebase, while every citation reads it as
rebase; `TABLET_THE_OPERATIONS.md:223` cites `H.0479` where `H.0480` is meant. Canon business,
recorded here and not edited.

## 6. Lineage A

[established-bounded; source-inspected] The per-event construction (`scaffold_lift.rs`,
`scaffold_excitation_receipt.rs`) is not retracted in `AGENTS.md`, whose standing list names its
founding record (`:185-188`); the Soulkiller audit and the blueprint retire it only "as the
return". Its dependents are 41 test functions across 15 files in `holonic-engine`, `soma/life`,
`soma/circulation-abi`, and the applications, three example deeds (AAC5's `alpha_cycle.rs`, SCF2,
MVF5), and two shipped commands (`demo-open`, `lift-gemma-receipt`); every runnable use is a
synthetic-codeword fixture, and the only real-model founding (SCF2) is already unrunnable
against the receipt its Python producer emits. The boundary-only departure (its
`SoulkillerDismantlingInput` inhabitation removed) is already in the working tree. Re-founding
the tests on `native_spool::tests::scaffold()` would be a different founding, not an alias, but
requires promoting a test fixture across crates; the workbench's product surface, the AAC5 and
MVF5 deeds' standing, and that promotion are Brandon's decisions.

## 7. What changed

[definition] The blueprint's §0b, §1, §2, §3, SKE2 and SKE3 grading notes, SKE4, SKE5, and
falsifiers were rewritten against the owners above; the `AGENTS.md` ruling bullet and retraction
entry were corrected to Brandon's words with their qualifiers and citations. The audit receipts
are deposited. The coordinate-grain SKE4 engine construction remains uncommitted; the generic
productive lane at the boundary and the coefficient intake with a mount from a productive lane
are apparatus the corrected construction may keep. No process ran on the card for this record.
