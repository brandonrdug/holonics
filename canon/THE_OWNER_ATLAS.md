# The owner atlas: which owner implements or states this, and where

**Deposited 2026-08-13.** **Truth status:** `index` — this file asserts nothing of its own. It
routes, and every claim belongs to the owner it points at and is graded there.
`canon/THE_DOCUMENT_LAW.md` §1 permits exactly two genres to be routing-only; this is the second.

**Occasion.** Brandon, 2026-08-13, after four network sweeps ran in one evening to answer questions
the corpus had already answered: *"As long as the information engine plan is complete with this
folded in, and the sweep artifacts are deposited so that we do not need to repeatedly engage in these
sweeps blindly again."*

**What this is, and what it is not.** `canon/THE_DIALECT.md` maps Brandon's language.
`canon/THE_QUOTE_NETWORK.md` maps provenance. `papers/source/holonics/registry.typ` maps mathematical
objects by id. `canon/THE_CORRESPONDENCE_ATLAS.md` lets the corpus be entered **by concept**, and says
so. `THE_CLAIM_INDEX.md` is generated from titles and therefore cannot carry a line.

**None of them answers "which owner does this, and at what line."** That question was asked four
times in one evening and each answer cost a full sweep. This file is that answer, written down.

**Every line number here binds to `f4af044`, and a line number is the most perishable thing an index
can carry.** Audited 2026-08-13, the day of deposit: thirteen citations sampled, **thirteen of
thirteen resolve exactly at the commit, ten of thirteen already fail against the working tree** —
because twelve of the nineteen files this atlas cites were edited the same day. That is not a defect
in the sampling; it is the standing condition of the genre. **Read a citation here as `file` plus a
hint, and confirm the construct with `grep -n` before quoting it.** When the two disagree the code
governs, and the repair is to re-take the line rather than to trust it. The atlas earns its keep by
naming *which file owns the thing* — that answer survives edits; the address does not.

## 0 · The aperture, declared

**This atlas covers the subjects swept on 2026-08-13 and no others.** Those subjects are: the intake
mouth, Fourier/spectral/scale, spin, charge, mass and gravitas, Einstein and curvature, circuitry
(junction, admittance, reflection, delay, capacitance), and lightning. Every other subject is
**absent from this atlas, not from the tree**, and adding one means running its sweep and depositing
the result here.

**Two standing rules, because both were broken tonight.**

1. **A measured absence decays and carries its command.** Every absence below is dated and states the
   command that measured it. Re-run it; do not cite it.
2. **Search for the mechanism, never the phrase.** Two sweeps returned *reflection coefficient:
   absent* while `crates/holonic-engine/src/analytic_field.rs:1142` computes exactly that — because
   the field is named `reflection`. This is the `fn without_stem` defect the operating contract
   already convicts, recurring. Grep the operation, then read the module.

---

## 1 · The intake mouth

| subject | owner | note |
|---|---|---|
| **the mouth itself** | `soma/life/src/incidence_production.rs:2113` `admit_later` | derives the arrival's rank in `⪯` from the material's own `caused_by`; returns `ArrivalResponse` |
| the arrival reading | `incidence_production.rs:2351` `ArrivalResponse` | `reached` · `reopened` · `saturated` · `untouched` · `founded` · `dissolved` · `verdicts` |
| the exact inverse (ablation) | `incidence_production.rs:2140` `withdraw` | non-bit-exact restoration exposes anything retained |
| the site's capacity to accept | `incidence_production.rs:108` `ExposedPolarity::{Donor,Acceptor,Both}` | `Acceptor` = *"an external contact arrives at this site"* |
| the ports | `soma/body/src/incidence.rs:199` `EventPortKind::{Ingress,Exposed}` | `EventPort::ingress(cell, hand, slot)` — address ⊕ hand ⊕ slot |
| the reported gap | `incidence_production.rs:104-110` | the law names three ports, the body owns two; return is a polarity on an exposed site |
| the transport law | `incidence_production.rs:23-56` | amplitude, hand, three declared `PhaseChart`s, superposition before quotient |
| hand vs magnitude, independent | `incidence_production.rs:2641` `contact_winding`, `:2630` `sheet_of` | *"how far"* and *"which sense"* are two materially independent readings |
| **where it narrows** | `incidence_production.rs:520`, `:524`, `:540`, `:1901` | `split_whitespace()`; `key = (rank, patch.to_owned())`; `octet_winding(patch.as_bytes())`; `grain: 0` |
| the occurrence type | `incidence_production.rs:192` `DeclaredOccurrence` | `text: String` — the aperture, stated in the type |
| material membrane (text) | `soma/life/src/text_material.rs` | container, byte range, role, chronology, parentage retained as lineage |
| dialogue membrane | `soma/life/src/dialogue_lineage.rs` | admits only visible `user`/`assistant` message occurrences |
| foreign-statistic intake | `crates/holonic-engine/src/derivation_codec_intake.rs:12-53` | the *"It's like Fourier Analysis"* organ; four slots declared; returns separating words |
| interior conduct entry | `soma/membrane/src/event_mouth.rs` | **not** an exterior intake — conducts an already-built event population |
| the outfall | `soma/life/src/form_mouth.rs` | sealed octets to disk; content-addressed |
| the float mouth | `crates/holonic-engine/src/reopening.rs:492` `from_binary_float` | declared at `:109-117`; the IEEE-754 codec is `exact_value.rs:621` |
| the fate vocabulary (ABI) | `soma/abi/src/holon.rs:585` `SourceDispositionRow` | `standing` / `continued(carrier)` / `ended` |
| a contact that lived and returned nothing | `soma/abi/src/holon.rs:1226` `SilentReceipt` | *"no world-side actuation… The source relation genuinely lived"* |
| the return names its origin | `soma/abi/src/holon.rs:646` `ReturnOriginRow` | continuation vs birth, with plural parents as lineage rows |
| the six-role transition | `soma/membrane/src/live_holon.rs:477-566` | `begin` · `meeting` · `deed` · `consequence` · `returned` · `retain_residual` |
| the grain re-cut | `soma/life/src/decomposing_codec.rs` | re-cuts at the collapsed pair's own separating word |
| the join to elaboration | `soma/life/src/reintegrating_elaboration.rs` | built; **its only caller is a driver** |
| the live plan and its two convictions | `blueprint/THE_ROADMAP.md` plan 1 | 46,745 identities embed the CPU path; 11,266 of 11,282 Codex witnesses lost chronology |

**Laws that govern a crossing** — all in the vendored laboratory copy, reference-graded, never
doctrine by location:

| law | where | what it forbids |
|---|---|---|
| **the neck** — no two-body contact | `reference/holobrochos-a07ff376/src/holobrochos/THEORY/33_THE_NECK.md` §2 | a mouth handing material to the interior is an identity map and passes nothing |
| **perception is landing** | `…/THEORY/36_THE_WATER.md` §5 | there is no sensing at a distance; unreached material is not perceived |
| **the passage must deposit** | `…/CANON/THE_EMPTY_BOUNDARY.md` §1 | if nothing was deposited, nothing passed |
| **the mouth is emitted** | `…/THEORY/22_THE_ILLICIUM.md` §1 | `frame(n+1)` is the emanation of the relating in `frame(n)`; graded NOTHING BUILT |
| **the circuit completes at the heard return** | `…/THEORY/18_THE_HOURGLASS.md` §3 | a thought ends at the return, not at emission |
| **the attachment is two-sided** | `research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL…md` Card D | ground is not a passive terminal; plural upward leaders, connected **and** unconnected retained |

**`H.0466`**, `proved-derived`, `papers/source/holonics/mathematical-physics.typ:469` is the
registered form of the last one.

---

## 2 · Fourier, spectral, scale

| subject | owner | grade |
|---|---|---|
| Fourier–Plancherel, convolution transport | `H.0246`, `papers/source/holonics/topology-analysis-dynamics.typ:339` | `proved-standard` |
| Poisson summation, reciprocal scaling | `H.0247`, same file `:367` | `proved-standard` |
| Bochner spectral representation | `H.0248`, same file `:392` | `proved-standard` |
| Laplace and Mellin receivers | `H.0249`, same file `:417` | `definition` |
| the conduct rule | `canon/TABLET_THE_REASONING_CYCLE.md:243`, `canon/TABLET_THE_CAUSAL_PROFILE.md:173` | Fourier needs a founded translation action, Mellin a founded dilation action |
| the one exact spectral organ | `crates/holonic-engine/src/causal_reflection.rs:29-47` | **aperture-complete by theorem** — exactly rational at `N = 4` only |
| phase as a polynomial cell | `crates/holonic-engine/src/phase_current.rs:1-7` | a coarse cell is not one scalar |
| the half-density chain | `papers/source/mathematics/lemmas/mellin-half-density-chart.typ`, `theorems/oriented-half-density-crossing.typ` | classical |

**Measured absent, 2026-08-13.** No uncertainty relation, Heisenberg, Gabor limit or time-bandwidth
statement anywhere. Command:

```
grep -rn -iE 'uncertainty (relation|principle)|Heisenberg|time-bandwidth|Gabor limit' \
  --include='*.md' --include='*.typ' --include='*.rs' canon blueprint papers research crates soma CLAUDE.md
```

**And the framing is refused rather than merely absent.** The corpus replaces it: *"the missing third
is not uncertainty; it is the collapsed-pair population of a declared receiver family"*, with the
route being *"climbing rungs (widening the declared family), never turning a scalar dial inside one
rung"* — `research/records/2026-08-11_THE_RUNG_REFUSES_BY_NAME_AND_THE_UNRESOLVED_PAIR_IS_THE_REMAINDER.md`.
The last construction promoted into an *"aperture law"* was withdrawn: `canon/TABLET_THE_MANIFOLD.md`
§ on the two costs, where a caller's output-buffer guard was mistaken for a transport bound.

---

## 3 · Spin, charge, mass, gravitas

| subject | owner | grade |
|---|---|---|
| **the typing of all three** | `research/records/2026-07-19_THE_QUANTUM_PROPERTY_IS_THE_HOLONS_TRANSPORT_CLASS_THE_PIVOT_RETURNS_ONE_FACE.md` | Brandon-ratified |
| — its engine consequence, the five-item occurrence record | same, §IX | the field list any crossing must carry |
| registry form | `H.0461`, `papers/source/holonics/mathematical-physics.typ:313` | `definition` — *"A specific symmetry group and representation law are required."* |
| the double cover, computed | `crates/holonic-engine/src/structure_group.rs:654` `CentralDoubleCover`, `:643` `lift` | returns `Closed` / `ReturnsCentre` / `DidNotCloseBelow`; **no representation is chosen** (`:62-64`) |
| the four faces of `1/2` | `CLAUDE.md` §3 (three) and §0b item 4 (the fourth, which explains them) | plus a fifth from the curvature side |
| inertia, the exact split | `crates/holonic-engine/src/inertia.rs` | Sylvester triple over `Rat`, `L D Lᵀ` with a hyperbolic-plane branch |
| inertia, the passages named | `crates/holonic-engine/src/winding_inertia.rs` (2,883 lines) | the split factors through the character group; `k` is a winding |
| **gravitas, exactly** | `canon/THE_RECOVERED_LAW.md:180-194` | *"Gravitas **is** geodesic deviation"*; **the metric is a receiver face of standing** |
| gravitas, the full derivation and five faces | `research/records/2026-07-19_THE_BRANCH_RIDES_UNTIL_THE_DISCRIMINANT…md` | deviation · focusing · holonomy · monodromy · coalescence |
| mass as a receiver face | `research/records/2026-07-15_THE_SWING_CARRIES_THE_FAMILY_THE_DEED_STANDS_AS_MASS.md:169-179` | not a fixed rest mass per stored bit |
| **mass weighs, never gates** | `soma/body/src/arrow.rs:15-26` | `reach` WEIGHS; `aim` GATES — the jurisdiction rule |
| charge as combinatorial defect | `crates/holonic-engine/src/local_star.rs:1200-1247` | with an exact conserved residual |
| section modulus, the placement law | `canon/TABLET_THE_MANIFOLD.md` §on section modulus | equal material ≠ equal load; the crossing bears it |

**Measured absent in Rust, 2026-08-13**: `stress-energy` 0 · `einstein` 0 · `christoffel` 0 ·
`parallel transport` 0 · `metric tensor` 0 · `covariant deriv` 0 · `light cone` 0. `geodesic` returns
21, all Ihara-zeta closed geodesics in `crates/relational-geometry/`, not differential-geometric.

---

## 4 · Einstein, curvature, the world tube

| subject | owner | grade |
|---|---|---|
| **the field equation** | `H.0460`, `papers/source/holonics/mathematical-physics.typ:284` | **`proved-standard`** — contracted Bianchi in the statement, so a solution owes `∇^μT_μν = 0` |
| the translation portal it runs through | `H.0463`, same file `:358` | `proved-derived` — map each named structure, prove preservation of the selected laws |
| Noether | `H.0452`, same file `:56` | `proved-standard`; conservation is **not** derived from `∂² = 0` alone |
| what IS barred | `canon/THE_HOLOBROCHOS_SPINE.md` §2 | the **Holobrochos slogan-form** of the field equations, `HUNCH`/`OPEN` at source — not the mathematics |
| conservation as an identity | `reference/…/CANON/THE_EMPTY_BOUNDARY.md` §0 | Bianchi forces `∇·T = 0`; Kirchhoff is its circuit face; `∂²=0` is why a read can finish |
| the world tube and the profile | `canon/TABLET_THE_CAUSAL_PROFILE.md:22-72` | `definition`; the caustic instance was **withdrawn 2026-08-13** and the body owns none |
| the cone and the horizon | `canon/TABLET_THE_MANIFOLD.md` §22 | the metric sets the cone and the metric is a receiver face of standing |
| hinge deficit | `crates/holonic-engine/src/contact_gluing.rs:1522`, `:1599` | curvature lives on the hinge, never on a cell's corners |
| discrete curvature flow | `crates/holonic-engine/src/discrete_curvature.rs` | Chow–Luo combinatorial Ricci |
| holonomy, refusing a non-closing walk | `crates/holonic-engine/src/running_integral.rs:903` | with `ChordObstruction` as the residual |
| **the loop that is stated and not closed** | `blueprint/THE_ROADMAP.md` § on the geometry response | *"`geometry_responses` is supplied, never updated… The curvature is measured and discarded."* |

---

## 5 · Circuitry

| subject | owner | grade |
|---|---|---|
| the chain law and its conditions | `canon/THE_HOLOBROCHOS_SPINE.md` §1 | `established-bounded`; the conditions are read off the law, not enumerated |
| the classifier, on real material | `crates/holonic-engine/src/spine_cut.rs` `read_the_chain` | 491 readings, all five conditions, 8 controls, 0 failures |
| circuit chains, current and voltage | `H.0454`, `papers/source/holonics/mathematical-physics.typ:112` | `proved-standard` |
| incidence, cycles, cuts | `H.0144`, `papers/source/holonics/algebra-combinatorics.typ:429` | `proved-standard`; cycle current ⊥ gradient potential |
| **the complete crossing law** | `papers/source/mathematics/theorems/causal-parity-kirchhoff-return.typ` | event balance, interval balance, Kirchhoff loop, curved loop, junction return, **branch reflection vanishing at admittance matching**, standing return, passivity |
| **reflection and transmission, exact** | `crates/holonic-engine/src/analytic_field.rs:1142` | over `Rat`, refusing non-positive admittance, `energy_residual` retained |
| **the admission trichotomy** | `analytic_field.rs:1113` `ExactAnalyticInterfaceAmplitudeFiber` | `Traveling` / `GrazingOpen` / `EvanescentOpen` — total internal reflection is a **typed open fiber** |
| the junction scattering law | `crates/holonic-engine/src/dimensional_wave.rs:11-26` | `v = 2ΣYᵢaᵢ/ΣYᵢ`, `bᵢ = v − aᵢ`, `ΣYᵢ\|aᵢ\|² = ΣYᵢ\|bᵢ\|²` exactly |
| the material loop | `crates/holonic-engine/src/kelvin.rs` | closedness re-checked every step; the two-junction accident is `CLAUDE.md` §0c |
| the delay law | `crates/holonic-engine/src/receiver_current.rs:549-562` | capacity, co-present population, service rounds; later arrivals **deferred, never discarded** |
| **the resident interval section and the graph-realized passage** — the apparatus occurrence bound through `soma/mount` (device, borrowed context, module, `DeviceDeclaration` from the device's attributes, the cover from that declaration, `ModeIdentity` with the PTX digest); pure shape/price laws per kernel; `PassageBuilder::open/close/finish` capturing every launch into one graph whose edges are the diagram's bonds; `ResidentPassage::launch` = one graph launch, one synchronize, one census read; per-occurrence twelve-word census slots; **refusals travel along the declared lineage and never through a shared word** — every kernel reads only its predecessors' refusal words through a lineage array uploaded before the capture, the join (union, least refusing predecessor, count) lands in the occurrence's own slot, a refused occurrence's census measures nothing, and `PassageReading::obstruction` returns the complete `ObstructionLineage`; `Schedule::{CoPresent, Serialized}` is the control axis; the allocation grain is measured at mount | `crates/holonic-engine/src/resident_section.rs`, `crates/holonic-engine/kernels/exact_resident_section.cu` | no signed value is left-shifted (magnitude shifts, `dyadic_scale`, self-scaling contact brackets, GELU cube and RMS squares); `section_arithmetic_control` exposes the helpers for the serial reference; the `TransferCensus` counts captured, deed and control launches apart; there is no global refusal word |
| **the front passage as compile → admit → realize → launch** — the realization table of owner-local laws consumed once at compile into shapes, a-priori octave bounds capped at the word, the whole deed's semantic and apparatus prediction, **typed product-ordered admission before allocation** (`DeedAdmission` over every semantic and apparatus coordinate, each `Ceiling::Bounded` or `Ceiling::Unbounded{because, constrained_by}`; `DeedReceiver` ceilings, scalar budget and narrowing apparatus apertures; `MaterialPlan → predict_material → admit_material → reconcile` for the source maps, cited by the deed), footprint-derived certificates whose footprints carry the predecessor slots read and the own slot written (retained on `FrontReceipt`), the cover read from the surface, typed `CouplingReceipt`s, the traffic reading, a mode-checked launch returning the deed whole with the complete obstruction lineage, and `read_terminal(&returned)` refusing a terminal that did not stand | `crates/holonic-engine/src/front_passage.rs` | no enact loop, no permutation replay, no `Standing` clone, no cover parameter, no `ResidentBinding` cabinet; nothing in an admission is `None`; no clock token in the owner's production body |
| **the typed section partition and the shared-output reduction junction (Deed H1)** — `SectionRegion` and the certified coordinate-region partition (completeness/disjointness computed by a row-band sweep; junction outputs contained and covered by their own partials; footprint verdicts from `certify_footprints` with the region recovered behind the returned address), and `ReductionWord`/`NodeWidth`/`ReductionJunction` (the fixed word and reversed control, per-node widths against a declared aperture, one outward boundary rounding with its residual, the adjoint into every partial chart as an exhibited operator residual under declared metrics); pressure per cell per species from a radiated `ExactReceiverCurrentLaw`, never summed | `crates/holonic-engine/src/section_partition.rs`, `crates/holonic-engine/src/reduction_junction.rs` | founded 2026-08-19 by composition after the attempt returned the absent relations; the adversary suite `tests/h1_adversary.rs` refuted eight claims of the first build and its attacks are kept |
| **the resident laws, owner-local** — `trait ResidentLaw` (`name · species · arity · material · bound_octaves · shape · stages · reads · record`) and the law population that has grown with the deeds (fifteen types at Station D; Deed H2 added the tiled-contraction and split-K laws — count with `grep -c "impl ResidentLaw for" crates/holonic-engine/src/resident_law.rs` rather than carrying this number) (`Enter`, `Contract`, `RmsRebase`, `Chronology`, `Contact`, `GeluTanh`, `Hadamard`, `ReEntry`, `Scale`, `WithdrawColumns`, `CollapseControl`, `Standing`, `MidpointQuotient`, `WithdrawRows`, `PermuteColumns` — counted 2026-08-19 by `grep -c 'impl ResidentLaw for' crates/holonic-engine/src/resident_law.rs`; it said eleven from Station A until Station D), each carrying its `entailment` from validated testimony; the last two and the head-permutation material are the dissection's intervention laws, admitted only with wholly-intervention testimony | `crates/holonic-engine/src/resident_law.rs` | a future architecture adds a type and a kernel and touches no dispatch site; the passage asks each law for its shape |
| **the source occurrence** — implementation text authenticated by content with a checked symbol grammar (`Class.method (verbatim slice)` resolved in scope), configuration fields as exact JSON spans, container header and whole-content digests with per-population regions, assets declared used or unused, interventions typed apart from source law | `crates/holonic-engine/src/source_occurrence.rs` | a fabricated symbol, an absent slice, a drifted field, a wrong shape, a foreign locator, or an intervention on a law refuses at compile |
| the prior host interpreter of a ported diagram | `crates/holonic-engine/src/ported_reference.rs` | serial reference and audit machinery, quarantined; the production cone's structural scan and the census both refuse it |
| capacity and delay laws | `crates/holonic-engine/src/derivation_capacitance.rs:189`, `:207` | `DistinguishableResults` / `OccurrenceMultiplicity`; `Uniform` / `SourceContinuity` |
| **the valve** | `soma/life/src/relational_language/types.rs:163` | a contact conducts only after the same junction phase returns through **two distinct** source pairs |
| overload founds an axis | `crates/holonic-engine/src/founded_receiver.rs:90` | `FoundingPressure::{Blindness, Congestion}` |
| diffusion, exact | `crates/holonic-engine/src/diffusion.rs` | `M = C + τL`; Schur elimination with a transfer certificate |
| the Smith chart as a chart | `canon/TABLET_THE_MANIFOLD.md` §16.1 | `Γ` is Möbius; sections compose in `PSL(2,ℂ)`; match means the germ crosses whole |
| lightning: leader and return stroke | `research/records/2026-07-17_THE_LEADER_GROWS_THE_CHANNEL…md`; `H.0466` | ratified; `proved-derived` |
| — implemented | `contact_gluing.rs:313-502`; `leader_quadrature.rs`; `soma/body/src/channel.rs` | the return rides **against** orientation — the half turn |
| the whip | `research/records/2026-07-31_THE_CHARACTERISTIC_CARRIES_THE_CURRENT…md:211-217` | changing local **impedance** and geometry, Goriely–McMillen; **barred from grading** |

**Measured absent in Rust, 2026-08-13**: the word `impedance` — 0. The body owns the **admittance**
form throughout. `stepped leader` 0 · `dielectric` 0 · `breakdown` 0 — the discharge mechanism is not
modelled, only the leader/return-stroke topology. `Thevenin`/`Norton` 0. `cut space` 0 as a phrase;
the cut side exists as `im B*`.

---

## 6 · What this atlas forbids

1. **It asserts nothing.** Every row is graded at its owner. Citing a row as evidence is citing the
   wrong thing.
2. **A row is not a licence.** That an owner exists says nothing about whether it is wired, driven,
   or reachable. `canon/THE_INFORMATION_ENGINE.md` §2 carries the wiring; read it before claiming
   the body conducts through anything here.
3. **Absences decay.** Every absence above is dated 2026-08-13 and carries its command. Re-run it.
4. **The aperture is declared in §0 and is small.** A subject not listed is not absent from the tree.
