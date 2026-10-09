# The whole Athena model is one morphodynamic circuit, and its design file is its declaration

**Date.** October 9. **Issues.** #63, #73, #386, #148, #62. **Grade.** Design record. Each node, edge and
circuit carries its own status. The derivations in §5 are `agent-inferred` unless marked otherwise.

## 1. The request and the method

[project-postulate] Brandon, October 9:
- Do not build Athena piece by piece. Design the whole model at once, ambitiously, because its effects
  cannot be gauged until it is whole: a complete model whose interactions with general helical codes can
  then be studied.
- The blueprint is an abstract mathematical diagram, category-theoretic or graph-theoretic. Claude and
  Epime iterate on it and implement it in Rust, with Lean for the abstract model where that is feasible.
- It is a morphodynamic circuit, so it can be drawn in physically literal ways. CAD and other file
  stores were raised before.
- He rejected a closed vocabulary of port and join types, and any vague framing of "how the dynamics
  attach", because either would admit contamination.

The October 3 requests (model the software as a formula and a graph network; a mechanical circuit with its
flux and configuration states visible) are the same request.

[definition] **The method** (agreed with Epime, October 9).
- The diagram's content is **what changes what**:
  - the World's current and constitution;
  - source moments and keys;
  - the receiving relation and the one retained family of alternatives;
  - preparation and probe consequences, and receipts;
  - reached covectors, and deposition's effect on later perception, release and learning.
- Each join is drawn with its producing and consuming operands and its finite-change or transport defect.
  It is not given a universal equation as metadata.
- Built and owed are marked on the same object. An owed join never mounts as realized.
- Categorical terms express a recovered relation only where its composition law is supplied. They never
  select the model.
- **Black-boxing keeps every interior a future probe distinguishes.** This is the retention quotient
  ([retention contract](../../docs/ELEMENTARY_OBJECTS.md#the-retention-contract)), not a compact-closed
  elimination. A declared feedback circuit keeps its circuit, its clock and its retained interior.

The history of earlier stores, recovered from the pre-reset tree
[`13f8c734`](https://github.com/brandonrdug/holonics/tree/13f8c734), sets one more constraint. Every
description of the machine that the machine did not consume drifted or was retired: the architecture map,
the generated ledgers, the side database and the CAD files. The design file is therefore the machine's own
declaration (§7).

## 2. Conventions

- A **node** is an open Holon `H = (K, ∂_A; Π; 𝒟; 𝓔; G; π)`: its law and its boundary. The boundary is
  the actual power pairing its law exposes (frame, clock, units, pairing `⟨e, f⟩`). It is read off the law,
  never chosen from a list of kinds.
- An **edge** is an interconnection: equal effort and opposite flow on a shared boundary (Dirac gluing).
  Where no power pairing exists yet, the edge is the consuming equation that its owner already checks.
- `⊗` places Holons side by side. A **declared circuit** closes a boundary of the composite onto itself,
  with its clock, and keeps its interior.
- Status: **[R]** built, with a receipt for its declared case; **[P]** built in part, with the missing term
  named; **[O]** owed.

## 3. Nodes

| Node | What it is | Owners | Status |
|---|---|---|---|
| W World | the participating terrain and its current; actions enter it and consequences return | `hnn/physical/action/world.rs` (the Robin termination `a = e + Y⁻¹f`), `hnn/physical/action.rs` (Ask on the phase family), `hnn/word/{world_boundary,action,action_return}.rs` | [P] the native relation is certified, but there is no World prediction |
| C Codec | the boundary chart from World samples to letters, one per modality | `hnn/encoding.rs` (`Encoded`, `check_step`); Lean `HNN/Encoding` | [P] text and pitch/amplitude charts only; image, acoustic and motor codecs owed |
| S Strand | the source's face on a navigator's helix, `m = Σ_k Ĝ(τ(k))⁻¹E(u_k)` | `hnn/moment.rs` (`SourceMoment`); Lean `HNN/Moment` | [R] |
| P Pairing | the partner strand by a fixed-point-free involution `σ` through pair contacts; the dihedral `⟨S, U⟩` | `compression/keys/duplex.rs`; `hnn/paired.rs` (`083640894`, native PASS, publication pending); Lean `Transport/HelicalCode` | [P] structural on the HNN carrier; equivariant deposition owed (the pair-port reversal law) |
| Fr Frames | receivers' residue partitions read with whole winding and epoch | `compression/keys/transport.rs`; Lean `HNN/Prediction.joint_residue_determines_position` | [R] |
| Dc Decoder | the receiver's quotient (its kernel fixed by the admitted future) and the designed placement | `receiver/face.rs`; Lean `Foundation/CausalRelevance`, `Transport/HelicalRepair` | [P] the designed-placement law owed (#62) |
| Tp Topology | the linking number of closed strands, `Lk = Tw + Wr` | Lean `Foundation/TopologicalReceiver` (conditional) | [O] no crate reads it |
| G Keys | navigators' configuration, clocks and phase lifts, located by loop closure | `navigator/`, `compression/keys.rs`, `hnn/keys.rs`; Lean `HNN/Keys`; `Transport/DeletionReceiver` (#123 laws, kernel-checked at `d5f7c140b`, publication pending) | [P] the exact form only; resonant location with soft keys owed |
| F Field `F[Θ]` | the Holarchy of parametron rings and helical pair contacts; the Word executes a passage | `hnn/field.rs` (`FieldDeclaration`, `Field::holarchy`), `holarchy/mod.rs` (`Holon::interconnect`), `hnn/word.rs`, `hnn/propagation.rs`; Lean `Holon/*`, `Holarchy/Join`, `HNN/*` | [P] incidence growth owed; no glued cell complex or receiver-region view |
| R Receivers | participating Holons at the receiving port: reception, receipt, the receiving map and the population of families | `receiver/reception.rs`, `receiver/receipt.rs`, `hnn/receiving.rs`, `receiver/population.rs`; Lean `Holarchy/{Reception,Receipt,View}` | [P] the population is not joined at power ports |
| A Alternatives | the one retained family of alternatives and its observation partition | `hnn/phase_family.rs`; `receiver/release.rs` (`ProbePartition`, `LeverageSeparation`, `ask`) | [P] the two-encounter acceptance pending |
| Q Comparison | `R = Ĝ_(T←H)`, `ℓ = log R` with its branch, and the covector `R⁻¹dR` through the producing operands | `hnn/ratio.rs`; Lean `Objects/Ratio`, `HNN/Ratio` | [R] |
| M Material | the constitution `Θ` as slow state; deposition is its only change | `hnn/constitution.rs`, `holon/deposition.rs`, `hnn/executed.rs`; Lean `Holon/Deposition.learned_energy_balance`, `HNN/LatticeDeposit` | [P] the no-event regime (§5, item 4) |
| Rel Release | one decision law (draw, commit, Ask, Hold or typed refusal), and actions into W | `receiver/release.rs`, `hnn/prediction.rs`, `hnn/word/action.rs`; Lean `HNN/Prediction` | [P] legible only on known truth |
| K Continuation | the future-sufficient quotient, the reception carry, save and restore | Lean `Foundation/Standing`; `hnn/reference.rs` (`mount_continued`), `ContactCut::continue_deposited` | [P] built on the host; whole-passage restore of a receiving resident refused; card continuation owed |
| T Clocks | aeons, epochs and cycles, and the first law over an aeon | `aeon/`, `navigator::Clock`; Lean `Aeon/*` | [P] |
| L Landmarks | the kernel (retention), the cokernel residual, and faces where navigator paths converge | Lean `Foundation/CausalRelevance`, `Landmarks/*` | [P] landmark discovery inside the circuit is key location |
| Dv Device | the card realization of the same constituents | `holonics-cuda::hnn` | [P] parity for campaigns 1-2; #76 owed |
| Er Rest | cultivation versus inference, and rest and remount of the whole | Lean `Computation/HolonicIntelligenceLifecycle`, `Computation/HolonicNeuralEcology` | [O] no Rust owner |
| X Exterior charts | attention, convolution, graph, state-space and diffusion read as receiver charts | Lean `Computation/HolonicArchitectureCharts` | [R] as exterior readings only, never Athena's state |

## 4. Edges and circuits

| Edge | The law at the consumer | Status |
|---|---|---|
| W ⇄ C | `decode(T_native(encode x)) = T(x)`; `E T = U E` (`Encoded::check_step`) | [P] |
| C → S | `m ← Ĝ⁻¹ m + E(u)` at the producing clock | [R] |
| S ⇄ P | `σ̄(w)_k = σ(w_{n−1−k})`; on the carrier `s(0)(σ̄u) = B P^(−(n−1)) s(0)(u)` with `B E = E Σ_σ` re-certified at each read | [R] keys and carrier (structural) |
| S, P → Fr | residues and whole winding; frames of coprime periods meet once per residue pair modulo their product | [R] |
| Fr → Dc | release iff the receiver's class is constant on the complete supported family; otherwise Hold with two witnesses | [R] keys level |
| S → F | the source moment enters the loaded field at its port | [R] |
| G ⇄ F | located transport steps rings by located advance; loop closure prunes keys | [R] exact form |
| F ⨝ F | Dirac gluing at every contact end: `Holon/Dirac.compose_isDirac`, `Holarchy/Join.interconnect_of_glues` with a typed defect | [P] the executed tick is the Word, not separate constituent advances |
| F → R | reception `I_C(\|H_S⟩, \|H_R⟩) = (\|H′_S⟩, \|H′_R⟩, f_R)` | [P] |
| R → A | exact phase statistics absorbed per receipt; the family and its leverage | [P] |
| R, A → Q | `ℓ = log R` and `R⁻¹dR` through the operands that produced the forward carriers | [R] |
| Q → M | deposition only from covectors that reached the locus; the certified step; `learned_energy_balance`; proposal + prior remainder = applied + new remainder + released | [P] applied part zero today (§5, item 4) |
| M → F | the next passage reads the deposited constitution, with the held momentum `C′w′ = Cw` and the moving-metric work `½xᵀĠx` | [P] |
| F, A → Rel | release by sections of the request's sheets; Ask executes the most distinguishing admitted probe | [P] |
| Rel → W → C | the action current and its returned wave through the admittance termination: reflection `(Y − G)/(Y + G)` at the junction | [P] |
| F → K → F | the reception carry from the last crossing; a restored resident continues the cut exactly | [R] host |
| T ↔ all | epochs at receiver sections, pump cycles, the carry-out aeon boundary | [P] |
| F → L | the kernel quotient and the cokernel residual | [P] |
| F ⇄ Dv | the card readout equals the host's advance line for line | [P] |

**Declared circuits.** Each keeps its clock and retained interior.
1. **Learning:** `F → R → Q → M → F` on reception epochs. [P] Closed on the host; the contacts sit in the
   no-event regime.
2. **Perception, selection and consequence:**
   `M → R → A → Rel(Ask) → W → C → S → F → R → Q → M`. This is the loop through which learning changes
   later learning. [P]
3. **Repair and generation as refinement:** `F_{k+1} = T_{g_k}(F_k) ∩ C_k`, with each released boundary
   fed back as a constraint. [P] Exact on known truth.
4. **The helical duplex:** strand ⇄ partner, the inner repetition code and the outer receiver quotient. [P]
5. **Continuation and aeon closure:** word → carry → next word. [R] host.
6. **Parametron pump cycles and locks** (Floquet certificate). [R]
7. **The joint avalanche:** a released joint loads its coupled joints. [O]
8. **Currents curve the constitution, and the constitution steers currents:** deposition as curvature.
   [O]

**The blueprint expression.** One composite, read as the passage and closed by the declared circuits:

```text
Athena = ⟲[1..8] ( W ⨝ C ⨝ (S ⨝ P ⨝ Fr ⨝ Dc ⨝ Tp) ⨝ (G ⊗ F[Θ]) ⨝ R ⨝ A ⨝ Q ⨝ M ⨝ Rel ⨝ W ) ⊗ T ⊗ K ⊗ L ⊗ Dv
```

`⨝` is interconnection at a named boundary with its law and defect. `⟲` closes the declared circuits,
keeping their clocks and interiors. Er acts on the whole composite. X are readings of F and R, never nodes
of Athena's state.

## 5. What the diagram makes visible

1. **The helical code is the boundary layer in both directions.** Read inward, a source enters as a strand
   (C → S), is paired (P), is read through receivers' frames (Fr) and is decoded by their quotient (Dc).
   Read outward, a release leaves through the same decoder and codec: generation is key location read the
   other way. The roles the [helical record](2026-10-08_THE_HELICAL_CODE_IS_HOW_HOLONS_HOLARCHIES_EPOCHS_AND_AEONS_ENCODE.md)
   assigns become nodes and clocks:
   - a Holon is an addressed strand;
   - a Holarchy is the paired and nested duplex;
   - an epoch is the clock on Fr;
   - an aeon's charge on closed strands is Tp.
2. **Plasticity has two readings, and the history does not yet decide between them.**
   - (a) Deposition is a 2-cell between open Holons with the same boundary.
   - (b) `Θ` is the state of a slow material Holon M, joined to the motion through its own power pair:
     effort `∂_Θ E`, flow `Θ̇`. The Holon's energy rate already carries this term. Its quadratic case is
     `Holon/Deposition.learned_energy_balance`, and the moving-metric law is `Geometry/Motion`. Under (b)
     plasticity is itself interconnection, so the whole model stays one interaction law, and the
     [medium-of-joints](2026-10-08_THE_MEDIUM_OF_JOINTS_SNAPS_CRACKLES_POPS_OR_FLOWS_AND_ITS_CURRENTS_CURVE_ITS_CONSTITUTION.md) reading
     of deposition as curvature is its internal case. Reading (a) is what (b) looks like once M is
     black-boxed.

   Topology change (incidence growth, a constituent split or merged, a learned pairing) is a rewrite of K
   in both readings, and nothing builds it yet.
3. **Learning to learn may be a tower of material Holons** (a hypothesis with no owner). If M's own law
   (its metric, step certificate or reach projector) is the slow state of a further Holon M₂, deposited by
   comparisons of M's outcomes, the result is a tower `H ← M ← M₂ ← …` with restrictions between levels:
   the tower object of the elementary objects.
4. **The no-event regime is one open edge, not an architectural failure.** [measured, October 9] The
   acceptance reader, validated natively at `6f0bd8dfd`, reads 0 of 4:
   - C, K and D each commit 0 of 36 lattice coordinates. Their largest proposals lie 22, 20 and 20 binary
     orders below the half-unit.
   - The compared station's later response equals the unmoved control.
   - The balances close over no committed change.
   - A cold restore reproduces material, carry and current with zero difference.

   Every circuit through M therefore carries no represented change. The repair is M's element relation: a
   finite-decrease admission for a first-reach step on Rest-opened Words. Its design passed source review,
   and the build is in progress (#73).
5. **Goals are boundary declarations.** On the Rel → W edge a goal is a magnitude cell, a phase grain and a
   quantifier. The edge admits it when the goal's cell meets the image of the control map.
6. **Embedding and context are not nodes.** An embedding is the learned metric of the receivers' frames,
   and context is the configuration state of the whole composite (`x`, `Θ`, carries, clocks). Drawing
   either as a box would split it from the circuit.
7. **Introspection is a receiver of the circuit's own passage** (owed). It reads path jets, the curvature
   of the comparison, phase slip and dissipation per interaction. It never stands in for the comparison.

## 6. The formal skeleton

- **Have:**
  - Dirac structures stay Dirac under composition through a link (`Holon/Dirac.compose_isDirac`,
    `kirchhoff_isDirac`, `tellegen`);
  - typed gluing with a defect (`Holarchy/Join`);
  - the Holon foundation;
  - retention as a quotient (`Foundation/Standing`);
  - the learned energy balance;
  - the motion primitives;
  - the helical code's laws;
  - the causal adjoint in reverse factor order (`Computation/HolonicAdjointNormalization.dualMap_comp_reverse_order`).
- **Owe, in order (#62):**
  1. identity and associativity of composition, a category of open Holons in which composition is partial
     where gluing fails and the defect is typed;
  2. element relations carried through composition, with a composite's passivity proved;
  3. closing a declared circuit while keeping its interior;
  4. the material Holon's power pair (reading (b)) or the 2-cell law (reading (a));
  5. black-boxing as the future-sufficient quotient;
  6. the helical code as a functor from paired words to frames and faces;
  7. a bridge from the cultivation and ecology statements to the same category.

## 7. The design file

- **One exact declaration** that Rust instantiates and Lean states: the composite of §3-§4, extending
  `FieldDeclaration` to the whole. Its admission is the owners' own checks (`Holon::interconnect`,
  `Field::holarchy`, `Encoded::check_step`, the pairing admission, the release assembly), never a lint.
- An owed join is a typed placeholder that refuses to mount.
- Equality between the Rust instantiation and the Lean statement is owed once the consumer exists.
- The atlas stays the store of laws, and the declaration references its rows. There are no hashes as
  identity, no generated census and no side database.
- **The drawing is a face of the same object.** It is a circuit rendering in which each node shows its
  configuration state and each edge its flux, as requested on October 3.

## 8. Where the history pulls against this framing

1. **"Port".** Brandon doubted (October 4) that a port captures collision, interference and resonance.
   Here a boundary is the actual power pairing a Holon's law exposes. Slip, interference and resonance live
   in element relations and contact Holons, and distributed coupling stays inside a node.
2. **Vocabulary.** No join taxonomy is added. Nodes and edges are named by their laws, which are revisable
   (the October 7 contract).
3. **Black-boxing and traces.** The skeleton needs a stateful closure that keeps probe-distinguishable
   interiors, not a compact-closed trace.
4. **Plasticity.** Readings (a) and (b) above. The October 7 lenses (learning to learn; currents curve
   the constitution) favour (b).
5. **A growing medium.** A fixed wiring diagram is a receiver's scaled view of a continuing, growing whole.
   Topology change is owed, not drawn as done.
6. **Whole at once versus short loops.** The design is whole. Builds land by consuming joins, each with its
   fixed acceptance; CLAUDE.md's short-loop rule governs the builds, not the scope of the design.
7. **Receivers as statistical families.** The population carries no energy pairing. As an open Holon it
   needs one, or an explicit non-physical join stated by its law.
8. **The codec's transducers.** A codec must expose structure without authoring it (no catered
   machinery), or declare its transducer exterior and revisable.
9. **Release as lightning.** The release arms are discrete. A leader/breakdown release is not built.
10. **Directionality.** The return is the causal adjoint in reverse factor order with its metric, never a
    privileged "backward" pass in time.

## 9. Next

Epime reviews this diagram against the owners. The first concrete gaps, in the order the diagram exposes
them:
1. Q → M: the finite-decrease landing (in build).
2. P: equivariant deposition (the pair-port reversal law).
3. R: the population at power ports.
4. F: the glued cell complex and the receiver-region view.
5. G: resonant key location with soft keys (the #123 joins).
6. The formal skeleton items 1-3.
