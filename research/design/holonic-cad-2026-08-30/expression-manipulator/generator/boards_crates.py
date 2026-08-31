from lib import *
from gen import board, note_on

@board("CratesComposition.dc.html", "Crates 1 — what already exists, face by face", 1560, 1060, "page-crates")
def crates_composition():
    t = table(["CAD face / need", "existing owner (exact)", "what it already carries", "the CAD adds only"], [
        ["passage, both boundary maps", "<span class='mono'>L/Foundation/Lineage.lean AddressedPassage</span> · <span class='mono'>holonic-engine addressed_current.rs AddressedCurrentPassage</span>", "occurrence population, source/target maps, pullback join, serial comp; exact weighted current, generator population, fibre", "a projection to a drawn edge"],
        ["holon / composite", "<span class='mono'>L/Foundation/Holon.lean Holon, BoundaryHolon</span>", "occurrences, ports, receive face, reconstruction fibre, comp/cartesian/diagonal bodies", "nothing"],
        ["Complex Parametron", "<span class='mono'>Millennium/HolonicComplexParametron.lean complexParametronHolon</span> · <span class='mono'>native_spool.rs NativeParametronCell, NativeThread</span> · CUDA <span class='mono'>conduct_coupled_complex_parametron</span>", "B, M, G=BᵀMB, reorientation covariance, complex current, relative phase, hand; resident tick", "a component sheet (symbol · footprint) around the existing model"],
        ["lattice / plaquettes", "<span class='mono'>lattice_gauge.rs Lattice {links, plaquettes}, GaugeConfiguration</span> · <span class='mono'>HolonicFourTorusCarrier.lean Vertex/Edge/Face/Chain</span>", "oriented links, plaquette walks, connection, exact spectrum; ℤ⁴ cellular carrier with boundaries", "site placement through a chart"],
        ["transport tick", "<span class='mono'>diffusion.rs DiffusionComplex, DiffusionCurrent</span> · <span class='mono'>HolonicDiscreteInduction.lean InductionGrain, ContinuityGrain</span> · <span class='mono'>HolonicDiscreteMaxwellOperator.lean MidpointMaxwellHistory</span>", "implicit exact transport M φ = n + s + τ∂j; Faraday/continuity grains; Poynting balance", "the scrubber and probes"],
        ["exact algebra, DOF", "<span class='mono'>exact_linear.rs ExactRatMatrix, LinearFactorization {rank, kernel, image, cokernel}</span>, <span class='mono'>RebaseReceipt</span> · <span class='mono'>L/Foundation/LatticeTransport.lean LatticeIndexReceipt</span>", "rank, kernel, image, cokernel, refused rebase — DOF = n − rank is a face of this", "constraint → residual generation (absent, below)"],
        ["receiver, chart, projection", "<span class='mono'>relational-geometry projection.rs Receiver {frame, orientation, projection, gauge, route_overrides}, ProjectionLaw</span> · <span class='mono'>model.rs LocalChart, LocalFrame, FrameRelation</span>", "orthographic / perspective / stereographic / isometric exact projection; crossings with orientation sign", "the 3+1 split as a chart choice"],
        ["diagram topology", "<span class='mono'>receiver_topology.rs ReceiverTopology, DiagramNode/Edge/Face, IharaSignature</span> · <span class='mono'>decorated_path.rs JointDecoratedPathOperator</span>", "planar diagram of a projected construction with faces and crossing marks", "nothing"],
        ["swing", "<span class='mono'>receiver_atlas.rs SwingCell {pivot[3], witness}, ReceivedSwing {cross_ratio}, JointSwing</span> · Provenance <span class='mono'>math_record_swing</span>", "the cross-ratio swing under a receiver; recorded swings", "the tactic-swing reading (species, fibre)"],
        ["scene, moments, archive", "<span class='mono'>scene.rs LabScene, SceneMoment, SceneArchive</span>", "construction + receivers + bookmarks; ordinal moments; cursor", "the time scrubber over moments"],
        ["Lean → trace", "<span class='mono'>LR/DerivationAtlas.lean AtlasBundle {expressionNodes, termOccurrences, proofEvents {before, after : GoalFace[]}}</span> · <span class='mono'>lean_development.rs DeclaredForm, ProofStep</span> · <span class='mono'>derivation_atlas.rs DerivationCircuit</span>", "kernel-checked expression graph, term occurrences, before/after goal faces; source reader; recruitment circuit (0/1-cells)", "assignment fibre and t-index (absent, below)"],
        ["ports / interaction", "<span class='mono'>interaction.rs OccurrencePort {event, hand, ordinal}, InteractionBond, InteractionPattern {temporality}</span>", "ports with hand and ordinal; bonds; co-present vs precedence", "PortKind (absent, below)"],
        ["chain, face, hand, junction", "<span class='mono'>holonic-structure chain.rs Chain {head, tail, unconnected}, face.rs Face, relating.rs Hand {Cohere, Anti, Ortho}, junction.rs CountedCrossing</span>", "both-ends-open chains retaining failures; scalar face with askable relation; hand that gates", "nothing"],
        ["causal body / evolution", "<span class='mono'>causal_body.rs CausalBodyStanding</span> · <span class='mono'>evolution.rs EvolutionShape</span> · <span class='mono'>category.rs CategoryPresentation</span>", "graded complex, openings, connections, holonomy generators, receivers; boundaries as a category", "nothing"],
        ["presentation / display", "<span class='mono'>presentation.rs ExactSurfacePresentation</span> · <span class='mono'>display.rs DisplayFace</span> · <span class='mono'>live_presentation.rs LiveCpuPresenter</span>", "exact cells → octets; caused receiver faces realized", "the editor chrome (apparatus)"],
        ["reflective codec runtime", "<span class='mono'>holonic-language ReflectiveRuntime, CodecStep, CodecObstruction</span>", "mount/open/receive/revise codecs with lineage refusals", "Lean and the agent as mounted codecs"],
    ])
    body = col([t, note("Every row was confirmed against the type census of 2026-08-30 (reports/holonics-types.md); paths are <span class='mono'>crates/…/src</span> and <span class='mono'>soma/formal/elementary-holonics/…</span>. Search before founding: these owners are rotated into typed contact first; only the five absences on the next board justify any new owner (AGENTS.md, circulation before new organs).")], "flex: 1 1 auto; min-height: 0; overflow: hidden")
    return artboard("Crate branch — what already exists, face by face", "the CAD composes existing owners; a large new subsystem would be a hidden foreman", 1560, 1060, body,
                    "sources: reports/holonics-types.md (read-only census) · AGENTS.md circulation before new organs · canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md")

@board("CratesBranch.dc.html", "Crates 2 — the branch, its absent types, and what must not be founded", 1560, 1000, "page-crates")
def crates_branch():
    absent = panel("the concrete absences that would justify an owner (each graded open)", col([
        box("obstructed", grade("open") + " <b>assignment fibre in the trace.</b> <span class='mono'>DerivationAtlas.lean ProofEvent</span> carries before/after <span class='mono'>GoalFace</span> arrays but not the mvar assignment, the mctx delta, the rewrite locus or the elaboration trace. Owner: a Lean-side extension of the exporter (schema v3), consumed by <span class='mono'>lean_development.rs</span>. Not a Rust interpreter of Lean."),
        box("obstructed", grade("open") + " <b>PortKind on ports.</b> <span class='mono'>interaction.rs OccurrencePort</span> has hand and ordinal, no kind; the contact matrix (Library 0) has no owner. Owner: a kind enum on the existing port and a pairwise rule as a receiver over <span class='mono'>InteractionPattern</span>."),
        box("obstructed", grade("open") + " <b>rule with fallback, signature-keyed materialization.</b> <span class='mono'>relational-geometry model.rs Construction</span> has frames/relations/entities/constraints, no rewrite rule; the engine's <span class='mono'>evolution.rs</span> has laws but no boundary-triggered fallback. Owner: one small module composing <span class='mono'>EvolutionShape</span> laws with a registry keyed by <span class='mono'>name:[signature]</span>."),
        box("obstructed", grade("open") + " <b>constraint residuals over exact params.</b> <span class='mono'>ConstraintKind {SharedVertex, PointOnConic, Declared}</span> has no equation generator and <span class='mono'>ExactValue::Expression</span> has no total derivative; rank/DOF already exist in <span class='mono'>LinearFactorization</span>. Owner: residual + partial on the existing expression type; the solve is a face of the factorization."),
        box("obstructed", grade("open") + " <b>holonic-json-v1 document codec.</b> No schema exists in canon or blueprint (AGENTS.md:97 only). Owner: a codec in <span class='mono'>holonic-language</span> terms, never a runtime topology."),
    ]), "flex: 1 1 auto")
    branch = panel("the branch · one workspace member, owner-local modules, no foreman", code(
"""crates/holonic-cad/                 -- workspace member; depends on holonic-structure, relational-geometry,
  src/lib.rs                        --   holonic-engine, holonic-language; no float in any semantic path
  src/trace.rs        (≤ 400 lines)  -- ProofEvent(v3) → TacticSwing; alias union; t index         [composes lean_development, DerivationAtlas]
  src/port_kind.rs    (≤ 200)        -- PortKind + contact receiver over InteractionPattern       [composes interaction.rs]
  src/rule.rs         (≤ 400)        -- rule + fallback + signature registry                       [composes evolution.rs laws]
  src/residual.rs     (≤ 300)        -- constraint → residual, partial on ExactValue::Expression   [composes exact_linear LinearFactorization]
  src/document.rs     (≤ 300)        -- holonic-json-v1 codec: occurrences, passages, components, swings, receipts
  src/faces/{trace,schematic,lattice,transport}.rs   -- projections only; each returns a PresentationFace-shaped value
  examples/           -- drivers: mount a .holon, invoke owners, write receipts (narrow apparatus, THE_DRIVER_ATLAS)
apparatus (separate crate, outside the semantic cone): holonic-cad-ui — egui/wgpu window,
  keyboard map, docks; consumes faces, emits swing proposals through one projection port""", "font-size: 9.5px") +
        note("size ratchets from CONS2 apply (file, function, public-API); every module names the owner it composes; the UI crate is an exterior chart and may hold floats only for pixels, never for identity."), "flex: 0 0 720px")
    refuse = panel("what must not be founded", row([
        box("refused", "<span class='mono'>Interpreter</span>, <span class='mono'>Scheduler</span>, <span class='mono'>ControlFlow</span>, <span class='mono'>Planner</span> — branch/loop/call/stack are receiver shadows (AGENTS.md circulation)"),
        box("refused", "<span class='mono'>Circuit</span>, <span class='mono'>Parametron</span>, <span class='mono'>Layer</span> cabinets — the carrier composes existing owners (canon §8d)"),
        box("refused", "a Lean AST/bytecode/grammar owner — Lean is an exterior codec port; the derivation atlas is testimony (AGENTS.md causal arithmetic)"),
        box("refused", "any construction from this page: the repository's live roadmap governs when anything is built — this page is design testimony, graded interpretation"),
    ]), "flex: 0 0 auto")
    body = row([absent, branch], "flex: 1 1 auto; min-height: 0") + refuse
    return artboard("Crate branch — absences, the branch, and refusals", "five graded absences justify five small owner-local modules; the UI is apparatus; nothing is scheduled", 1560, 1000, body,
                    "sources: AGENTS.md construction grade / circulation / apparatus · blueprint/THE_ROADMAP.md CONS1–CONS5 · reports/holonics-types.md")

note_on("n-crates-1", "page-crates", 1680, 0, 320, "Grade of this page: interpretation. It names existing owners by exact path and the absent types by exact field; it schedules nothing. The roadmap's CONS2 size ratchets would govern any of these modules.")
