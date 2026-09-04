from lib import *
from gen import board, note_on

def cite(t): return f'<span class="meta">{t}</span>'

@board("TypesOntology.dc.html", "Types 1 — the ontology every face is drawn from", 1560, 1060, "page-ontology")
def types_ontology():
    left = col([
        typ("Occurrence", ["id: (birth moment, rank) — owner-minted, never a value/hash", "kind: site | edge | cell | port | swing | …", "chart: declared presentation", "lineage: caused_by[]", "grade: Grade"],
            "a datum occurs in a declared type/fibre, parameter, event cut, source boundary and incidence context; equal bytes do not imply the same occurrence", "docs/canon/00_PURE_HOLONICS.md:9"),
        typ("Holon", ["members: Occurrence[] (composite of holons)", "closure: transitions internal to H close in H", "exterior: explicit crossing incidence", "boundary: receiver-relative B_ρ", "obstruction: O retained"],
            "a relative local closure with its exterior explicit — a black box with a face; always a composite", "docs/canon/00_PURE_HOLONICS.md:66,71 · THE_HOLOBROCHOS_SPINE.md:193"),
        typ("AddressedPassage (span X ← W_f → Y)", ["source: Occurrence (X)", "occurrences: W_f — the population that crossed", "target: Occurrence (Y)", "boundary_src, boundary_tgt: both maps, retained", "ports: Port[] typed", "current: exact complex section", "phase, hand", "chronology, obstruction, open_exterior", "fibre: ReconstructionFiber"],
            "the elementary lineage-bearing passage; serial composition keeps the pullback W_f ×_Y W_g; endpoint connectivity alone is a receiver shadow", "docs/canon/07_CAUSAL_ALGEBRAIC_GEOMETRY.md:64 · AGENTS.md ownership"),
        typ("Port", ["name, kind: PortKind (see Library — contact rules)", "orientation: in | out | shared", "chart: local frame", "lineage: which passage exposed it"],
            "exposed subscheme / module map / correspondence leg / typed boundary section — not interchangeable", "docs/canon/07:51 · 01:16,105"),
    ], "flex: 1 1 0")
    mid = col([
        typ("Receiver ⟨ρ|", ["map: ρ : X → Y (or relation)", "aperture, calibration", "preserved: what it keeps", "forgotten: fibres it drops (named)", "transition law"],
            "a declared map, instrument, use or comparison presenting one face; evaluation, trace, spectrum, rendered image are different receivers", "docs/canon/00:12 · SPINE:181 · 08:160"),
        typ("Face ⟨φ|ψ⟩", ["receiver: Receiver", "of: Holon | Passage", "value: exact carrier element (ℚ, ℚ(i), ℚ(ζₙ), …)", "forgets: named collapsed population", "exact: bool — every future distinction at scope factors through it"],
            "testimony about x through ρ, never its identity; a float is a face retained as if it were the construction", "docs/canon/00:13 · OPERATIONS:47 · SPINE:183"),
        typ("Swing", ["before: Occurrence", "operator: Transport | Tactic | Rewrite | Tick", "after: Occurrence", "receiver: Receiver", "hypotheses: Occurrence[]", "orientation: hand (+ | −, e^{iπ})", "boundary: spawned / owed", "grade: Grade", "fibre: ReconstructionFiber (assignment, kernels)"],
            "algebraic manipulations and proof derivations are typed swings through mathematical objects", "AGENTS.md:99 · docs/canon/08:115 (cross-ratio swing) · THE_DIALECT:89 (constraint equations)"),
        typ("Chain", ["swings: Swing[] ordered", "interior: retained Σ_k (telescoped in the face, kept in lineage)", "transport: matrix, not ratio", "cocycle: composes path-independently or reports holonomy"],
            "∂E_k = Σ_{k+1} − Σ_k + Γ_k; chronology is part of the construction even when an endpoint quotient is equal", "docs/canon/SPINE:49,62 · 01:58 · blueprint/THE_TRAVERSIBLE_CHAIN:72"),
        typ("Cell (higher)", ["paths: (P, Q) parallel passages with equal source address", "filling: declared higher boundary map (∂∂ = 0 only after it exists)"],
            "a comparison cell relates two complete paths with compatible boundaries; never a new solver or universal holon type", "docs/canon/01:10 · SPINE:197 · ADDRESSED_TRANSPORT_CHAIN:237"),
    ], "flex: 1 1 0")
    right = col([
        typ("Lattice", ["sites: Occurrence[] (ℤⁿ coordinates in a chart)", "incidence: oriented, exact, ∂² = 0", "cells: 0..k", "members may present an internal lattice (recursion)"],
            "lattice = founded incidence; crystal adds locked phase transport; fractal recurs under restriction/rebase", "docs/canon/TABLET_THE_REASONING_CYCLE.md:487 · blueprint ATHENA_ALPHA:309"),
        typ("Site / Arc / Junction", ["site: capacity", "arc: one conducting channel (ordered)", "junction: current distributes (co-present)"],
            "the site carries capacity, the passage carries characteristic delay; chronology is not seriality", "docs/canon/THE_SURFACES_ARE_PATHS.md:79,99"),
        typ("Current / Storage / Boundary map", ["q: locally stored response", "j: transported current", "B: incidence", "r: supplied residual", "law: q_{k+1} − q_k + B j_k = r_k"],
            "current and form are roles: a relation is current while crossing a selected cut, form when retained for a later cut", "docs/canon/02_INFORMATION_PHYSICS.md:35,48,53"),
        typ("Membrane", ["ports: crossing points (ingress/egress = one membrane, two orientations)", "phase: distributed local sampling", "radiation, return"],
            "a clock is a distributed local phase and sampling membrane, not a global instant", "docs/canon/02:67 · blueprint WORLD_TUBE:91"),
        typ("ReconstructionFiber", ["quotient: q_R", "population: predecessors compatible with one observed future class", "separator: shortest reopening history"],
            "RF(D_K,R;[y]) = (q_R ∘ D_K)⁻¹([y]); not a probability, a nearest neighbour, or a chosen representative", "docs/canon/TABLET_THE_OPERATIONS.md:275"),
        typ("Grade", ["truth: definition | project-postulate | proved-standard | proved-derived | established-bounded | conditional | interpretation | conjecture | counterexample | open | historical", "evidence: formal-checked | implemented-exact | measured | computational-witness | source-inspected | source-audit | process-audit"],
            "exactly one truth grade, zero or more tags; orthogonal", "docs/canon/EPISTEMIC_GRADES.md"),
    ], "flex: 1 1 0")
    body = row([left, mid, right], "flex: 1 1 auto; min-height: 0") + note("Each type here is a <b>reading</b> of an existing canon definition, not a proposed struct: the Crate page names which existing Rust owner already carries it and where the CAD would add only a projection. Field lists are top-level and illustrative of what a document must retain; none is a database schema.")
    return artboard("Ontology — the types every face is drawn from", "occurrence · holon · addressed passage · port · receiver · face · swing · chain · cell · lattice · current · membrane · fibre · grade", 1560, 1060, body,
                    "sources: canon glossary extraction 2026-08-30 (00_PURE_HOLONICS, 01_CAUSAL_CALCULUS, 02_INFORMATION_PHYSICS, 07, 08, SPINE, OPERATIONS, REASONING_CYCLE, EPISTEMIC_GRADES) · AGENTS.md")

@board("TypesTrace.dc.html", "Types 2 — the trace: what paperproof emits and what the CAD keeps", 1560, 980, "page-ontology")
def types_trace():
    pp = panel("paperproof wire format (verbatim, lean/Services/BetterParser.lean · app/types/LeanProofTree.ts)", code(
"""structure Hypothesis where            -- id = fvarId (_uniq.N)
  username type : String ; value : Option String ; id : String ; isProof : String  -- "proof"|"universe"|"data"
structure GoalInfo where              -- id = mvarId ; BEq by id only
  username type : String ; hyps : List Hypothesis ; id : MVarId
structure ProofStep where
  tacticString : String ; goalBefore : GoalInfo ; goalsAfter : List GoalInfo
  tacticDependsOn : List String         -- fvarIds, from collectFVars on the assignment
  spawnedGoals : List GoalInfo          -- orphan mvars: have / by / calc bodies
  position : ProofStepPosition ; theorems : List TheoremSignature
-- TS render model: Box {id, parentId ∈ {box, "haveBox", "byBox"}, goalNodes, hypLayers, hypTables}
--                  Tactic {goalArrows, hypArrows, successGoalId, haveBoxIds, byBoxIds, dependsOnIds}
--                  equivalentIds : { displayedId ↦ inferiorId[] }   -- one-level alias table""") +
        note("edges are semantic: goal parent/child from <span class='mono'>Meta.collectMVars</span> on <span class='mono'>eAssignment</span>; hypothesis use from <span class='mono'>collectFVars</span>; no-op tactics vanish by <span class='mono'>commonGoals</span> removal; authored steps are those with <span class='mono'>stx.getSubstring?</span>"), "flex: 1 1 0")
    cad = panel("the CAD's trace types — the same objects, retyped as swings, with the dropped fibre retained", col([
        typ("TacticSwing : Swing (AGENTS.md:99 · paperproof ProofStep)", ["before: GoalOccurrence (mvarId, lctx snapshot t)", "operator: TacticInfo {syntax, elaborated Expr, theorems: TheoremSignature[]}", "after: GoalOccurrence[] (owed) · spawned: GoalOccurrence[] (side quests)", "receiver: goal type printed at mctxAfter", "hypotheses: HypOccurrence[] used (fvarId)", "orientation: rewrite hand ← / →, case hand", "boundary: box parent (tacticSeq | have | by | calc)", "grade: Grade (proved-derived · formal-checked pending until kernel event)", "fibre: {assignment Expr, dAssignment, mctx delta, rewrite locus, unification trace, instance trace}"],
            "one authored tactic = one swing; t indexes the world-tube; the assignment is the reconstruction fibre"),
        typ("HypOccurrence / GoalOccurrence (paperproof Hypothesis, GoalInfo · DerivationAtlas GoalFace)", ["id: fvarId | mvarId (Lean-minted, never invented)", "alias: EquivalentIds union (same object, new id)", "born: t · changed: t[] · cleared: t? (retained, drawn refused — not dropped)", "isProof: proof | data | universe", "type: Expr (binder info, universes kept) + pretty face"],
            "two-key identity: id first, name second, alias table for rewrites"),
        typ("Frame (stack) (paperproof Box.parentId · AGENTS.md circulation)", ["kind: tacticSeq | have | by | calc | case", "goal owed, hyps in scope, depth", "children: Frame[]"],
            "the call/return stack is a receiver shadow of nested boundary transport — drawn, never an owner"),
        typ("WorldEvent (AGENTS.md mathematical production boundary)", ["kind: kernel-accepted | kernel-refused | sorry-open | timeout", "attached_to: projected passage id", "receipt: toolchain, imports, axioms"],
            "kernel acceptance is a later world occurrence attached to one projected passage, never a phase or gate"),
    ]), "flex: 1 1 0")
    lower = panel("what a lower-level trace must add (paperproof stops at strings)", table(["level", "paperproof", "CAD retains", "why it matters for auto-formalization"], [
        ["term-mode proofs", "one opaque step", "TermInfo tree as swings", "an LLM's `exact ⟨p, hp⟩` must be inspectable step by step"],
        ["mvar assignment history", "before/after only", "every mctx snapshot, delayed assignments", "replay is deterministic only with the full history"],
        ["elaboration order", "dropped", "unification + synthInstance trace, postponed problems", "the shortest separating intervention lives here"],
        ["universe levels / implicits", "dropped", "Expr + Level kept", "universe errors are the commonest auto-formalizer failure"],
        ["rewrite locus", "whole-type string diff", "subterm path, motive, at-* fan-out", "a rewrite is a transport with an address"],
        ["disappeared hypotheses", "opacity", "refused occurrence with t", "nothing leaves the route space silently"],
    ]), "flex: 0 0 auto")
    body = row([pp, cad], "flex: 1 1 auto; min-height: 0") + lower
    return artboard("Trace types — what paperproof emits and what the CAD keeps", "the deterministic debugger needs the fibre paperproof drops: Expr, assignment history, elaboration order, rewrite locus", 1560, 980, body,
                    "sources: Paper-Proof/paperproof 69401f7 · AGENTS.md:99 typed swings · AGENTS.md mathematical production boundary")

@board("TypesCarrier.dc.html", "Types 3 — the Complex Parametron carrier as a computational object", 1560, 960, "page-ontology")
def types_carrier():
    carrier = panel("the carrier (canon §8d, verbatim role)", code(
"""(addressed coefficient nodes,
 oriented carrier incidence B,
 exact complex current c,
 declared receiver form M,
 pulled storage G = B^T M B,
 kernel(B), kernel(G), lineage, open exterior)

realized section   : B c
receiver storage   : c* G c = (B c)* M (B c)
reorientation      : transports B and M together; storage and generalized LC response preserved
intervention       : holding drive or mutual coupling fixed
binary parametron  : the sign face — an exact quotient ONLY on the declared locked population
lattice            : a population of carriers through typed shared incidence; each member may
                     present a further internal lattice""") +
        note(grade("proved-derived") + " " + tag("formal-checked") + " Millennium/HolonicParametron.lean (two half-turn-related locked sheets; cosine coupling → Ising only after the lock) and Millennium/HolonicComplexParametron.lean (B, M, G = BᵀMB, reorientation covariance) — docs/canon/TABLET_THE_REASONING_CYCLE.md:460–495"), "flex: 1 1 0")
    types_ = panel("as CAD types — a component instance, its finite lattice, its tick", col([
        typ("ParametronCarrier", ["nodes: Site[n] (addressed coefficient nodes)", "branches: OrientedEdge[m] — B : m×n, entries {−1,0,1}", "c: Vec&lt;Exact&lt;ℂ&gt;&gt;ⁿ — ℚ(i) / ℚ(ζ_k) / multiquadratic tower", "M: Hermitian m×m exact (per-branch L, C, R; mutual coupling off-diagonal)", "G: derived = BᵀMB (never stored as truth)", "ker_B, ker_G: retained fibres", "drive: Pump? (ω exact phase, parametric)", "lineage: growth rule + signature", "exterior: Port[] undeclared"],
            "the productive object; width, branch count and lock do not bound its semantic capacity"),
        typ("Tick (transport swing)", ["law: DiscreteInduction | DiscreteMaxwell | MembraneAction", "before: c_t · after: c_{t+1}", "receipts: ∂²=0, Stokes, storage equality, reorientation covariance", "interventions: drive/coupling changes recorded, never folded into the law"],
            "one tick = one swing; the receipts are kinematic; conservation owes storage, current, source, constitutive, boundary and chronology laws"),
        typ("LockedFace (binary Parametron)", ["quotient: sign of phase on the locked population", "loss: the other sheet + relative phase (named, retained)", "valid_on: locked population only"],
            "a later receiver chart; a perceptron is the exterior ML comparison of this face"),
        typ("CoupledLattice", ["members: ParametronCarrier[]", "shared: typed shared incidence (node identification through junction components)", "recursion: member.internal : CoupledLattice?"],
            "the product's Athena-shaped object: a simplicial/cellular ecology of Complex Parametrons"),
    ]), "flex: 1 1 0")
    refuse = panel("what these types must not become", row([
        box("refused", "no <span class='mono'>Parametron</span>, <span class='mono'>Perceptron</span>, <span class='mono'>Circuit</span>, <span class='mono'>Layer</span> or <span class='mono'>Scheduler</span> subsystem — the carrier composes the existing exact-linear, complex-wave, incidence, receiver-fibre, morphology and resident-apparatus owners (canon §8d project-postulate)"),
        box("refused", "no float determines an index, coefficient, topology, identity or a committed bit; a displayed magnitude is a face (AGENTS.md apparatus)"),
        box("refused", "no condensation of a direction unless every declared future receiver factors through it, with the fibre and shortest reopening separator retained"),
    ]), "flex: 0 0 auto")
    body = row([carrier, types_], "flex: 1 1 auto; min-height: 0") + refuse
    return artboard("Carrier types — the Complex Parametron as a computational object", "an oriented incidence, an exact complex current, a receiver form, a pulled storage; its finite lattice transports action like electricity, literally", 1560, 960, body,
                    "sources: docs/canon/TABLET_THE_REASONING_CYCLE.md §8d · AGENTS.md causal arithmetic clause on the Complex Parametron · Millennium/HolonicComplexParametron.lean · HolonicParametron.lean")
