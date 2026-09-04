from lib import *
from gen import board, note_on

@board("Main.dc.html", "Atlas — one native complex, four faces", 1560, 920, "page-atlas")
def atlas():
    # central diagram
    d = s_arrow_defs()
    cx, cy = 470, 300
    d += s_rect(cx-150, cy-60, 300, 120, "ink", 8, 'fill="#fffdf8"')
    d += s_text(cx-138, cy-36, "ONE NATIVE COMPLEX (one owner)", "svgtxt")
    d += s_text(cx-138, cy-18, "operation / state-transition complex", "svgtxt")
    d += s_text(cx-138, cy-2, "incidence · ordered transport words · event readings", "svgtxt")
    d += s_text(cx-138, cy+14, "· open exterior · complete reconstruction fibre", "svgtxt")
    d += s_text(cx-138, cy+34, "grades per object · lineage · retained kernels", "svgtxt")
    d += s_text(cx-138, cy+50, "no Interpreter / Scheduler / Circuit cabinet", "svgtxt")
    faces = [("TRACE FACE", "time: swings t₀…tₙ", "goal/hyp boxes · tactic species · stack", cx-330, cy-200),
             ("SCHEMATIC FACE", "incidence: components + nets", "ports · passages · ERC", cx+30, cy-200),
             ("LATTICE FACE", "space: ℤⁿ sites, projection chart", "CSG program · constraints · DOF", cx-330, cy+140),
             ("TRANSPORT FACE", "action over time: exact current", "probes · storage cᴳc · receipts", cx+30, cy+140)]
    for (t, s1, s2, x, y) in faces:
        d += s_rect(x, y, 300, 62, "ink", 6, 'fill="#efece4"')
        d += s_text(x+10, y+18, t, "svgtxt", 'font-weight="500"')
        d += s_text(x+10, y+34, s1, "svgtxt"); d += s_text(x+10, y+50, s2, "svgtxt")
        # arrow from complex to face (a face is a reading; arrow points to the face)
        fx, fy = x+150, (y+62 if y < cy else y)
        d += s_line(cx + (fx-cx)*0.36, cy + (fy-cy)*0.5, fx, fy, "wire", 'marker-end="url(#ah)"')
        d += s_text(cx + (fx-cx)*0.36 + (8 if fx>cx else -60), cy + (fy-cy)*0.5 + (14 if fy>cy else -6), "⟨face|", "svgmath")
    # lean codec port (left) and provenance (right)
    d += s_rect(20, cy-40, 150, 80, "ink", 6, 'stroke-dasharray="4 3" fill="#fffdf8"')
    d += s_text(30, cy-20, "LEAN CODEC PORT", "svgtxt", 'font-weight="500"')
    d += s_text(30, cy-4, "source → InfoTree →", "svgtxt"); d += s_text(30, cy+12, "swings; kernel verdict", "svgtxt")
    d += s_text(30, cy+28, "= later world event", "svgtxt")
    d += s_line(170, cy, cx-150, cy, "wire", 'marker-end="url(#ah)" marker-start="url(#ah)"')
    d += s_rect(cx+180, cy-40, 160, 80, "ink", 6, 'stroke-dasharray="4 3" fill="#fffdf8"')
    d += s_text(cx+190, cy-20, "PROVENANCE / GRADES", "svgtxt", 'font-weight="500"')
    d += s_text(cx+190, cy-4, "holonic-json-v1 faces,", "svgtxt"); d += s_text(cx+190, cy+12, "claim index, cursors,", "svgtxt")
    d += s_text(cx+190, cy+28, "typed swings recorded", "svgtxt")
    d += s_line(cx+150, cy, cx+180, cy, "wire", 'marker-end="url(#ah)"')
    diagram = svg(960, 520, d)

    thesis = col([
        note("<b>What this is.</b> Wireframes for a CAD in which a Lean development is designed the way a board or a part is designed: one native complex owns the mathematics; the proof trace, the circuit schematic, the nD lattice geometry, and the action-transport simulation are four <i>receiver faces</i> of that one object. Lean is the exterior codec and checker port; the kernel's verdict is a later world event attached to a projected passage (AGENTS.md, mathematical production boundary)."),
        note(grade("definition") + " A <b>swing</b> is the unit of every face: before occurrence, operator/current, after occurrence, receiver, hypotheses, orientation, boundary, truth grade, complete reconstruction fibre. A tactic step, a wire, a lattice edge, and a transport tick are each one swing read through one face."),
        note(grade("definition") + " A <b>component</b> is a holon: a composite of holons with typed ports, one constitutive law, a rewrite rule with a fallback base case, and three linked projections — symbol, lattice footprint, Lean structure — the way a KiCad part links symbol, footprint, and 3D model."),
        note(grade("project-postulate") + " The <b>Complex Parametron</b> is the primitive computational component: (addressed coefficient nodes, oriented incidence <span class='math'>B</span>, exact complex current <span class='math'>c</span>, receiver form <span class='math'>M</span>, storage <span class='math'>G = BᵀMB</span>, kernels, lineage, open exterior). Its finite lattice transports action exactly — no float in the semantic cone — and a population of them forms a lattice by typed shared incidence (docs/canon/TABLET_THE_REASONING_CYCLE.md §8d)."),
        note(grade("interpretation") + " Everything on these pages is design testimony. No capability is asserted implemented; every proposed owner names the existing owners it composes and the absent type that would justify it (Crate branch page)."),
    ], "flex: 0 0 540px")

    species = row([
        sp("construction"), sp("transport"), sp("face"), sp("quotient"), sp("deposit"), sp("receiver"), sp("refused", "obstruction"),
    ], "flex-wrap: wrap; gap: 6px")
    legend = panel("Colour tells you what a thing is (species, docs/canon/TABLET_THE_OPERATIONS.md §1)", species + note("construction composes and keeps residue · transport carries between charts · face reads and says what it forgets · quotient identifies and names the collapsed population · deposit |a⟩⟨a| turns a construction into terrain · receiver ⟨φ| is the bra · obstruction is a returned refusal, never an error."))

    pages = panel("Pages of this canvas", table(["page", "what it holds"], [
        ["Atlas", "this thesis, the reference-extraction matrix, the ten sources and what each lends"],
        ["Ontology and types", "type sheets: document, swing/trace, component, lattice, transport, identity, file format, grades"],
        ["Views", "wireframes of every workspace face: trace/debugger, schematic, lattice (nD), transport, growth/code, library, notation, interaction, constraints, provenance"],
        ["Component library", "parametric component sheets — Complex Parametron first — each with symbol · footprint · Lean model · ports · rule · ERC"],
        ["Machinery", "pipelines lifted from the references and retyped: extraction, growth, connection graph, constraint solve, transport tick, recompute, identity"],
        ["Crate branch", "how this composes the existing holonics crates; the absent types; what must not be founded"],
        ["Archive", "the previous draft (the descent at five) and the cached prototypes, untouched"],
    ]))

    body = row([thesis, col([diagram, legend], "flex: 1 1 auto")], "flex: 0 0 auto") + pages
    return artboard("Holonic CAD — atlas", "a Lean development designed like a board, a part, and a circuit at once · low-fidelity wireframe blueprint", 1560, 920, body,
                    "draft 1 · 2026-08-30 · graded per claim; the canvas as a whole is interpretation")

note_on("n-atlas-1", "page-atlas", 1680, 0, 300, "Reading order: Atlas → Ontology → Views → Library → Machinery → Crates. Each artboard names its sources (canon path or reference repo + commit). Nothing here schedules construction; the roadmap is CONS1 and UAR is frozen.")

@board("AtlasMatrix.dc.html", "Atlas 2 — the ten references and what each lends", 1560, 1100, "page-atlas")
def atlas_matrix():
    rows = [
        ["<b>paperproof</b> (69401f7)", "ProofStep {goalBefore, goalsAfter, spawnedGoals, tacticDependsOn}; Box/Tactic; equivalentIds", "Lean fvarId/mvarId, alias union", "InfoTree walk → mctx diff → semantic edges → flat steps → pure converter", "the trace face: boxes, read-towards-the-middle, assignment-driven edges, orphan = side quest", "term mode, assignment history, elaboration order, rewrite locus"],
        ["<b>MorphoHDL</b> (dc8dd2e)", "cellDef {ssa, fallback}; SoA cells/pins/nets; registry name:[sig]", "append-only index, active flag, parent lineage", "materialize on demand → local rewrite per step → const-prop/DCE worklists → force layout", "component = rule + fallback; width inferred; geometry co-grows by division; order-independent growth", "timing, physical law, 3D, cycles/state, exact arithmetic"],
        ["<b>OpenSCAD</b> (1c9ee2b)", "AST (Expression, ModuleInstantiation, LocalScope); AbstractNode tree; CSG term; Value variants", "idx reset per compile; modinst → syntax", "parse → evaluate → CSG → Goldfeather normalize → geometry (Manifold/CGAL) → preview/render", "program-as-model; ! # % * modifiers; customizer from top-level literals + comments; $preview split; text dump is the interchange", "state, constraints, assemblies, stable topology names, doubles only"],
        ["<b>SolveSpace</b> (3297d9a)", "Request → Entity → Param; Constraint → Equation{Expr}; Group; SolveResult", "handles: request&lt;&lt;16 | idx; persisted remap", "requests generate; equations; substitution; symbolic Jacobian; rank/DOF; leave-one-out; free params", "declared vs generated; sequential groups; type-blind solver; four result states; soft drag; charts as entities", "doubles; 2048 unknowns; no exact carrier"],
        ["<b>KiCad</b> (master, kicad_sch 20250114)", "SCH_SYMBOL/LIB_SYMBOL/SCH_PIN with ELECTRICAL_PINTYPE; SCH_LINE wire/bus; SCH_LABEL kinds; SCH_SHEET + sheet pins; CONNECTION_GRAPH; BOARD/FOOTPRINT/PAD/NET", "KIID uuid per item; sheet-path instance references", "geometry + labels → connection graph → nets → ERC matrix; netlist; SPICE via Sim.* fields; DRC rules language", "symbol · footprint · 3D triple; typed pins + PIN_ERROR matrix + drive lattice make contact checkable; per-path identity (KIID_PATH, SCH_SYMBOL_INSTANCE); nets derived by a PRIORITY driver lattice; netclass attributes carry their source; COMMIT stages pre-images", "no dynamics (only SPICE export), no solver, undirected nets, fields are strings, 2.5D"],
        ["<b>FreeCAD</b> (main 3b2c969)", "DocumentObject + typed Property catalogue; DepEdge; ExpressionEngine; Sketcher Constraint (22 types) → planegcs (37); TopoShape names", "Name vs Label; topological naming (IndexedName / MappedName)", "buildDependencyList → topological sort → expressions(non-output) → execute → expressions(output); DogLeg/LM/BFGS; diagnose DOF/conflicting/redundant", "everything is a node with typed properties in a recomputed DAG; expressions with units; links with scope; errors as data on the node", "exactness; provenance-stable names are the hard problem"],
        ["<b>LibreCAD</b> (master a05b426)", "RS_Entity hierarchy (50 types) with Data structs; RS_EntityContainer; RS_Layer; RS_Block/RS_Insert; RS_Pen ByLayer/ByBlock", "immortal undoables with a deleted flag", "action = state machine on coordinate/command events; snapper bitmask; RS_Information intersections; RS_Modification statics", "actions resumable and scriptable; snapping as nearest-candidate with evidence; blocks as parameterless instancing", "3D, constraints, semantics"],
        ["<b>GElectrical</b> (47082c7)", "ElementModel {ports, fields{value,type}, schem_model, text_model, res_fields}; get_nodes; get_power_model", "code registry; gnodes derived", "port coincidence → connected components → networkx graph → pandapower → results as elements", "element = glyph + terminals + typed record + projections; results typed like inputs; rules as data over the derived graph", "exactness; schema lives in code"],
        ["<b>QElectroTech</b> (899f105)", "element XML (primitives, terminals, kindInformations, link_type); Conductor between terminal uuids; Diagram folio grid; CrossRefItem", "QUuid per element/terminal/conductor; master/slave, next/previous report", "potential by DFS at query time; formula autonumbering propagated over the potential; %f-%l%c grid addresses", "link types = identity across folios; cross-reference glyphs from grid addresses; collections common:// custom:// embed://", "simulation; semantics beyond documentation"],
        ["<b>circuitikz</b> (b882b15)", "\\pgfcircdeclarebipolescaled {class, anchors, extents, drawing}; node shapes with named anchors; v/i/f decorations", "names per path (random if absent)", "to-path: midpoint node rotated to the path, leads to .left/.right, decorations in the local frame; subcircuit anchors pre-measured", "path-style vs node-style; typed oriented decorations; style as a key hierarchy separate from geometry; subcircuits placed by any anchor", "no model at all — a codec"],
    ]
    t = table(["reference", "primary objects", "identity", "pipeline", "lifted into the CAD as", "not modelled (we add)"], rows)
    body = col([t, note("Grades: every cell is <span class='mono'>source-inspected</span> testimony from sparse read-only clones taken 2026-08-30 (commits in parentheses); KiCad cells cite common/pin_type.h, erc_settings.cpp, connection_graph.h, kiid.h and the dev-docs s-expression pages. The right two columns are <span class='mono'>interpretation</span>: what this design lifts, and what it must add because the reference stops there.")], "flex: 1 1 auto; min-height: 0")
    return artboard("The ten references and what each lends", "data types and machinery conventions extracted, then retyped as holonic faces", 1560, 1100, body,
                    "sources: paperproof · MorphoHDL · OpenSCAD · SolveSpace · KiCad · FreeCAD · LibreCAD · GElectrical · QElectroTech · circuitikz (reports 2026-08-30)")

note_on("n-atlas-2", "page-atlas", 1680, 200, 300, "Starred references (paperproof, MorphoHDL, OpenSCAD, SolveSpace, KiCad) each own at least one Views artboard and one Machinery artboard; the five others contribute rows to Library 0, Machinery 3/6/7 and this matrix.")
