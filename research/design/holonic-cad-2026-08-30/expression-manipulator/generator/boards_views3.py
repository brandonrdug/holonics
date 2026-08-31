from lib import *
from gen import board, note_on
import boards_library as L

# ---------- V2 schematic ----------
@board("ViewSchematic.dc.html", "View 2 — Schematic: components and nets", 1560, 1000, "page-views")
def view_schematic():
    tb = toolbar([btn("sheet: root / membrane M₁ (instance path /a1b2/)"), btn("place component"), btn("wire"), btn("bus"), btn("junction"), btn("label"), btn("hier. label"), btn("sheet (membrane)"), btn("no-connect"),
                  '<span class="lbl" style="margin-left:8px">check</span>', btn("ERC ✓ 0 refusals · 1 open exterior"), btn("net navigator"), btn("→ lattice"), btn("→ transport"), btn("→ trace")])
    d = s_arrow_defs()
    # two parametrons, a pump, a receiver probe, a junction, a membrane sheet
    def cp(x, y, name):
        inner, pts = L.ring_glyph(x, y, 26, ("", "", ""))
        out = inner + s_rect(x-42, y-40, 84, 80, "ink", 8, 'stroke-dasharray="4 3"') + s_text(x-40, y-46, name, "svgtxt")
        return out, pts
    a, pa = cp(220, 200, "CP₁ · B 3×3 · M(1/2,3,0)"); d += a
    b, pb = cp(470, 200, "CP₂ · B 3×3 · M(1/2,3,0)"); d += b
    # shared node wire between CP1.n1 and CP2.n2 with junction
    d += s_line(pa[1][0], pa[1][1], 340, pa[1][1], "wire", 'stroke-width="2"'); d += s_line(340, pa[1][1], pb[2][0], pb[2][1], "wire", 'stroke-width="2"')
    d += s_circ(340, pa[1][1], 5, "ink", 'fill="#292418"'); d += s_text(330, pa[1][1]-10, "J₁ (+,+,−)", "svgtxt")
    d += s_line(340, pa[1][1], 340, 300, "wire", 'stroke-width="2"'); d += s_text(346, 300, "N₃ · shared", "svgtxt")
    # pump
    d += s_circ(120, 90, 18, "ink"); d += s_path("M 105 90 q 7 -12 15 0 t 15 0", "ink"); d += s_text(100, 60, "P₁ ω=2π/12", "svgtxt")
    d += s_line(138, 90, 220, 90, "wire"); d += s_line(220, 90, 220, 160, "wire", 'marker-end="url(#ah)"'); d += s_text(150, 84, ".pump", "svgtxt")
    # receiver probe on N3
    d += s_path("M 400 300 L 380 320 L 400 340", "ink", 'stroke-width="2"'); d += s_line(340, 300, 380, 320, "grey"); d += s_text(404, 326, "⟨ρ₁| probe", "svgtxt")
    # hierarchical sheet = membrane
    d += s_rect(600, 120, 170, 150, "ink", 10, 'stroke-dasharray="6 4" stroke-width="2" fill="#fbf8f2"'); d += s_text(608, 138, "M₁ membrane sheet", "svgtxt"); d += s_text(608, 154, "file: sheet4.holon · 2 instances", "svgtxt")
    d += s_rect(596, 190, 8, 10, "ink", 2, 'fill="#3c6ea5"'); d += s_text(560, 198, "in", "svgtxt"); d += s_line(pb[1][0], pb[1][1], 596, 195, "wire", 'stroke-width="2"')
    d += s_rect(766, 230, 8, 10, "ink", 2, 'fill="#b04e4e"'); d += s_text(778, 238, "out (radiation)", "svgtxt"); d += s_line(774, 235, 840, 235, "wire", 'marker-end="url(#ah)"')
    # labels
    d += s_text(300, 150, "N₁", "svgtxt"); d += s_rect(292, 138, 24, 16, "ink", 3, 'fill="#efece4" stroke="none"'); d += s_text(297, 150, "N₁", "svgtxt")
    d += s_text(860, 240, "global label: RAD_1", "svgtxt")
    # ERC refusal
    d += s_circ(pa[0][0], pa[0][1], 9, "grey", 'stroke="#9c5480" stroke-width="2" stroke-dasharray="3 2"'); d += s_text(60, 330, "ERC: CP₁.n0 exterior — open, visible (dashed ring)", "svgtxt")
    canvas = svg(900, 380, d, "width:100%; height:auto")
    left = panel("canvas · symbols with typed ports; nets are derived from wire geometry + labels by the connection graph, never authored", canvas +
                 note("a wire is a passage with both boundary maps (Library 3); a junction is a component with hands (Library 5); a hierarchical sheet is a membrane whose interior is instanced per path (Library 7) — the same file placed twice gives two instances with per-path identity (KiCad sheet-path instances)"), "flex: 1 1 auto")
    props = panel("properties · CP₂", kv([("lib_id", "holonic:ComplexParametron"), ("at", "(470, 200, 0) · chart z4 / 3+1"), ("unit", "1 of 1"), ("uuid", "occurrence (born 12, rank 3)"), ("params", "n=3 · M=(1/2,3,0) · ω=2π/12 · lock=off"),
                                          ("symbol", "holonic-sym: cp3 · anchors .n0 .n1 .n2 .pump"), ("footprint", "lattice: oriented_cycle 3 · placed at (1,1,1,0)"), ("model", "Millennium/HolonicComplexParametron.lean · complexParametronHolon"), ("grade", "model " + grade("proved-derived") + " " + tag("formal-checked") + " (HolonicComplexParametron.lean); this instance: unchecked")]), "flex: 0 0 auto")
    nets = panel("net navigator · connection graph result", table(["net", "members", "kind", "check"], [
        ["N₁", "P₁.out → CP₁.pump", "pump", "ok"], ["N₂", "CP₂.n1 → M₁.in", "shared → return", "ok"], ["N₃", "CP₁.n1 · J₁ · CP₂.n2 · ⟨ρ₁|", "shared + receiver", "ok"],
        ["RAD_1", "M₁.out → global label", "emission", "ok"], ["—", "CP₁.n0", "exterior", "<span class='sp sp-quotient'>open</span> stays visible"]]), "flex: 0 0 auto")
    right = col([props, nets, panel("ERC · pairwise contact rules (Library 0)", box("obstructed", "1 open exterior · 0 refusals · 0 warnings — a refusal would be a returned obstruction drawn on the net, never a dialog that blocks"), "flex: 0 0 auto")], "flex: 0 0 420px")
    body = tb + row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Schematic — components and nets", "KiCad's schematic capture retyped: symbol · footprint · model triple, typed pins, derived nets, hierarchical sheets as membranes, ERC as contact rules", 1560, 1000, body,
                    "sources: KiCad master (kicad_sch 20250114): sch_symbol.h SCH_SYMBOL_INSTANCE {KIID_PATH, Reference, Unit}, sch_sheet_path.h, sch_connection.h CONNECTION_TYPE, connection_graph.h CONNECTION_SUBGRAPH · GElectrical networkmodel.py · QET link types · canon ports/junction/membrane")

# ---------- V6 library browser ----------
@board("ViewLibraryBrowser.dc.html", "View 6 — Component library browser", 1400, 900, "page-views")
def view_library():
    tree = panel("collections · scheme-addressed, embeddable (QET common:// custom:// embed://)", col([
        box("lean", "<b>holonic://</b> canon-owned<br>&nbsp;&nbsp;carriers: Complex Parametron · Site · Edge · Coupling · Pump<br>&nbsp;&nbsp;receivers: ⟨ρ| · Chart · Quotient/lock · Deposit<br>&nbsp;&nbsp;interactions: Junction · Vertex · Membrane<br>&nbsp;&nbsp;trace: Tactic swing · Hypothesis · Goal"),
        box("hyp", "<b>project://</b> this document's own rules (tree, tube, chain, medusa…)"),
        box("hyp", "<b>embed://</b> copies of every definition this document uses (the file is self-contained)"),
        box("hyp", "<b>foreign://</b> exterior codecs: SPICE model, circuitikz macro, KiCad symbol — lineage only, never state"),
    ]), "flex: 0 0 360px")
    grid = panel("browser · search by kind, port signature, Lean structure, grade", toolbar([btn("search: parametron"), btn("kind: carrier"), btn("ports: shared×3 + pump"), btn("grade ≥ proved-derived"), btn("has Lean model ✓")]) +
                 '<div style="display:grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 10px">' +
                 ''.join(f'<div class="box box-lean" style="display:flex; flex-direction:column; gap:4px">{ph(90, "100%", g)}<div class="mono" style="font-size:10.5px">{n}</div><div class="meta">{m}</div></div>' for (g, n, m) in [
                     ("symbol · footprint · model", "ComplexParametron", "n:int · M:exact · ω:phase · proved-derived"), ("symbol", "Receiver ⟨ρ|", "chart:enum · definition"), ("symbol · footprint", "Junction", "arms:int · hands · definition"),
                     ("symbol", "Pump", "ω,φ exact · proved-derived"), ("symbol · footprint", "Membrane", "ports:list · definition"), ("rule", "tree (project)", "fallback:=chain · est. 61 cells"),
                 ]) + '</div>' + note("each card is the KiCad symbol-chooser triple: the glyph, the footprint preview, the model; the preview is rendered from the rule at signature [3], not from a stored bitmap"), "flex: 1 1 auto")
    inspect = panel("preview · ComplexParametron [3]", ph(140, "100%", "symbol at signature [3] · anchors labelled") + kv([("parameter sets", btn("default") + " " + btn("locked-binary") + " " + btn("torus-4")), ("presets file", "<span class='mono'>ComplexParametron.params.json</span> (OpenSCAD parameterSets shape)"), ("used by", "this document · 2 instances (sample)"), ("provenance", "canon §8d · Lean file · claim H.0476")]), "flex: 0 0 340px")
    body = row([tree, grid, inspect], "flex: 1 1 auto; min-height: 0")
    return artboard("Component library browser", "a card is a symbol, a footprint and a model; collections are scheme-addressed and embeddable; parameter sets ride beside the rule", 1400, 900, body,
                    "sources: KiCad symbol chooser + lib tables (form) · QElectroTech collections common:// custom:// embed:// · OpenSCAD parameter sets JSON")

# ---------- V11 workspace shell ----------
@board("ViewWorkspace.dc.html", "View 11 — Workspace: one selection, four faces", 1560, 1000, "page-views")
def view_workspace():
    tb = toolbar([btn("parametron_lattice.holon"), btn("Lean: pending"), btn("t = 7 / 20"), btn("chart 3+1"), btn("grade filter: all"), '<span class="lbl" style="margin-left:8px">layout</span>', btn("quad", True), btn("trace | lattice"), btn("schematic | transport"), btn("single")])
    def face(title, content, w="1 1 0"):
        return panel(title, content, f"flex: {w}")
    q = row([face("trace face", ph(300, "100%", "swing graph · t=7 highlighted")), face("schematic face", ph(300, "100%", "CP₂.n2 net N₃ highlighted"))], "flex: 1 1 0") + \
        row([face("lattice face", ph(300, "100%", "site (1,1,1,0) highlighted · chart 3+1")), face("transport face", ph(300, "100%", "⟨ρ₁| trace · t=7 cursor"))], "flex: 1 1 0")
    center = col([q], "flex: 1 1 auto")
    side = panel("linked selection · the same occurrence in every face", kv([("selected", "occurrence (born 12, rank 3) — CP₂"), ("in trace", "swing t=7 rw [orient_neg] touched its storage lemma"), ("in schematic", "CP₂ on nets N₂, N₃"), ("in lattice", "3 sites, 3 edges at (1,1,1,0)"), ("in transport", "c₇ = (3/2 − i, 1/2, …) · |c|² = 13/4"), ("grade", "model " + grade("proved-derived") + " " + tag("formal-checked") + "; instance unchecked")]) +
        box("carried", "a face never edits the object: editing happens in the program (Lean) or through a projection port that emits a swing proposal; the faces re-project (OpenSCAD's from-scratch compile, incremental by touched frames — FreeCAD's DAG)") +
        box("lean", "keyboard: single letters place and constrain (SolveSpace convention) · Tab toggles the browser · Space regenerates · Esc unselects") +
        box("obstructed", "one apparatus rule: the UI is an exterior chart; nothing rendered re-enters the construction (blueprint/THE_PRESENTATION_ORGAN.md:261)"), "flex: 0 0 380px")
    body = tb + row([center, side], "flex: 1 1 auto; min-height: 0")
    return artboard("Workspace — one selection, four faces", "the quad layout: trace, schematic, lattice, transport are four readings of one native complex; selection is linked by occurrence identity", 1560, 1000, body,
                    "sources: Atlas thesis · OpenSCAD editor/viewer/console/customizer docks · FreeCAD combo view · SolveSpace keyboard convention")

# ---------- V12 auto-formalization ----------
@board("ViewAutoformalize.dc.html", "View 12 — Auto-formalization: an agent proposes swings, no chooser", 1560, 1000, "page-views")
def view_auto():
    tb = toolbar([btn("goal ?m.432 · box 3 · neg"), btn("ask agent for 4 candidate swings"), btn("route space"), btn("kernel: check all"), btn("grade gate: none — verdicts are events"), btn("human: pick or defer")])
    routes = panel("route space · every candidate is a retained fibre; nothing is erased when one is chosen (canon: OPEN does not choose)", col([
        row([box("carried", "<b>r₁</b> rw [orient_neg]; exact pullback_neg h<br><span class='meta'>kernel: accepted · 2 swings · theorems: pullback_neg · grade proved-derived</span>"),
             box("obstructed", "<b>r₂</b> simp [orient_neg, pullback_neg]<br><span class='meta'>kernel: refused — simp made no progress · obstruction retained: missing simp lemma</span>")]),
        row([box("refused", "<b>r₃</b> exact pullback_pos h<br><span class='meta'>kernel: refused STRUCTURALLY — h : orient = neg, expected pos · the node model is wrong here (TYPED_TRANSPORT_ATLAS verdict: Contradicted)</span>"),
             box("hyp", "<b>r₄</b> sorry<br><span class='meta'>open fibre · drawn dashed · never hidden · never counted as progress</span>")]),
        note("verdict kinds lifted from blueprint/THE_TYPED_TRANSPORT_ATLAS.md:251 — Decisive · OpenedAndFound (an atlas edge) · OpenedAndRefused (a genuine obstruction) · Contradicted (the node model is wrong). The agent's proposals are exterior occurrences; the kernel's verdicts are later world events attached to each projected passage."),
    ]), "flex: 1 1 auto")
    agent = panel("agent port · exterior codec, lineage only", kv([("who", "any model: provider identity never crowns a candidate (AGENTS.md)"), ("input", "the swing inspector's fibre for the selected goal — Expr, hyps, mctx, elab trace — never a pretty string alone"), ("output", "candidate TacticSwing proposals with claimed species and theorems"), ("recorded", "each proposal as an occurrence with lineage; each verdict as a world event"), ("measure", "shortest separating intervention between r₁ and r₂: the missing simp lemma — returned, not scored")]) +
        box("refused", "no accepted-count gate, no loss, no leaderboard: a scalar that measures is lawful, a scalar that governs is not (TABLET_THE_FLOW:38)") +
        box("carried", "the human and the agent see the same faces; auto-formalization is the same CAD driven through the same projection port"), "flex: 0 0 440px")
    body = tb + row([routes, agent], "flex: 1 1 auto; min-height: 0")
    return artboard("Auto-formalization — proposals as plural continuation", "an agent proposes candidate swings; the kernel returns verdicts as world events; the route space retains every fibre; no chooser quotient is taken silently", 1560, 1000, body,
                    "sources: blueprint/THE_TYPED_TRANSPORT_ATLAS.md:251,288 · canon/THE_HOLOBROCHOS_SPINE.md:201 · AGENTS.md dialogue/agent rollouts as world-tubes · TABLET_THE_FLOW.md:38")
