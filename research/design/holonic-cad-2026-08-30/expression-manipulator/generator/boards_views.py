from lib import *
from gen import board, note_on

def gutter_code(lines, cur=None, bps=(), marks=()):
    out = []
    for i, l in enumerate(lines, 1):
        g = "▶" if i == cur else ("◆" if i in bps else ("●" if i in marks else " "))
        out.append(f'<div style="display:flex; gap:8px; white-space:pre; {"background:#efece4" if i==cur else ""}"><span class="ln" style="width:22px; text-align:right; color:#b3a27d">{i}</span><span class="ln" style="width:12px; color:#a67a2e">{g}</span><span class="mono" style="font-size:10.5px">{esc(l)}</span></div>')
    return '<div style="display:flex; flex-direction:column; gap:1px; line-height:1.5">' + ''.join(out) + '</div>'

def tac(t, kind, text, cur=False):
    return (f'<div style="display:flex; align-items:center; gap:6px; padding:2px 4px; {"outline:2px solid #b45309; border-radius:6px" if cur else ""}">'
            f'<span class="ln" style="width:28px">t={t}</span>{sp(kind)}<span class="mono" style="font-size:10.5px">{esc(text)}</span></div>')

@board("ViewTrace.dc.html", "View 1 — Trace: the proof as a debugger", 1560, 1040, "page-views")
def view_trace():
    tb = toolbar([btn("Millennium/HolonicComplexParametron.lean"), btn("storage_pullback"),
                  '<span class="lbl">mode</span>', btn("tree", True), btn("single tactic"), btn("term / elaboration"),
                  '<span class="lbl" style="margin-left:10px">transport</span>', btn("⏮"), btn("⤴ step out"), btn("⏴ step over"), btn("⏵ step in"), btn("⏭"), btn("⟲ replay"),
                  '<div style="display:flex; align-items:center; gap:6px; margin-left:8px"><span class="lbl">t</span><div style="width:220px; height:6px; background:#ddd5c5; border-radius:3px; position:relative"><div style="position:absolute; left:0; top:0; height:6px; width:40%; background:#3c6ea5; border-radius:3px"></div><div style="position:absolute; left:40%; top:-4px; width:4px; height:14px; background:#292418; border-radius:2px"></div></div><span class="mono" style="font-size:10px">3 / 8</span></div>',
                  btn("◆ breakpoints"), btn("grade ≥ established")])
    src = [
        "theorem storage_pullback (P : ComplexParametron)",
        "    (c : P.Node → ℂ) :",
        "    cStar c (G P) c = cStar (B P c) (M P) (B P c) := by",
        "  unfold G",
        "  rw [Matrix.mul_assoc]",
        "  rw [← Matrix.mulVec_mulVec]",
        "  simp only [star_mulVec]",
        "  cases P.orient with",
        "  | pos h => exact pullback_pos h",
        "  | neg h =>",
        "      rw [orient_neg]",
        "      exact pullback_neg h",
    ]
    left = panel("source · gutter = swing marks (● tactic · ◆ breakpoint · ▶ t)", gutter_code(src, cur=6, bps=(8,), marks=(4,5,7,9,11,12)) +
                 note("sample proof, illustrative statement · every user-written tactic = one swing (paperproof: <span class='mono'>stx.getSubstring?</span> separates authored steps from macro noise)"), "flex: 0 0 400px")

    # swing graph (paperproof-shaped, read towards the middle, plus time index)
    root = (
        '<div style="border:1.5px dashed #8a8071; border-radius:8px; padding:8px; background:#fbf8f2; display:flex; flex-direction:column; gap:6px">'
        + lbl("box 1 · hypotheses descend") +
        row([box("hyp", "<span class='mono'>P</span> : ComplexParametron <span class='meta'>_uniq.301 · data · init</span>"),
             box("hyp", "<span class='mono'>c</span> : P.Node → ℂ <span class='meta'>_uniq.377 · data · init</span>")], gap=6)
        + tac(1, "transport", "unfold G") + tac(2, "transport", "rw [Matrix.mul_assoc]") + tac(3, "transport", "rw [← Matrix.mulVec_mulVec]", True)
        + tac(4, "transport", "simp only [star_mulVec]")
        + '<div style="display:flex; gap:10px; align-items:flex-end">'
        +   '<div style="border:1.5px dashed #8a8071; border-radius:8px; padding:6px; background:#f3efe6; flex:1">' + lbl("box 2 · pos") + box("hyp", "<span class='mono'>h</span> : P.orient = pos <span class='meta'>_uniq.401 ← t=5</span>") + tac(6, "transport", "exact pullback_pos h  — conjugacy; the closing read is the face") + box("goal", "<span class='math'>c*Gc = (Bc)*M(Bc)</span> <span class='meta'>?m.431</span>") + '</div>'
        +   '<div style="border:1.5px dashed #8a8071; border-radius:8px; padding:6px; background:#f3efe6; flex:1">' + lbl("box 3 · neg") + box("hyp", "<span class='mono'>h</span> : P.orient = neg <span class='meta'>_uniq.402 ← t=5</span>") + tac(7, "transport", "rw [orient_neg]") + tac(8, "transport", "exact pullback_neg h") + box("goal", "<span class='math'>c*Gc = (B'c)*M'(B'c)</span> <span class='meta'>?m.440 ← ?m.432</span>") + '</div>'
        + '</div>'
        + tac(5, "construction", "cases P.orient  — plural continuation: two retained fibres, no chooser")
        + box("goal", "<span class='math'>c*Gc = (Bc)*M(Bc)</span> <span class='meta'>?m.418 · after t=3</span>")
        + box("goal", "<span class='math'>c*(BᵀMB)c = (Bc)*M(Bc)</span> <span class='meta'>?m.412 · goal ascends</span>")
        + '</div>')
    center = panel("swing graph · hypotheses descend, goals ascend, the closing face sits where they meet · t indexes the world-tube", root +
                   note("boxes = nested boundary transports (paperproof <span class='mono'>Box.parentId ∈ {box, haveBox, byBox}</span>) · arrows are semantic: parent/child goal edges from <span class='mono'>collectMVars</span> on the assignment, dependencies from <span class='mono'>collectFVars</span> — never from tactic syntax · a branch is plural continuation, never a chooser; both fibres stay in the route space"),
                   "flex: 1 1 auto")

    insp = panel("swing inspector · t = 3", kv([
        ("before", "<span class='mono'>?m.415</span> <span class='math'>c*(BᵀM)(Bc) = …</span>"),
        ("operator", sp("transport") + " <span class='mono'>rw [← Matrix.mulVec_mulVec]</span>"),
        ("theorem", "<span class='mono'>Matrix.mulVec_mulVec</span> " + grade("proved-standard") + " Mathlib"),
        ("after", "<span class='mono'>?m.418</span>"),
        ("receiver", "goal type, read in <span class='mono'>mctxAfter</span>"),
        ("hyps used", "<span class='mono'>_uniq.377 c</span> (collectFVars on assignment)"),
        ("orientation", "← (rewrite hand reversed)"),
        ("boundary", "spawned goals: none · owed goals: 1"),
        ("grade", grade("proved-derived") + " " + tag("formal-checked pending")),
        ("fibre", "<span class='mono'>?m.415 := Eq.mpr (congrArg … ) ?m.418</span> — the assignment is the reconstruction fibre, retained"),
    ]) + lbl("below paperproof — retained here, not there") + table(["level", "what the CAD keeps", "source"], [
        ["term", "Expr with binder info, implicit args, universe levels", "TermInfo, not only TacticInfo"],
        ["assignment history", "eAssignment and dAssignment per intermediate mctx", "all mctx snapshots, not before/after only"],
        ["rewrite locus", "subterm path [1,0,2], motive, at-* fan-out", "rw elaboration"],
        ["elaboration order", "unification, postponed problems, synthInstance trace", "elab trace"],
        ["disappeared hyps", "kept as refused/cleared occurrences with t", "paperproof drops (opacity)"],
    ]), "flex: 0 0 400px")

    stack = panel("stack · nested boundary transports (receiver shadow of the call/return chart)", row([
        col([lbl("frames"), box("lean", "<span class='mono'>tacticSeq</span> storage_pullback · goals owed 1 · hyps 2"),
             box("carried", "<span class='mono'>rw [← Matrix.mulVec_mulVec]</span> · t=3 · current frame · box 1"),
             box("hyp", "<span class='meta'>later frames (t=5 cases … | pos | neg) are not yet entered at t=3</span>")], "flex:1"),
        col([lbl("watch · hypothesis lineage"), table(["name", "id", "born", "changed", "cleared"], [
            ["c", "_uniq.377", "init", "—", "—"], ["h", "_uniq.402", "t=5 cases (future at t=3)", "—", "—"], ["G-unfolded goal", "?m.412→?m.418", "t=1", "t=2,3,4 (alias table)", "—"]])], "flex:1.4"),
        col([lbl("world events, not phases"), box("obstructed", "kernel verdict: pending · attaches to the projected passage, never a gate"), box("refused", "sorry at t=… would be an open fibre, drawn dashed, never hidden")], "flex:0.9"),
    ]), "flex: 0 0 200px")

    body = tb + row([left, center, insp], "flex:1 1 auto; min-height:0") + stack
    return artboard("Trace — the proof as a debugger", "paperproof's box tree + a deterministic time index + the retained fibre paperproof drops", 1560, 1040, body,
                    "sources: Paper-Proof/paperproof 69401f7 (lean/Services/BetterParser.lean, app/types/*.ts) · docs/canon/TABLET_THE_REASONING_CYCLE.md §2")

@board("ViewGrowth.dc.html", "View 5 — Growth: program → lattice", 1560, 980, "page-views")
def view_growth():
    tb = toolbar([btn("parametron_lattice.lean"), '<span class="lbl">schedule</span>', btn("BFS", True), btn("largest-first"), btn("traced (DFS)"),
                  btn("▶ grow"), btn("⏸"), btn("step"), btn("re-grow"), '<span class="lbl" style="margin-left:8px">fanout ≤</span>', btn("4"),
                  btn("const-prop ✓"), btn("DCE ✓"), btn("export netlist · mask · holonic-json-v1")])
    src = [
        "-- primitive: a Complex Parametron cell, 3 nodes / 3 oriented branches",
        "def cell : Carrier := Parametron.ring 3",
        "",
        "@[holon fallback := cell]      -- rewrite rule + base case",
        "def chain (x : Bus) (n : Bus) : Bus :=",
        "  let (n0, n1) := SPLIT n      -- boundary if |n| < 2 → fallback",
        "  chain (couple (chain x n0)) n1",
        "",
        "@[holon fallback := 0]         -- pass argument 0 through",
        "def tube (x : Bus) (n : Bus) : Bus :=",
        "  let (n0, n1) := SPLIT n",
        "  tube (ring (tube x n0)) n1",
        "",
        "@[holon fallback := chain]",
        "def tree (x : Bus) (n : Bus) : Bus :=",
        "  let y := tube x n",
        "  let (y0, y1) := SPLIT y",
        "  CAT (tree y0 n) (tree y1 n)",
        "",
        "#grow tree (n := 8) (schedule := .bfs)",
    ]
    left = panel("program · widths are never declared; they are inferred at instantiation", gutter_code(src, cur=15, marks=(2,5,10,15,20)) +
                 note("surface syntax is illustrative. The attribute marks a rewrite rule with a fallback; SPLIT/CAT/LSLICE/HSLICE/REPEAT are the only bus combinators; a boundary (empty bus, out-of-range index) is the sole control flow and unwinds to the fallback (MorphoHDL <span class='mono'>tiny_morpho.py:79</span>)"), "flex: 0 0 440px")

    # growth canvas
    d = s_arrow_defs()
    # inputs
    for i in range(4):
        d += s_circ(30, 60 + i*40, 6, "ink", 'fill="#3c6ea5"'); d += s_text(8, 64 + i*40, f"x{i}", "svgtxt")
    # expanded tube cells (ring of sites)
    import math
    for k, (cx, cy) in enumerate([(170, 120), (300, 120)]):
        pts = []
        for j in range(3):
            a = -math.pi/2 + j*2*math.pi/3
            pts.append((cx + 34*math.cos(a), cy + 34*math.sin(a)))
        for j in range(3):
            (x1, y1), (x2, y2) = pts[j], pts[(j+1) % 3]
            d += s_line(x1, y1, x2, y2, "wire", 'marker-end="url(#ah)"')
        for (x, y) in pts: d += s_circ(x, y, 5, "ink", 'fill="#fffdf8"')
        d += s_text(cx-22, cy+52, f"cell:[1] #{k+3}", "svgtxt")
    d += s_line(36, 60, 136, 90, "wire"); d += s_line(36, 100, 136, 120, "wire"); d += s_line(36, 140, 140, 150, "wire")
    d += s_line(204, 120, 266, 120, "wire", 'marker-end="url(#ah)"'); d += s_text(215, 112, "couple", "svgtxt")
    # unexpanded morpho cells (amber)
    for (x, y, t) in [(420, 70, "tree:[4,3] #9"), (420, 170, "tree:[4,3] #10")]:
        d += s_rect(x, y, 110, 40, "ink", 6, 'fill="#f3d79a"'); d += s_text(x+8, y+24, t, "svgtxt")
        d += s_line(334, 120, x, y+20, "wire", 'marker-end="url(#ah)"')
    d += s_rect(560, 110, 110, 40, "ink", 6, 'fill="#f3d79a"'); d += s_text(568, 134, "tube:[8,3] #11", "svgtxt")
    d += s_line(530, 90, 560, 125, "wire"); d += s_line(530, 190, 560, 135, "wire")
    d += s_text(560, 100, "expandable · parent #2 · pos inherited", "svgtxt")
    # outputs
    for i in range(3):
        d += s_circ(700, 90 + i*40, 6, "ink", 'fill="#b04e4e"'); d += s_text(712, 94 + i*40, f"y{i}", "svgtxt")
        d += s_line(670, 130, 694, 90 + i*40, "wire")
    # legend
    d += s_circ(20, 250, 5, "ink", 'fill="#3c6ea5"'); d += s_text(30, 254, "input port", "svgtxt")
    d += s_circ(110, 250, 5, "ink", 'fill="#fffdf8"'); d += s_text(120, 254, "site (node)", "svgtxt")
    d += s_rect(200, 244, 14, 12, "ink", 3, 'fill="#f3d79a"'); d += s_text(220, 254, "unexpanded rule (amber)", "svgtxt")
    d += s_line(380, 250, 410, 250, "wire", 'marker-end="url(#ah)"'); d += s_text(416, 254, "oriented incidence / net", "svgtxt")
    d += s_circ(580, 250, 5, "ink", 'fill="#b04e4e"'); d += s_text(590, 254, "output port", "svgtxt")
    canvas = svg(740, 270, d)
    growth = panel("growth canvas · one step = one local rewrite; children are born at the parent's position", canvas +
                   row([col([lbl("materialization registry · key = name:[signature]"), table(["key", "est. cells", "state"], [
                        ["tree:[8,3]", "61", "expanded #2"], ["tube:[8,3]", "24", "expanded #3, #11 pending"], ["ring:[8]", "8", "expanded"], ["chain:[8,1]", "9", "cached"], ["cell:[1]", "1", "leaf (3 sites)"]])], "flex:1"),
                        col([lbl("receipts"), box("lean", "order-independence receipt (required, not yet returned): final graph digest equal under BFS / largest-first / traced — MorphoHDL states this property for its own compiler; the schedule is aesthetic and placement only"),
                             box("lean", "identity: append-only cell index · <span class='mono'>active</span> flag · <span class='mono'>parent</span> lineage — nothing is deleted, undo is implicit"),
                             box("obstructed", "step 14 / 61 · fanout buffer inserted at net 37 (limit 4)")], "flex:1")]), "flex: 1 1 auto")

    right = panel("customizer · inferred from top-level parameters + annotations (OpenSCAD) · tweaks are levers", kv([
        ("n", '<div style="display:flex; align-items:center; gap:6px"><div style="width:120px; height:6px; background:#ddd5c5; border-radius:3px; position:relative"><div style="position:absolute; left:0; width:25%; height:6px; background:#292418; border-radius:3px"></div></div><span class="mono">8</span> <span class="meta">[1:32]</span></div>'),
        ("fallback", btn("cell") + " <span class='meta'>enum: cell · chain · 0</span>"),
        ("schedule", btn("bfs", True) + " " + btn("largest") + " " + btn("traced")),
        ("fanout", btn("4") + " <span class='meta'>int, structural buffer insertion</span>"),
        ("M (per branch)", "<span class='mono'>L = 1/2 · C = 3 · R = 0</span> <span class='meta'>exact ℚ, never float</span>"),
        ("drive ω", "<span class='mono'>2π/12</span> <span class='meta'>ℚ(ζ₁₂) cyclotomic phase</span>"),
        ("lock", btn("off") + " <span class='meta'>binary quotient is a later receiver</span>"),
    ]) + lbl("console") + code("#grow tree n:=8 schedule:=bfs\n  rules materialized: 5   cells: 61   sites: 183\n  const-prop: 12 cells   DCE: 5 nets   buffers: 3\n  digest: 9f3a…c1 (structural, receipt only)\nkernel: pending — a later world event, never a phase"), "flex: 0 0 330px")

    timeline = panel("growth timeline → becomes the Transport face's time axis", row([
        ''.join(f'<div style="flex:1; height:62px" class="ph"><span class="lbl">t={t}</span></div>' for t in range(0, 8)) ,
    ], gap=6) + note("unit-delay sweep (<span class='mono'>firstTime/lastTime</span>, Kahn order) is the only temporal quantity in MorphoHDL; here it seeds the discrete induction tick of the Complex Parametron transport (Millennium/HolonicDiscreteInduction.lean)"), "flex: 0 0 150px")

    body = tb + row([left, growth, right], "flex:1 1 auto; min-height:0") + timeline
    return artboard("Growth — program → lattice", "a component is a rewrite rule with a fallback base case; the lattice is the deterministic evaluation of the program (MorphoHDL × OpenSCAD)", 1560, 980, body,
                    "sources: paradigms-of-intelligence/morpho dc8dd2e (tiny_morpho.py, js/compiler.js) · openscad customizer")

note_on("n-views-1", "page-views", 1680, 0, 320, "Twelve faces of one workspace. Each artboard is a low-fidelity wireframe: boxes and labels are real (types, ids, receipts), positions are not. Species colour tells you what a control does; a dashed border is an obstruction that stays visible.")
note_on("n-ontology-1", "page-ontology", 1680, 0, 320, "Type sheets are readings of canon definitions with path:line citations. The Crate page says which existing Rust/Lean owner already carries each one.")
note_on("n-library-1", "page-library", 1680, 0, 320, "Every component is a KiCad-style triple (symbol · footprint · model) plus a MorphoHDL rule with a fallback and SolveSpace-style constraints. Library 0 is the contact-rule matrix every net is checked against.")
note_on("n-machinery-1", "page-machinery", 1680, 0, 320, "Pipelines lifted from the references and retyped: each stage carries its species; the boundary panel says what canon refuses.")
note_on("n-archive-1", "page-archive", 1680, 0, 320, "The previous draft (The descent at five) and the cached prototypes, unchanged. Their vocabulary — species colours, box kinds, STIX/Plex faces — is what the new pages inherit.")
