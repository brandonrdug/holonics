from lib import *
from gen import board, note_on
import math

def slider(label, val, pct):
    return f'<div style="display:flex; align-items:center; gap:6px"><span class="lbl" style="width:60px">{label}</span><div style="width:110px; height:6px; background:#ddd5c5; border-radius:3px; position:relative"><div style="position:absolute; left:0; width:{pct}%; height:6px; background:#292418; border-radius:3px"></div></div><span class="mono" style="font-size:10px">{val}</span></div>'

# ---------- V3 lattice ----------
@board("ViewLattice.dc.html", "View 3 — Lattice: nD geometry with a projection chart", 1560, 1000, "page-views")
def view_lattice():
    tb = toolbar([btn("lattice: parametron_ring.lean"), '<span class="lbl">chart</span>', btn("3+1 split (x,y,z | t)", True), btn("planes: 6 alternating"), btn("cycle directions: 4"),
                  '<span class="lbl" style="margin-left:8px">view</span>', btn("orthogonal"), btn("perspective", True), btn("top"), btn("front"), btn("diagonal"), btn("fit"),
                  '<span class="lbl" style="margin-left:8px">mode</span>', btn("preview ($preview)"), btn("exact render", True), btn("thrown together"),
                  btn("axes ✓"), btn("scale ✓"), btn("edges ✓")])
    # viewport: isometric lattice drawing
    d = s_arrow_defs()
    ox, oy = 360, 300
    def iso(x, y, z):
        return (ox + (x - y) * 38, oy + (x + y) * 19 - z * 40)
    # grid of sites 4x4x2
    pts = {}
    for z in range(2):
        for x in range(4):
            for y in range(4):
                pts[(x, y, z)] = iso(x, y, z)
    for (x, y, z), (px, py) in pts.items():
        if x < 3: qx, qy = pts[(x+1, y, z)]; d += s_line(px, py, qx, qy, "grey")
        if y < 3: qx, qy = pts[(x, y+1, z)]; d += s_line(px, py, qx, qy, "grey")
        if z < 1: qx, qy = pts[(x, y, z+1)]; d += s_line(px, py, qx, qy, "grey", 'stroke-dasharray="2 3"')
    # a parametron ring footprint occupying three sites with oriented incidence
    ring = [(1, 1, 1), (2, 1, 1), (1, 2, 1)]
    for i in range(3):
        (x1, y1), (x2, y2) = pts[ring[i]], pts[ring[(i+1) % 3]]
        d += s_line(x1, y1, x2, y2, "wire", 'marker-end="url(#ah)" stroke-width="2.5"')
    for (x, y, z), (px, py) in pts.items():
        r = 6 if (x, y, z) in ring else 3
        d += s_circ(px, py, r, "ink", 'fill="#fffdf8"' if r == 3 else 'fill="#3c6ea5"')
    for i, s in enumerate(ring):
        px, py = pts[s]; d += s_text(px + 8, py - 6, f"n{i}", "svgtxt")
    # constraint glyphs: distance between n0,n1 and a 'coincident' marker
    (ax, ay), (bx, by) = pts[ring[0]], pts[ring[1]]
    d += s_line(ax, ay - 26, bx, by - 26, "ink", 'marker-end="url(#ahk)" marker-start="url(#ahk)" stroke-width="1"')
    d += s_text((ax + bx) / 2 - 22, ay - 30, "|n0 n1| = 1 (ref)", "svgtxt")
    d += s_text(pts[(3,3,0)][0] + 10, pts[(3,3,0)][1] + 4, "free site (DOF)", "svgtxt")
    d += s_circ(*pts[(3,3,0)], 5, "ink", 'fill="#a67a2e"')
    # axes
    d += s_line(40, 400, 100, 400, "ink", 'marker-end="url(#ahk)"'); d += s_text(104, 404, "x", "svgmath")
    d += s_line(40, 400, 40, 340, "ink", 'marker-end="url(#ahk)"'); d += s_text(36, 332, "z", "svgmath")
    d += s_line(40, 400, 12, 428, "ink", 'marker-end="url(#ahk)"'); d += s_text(4, 442, "y", "svgmath")
    d += s_text(40, 460, "t: hidden axis of this chart · slice t = 0 · scrub →", "svgtxt")
    d += s_rect(560, 30, 150, 60, "ink", 6, 'stroke-dasharray="4 3" fill="#fffdf8"')
    d += s_text(568, 48, "PROJECTION RECEIVER", "svgtxt", 'font-weight="500"'); d += s_text(568, 64, "4 cycle directions →", "svgtxt"); d += s_text(568, 80, "3 shown + 1 sliced", "svgtxt")
    view = panel("viewport · a face of the ℤ⁴ lattice through one declared chart; the chart is an entity (workplane = point + quaternion), not a camera setting",
                 svg(740, 470, d, "width:100%; height:auto") + note("sites are situated occurrences; grey edges are founded incidence; the blue oriented triangle is one Complex Parametron footprint (3 nodes, 3 branches, <span class='math'>B</span> = 3×3 oriented incidence) · <span class='mono'>#</span> highlight, <span class='mono'>%</span> ghost, <span class='mono'>!</span> root, <span class='mono'>*</span> disable — per-node modifiers propagate through the term (OpenSCAD)"), "flex: 1 1 auto")

    prog = panel("lattice program · evaluated from scratch per compile; the node tree is the trace", code(
"""-- OpenSCAD-shaped, Lean-typed (illustrative)
def ring3 : Footprint := oriented_cycle 3           -- B : 3×3
def sheet (n : ℕ) : Lattice := grid ℤ² n            -- founded incidence
def body : Lattice :=
  union
    (sheet 4)
    (translate ⟨1,1,1⟩ (place ring3))                -- occupancy: 3 sites
    (! (mirror ⟨0,1,0⟩ (place ring3)))                -- ! isolates this subtree
constraint (dist n0 n1 = 1) (reference := true)      -- measured, no equation
constraint (coincident (site 2 2 1) ring3.n2)        -- equation, 3 scalars
#project body (chart := split3p1)                    -- the face"""), "flex: 0 0 400px")

    groups = panel("groups · sequential: earlier groups are fixed inputs (SolveSpace text window)", table(["active", "shown", "dof", "group"], [
        ["○", "✓", "ok", "g001-#references"], ["○", "✓", "0", "g002-sheet-in-plane"], ["●", "✓", "3", "g003-parametron-place"], ["○", "–", "redundant", "g004-mirror (remove any one of c007, c009)"]]) +
        kv([("requests", "r003-oriented-cycle · r004-datum-site · r005-workplane"), ("constraints (3 DOF)", "c006-pt-pt-distance (ref) · c007-coincident · c009-coincident"),
            ("solve", grade("established-bounded") + " rank(J)=5 of m=5 · n=8 → dof 3 · Newton 4 it · exact ℚ Jacobian"),
            ("policy", btn("allow redundant") + " " + btn("relax") + " " + btn("all dims reference"))]), "flex: 0 0 auto")
    right = col([prog, groups], "flex: 0 0 400px")
    body = tb + row([view, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Lattice — nD geometry through a chart", "OpenSCAD's program-as-model × SolveSpace's request → entity → param → equation solve, over ℤⁿ sites with a declared 3+1 receiver", 1560, 1000, body,
                    "sources: openscad 1c9ee2b (src/core/node.h, CSGTreeNormalizer) · solvespace 3297d9a (src/sketch.h, system.cpp) · AGENTS.md typed physical theory (4 cycle directions, 6 planes)")

# ---------- V4 transport ----------
@board("ViewTransport.dc.html", "View 4 — Transport: action over the lattice, exactly", 1560, 1000, "page-views")
def view_transport():
    tb = toolbar([btn("body: parametron_ring × sheet 4"), btn("⏮"), btn("⏴"), btn("▶ tick"), btn("⏭"), '<span class="lbl">t</span>',
                  '<div style="width:260px; height:6px; background:#ddd5c5; border-radius:3px; position:relative"><div style="position:absolute; left:0; width:35%; height:6px; background:#3c6ea5; border-radius:3px"></div><div style="position:absolute; left:35%; top:-4px; width:4px; height:14px; background:#292418; border-radius:2px"></div></div>',
                  '<span class="mono" style="font-size:10px">7 / 20</span>', '<span class="lbl" style="margin-left:8px">law</span>', btn("discrete induction", True), btn("discrete Maxwell"), btn("membrane action"),
                  '<span class="lbl" style="margin-left:8px">carrier</span>', btn("ℚ(i)", True), btn("ℚ(ζ₁₂)"), btn("no float")])
    # heat lattice
    d = s_arrow_defs()
    vals = [[0,1,2,1],[1,3,5,2],[2,5,8,3],[1,2,3,1]]
    from fractions import Fraction as Fr
    for y in range(4):
        for x in range(4):
            v = vals[y][x]; a = 0.12 + 0.1 * v
            d += f'<rect x="{40+x*70}" y="{30+y*70}" width="62" height="62" rx="6" fill="rgba(60,110,165,{a:.2f})" stroke="#8a8071" stroke-width="1"/>'
            d += s_text(48+x*70, 50+y*70, f"c={v}/2+{(v*3)%5}i", "svgtxt")
            k=(v*3)%5; m=Fr(v*v,4)+k*k; d += s_text(48+x*70, 84+y*70, f"|c|²={m}", "svgtxt")
    # branches with arrows for the ring
    d += s_line(102, 130, 180, 130, "wire", 'marker-end="url(#ah)" stroke-width="2.5"'); d += s_text(120, 122, "i₀₁ = 3/2 − i", "svgtxt")
    d += s_line(180, 160, 110, 200, "wire", 'marker-end="url(#ah)" stroke-width="2.5"')
    d += s_line(80, 200, 80, 160, "wire", 'marker-end="url(#ah)" stroke-width="2.5"')
    d += s_text(360, 40, "probe ⟨ρ₁| at site (2,2)", "svgtxt"); d += s_circ(355, 36, 4, "ink", 'fill="#a67a2e"')
    d += s_text(360, 300, "boundary flux ∂: 0 (closed) · radiation port: none declared", "svgtxt")
    lattice = panel("lattice face · exact complex coefficient current c per node, branch current Bc, shading = storage density c̄Gc (a declared receiver quotient)", svg(520, 320, d) +
                    note("no value here is a float: coefficients live in ℚ(i) or a cyclotomic tower (existing owners: exact_linear, multiquadratic, rational_polynomial); a displayed magnitude is a face, never the construction"), "flex: 0 0 560px")
    # oscilloscope traces
    t = ""
    t += s_line(30, 120, 470, 120, "grey"); t += s_line(30, 20, 30, 220, "grey")
    pts1 = " ".join(f"{30+i*22},{120-60*math.sin(i*0.7)}" for i in range(21))
    pts2 = " ".join(f"{30+i*22},{120-40*math.cos(i*0.7+0.4)}" for i in range(21))
    t += f'<polyline points="{pts1}" class="wire"/>'; t += f'<polyline points="{pts2}" stroke="#a67a2e" fill="none" stroke-width="1.5"/>'
    t += s_line(30+7*22, 20, 30+7*22, 220, "ink", 'stroke-dasharray="3 3"'); t += s_text(30+7*22+4, 30, "t=7", "svgtxt")
    t += s_text(34, 232, "Re ⟨ρ₁|c⟩ (blue) · Im (amber) — each sample is an exact rational, the curve is a rendering", "svgtxt")
    scope = panel("probes · ⟨ρ|c_t⟩ over the world-tube; a probe is a receiver component placed on the lattice", svg(490, 240, t) + row([btn("+ probe"), btn("⟨ρ₁| site (2,2)", True), btn("⟨ρ₂| branch 0→1"), btn("storage total"), btn("export holonic-json-v1")], gap=6), "flex: 1 1 auto")
    receipts = panel("receipts per tick · kinematic identities are checked, conservation owes its laws", table(["receipt", "t=7", "grade"], [
        ["∂² = 0 on the chain complex", "holds", grade("proved-standard")],
        ["Stokes on every 2-cell", "holds", grade("proved-standard")],
        ["storage c̄Gc = (Bc)̄M(Bc)", "equal (exact)", grade("proved-derived") + " " + tag("formal-checked")],
        ["conservation: storage + boundary flux + source", "declared: source ω-drive, boundary closed", grade("conditional")],
        ["reorientation covariance (flip branch 2)", "storage unchanged", grade("proved-derived")],
        ["locked quotient (binary parametron)", "not taken — sheets retained", grade("definition")],
    ]), "flex: 1 1 auto")
    state = panel("carrier state · the Complex Parametron carrier (canon §8d)", kv([
        ("nodes", "<span class='mono'>3 + 16</span> addressed coefficient nodes"),
        ("B", "<span class='mono'>27×19</span> (branches × nodes) oriented incidence, entries ∈ {−1, 0, 1}"),
        ("c", "exact complex current, ℚ(i)¹⁹"),
        ("M", "receiver constitutive form, per branch (L, C, R) exact"),
        ("G", "<span class='math'>BᵀMB</span> pulled storage"),
        ("ker B / ker G", "dim 2 / dim 1 — retained, shown as fibres"),
        ("phase", "relative phase per sheet · half-turn pair retained"),
        ("lineage", "born t=0 by growth #2 · rule tree:[8,3]"),
        ("open exterior", "1 undeclared port (CP₁.n0)"),
    ]), "flex: 0 0 auto")
    obstr = panel("obstructions", box("obstructed", "t=5: drive ω changed mid-tube — recorded as an intervention, not folded into the law") + box("refused", "energy in joules: unknown — physical calibration enters only through a declared sector port"), "flex: 0 0 auto")
    body = tb + row([lattice, col([scope, receipts], "flex: 1 1 auto"), col([state, obstr], "flex: 0 0 360px")], "flex: 1 1 auto; min-height: 0")
    return artboard("Transport — action over the lattice, exactly", "the electricity analogy made literal: exact complex current through oriented incidence, ticked by a discrete induction law, read by placed receivers", 1560, 1000, body,
                    "sources: canon/TABLET_THE_REASONING_CYCLE.md §8d · Millennium/HolonicComplexParametron.lean · HolonicDiscreteInduction.lean · HolonicMembraneActionTransport.lean · KiCad simulator / GElectrical results overlay (form only)")

# ---------- V7 notation ----------
@board("ViewNotation.dc.html", "View 7 — Notation: typed Dirac primitives", 1400, 900, "page-views")
def view_notation():
    pal = panel("palette · each primitive carries its species; the editor refuses an untyped bracket", table(["glyph", "species", "meaning"], [
        ["<span class='math'>|ψ⟩</span>", sp("construction"), "a holon presented in a chart"],
        ["<span class='math'>⟨φ|</span>", sp("receiver"), "a receiver covector"],
        ["<span class='math'>⟨φ|ψ⟩</span>", sp("face"), "the reading of that construction at that receiver — forgets, and says what it forgets"],
        ["<span class='math'>X</span>", sp("transport"), "carries a holon between charts; invertible transport is rebase"],
        ["<span class='math'>|a⟩⟨a|</span>", sp("deposit"), "a construction reversed into a receiver: the emanation becomes the pole"],
        ["<span class='math'>Σᵢ|aᵢ⟩⟨aᵢ|</span>", sp("quotient"), "= I only for a G-orthonormal family; otherwise the frame operator S ≠ I, reconstruction through the dual frame S⁻¹|aᵢ⟩"],
        ["<span class='math'>tr X</span>", sp("face"), "basepoint-free face of the closed loop"],
        ["<span class='math'>u·v + u∧v</span>", sp("construction"), "geometric product: alignment (grade 0) + founded oriented plane (grade 2)"],
        ["<span class='math'>e^{iπ}</span>", sp("transport"), "the half-turn: subtraction is addition with one hand reversed"],
    ]), "flex: 0 0 560px")
    tree = panel("expression as container occurrence · holonic-json-v1 is the primary face; LaTeX / Unicode / Lean are exterior renderings", code(
"""{ "kind": "face",  "receiver": {"kind":"bra","id":"rho_1","chart":"site(2,2)"},
  "of": { "kind": "transport", "op": "X", "orientation": "+",
          "of": { "kind": "construction", "id": "c_t", "carrier": "Q(i)^19",
                  "terms": [ {"role":"coefficient","site":"n0","value":"3/2-1i"},
                             {"role":"coefficient","site":"n1","value":"1/2"} ] } },
  "grade": "established-bounded",
  "fibre": { "kernel_B": 2, "kernel_G": 1, "hypotheses": ["G = B^T M B"] } }""") +
        note("every bracketed expression is itself a container occurrence with ordered, role-bearing term/factor incidences (AGENTS.md, Provenance clauses) · an integer or rational is a situated receiver face, never a quiet scalar identity"), "flex: 1 1 auto")
    edit = panel("editor · selection is linked: a bracket here lights its swing in Trace, its net in Schematic, its site in Lattice, its probe in Transport", row([
        box("lean", "<span class='math' style='font-size:16px'>⟨ρ₁| X |c₇⟩</span> <span class='meta'>= 3/2 − i · face · t=7</span>"),
        box("lean", "<span class='math' style='font-size:16px'>|X_{t+1}⟩ = N_t(|X_t⟩ + O_t|δX_t⟩ + |δX_t^{const}⟩)</span> <span class='meta'>local return, canon §2</span>"),
    ], gap=8) + row([btn("insert ket"), btn("insert bra"), btn("close face"), btn("compose transport"), btn("deposit |a⟩⟨a|"), btn("resolution (declare G)"), btn("render: LaTeX · Unicode · Lean")], gap=6) +
        box("obstructed", "refused: <span class='math'>Σᵢ|aᵢ⟩⟨aᵢ| = I</span> without a declared inner product G — the editor asks for the metric (corrected 2026-08-17, canon §1)"), "flex: 0 0 auto")
    body = row([pal, tree], "flex: 1 1 auto; min-height: 0") + edit
    return artboard("Notation — typed Dirac primitives", "bra-ket is machinery here, not ornament: every symbol is a construction, transport, face, quotient, or deposit", 1400, 900, body,
                    "sources: canon/TABLET_THE_OPERATIONS.md §1–3 (H.0476) · canon/TABLET_THE_REASONING_CYCLE.md §2 · AGENTS.md Provenance clauses")

# ---------- V8 interaction ----------
@board("ViewInteraction.dc.html", "View 8 — Interaction: the Feynman vertex as a typed component", 1400, 900, "page-views")
def view_interaction():
    d = s_arrow_defs()
    # vertex
    vx, vy = 330, 200
    d += s_circ(vx, vy, 14, "ink", 'fill="#292418"')
    # incoming
    d += s_line(80, 120, vx-12, vy-8, "wire", 'marker-end="url(#ah)" stroke-width="2"'); d += s_text(90, 112, "|u₁⟩ in · port p₁ · hand +", "svgtxt")
    d += s_line(80, 280, vx-12, vy+8, "wire", 'marker-end="url(#ah)" stroke-width="2"'); d += s_text(90, 296, "|u₂⟩ in · port p₂ · hand −", "svgtxt")
    # outgoing
    d += s_line(vx+14, vy, 600, vy, "wire", 'marker-end="url(#ah)" stroke-width="2"'); d += s_text(430, vy-8, "outgoing current |δx⟩ = Σ αⱼ|uⱼ⟩", "svgtxt")
    # cross term (wavy)
    wav = "M " + " ".join(f"{vx+ (i*14)},{vy-40 - (8 if i%2 else -8)}" for i in range(0, 16))
    d += s_path(wav, "grey", 'stroke="#9c5480" stroke-width="1.5"'); d += s_text(vx+20, vy-60, "cross term u∧v (grade 2) · founded plane", "svgtxt")
    # residue / obstruction
    d += s_line(vx, vy+14, vx, vy+90, "ink", 'stroke-dasharray="3 3"'); d += s_rect(vx-60, vy+90, 120, 30, "ink", 6, 'stroke-dasharray="4 3" fill="#f5ecef"')
    d += s_text(vx-52, vy+109, "residue · obstruction", "svgtxt")
    d += s_text(vx-20, vy+40, "Γ: constitutive law", "svgtxt")
    # deposit loop
    d += s_path(f"M {600},{vy} C 680,{vy-120} 680,{vy+120} {600},{vy}", "grey", 'stroke="#29426b" stroke-width="1.5"'); d += s_text(612, vy+70, "loop · tr X basepoint-free · holonomy", "svgtxt")
    fig = panel("diagram · a vertex is the typed interaction, not the dot used to draw it", svg(720, 340, d) +
                note("the vertex = incoming ports, hand, cross term, outgoing current, obstruction, residue (canon §2) · an edge is one swing read as transport · a loop returns a basepoint-free face (trace) and a holonomy · a diagram with n vertices is a chain of swings, composable only through both boundary maps"), "flex: 1 1 auto")
    insp = panel("vertex inspector", kv([
        ("ports in", "p₁ (+), p₂ (−) — typed, ERC-checked against port kinds"),
        ("law Γ", "declared local constitutive reaction · softmax ⇒ barycentric αⱼ · here: exact bilinear"),
        ("cross term", "u∧v retained (multivector keeps both grades)"),
        ("out", "one current on one port · fan-out only through a junction component"),
        ("obstruction", "none · a refused contact would be drawn dashed and kept"),
        ("residue", "chronological standing |δX^{const}⟩ — not a scratchpad"),
        ("grade", grade("interpretation") + " bra-ket types transport; no quantum identity is asserted"),
    ]) + lbl("composition") + table(["rule", "requirement"], [
        ["serial", "pullback population W_f ×_Y W_g retained; both boundary maps preserved"],
        ["parallel", "exact independence / interchange receipt — worker count proves nothing"],
        ["loop", "declared receiver for the trace; holonomy is a returned face"],
    ]), "flex: 0 0 420px")
    lib = panel("vertex kinds in the library", row([btn("junction (+/−)"), btn("coupling"), btn("pump / drive"), btn("membrane crossing"), btn("radiation / return"), btn("deposit |a⟩⟨a|"), btn("quotient (lock)")], gap=6), "flex: 0 0 auto")
    body = row([fig, insp], "flex: 1 1 auto; min-height: 0") + lib
    return artboard("Interaction — the Feynman vertex as a typed component", "diagrams are chains of swings; a vertex owns its ports, hand, cross term, current, obstruction and residue", 1400, 900, body,
                    "sources: canon/TABLET_THE_REASONING_CYCLE.md §2 · canon/TABLET_THE_OPERATIONS.md §3.2, §5 · AGENTS.md ownership/composition · circuitikz node-style anchors (form only)")

# ---------- V9 constraints ----------
@board("ViewConstraints.dc.html", "View 9 — Constraint and DOF inspector", 1400, 860, "page-views")
def view_constraints():
    left = panel("browser · SolveSpace's text window, retyped: every diagnostic row links back into selection", table(["", "kind", "id", "detail"], [
        ["●", "request", "r003", "oriented-cycle 3 · owns e003.0 (cycle), e003.1..3 (sites), p003.16..24"],
        ["", "request", "r004", "datum-site (2,2,1) · e004.0 · p004.16,17"],
        ["", "constraint", "c006", "pt-pt-distance |n0 n1| = 1 <b>(ref)</b> — measured, generates no equation"],
        ["", "constraint", "c007", "coincident e004.0 ≡ e003.3 → 3 equations (2 in-chart)"],
        ["", "constraint", "c009", "coincident e004.0 ≡ e003.3 → <span class='sp sp-refused'>redundant</span>"],
        ["", "entity", "e003.2", "site · free (column drop leaves rank unchanged)"],
    ]) + lbl("handles carry lineage") + code("hEntity = request << 16 | index      0x00030002 = e003.2\nhParam  = owner   << 16 | slot       0x00030010 = p003.16 (site 0, u)\nhEquation.constraint() = v >> 16      every residual names its source", ""), "flex: 1 1 auto")
    right = panel("solve report · group g004", kv([
        ("result", tag("REDUNDANT_OKAY") + " rank(J) = 5, m = 6, n = 8"),
        ("dof", "<b>3</b> = n − rank"),
        ("remove any one of", btn("c007") + " " + btn("c009") + " <span class='meta'>leave-one-out with a time budget (SolveSpace findToFixTimeout)</span>"),
        ("unsatisfied", "none (residuals ≤ tolerance, exact zero in ℚ)"),
        ("free params", "p003.22, p003.23, p003.24 → site e003.2 drawn amber"),
        ("dragged", "soft weight 1/20 on p004.16 — DOF unchanged; hard lock = where-dragged constraint"),
        ("jacobian", "assembled symbolically once (Expr with total PartialWrt); evaluated per Newton step; exact over ℚ, no float"),
        ("policy", btn("allow redundant") + " " + btn("relax") + " " + btn("suppress dof")),
    ]) + box("obstructed", "a constraint that cannot be typed as an equation over declared params is refused at authoring time, not at solve time") +
        box("lean", "constraint grammar is a small inductive (15 constructors in SolveSpace's Expr) — small enough to carry a proven derivative: a verified Jacobian is the Lean model of this panel"), "flex: 0 0 520px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Constraints and degrees of freedom", "requests expand to entities and params; constraints generate equations; the solver is type-blind and reports exactly four states plus DOF", 1400, 860, body,
                    "sources: solvespace 3297d9a (src/sketch.h handles, src/system.cpp TestRank / FindWhichToRemoveToFixJacobian, src/textscreens.cpp)")

# ---------- V10 provenance ----------
@board("ViewProvenance.dc.html", "View 10 — Provenance and grades", 1400, 860, "page-views")
def view_provenance():
    left = panel("grades · every object carries exactly one truth-status grade and any evidence tags", table(["grade", "meaning", "required boundary"], [
        [grade("definition"), "a declared term or construction", "types, scope, construction rule"],
        [grade("project-postulate"), "a governing discipline adopted by this project", "consistency boundary; never a theorem of all mathematics"],
        [grade("proved-standard"), "a standard external theorem", "primary source or named library theorem"],
        [grade("proved-derived"), "a theorem derived in the project", "complete proof and dependencies"],
        [grade("established-bounded"), "a capability for a declared construction/receiver family", "exact scope + direct evidence"],
        [grade("conditional"), "a conclusion under named hypotheses", "full hypothesis and dependency chain"],
        [grade("interpretation"), "a structure-preserving correspondence in development", "maps, limits, preserved diagram, first derivation target, a falsifier"],
        [grade("conjecture"), "a precise unproved claim", "testable statement, known obstructions"],
        [grade("counterexample"), "a construction refuting a stronger claim", "exact refuted statement and witness"],
        [grade("open"), "a named unresolved fibre", "concrete missing return"],
        [grade("historical"), "preserved provenance", "source and disposition"],
    ]) + row([tag("formal-checked"), tag("implemented-exact"), tag("measured"), tag("computational-witness"), tag("source-inspected"), tag("source-audit"), tag("process-audit")], "flex-wrap: wrap; gap: 4px"), "flex: 1 1 auto")
    right = panel("selection · theorem storage_pullback", kv([
        ("grade", grade("interpretation") + " until the kernel event returns"),
        ("kernel receipt", "pending — the theorem shown in the Trace view is illustrative; a receipt would list toolchain, imports, axioms, sorry count"),
        ("world event", "attached to the projected passage · not a phase, gate, or loss"),
        ("claim index", "H.0476 (species) · §8d carrier · HolonicComplexParametron.lean"),
        ("provenance cursor", "a pivot at the source locus, side-session; intent and completion recorded"),
        ("lineage", "swings t=1..8 recorded as typed swings (math_record_swing) — before, operator, after, receiver, hypotheses, orientation, boundary, grade, fibre"),
    ]) + box("carried", "a claim without a grade cannot be saved: the document law is enforced at authoring") + box("refused", "a diagnostic hash, a nonempty output, or a passing self-authored test does not raise a grade"), "flex: 0 0 520px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Provenance and grades", "the epistemic grade is a first-class field of every object; kernel acceptance is a later world event attached to one projected passage", 1400, 860, body,
                    "sources: canon/EPISTEMIC_GRADES.md · AGENTS.md Provenance sidecar · mathematical production boundary")
