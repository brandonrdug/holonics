from lib import *
from gen import board, note_on
import math

PORT_KINDS = [
    ("emission", "a current leaves the holon here (source leg)"),
    ("return", "a returned consequence re-enters here (sink leg)"),
    ("shared", "node identified with another holon's node — typed shared incidence"),
    ("pump", "parametric drive input (ω, phase); an intervention channel"),
    ("receiver", "a bra: reads, forgets, carries nothing back"),
    ("feedback", "explicit re-entry of a returned output (canon 01:105)"),
    ("exterior", "open, undeclared — stays visible as open exterior"),
]

def sheet(name, kind, symbol_svg, footprint_svg, lean, params, ports, rule, receipts, nots, sources="", w=1400, h=780):
    sym = panel("symbol · schematic glyph with named anchors (circuitikz / KiCad symbol)", symbol_svg, "flex: 0 0 auto")
    fp = panel("footprint · lattice occupancy in ℤⁿ (KiCad footprint / OpenSCAD leaf)", footprint_svg, "flex: 0 0 auto")
    model = panel("model · Lean structure and constitutive law (the third linked projection)", code(lean), "flex: 1 1 auto")
    pr = panel("parameters · customizer-inferred, exact", table(["name", "type", "default", "note"], params), "flex: 0 0 auto")
    po = panel("ports", table(["port", "kind", "orientation", "note"], ports), "flex: 0 0 auto")
    ru = panel("rule · rewrite body + fallback (MorphoHDL); constraints (SolveSpace)", code(rule), "flex: 1 1 auto")
    rc = panel("receipts and grade", ''.join(receipts), "flex: 0 0 auto")
    nt = panel("what it is not", ''.join(box("refused", n) for n in nots), "flex: 0 0 auto")
    body = row([col([sym, fp, model], "flex: 0 0 470px"), col([pr, po, ru], "flex: 1 1 auto"), col([rc, nt], "flex: 0 0 330px")], "flex: 1 1 auto; min-height: 0")
    return artboard(name, kind, w, h, body, sources)

def sym_box(inner, w=430, h=170):
    return svg(w, h, s_arrow_defs() + inner)

def ring_glyph(cx, cy, r=34, labels=("n0","n1","n2")):
    pts = [(cx + r*math.cos(-math.pi/2 + j*2*math.pi/3), cy + r*math.sin(-math.pi/2 + j*2*math.pi/3)) for j in range(3)]
    d = ""
    for j in range(3):
        (x1,y1),(x2,y2) = pts[j], pts[(j+1)%3]; d += s_line(x1,y1,x2,y2,"wire",'marker-end="url(#ah)" stroke-width="2"')
    for j,(x,y) in enumerate(pts):
        d += s_circ(x,y,5,"ink",'fill="#fffdf8"'); d += s_text(x+7,y-6,labels[j],"svgtxt")
    return d, pts

@board("LibPortKinds.dc.html", "Library 0 — port kinds and the contact rules (ERC)", 1560, 900, "page-library")
def lib_ports():
    kinds = panel("port kinds · KiCad's ELECTRICAL_PINTYPE retyped as holonic contact roles", table(["kind", "meaning"], [[f"<span class='mono'>{k}</span>", m] for k, m in PORT_KINDS]) +
                  note("KiCad's <span class='mono'>ELECTRICAL_PINTYPE</span> (PT_INPUT, PT_OUTPUT, PT_BIDI, PT_TRISTATE, PT_PASSIVE, PT_NIC, PT_UNSPECIFIED, PT_POWER_IN, PT_POWER_OUT, PT_OPENCOLLECTOR, PT_OPENEMITTER, PT_NC — common/pin_type.h) is a receiver chart of the same question; its ERC keeps a <span class='mono'>PIN_ERROR</span> matrix (OK / WARNING / PP_ERROR / UNCONNECTED) and a drive lattice NOC &lt; NPI &lt; NET_NC &lt; NOD &lt; DRV per net (erc_settings.cpp). The connection graph resolves one driver per net by PRIORITY: NONE &lt; PIN &lt; SHEET_PIN &lt; HIER_LABEL &lt; LOCAL_LABEL &lt; LOCAL_POWER_PIN &lt; GLOBAL_POWER_PIN &lt; GLOBAL (connection_graph.h)."), "flex: 0 0 560px")
    ks = [k for k, _ in PORT_KINDS]
    def cell(a, b):
        if a == "receiver" and b == "receiver": return "<span class='sp sp-refused'>refused</span> nothing is read"
        if "receiver" in (a, b): return "ok"
        if a == "emission" and b == "emission": return "<span class='sp sp-refused'>refused</span> two drivers, no junction"
        if a == "pump" and b == "pump": return "ok · a drive meets its intake; a second drive on one net is recorded as an intervention"
        if "exterior" in (a, b): return "<span class='sp sp-warn'>open</span> stays visible"
        if "feedback" in (a, b) and "emission" in (a, b): return "ok via feedback port only"
        if a == "return" and b == "return": return "<span class='sp sp-warn'>warn</span> co-presence is not contact"
        return "ok"
    rows = [[f"<span class='mono'>{a}</span>"] + [cell(a, b) for b in ks] for a in ks]
    matrix = panel("contact rules · a net is checked pairwise like KiCad's ERC pin matrix; a refusal is a returned obstruction, drawn, never hidden", table([""] + [f"<span class='mono'>{k}</span>" for k in ks], rows) +
                   note(grade("definition") + " port kinds · " + grade("project-postulate") + " contact rules — rules descend from canon: co-presence is not contact, contact requires a declared interaction (AGENTS.md ownership) · a returned output may re-enter only through an explicit feedback port (docs/canon/01:105) · two emissions meeting without a junction component have no declared law · an all-receiver net reads nothing."), "flex: 1 1 auto")
    body = row([kinds, matrix], "flex: 1 1 auto; min-height: 0")
    return artboard("Port kinds and the contact rules", "every component port carries a kind; nets are derived from geometry + labels and checked pairwise", 1560, 900, body,
                    "sources: KiCad master (post-9.0) common/pin_type.h, eeschema/erc/erc_settings.cpp m_defaultPinMap + m_PinMinDrive, connection_graph.h PRIORITY · AGENTS.md ownership and composition · docs/canon/01_CAUSAL_CALCULUS.md:105")

@board("LibParametron.dc.html", "Library 1 — Complex Parametron", 1400, 820, "page-library")
def lib_parametron():
    d, pts = ring_glyph(120, 85)
    d += s_rect(60, 30, 130, 120, "ink", 8, 'stroke-dasharray="4 3"')
    for j,(x,y) in enumerate(pts):
        ex, ey = (x + (x-120)*1.1, y + (y-85)*1.1)
        d += s_line(x, y, ex, ey, "ink"); d += s_circ(ex, ey, 3, "ink", 'fill="#292418"'); d += s_text(ex+5, ey+4, f".n{j}", "svgtxt")
    d += s_line(125, 30, 125, 8, "ink"); d += s_text(130, 12, ".pump ω", "svgtxt")
    d += s_text(230, 50, "anchors: .n0 .n1 .n2 .pump .center", "svgtxt")
    d += s_text(230, 70, "label: CP₁ · B 3×3 · M(L,C,R)", "svgtxt")
    d += s_text(230, 90, "path-style: to[CP, n=3, l=$CP_1$]", "svgtxt")
    d += s_text(230, 110, "node-style: node[cp](cp1){} · cp1.n0", "svgtxt")
    sym = sym_box(d)
    f = s_arrow_defs("f")
    ox, oy = 60, 110
    def iso(x, y, z): return (ox + (x - y) * 30, oy + (x + y) * 15 - z * 30)
    for x in range(3):
        for y in range(3):
            px, py = iso(x, y, 0); f += s_circ(px, py, 2.5, "grey", 'fill="#8a8071"')
            if x < 2: qx, qy = iso(x+1, y, 0); f += s_line(px, py, qx, qy, "grey")
            if y < 2: qx, qy = iso(x, y+1, 0); f += s_line(px, py, qx, qy, "grey")
    occ = [iso(0,0,0), iso(1,0,0), iso(0,1,0)]
    for j in range(3):
        (x1,y1),(x2,y2) = occ[j], occ[(j+1)%3]; f += s_line(x1,y1,x2,y2,"wire",'marker-end="url(#ahf)" stroke-width="2"')
    for (x,y) in occ: f += s_circ(x, y, 5, "ink", 'fill="#3c6ea5"')
    f += s_text(230, 50, "occupies 3 sites · 3 oriented edges", "svgtxt"); f += s_text(230, 70, "keep-out: none · shared nodes allowed", "svgtxt")
    f += s_text(230, 90, "nD: any 3 sites with a 2-cell between", "svgtxt"); f += s_text(230, 110, "param n → n sites on an oriented n-cycle", "svgtxt")
    fp = sym_box(f)
    lean = """-- Millennium/HolonicComplexParametron.lean (owner of the law; names per that file)
carrier : (nodes : Fin n) (branches : Fin m)
  B : Matrix (Fin m) (Fin n) ℤ           -- oriented incidence, entries -1/0/1
  c : Fin n → K                          -- K = ℚ(i) or a cyclotomic/multiquadratic tower
  M : Matrix (Fin m) (Fin m) K           -- receiver constitutive form, Hermitian
  G := Bᵀ M B                            -- pulled storage (derived)
law  : star c ⬝ G ⬝ c = star (B c) ⬝ M ⬝ (B c)
reorient (σ : branch → ±1) : B ↦ σB, M ↦ σMσ ; G unchanged
lock : Quotient (locked population) → sign face   -- HolonicParametron.lean"""
    params = [["n", "int [1:64]", "3", "node count (oriented cycle)"], ["B", "incidence", "cycle n", "editable oriented graph"], ["M", "exact Hermitian", "L=1/2, C=3, R=0 per branch", "mutual coupling off-diagonal"],
              ["ω", "exact phase", "2π/12 ∈ ℚ(ζ₁₂)", "pump drive"], ["lock", "bool", "off", "binary quotient is a receiver, not state"], ["internal", "lattice?", "none", "member may present an internal lattice"]]
    ports = [[".n0 … .n{n−1}", "shared", "shared", "typed shared incidence with the lattice"], [".pump", "pump", "in", "intervention channel"], [".probe", "shared", "shared", "a site a receiver ⟨ρ| may attach to"], ["(exterior)", "exterior", "—", "undeclared nodes stay visible"]]
    rule = """@[holon fallback := site]           -- base case: one site, no branch
def parametron (n : Bus) : Carrier :=
  let (n0, n1) := SPLIT n            -- boundary if |n| < 2 → fallback
  couple (parametron n0) (parametron n1)   -- shared node = junction
constraints:  |n_i n_{i+1}| = 1 (ref)  ·  cycle closes  ·  B c ∈ range(B)"""
    receipts = [box("carried", grade("proved-derived") + " " + tag("formal-checked") + " storage pullback and reorientation covariance (HolonicComplexParametron.lean)"),
                box("carried", grade("proved-derived") + " two locked sheets; sign face exact only on the locked population (HolonicParametron.lean)"),
                box("obstructed", grade("open") + " runtime conformance of an exact GPU tick to the formal law — the roadmap's UAR obligation, frozen")]
    nots = ["a perceptron, a neuron, a layer: those are locked receiver faces", "a float circuit: coefficients are exact", "a SPICE model: the law is the Lean structure, SPICE would be an exterior codec"]
    return sheet("Complex Parametron", "the primitive computational component: exact complex current through oriented incidence with a receiver form", sym, fp, lean, params, ports, rule, receipts, nots,
                 h=820, sources="sources: docs/canon/TABLET_THE_REASONING_CYCLE.md §8d · Millennium/HolonicComplexParametron.lean · HolonicParametron.lean · MorphoHDL rule/fallback · KiCad symbol/footprint/model triple")

def simple_sheet(file, title, kind, glyph_fn, foot_txt, lean, params, ports, rule, receipts, nots, sources):
    @board(file, title, 1400, 760, "page-library")
    def _b():
        d = s_arrow_defs() + glyph_fn()
        f = ''.join(s_text(20, 30 + 20*i, t, "svgtxt") for i, t in enumerate(foot_txt))
        return sheet(title.split(" — ")[-1], kind, sym_box(d), sym_box(f, 430, 110), lean, params, ports, rule, receipts, nots, sources, 1400, 760)
    return _b

def g_receiver():
    d = s_path("M 120 40 L 90 85 L 120 130", "ink", 'stroke-width="2.5"'); d += s_line(120, 85, 200, 85, "ink"); d += s_circ(200, 85, 3, "ink", 'fill="#292418"')
    d += s_text(60, 60, "⟨ρ|", "svgmath"); d += s_text(210, 89, ".in", "svgtxt"); d += s_text(230, 40, "anchors: .in .label", "svgtxt"); d += s_text(230, 60, "reads one face; carries nothing back", "svgtxt")
    return d
simple_sheet("LibReceiver.dc.html", "Library 2 — Receiver ⟨ρ|", "a bra placed on the lattice: a probe, a projection, a measurement", g_receiver,
    ["occupies 0 sites · attaches to 1 site or 1 edge", "no keep-out · many receivers per site allowed", "the face is drawn beside it, never on the net"],
    "receiver : (X → Y) with aperture, calibration, preserved, forgotten, transition law   -- docs/canon/08:160\nface   ρ x : Y                    -- testimony about x through ρ, never its identity\nexact  ρ : ∀ future distinction at scope factors through ρ",
    [["chart", "enum", "site", "site | edge | storage | phase"], ["carrier", "enum", "ℚ(i)", "reading carrier"], ["forgets", "text", "declared", "named collapsed population"]],
    [[".in", "receiver", "in", "the only port"]],
    "no rewrite: a receiver is atomic\nconstraint: attaches to exactly one occurrence",
    [box("carried", grade("definition") + " docs/canon/00_PURE_HOLONICS.md:12 · SPINE:181")],
    ["a wire: it carries nothing", "an output: it is a reading, not an emission"],
    "sources: docs/canon/00:12 · 08:160 · TABLET_THE_OPERATIONS.md:59")

def g_transport():
    d = s_line(40, 85, 110, 85, "ink"); d += s_rect(110, 65, 90, 40, "ink", 4); d += s_text(140, 90, "X", "svgmath"); d += s_line(200, 85, 270, 85, "ink", 'marker-end="url(#ahk)"')
    d += s_text(30, 75, ".a", "svgtxt"); d += s_text(272, 75, ".b", "svgtxt"); d += s_text(230, 40, "path-style bipole: to[X=…, l=, hand=]", "svgtxt"); d += s_text(230, 130, "invertible ⇒ rebase (chart change carries a Jacobian)", "svgtxt")
    return d
simple_sheet("LibTransport.dc.html", "Library 3 — Transport X", "an edge component: carries a holon between charts; invertible transport is rebase", g_transport,
    ["occupies 1 oriented edge (or a path of edges)", "orientation = hand; reversal exchanges faces and negates the difference", "a chart transition carries its Jacobian"],
    "transport T_f : H_v → H_(v+1)       -- lawful composite when output ports meet input ports and port lineage is retained (docs/canon/01:56)\n<ρ|y> = <ρ|T_f|x>                    -- docs/canon/TABLET_THE_REASONING_CYCLE.md:79\nrebase ⇔ invertible; kernel/image/cokernel returned otherwise (AGENTS: matrix inversion is only the rebase case)",
    [["law", "enum", "linear", "linear | conjugation | continuation | rewrite"], ["hand", "±", "+", "e^{iπ} reverses"], ["exact", "bool", "true", "exact carrier required"]],
    [[".a", "shared", "in", "source node"], [".b", "shared", "out", "target node"]],
    "composition: serial keeps W_f ×_Y W_g; parallel needs an interchange receipt\nconstraint: both boundary maps preserved (passage equivalence)",
    [box("carried", grade("definition") + " docs/canon/TABLET_THE_OPERATIONS.md:46 · 01:56")],
    ["a wire in the EDA sense: a wire here is a passage with both boundary maps, not a connection"],
    "sources: docs/canon/TABLET_THE_OPERATIONS.md §1,§3.1 · docs/canon/01_CAUSAL_CALCULUS.md:56")

def g_deposit():
    d = s_line(40, 85, 120, 85, "ink"); d += s_line(120, 55, 120, 115, "ink", 'stroke-width="3"'); d += s_line(140, 55, 140, 115, "ink", 'stroke-width="3"'); d += s_line(140, 85, 220, 85, "ink")
    d += s_text(100, 40, "|a⟩⟨a|", "svgmath"); d += s_text(230, 60, "a construction reversed into a receiver", "svgtxt"); d += s_text(230, 80, "the emanation becomes the pole the next", "svgtxt"); d += s_text(230, 100, "arrival is related from (SPINE §4)", "svgtxt")
    return d
simple_sheet("LibDeposit.dc.html", "Library 4 — Deposit |a⟩⟨a|", "terrain: a construction reversed into a receiver; memory and conditioning live here", g_deposit,
    ["occupies 1 site (the pole)", "changes the continuation fibre of later current", "one symbol, two species: quotient when applied, deposit when read as terrain"],
    "deposit |a⟩⟨a| : construction → receiver          -- docs/canon/TABLET_THE_OPERATIONS.md:62\nΣᵢ |aᵢ⟩⟨aᵢ| = I  only for a G-orthonormal family; else frame operator S, dual frame S⁻¹|aᵢ⟩\nresidue changes the continuation fibre; later passage navigates terrain drawn by earlier motion (CIRCULATING_CARTOGRAPHER:24)",
    [["G", "inner product", "declared", "required before any resolution claim"], ["family", "list", "[a]", "deposited constructions"]],
    [[".pole", "shared", "shared", "the site it conditions"], [".read", "shared", "shared", "a site a receiver may attach to; read as terrain"]],
    "no rewrite\nconstraint: G declared or the resolution row is refused",
    [box("carried", grade("definition") + " " + grade("proved-standard") + " frame operator / dual frame (corrected 2026-08-17)")],
    ["a database record: nothing is looked up; later current rides it", "a projection without its metric"],
    "sources: docs/canon/TABLET_THE_OPERATIONS.md:62–82 · THE_HOLOBROCHOS_SPINE.md §4")

def g_junction():
    d = s_circ(130, 85, 6, "ink", 'fill="#292418"'); d += s_line(40, 85, 124, 85, "ink"); d += s_line(136, 85, 220, 85, "ink"); d += s_line(130, 20, 130, 79, "ink")
    d += s_text(50, 75, "+", "svgmath"); d += s_text(135, 40, "−  (e^{iπ}: the other hand)", "svgmath"); d += s_text(230, 60, "addition = co-presence at a junction", "svgtxt"); d += s_text(230, 80, "subtraction = same, one arm turned", "svgtxt"); d += s_text(230, 100, "what leaves is co-present, not serial", "svgtxt")
    return d
simple_sheet("LibJunction.dc.html", "Library 5 — Junction (+/−)", "where current distributes: the construction behind addition and subtraction", g_junction,
    ["occupies 1 site", "arms: k ≥ 2 oriented edges with hands", "the difference is a face of the retained pair, not the pair"],
    "junction : co-presence of arms at one site; each arm carries a hand ∈ {+, −}\nComparativeMultiplicity retains both arms: is_zero (nothing deposited) ≠ difference_is_zero (passages cancel)  -- OPERATIONS §2\nrouter (ML chart) = conditional transport junction",
    [["arms", "int", "3", "≥ 2"], ["hands", "list ±", "[+,+,−]", "per arm"]],
    [[".arm[i]", "shared", "in/out", "typed"], [".out", "emission", "out", "co-present current"]],
    "fallback := wire (arms = 2, hands equal)\nconstraint: hands declared before any additive receiver maps into a signed chart",
    [box("carried", grade("definition") + " docs/canon/TABLET_THE_OPERATIONS.md §2 · THE_SURFACES_ARE_PATHS.md:79")],
    ["an adder: nothing scales; a sum is a face of co-presence"],
    "sources: docs/canon/TABLET_THE_OPERATIONS.md §2 · THE_SURFACES_ARE_PATHS.md:79 · TABLET_THE_TURN.md")

def g_vertex():
    d = s_circ(150, 85, 10, "ink", 'fill="#292418"'); d += s_line(50, 40, 142, 80, "wire", 'marker-end="url(#ah)"'); d += s_line(50, 130, 142, 90, "wire", 'marker-end="url(#ah)"'); d += s_line(160, 85, 250, 85, "wire", 'marker-end="url(#ah)"')
    d += s_path("M 150 75 " + " ".join(f"L {150+i*8} {60 - (6 if i%2 else -6)}" for i in range(1, 10)), "grey", 'stroke="#9c5480"'); d += s_text(230, 40, "vertex = typed interaction", "svgtxt"); d += s_text(230, 130, "ports, hand, cross term, current, obstruction, residue", "svgtxt")
    return d
simple_sheet("LibVertex.dc.html", "Library 6 — Interaction vertex", "the Feynman vertex as a component: local constitutive interaction with its cross term and residue", g_vertex,
    ["occupies 1 site", "legs: typed ports; internal edges: transported relations", "loops: plural internal histories; face = Σ_Γ ⟨β|T_Γ|α⟩"],
    "vertex : (ports_in, hand, Γ : constitutive law, cross u∧v, out current, obstruction, residue)   -- REASONING_CYCLE:106\nα_j = Γ(⟨ρ|c_1⟩ … ⟨ρ|c_n⟩)_j ;  |δx⟩ = Σ_j α_j |u_j⟩                                          -- REASONING_CYCLE §2\ngeometric product uv = u·v + u∧v keeps both grades                                             -- OPERATIONS §3.2",
    [["Γ", "law", "bilinear", "softmax ⇒ barycentric (declared)"], ["legs", "int", "3", "≥ 2"], ["keep cross", "bool", "true", "multivector retained"]],
    [[".in[i]", "return", "in", "carried constructions"], [".out", "emission", "out", "one current"], [".residue", "exterior", "—", "chronological standing"]],
    "fallback := junction (Γ linear, no cross term)\nconstraint: obstruction retained; a refused contact is drawn dashed",
    [box("carried", grade("interpretation") + " external legs = typed ports, vertices = local constitutive interactions (TABLET_THE_CAUSAL_PROFILE.md:146)")],
    ["a claim of quantum field identity: bra-ket types transport only (CAUSAL_PROFILE:215)"],
    "sources: docs/canon/TABLET_THE_REASONING_CYCLE.md §2,:106 · TABLET_THE_CAUSAL_PROFILE.md:146,215 · OPERATIONS §3.2")

def g_membrane():
    d = s_rect(70, 30, 160, 110, "ink", 10, 'stroke-dasharray="6 4" stroke-width="2"'); d += s_line(20, 60, 70, 60, "wire", 'marker-end="url(#ah)"'); d += s_line(230, 110, 280, 110, "wire", 'marker-end="url(#ah)"'); d += s_line(280, 60, 230, 60, "wire", 'marker-end="url(#ah)"')
    d += s_text(80, 90, "one membrane, two orientations", "svgtxt"); d += s_text(20, 50, "ingress", "svgtxt"); d += s_text(236, 130, "egress / radiation", "svgtxt"); d += s_text(236, 50, "return", "svgtxt")
    return d
simple_sheet("LibMembrane.dc.html", "Library 7 — Membrane", "a boundary with ports: ingress and egress are one membrane read in two orientations; the clock lives here", g_membrane,
    ["occupies a closed (k−1)-cycle of the lattice", "ports = crossing sites; nothing crosses elsewhere", "hierarchical sheet: a membrane is how a sub-lattice is instanced (KiCad sheet pins)"],
    "membrane : distributed local phase and sampling boundary, not a global instant  -- docs/canon/02:67\ningress/egress : opposite orientations of one membrane                            -- blueprint WORLD_TUBE:91\nboundary flux : the only terms that decouple a partition are boundary fluxes; every other term is a barrier (SPINE:710, H.0219)",
    [["ports", "list", "[]", "crossing sites"], ["phase", "sampling", "local", "no global instant"], ["instance", "sheet", "—", "per-path identity of the interior"]],
    [[".in[i]", "return", "in", "ingress crossing"], [".out[j]", "emission", "out", "egress / radiation"], [".ret", "feedback", "in", "exterior return"]],
    "rewrite: instantiate the interior lattice per instance path (hierarchical sheets)\nconstraint: every interior passage crossing the cycle passes a declared port",
    [box("carried", grade("definition") + " docs/canon/02:67 · SPINE:710")],
    ["a container: it is a cut with ports, not a place"],
    "sources: docs/canon/02_INFORMATION_PHYSICS.md:67 · THE_HOLOBROCHOS_SPINE.md:710 · KiCad hierarchical sheets (form)")

def g_site():
    d = s_circ(80, 85, 6, "ink", 'fill="#fffdf8"'); d += s_circ(200, 85, 6, "ink", 'fill="#fffdf8"'); d += s_line(86, 85, 194, 85, "wire", 'marker-end="url(#ah)" stroke-width="2"')
    d += s_text(60, 110, "site", "svgtxt"); d += s_text(120, 75, "oriented edge: target − source", "svgtxt"); d += s_text(230, 60, "primitives of the lattice face", "svgtxt"); d += s_text(230, 80, "a cell is admitted by a caused occurrence,", "svgtxt"); d += s_text(230, 100, "never minted by projection", "svgtxt")
    return d
simple_sheet("LibSite.dc.html", "Library 8 — Site and oriented edge", "the lattice primitives: situated occurrence and exact oriented incidence", g_site,
    ["site: 1 coordinate tuple in a chart, capacity", "edge: ordered pair, entry ±1 in B", "cells admitted only by caused occurrence or explicit inherited construction"],
    "site  : Occurrence with capacity                                       -- THE_SURFACES_ARE_PATHS:99\nedge  : target − source ; reversal exchanges faces and negates (ADDRESSED_TRANSPORT_CHAIN:432)\n(C_•, ∂) graded occurrence complex with exact oriented incidence, ∂² = 0   -- docs/canon/01:10",
    [["chart", "enum", "ℤ⁴", "coordinates live in a declared chart"], ["capacity", "exact", "1", "site"], ["delay", "exact", "1", "passage characteristic"]],
    [[".self", "shared", "shared", "a site is a node others may share"]],
    "no rewrite\nconstraint: coordinates from a request; freeness reported by the solver",
    [box("carried", grade("definition") + " docs/canon/01:10 · THE_SURFACES_ARE_PATHS.md:99")],
    ["a pixel or a sample: an observer's coordinate mints nothing"],
    "sources: docs/canon/01_CAUSAL_CALCULUS.md:10 · THE_SURFACES_ARE_PATHS.md:99 · blueprint ADDRESSED_TRANSPORT_CHAIN:432")

def g_pump():
    d = s_circ(130, 85, 30, "ink"); d += s_path("M 105 85 q 12 -20 25 0 t 25 0", "ink"); d += s_line(160, 85, 240, 85, "ink"); d += s_line(20, 85, 100, 85, "ink")
    d += s_text(120, 130, "ω, φ exact", "svgmath"); d += s_text(230, 50, "parametric drive: an intervention channel", "svgtxt"); d += s_text(230, 70, "holding it fixed is an intervention (§8d)", "svgtxt")
    return d
simple_sheet("LibPump.dc.html", "Library 9 — Pump / drive", "the parametric drive: the source of the two locked sheets", g_pump,
    ["occupies 1 edge", "phase in ℚ(ζ_k) — exact cyclotomic", "a source term r_k in q_{k+1} − q_k + B j_k = r_k"],
    "drive ω : exact phase ; pump-storage receiver identifies the two half-turn-related sheets while the complex carrier changes sign  -- HolonicParametron.lean (§8d)\nsource r_k supplied residual                                                                                                -- docs/canon/02:53",
    [["ω", "exact phase", "2π/12", "ζ₁₂"], ["φ", "exact phase", "0", "relative"], ["amplitude", "exact", "1", "ℚ"]],
    [[".out", "pump", "out", "into a .pump port"]],
    "no rewrite\nconstraint: exactly one .pump target",
    [box("carried", grade("proved-derived") + " " + tag("formal-checked") + " HolonicParametron.lean")],
    ["a clock: a clock is a membrane phase, not a source"],
    "sources: docs/canon/TABLET_THE_REASONING_CYCLE.md §8d · 02_INFORMATION_PHYSICS.md:53")

def g_coupling():
    d = s_line(40, 60, 240, 60, "wire", 'marker-end="url(#ah)"'); d += s_line(40, 110, 240, 110, "wire", 'marker-end="url(#ah)"'); d += s_line(140, 60, 140, 110, "ink", 'stroke-dasharray="3 3"'); d += s_text(150, 90, "M_ij ≠ 0", "svgmath")
    d += s_text(230, 40, "mutual coupling: off-diagonal receiver form", "svgtxt"); d += s_text(230, 140, "shared node: identify sites (junction)", "svgtxt")
    return d
simple_sheet("LibCoupling.dc.html", "Library 10 — Coupling", "how carriers form a lattice: typed shared incidence or an off-diagonal constitutive term", g_coupling,
    ["shared: identifies one site of each carrier (0 new sites)", "mutual: an off-diagonal entry of M between two branches", "a population of carriers forms a lattice through typed shared incidence (§8d)"],
    "shared  : n_i(A) ≡ n_j(B) — typed shared incidence\nmutual  : M_{ab} = M_{ba}^* ≠ 0 between branches a ∈ A, b ∈ B ; holding it fixed is an intervention\nfusion  : plural spools fuse only after a successor-equivariant common transport subcomplex is founded (AGENTS Hexis clause)",
    [["kind", "enum", "shared", "shared | mutual"], ["M_ab", "exact", "1/4", "mutual only"]],
    [[".a", "shared", "shared", "carrier A site/branch"], [".b", "shared", "shared", "carrier B site/branch"]],
    "rewrite: couple(x, y) = junction at the shared node\nconstraint: hermiticity of M after coupling",
    [box("carried", grade("definition") + " canon §8d · " + grade("project-postulate") + " fusion law (AGENTS)")],
    ["a wire between boxes: coupling changes the storage form, not just connectivity"],
    "sources: docs/canon/TABLET_THE_REASONING_CYCLE.md:487 · AGENTS.md hexis/fusion clause")

def g_quotient():
    d = s_line(40, 55, 130, 85, "ink"); d += s_line(40, 115, 130, 85, "ink"); d += s_line(130, 85, 240, 85, "ink", 'marker-end="url(#ahk)"'); d += s_rect(120, 70, 20, 30, "ink", 3, 'fill="#9c5480"')
    d += s_text(20, 45, "sheet +", "svgtxt"); d += s_text(20, 135, "sheet −", "svgtxt"); d += s_text(150, 75, "sign face", "svgtxt"); d += s_text(230, 40, "quotient: names the collapsed population", "svgtxt"); d += s_text(230, 130, "binary Parametron = this face on the locked population", "svgtxt")
    return d
simple_sheet("LibQuotient.dc.html", "Library 11 — Quotient / lock", "a declared receiver's identification with the collapsed population as the exact loss", g_quotient,
    ["occupies 0 sites; attaches to a carrier", "outputs a face; retains the fibre beside it", "exact only when every declared future receiver factors through it"],
    "quotient q_R : X → X/~_R ; RF_R([x]) = (q_R)⁻¹([x]) retained                 -- OPERATIONS:286\nlock : sign face exact only on the declared locked population                  -- §8d\ncondensation removes a direction only if every declared future receiver factors; shortest reopening separator retained",
    [["receiver family", "list", "[sign]", "declared future receivers"], ["retain fibre", "bool", "true", "always"]],
    [[".in", "return", "in", "carrier"], [".face", "emission", "out", "the quotient face"], [".fibre", "exterior", "—", "kept visible"]],
    "no rewrite\nconstraint: refuses without a declared receiver family",
    [box("carried", grade("definition") + " OPERATIONS:48,286 · §8d")],
    ["lossy compression: the loss is named and its fibre kept"],
    "sources: docs/canon/TABLET_THE_OPERATIONS.md:48,275–286 · TABLET_THE_REASONING_CYCLE.md §8d")

def g_chart():
    d = s_path("M 60 120 L 140 120 L 180 60 L 100 60 Z", "ink", 'fill="#efece4"'); d += s_line(120, 90, 120, 30, "ink", 'marker-end="url(#ahk)"'); d += s_text(126, 40, "n (quaternion)", "svgtxt"); d += s_circ(120, 90, 3, "ink", 'fill="#292418"'); d += s_text(126, 100, "origin", "svgtxt")
    d += s_text(230, 50, "a chart is an entity: point + normal", "svgtxt"); d += s_text(230, 70, "3+1 split of 4 cycle directions", "svgtxt"); d += s_text(230, 90, "receiver coordinate, never the object", "svgtxt")
    return d
simple_sheet("LibChart.dc.html", "Library 12 — Chart / projection receiver", "a workplane-like entity: the declared reading through which nD sites are drawn", g_chart,
    ["occupies 0 sites; an entity of the geometry group", "sites store (u,v,w) in-chart and lift through the chart's basis", "chart change is the pullback of the reading — the Jacobian, nothing else"],
    "chart : (origin site, basis/quaternion, split : which cycle directions are shown, which sliced)\nreceiver-relative: a coordinate system is a declaration made by something that reads the space  -- TABLET_THE_CHART:17\natlas : charts + transition maps with cocycle g_ik = g_ij ∘ g_jk                                      -- TABLET_THE_MANIFOLD:65",
    [["split", "enum", "3+1", "3+1 | 2+2 | 1+3"], ["origin", "site", "(0,0,0,0)", ""], ["basis", "exact", "identity", "quaternion / frame"]],
    [[".origin", "shared", "shared", "anchoring site"]],
    "no rewrite\nconstraint: cocycle on triple overlaps when several charts are declared",
    [box("carried", grade("definition") + " TABLET_THE_CHART.md:17 · TABLET_THE_MANIFOLD.md:65 · SolveSpace workplane (form)")],
    ["a camera: the camera is a view preset; the chart is a type"],
    "sources: docs/canon/TABLET_THE_CHART.md · TABLET_THE_MANIFOLD.md §15 · AGENTS.md typed physical theory (4 directions, 6 planes) · solvespace workplane entity")

def g_tactic():
    d = s_rect(40, 60, 240, 50, "ink", 8, 'fill="#fffdf8"'); d += s_rect(50, 72, 70, 24, "ink", 4, 'fill="#3c6ea5" stroke="none"'); d += s_text(58, 88, "TRANSPORT", "svgtxt", 'fill="#fbf8f2"'); d += s_text(130, 90, "rw [h] at h₂", "svgtxt")
    d += s_text(300, 60, "species by tactic class (proposal):", "svgtxt"); d += s_text(300, 78, "rw/simp/unfold → transport · exact/apply → conjugacy (transport)", "svgtxt"); d += s_text(300, 96, "rfl → face · intro/have → construction/deposit · cases → plural continuation", "svgtxt"); d += s_text(300, 114, "linarith/ring → faces, not edges (TYPED_TRANSPORT_ATLAS:288)", "svgtxt")
    return d
simple_sheet("LibTactic.dc.html", "Library 13 — Tactic swing", "the trace component: one authored tactic as a typed swing with its species", g_tactic,
    ["occupies 1 step of the world-tube (t)", "boxes: nested boundary transports", "the chip is the symbol; the fibre is the model"],
    "TacticSwing : Swing with operator = TacticInfo, fibre = assignment Expr + mctx delta   -- Types 2\nedge species: rw = substitution (chart transition, carries a Jacobian) · exact/apply = conjugacy · induction = recurrence · linarith/ring = faces  -- blueprint/THE_TYPED_TRANSPORT_ATLAS.md:288, THE_METHOD_ATLAS:117",
    [["species", "enum", "auto", "override allowed, recorded"], ["breakpoint", "bool", "false", "debugger"]],
    [[".before", "return", "in", "goal occurrence"], [".after[i]", "emission", "out", "owed goals"], [".spawned[j]", "exterior", "—", "side quests (have/by/calc)"]],
    "rewrite: macro expansion → innermost authored tactic wins (paperproof commonGoals rule)\nconstraint: goalBefore unique per step; backtracking keeps last writer",
    [box("carried", grade("definition") + " AGENTS.md:99 · " + grade("interpretation") + " species assignment per tactic class")],
    ["a line of text: the string is the symbol's label; the swing is the object"],
    "sources: paperproof handleTacticApp cases · blueprint/THE_TYPED_TRANSPORT_ATLAS.md:288 · THE_METHOD_ATLAS.md:117")

def g_hypgoal():
    d = s_rect(30, 40, 180, 36, "ink", 6, 'fill="#efece4"'); d += s_text(40, 62, "h : a ≤ b   _uniq.377 · data", "svgtxt"); d += s_rect(30, 100, 180, 36, "ink", 6, 'fill="#fffdf8" stroke="#a67a2e" stroke-width="1.5"'); d += s_text(40, 122, "⊢ a < b + 1   ?m.412", "svgtxt")
    d += s_text(230, 50, "hypothesis: what we know (green in paperproof)", "svgtxt"); d += s_text(230, 70, "goal: what is left to show (red)", "svgtxt"); d += s_text(230, 110, "identity: fvarId / mvarId, Lean-minted", "svgtxt"); d += s_text(230, 130, "cleared hyps stay, drawn refused", "svgtxt")
    return d
simple_sheet("LibHypGoal.dc.html", "Library 14 — Hypothesis and goal", "the two occurrence kinds of the trace face; boxes nest by boundary", g_hypgoal,
    ["hypothesis: 1 row of a box's hyp table; goal: 1 rung of the ascending stack", "child boxes for plural continuation; have/by boxes for side quests", "identity is Lean's, aliased by an equivalent-ids union"],
    "HypOccurrence  : {id : fvarId, name, type : Expr, isProof, born t, changed t[], cleared t?, alias}\nGoalOccurrence : {id : mvarId, type : Expr, hyps, box, owed_by : swing, closed_by : swing? (successGoalId)}\nunsolved goal  : no swing has it as before — drawn as an open fibre (…), never hidden",
    [["show universes", "bool", "false", "paperproof drops; we retain, hide by default"], ["hoist data", "bool", "true", "childless data hyps to the header"]],
    [[".from", "return", "in", "the swing that made it"], [".to[i]", "emission", "out", "swings that use it (dependsOn)"]],
    "layout: grid by descendant width (a hyp sits above what it derives) — paperproof hypsToTables\nconstraint: one closing swing per box",
    [box("carried", grade("definition") + " paperproof ConvertedProofTree · Types 2")],
    ["a variable in a debugger watch: it has lineage, species and a grade"],
    "sources: Paper-Proof/paperproof app/types/ConvertedProofTree.ts · app/src/services/hypsToTables.ts")
