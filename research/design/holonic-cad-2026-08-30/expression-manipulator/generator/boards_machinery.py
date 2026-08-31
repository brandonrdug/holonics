from lib import *
from gen import board, note_on

def pipeline(stages, w=1340, h=150):
    n = len(stages); bw = (w - 20 - (n-1)*26) / n; d = s_arrow_defs()
    for i, (t, l1, l2, kind) in enumerate(stages):
        x = 10 + i*(bw+26)
        fill = {"transport": "#e4ecf5", "face": "#f3ead9", "construction": "#e6efe6", "quotient": "#f3e6ec", "": "#fffdf8"}[kind]
        d += s_rect(x, 20, bw, 100, "ink", 6, f'fill="{fill}"')
        d += s_text(x+8, 40, t, "svgtxt", 'font-weight="500"'); d += s_text(x+8, 62, l1, "svgtxt"); d += s_text(x+8, 80, l2, "svgtxt")
        if kind: d += s_text(x+8, 108, kind.upper(), "svgtxt", 'fill="#7a7060"')
        if i < n-1: d += s_line(x+bw, 70, x+bw+24, 70, "wire", 'marker-end="url(#ah)"')
    return svg(w, h, d, "width:100%; height:auto")

@board("MachExtract.dc.html", "Machinery 1 — Lean → trace: extraction as a receiver", 1400, 860, "page-machinery")
def mach_extract():
    p = pipeline([("snapshot", "withWaitFindSnapAtPos", "elab snapshot at cursor", ""),
                  ("InfoTree walk", "post-order visitM", "TacticInfo + TermInfo nodes", "transport"),
                  ("authored filter", "stx.getSubstring?", "drop macro noise", "quotient"),
                  ("mctx diff", "unassigned before/after", "commonGoals removed", "face"),
                  ("edges", "collectMVars / collectFVars", "on the assignment", "construction"),
                  ("orphans", "allGoals − in-edges", "spawned: have/by/calc", "construction"),
                  ("swings", "flat List ProofStep", "+ t index, fibre, grade", "construction"),
                  ("boxes", "pure converter (ms)", "nest by parentId", "face")])
    left = panel("paperproof's pipeline, retyped (each stage is a species)", p + table(["stage", "paperproof", "the CAD"], [
        ["identity", "fvarId / mvarId strings; equivalentIds alias", "same ids + alias union; cleared occurrences retained with t"],
        ["update", "full refetch per cursor move; no cache", "incremental: the InfoTree is a chain; re-extract only frames whose syntax range changed"],
        ["fibre", "goalsAfter/spawned printed at mctxAfter", "every mctx snapshot, assignment Expr, delayed assignments, elab/instance trace"],
        ["term mode", "not modelled", "TermInfo tree walked as swings"],
        ["offline", "lake exe terminal FILE CONST OUT.json", "same, plus golden #assert_parser snapshots as receipts"],
        ["direction", "Lean → view only", "view → Lean through the projection port: a diagram edit emits a tactic swing proposal, kernel verdict returns later"],
    ]), "flex: 1 1 auto")
    right = panel("boundary", box("lean", "Lean is an exterior codec/checker port: the extraction is a <b>receiver</b> over Lean's InfoTree, and the trace it returns is a face of the native complex. The kernel verdict is a later world event attached to a projected passage.") +
                  box("obstructed", "an import graph, syntax tree, or kernel verdict may supply exterior testimony but may not become the map (AGENTS.md causal arithmetic clause on Lean)") +
                  box("carried", "golden testing: <span class='mono'>#assert_parser in</span> + <span class='mono'>#guard_msgs</span> gives deterministic textual receipts per theorem without an IDE") + box("hyp", grade("interpretation") + " the retyping is proposed; the paperproof stages are source-inspected"), "flex: 0 0 360px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Lean → trace", "extraction as a receiver over the InfoTree; assignment-driven edges; the flat step list plus a pure structural converter", 1400, 860, body,
                    "sources: Paper-Proof/paperproof lean/Services/BetterParser.lean, app/src/services/converter.ts · AGENTS.md mathematical production boundary")

@board("MachGrow.dc.html", "Machinery 2 — program → lattice: evaluate, grow, normalize", 1400, 860, "page-machinery")
def mach_grow():
    p = pipeline([("parse", "AST with Location", "every node carries its span", ""),
                  ("evaluate", "AST → node tree", "from scratch per compile; $-vars dynamic", "transport"),
                  ("materialize", "name:[signature] registry", "widths inferred, memoized", "construction"),
                  ("grow", "local rewrite per step", "fallback on boundary", "construction"),
                  ("optimize", "const-prop · DCE · fanout", "worklists, self-invalidating", "quotient"),
                  ("normalize", "Goldfeather → Σ products", "canonical before rendering", "quotient"),
                  ("geometry", "exact lattice / mesh", "cache key = subtree dump", "face"),
                  ("project", "chart → 2D/3D face", "$preview vs exact", "face")])
    left = panel("OpenSCAD's tower × MorphoHDL's growth, as one deterministic evaluation", p + table(["stage", "OpenSCAD", "MorphoHDL", "the CAD"], [
        ["identity", "idx reset per compile; modinst → syntax", "append-only index; active flag; parent", "occurrence id = (birth moment, rank); parent lineage; never reset"],
        ["parameters", "top-level literals + comment annotations → customizer; presets JSON", "signature = input widths", "customizer inferred from the Lean def's explicit args + attributes; presets as parameter sets"],
        ["control flow", "if/for/let are modules; no state", "fallback is the only control flow", "boundary → fallback; branch = plural continuation, never a chooser"],
        ["modifiers", "! # % * per node", "—", "same four, propagated through the term"],
        ["canonical form", "CSG sum of products", "netlist after DCE", "the normalized complex; digest is a receipt only"],
        ["cache", "GeometryCache by getIdString", "registry by name:[sig]", "both; keyed by content, invalidated by content"],
        ["order", "postfix visitor", "BFS / largest-first / traced, order-independent result", "schedule is aesthetic and placement only; receipt: equal digest under all schedules"],
    ]), "flex: 1 1 auto")
    right = panel("boundary", box("lean", "the program is Lean; the attribute marks a rewrite rule with a fallback; the lattice is <span class='mono'>eval(program, chart)</span> — no persistent geometry state, reproducibility free") +
                  box("obstructed", "OpenSCAD's doubles and MorphoHDL's JS numbers are refused: coordinates and coefficients are exact; a float may not determine an index or topology") +
                  box("refused", "no Interpreter / Scheduler cabinet: evaluation and growth compose existing owners (evolution, category, exact_linear, lattice_gauge); the schedule is a receiver shadow") + box("hyp", grade("interpretation") + " the tower is proposed; the OpenSCAD and MorphoHDL stages are source-inspected"), "flex: 0 0 360px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Program → lattice", "parse · evaluate · materialize · grow · optimize · normalize · geometry · project — one deterministic tower", 1400, 860, body,
                    "sources: openscad 1c9ee2b (node.h, CSGTreeNormalizer, customizer) · morpho dc8dd2e (compiler.js materialize, grower.js)")

@board("MachSolve.dc.html", "Machinery 4 — constraints: request → entity → param → equation → solve", 1400, 820, "page-machinery")
def mach_solve():
    p = pipeline([("requests", "declared: site, cycle, chart", "editable state", ""),
                  ("generate", "entities + params", "fixed slot layout per owner", "construction"),
                  ("equations", "constraints → residuals", "workplane picks 2 vs 3", "construction"),
                  ("substitute", "a = b unified symbolically", "solve-alone pass", "quotient"),
                  ("jacobian", "symbolic PartialWrt once", "evaluated per step, exact", "transport"),
                  ("rank / DOF", "dof = n − rank", "four result states", "face"),
                  ("diagnose", "leave-one-out redundancy", "free params by column drop", "face")])
    left = panel("SolveSpace's solver, retyped for lattice sites, ports and passages", p + table(["pattern", "SolveSpace", "the CAD"], [
        ["declared vs generated", "group/request/constraint editable; entity/param regenerated", "sites/ports/passages declared; the site table and unknowns regenerated, old values as guesses"],
        ["handles", "hEntity = request&lt;&lt;16 | idx; hEquation → constraint", "occurrence id carries the request lineage; every residual names its source"],
        ["sequential groups", "only the active group's params are unknowns", "earlier lattice groups are fixed inputs downstream — ordered passages"],
        ["algebra", "Expr: 15 ops, total PartialWrt, doubles", "the same inductive over ℚ / ℚ(i) with a proven derivative: a verified Jacobian is the Lean model"],
        ["drag", "soft weight 1/20; hard lock = WHERE_DRAGGED", "interactive exploration weights, never constrains; DOF unchanged"],
        ["reference", "generates no equation; ModifyToSatisfy", "a measurement is a face, not a constraint"],
        ["report", "OKAY / REDUNDANT_OKAY / DIDNT_CONVERGE / REDUNDANT_DIDNT_CONVERGE + dof + remove-any-one-of", "exactly these, as returned obstructions with receipts"],
    ]), "flex: 1 1 auto")
    right = panel("boundary", box("lean", "the swing in canon's dialect is <i>constraint equations</i> (THE_DIALECT:89): a constraint is a swing whose receiver is equality in the declared carrier") +
                  box("obstructed", "Newton over doubles is refused for identity-bearing decisions; exact rational arithmetic for rank/DOF, numeric only as a face for display") +
                  box("carried", "DOF is a first-class number on every lattice group; a free site is drawn amber") + box("hyp", grade("interpretation") + " this pipeline retypes SolveSpace; nothing here is implemented"), "flex: 0 0 360px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Constraints → DOF", "declared requests expand to entities and params; constraints are equation generators; the solver is type-blind and reports four states plus DOF", 1400, 820, body,
                    "sources: solvespace 3297d9a (src/sketch.h, generate.cpp, system.cpp) · canon/THE_DIALECT.md:89")

@board("MachIdentity.dc.html", "Machinery 7 — identity, history and the file", 1400, 820, "page-machinery")
def mach_identity():
    left = panel("identity across the references and the rule the CAD adopts", table(["system", "identity", "history", "lifted rule"], [
        ["paperproof", "Lean's fvarId/mvarId; alias union", "none (refetch)", "never mint ids for Lean objects; alias, don't rename"],
        ["MorphoHDL", "append-only index; active flag; parent", "implicit (nothing deleted)", "occurrence id = (birth moment, rank); deletion is a flag"],
        ["OpenSCAD", "idx reset per compile; modinst", "text undo only", "anchor every node to its syntax span both ways"],
        ["SolveSpace", "lineage handles; persisted remap for derived copies", "100-deep snapshot ring", "derived ids stable across regeneration via a persisted remap"],
        ["KiCad (master)", "KIID uuid per item; sheet-path instances", "COMMIT undo", "one uuid per occurrence; per-path instance identity for reused membranes"],
        ["FreeCAD (main 3b2c969)", "Name vs Label; topological naming problem", "transactions", "element names must survive recompute — the hard problem, owned explicitly"],
    ]) + note("the canon rule under all of these: unqualified equality is occurrence identity; every other equality is typed (canon/08:53). Equal bytes, hashes, coordinates or text never imply the same occurrence (canon/00:9)."), "flex: 1 1 auto")
    right = panel("the file · holonic-json-v1 as the primary face", code(
"""{ "document": { "owner": "one ecology", "grade": "…", "lineage": [...] },
  "occurrences": [ { "id": {"born": 4, "rank": 1}, "kind": "site", "chart": "z4", "coords": ["1","1","1","0"], "grade": "definition" } ],
  "passages":    [ { "id": …, "source": …, "population": [...], "target": …, "boundary_src": …, "boundary_tgt": …, "ports": [...], "current": {"carrier":"Q(i)","values":[...]}, "fibre": {...} } ],
  "components":  [ { "id": …, "rule": "parametron", "signature": [3], "params": {"M":…}, "symbol": …, "footprint": …, "model": "HolonicComplexParametron" } ],
  "swings":      [ { "t": 7, "before": …, "operator": …, "after": …, "receiver": …, "hypotheses": [...], "orientation": "+", "boundary": …, "grade": "…", "fibre": … } ],
  "receipts":    [ { "kind": "kernel", "attached_to": …, "toolchain": …, "axioms": [...] } ] }""") +
        note("s-expression (KiCad) and key=value (SolveSpace) are equally lawful exterior serializations; the JSON is the programmatic face named by AGENTS.md:97. A file store is an exterior chart, never the runtime topology; bytes are lineage, not identity. No schema exists in canon yet — this is a proposal, graded interpretation.") +
        box("obstructed", grade("open") + " holonic-json-v1 has no object schema in canon or blueprint; the sole normative mention is AGENTS.md:97"), "flex: 0 0 640px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Identity, history and the file", "occurrence identity is owner-minted; every reference's id scheme is a lesson; the file is a face", 1400, 820, body,
                    "sources: canon/08_CORE_MATHEMATICAL_INSTRUMENTS.md:53 · 00_PURE_HOLONICS.md:9 · AGENTS.md:97 · reference reports")

@board("MachNets.dc.html", "Machinery 3 — schematic → nets: the connection graph", 1400, 820, "page-machinery")
def mach_nets():
    p = pipeline([("place", "symbols with typed ports", "at a chart position", ""),
                  ("coincide", "port ↔ port by geometry", "grid-snapped, per sheet", "construction"),
                  ("label / link", "labels, sheet pins, report links", "coordinate-less ports", "transport"),
                  ("union", "connected components", "wires are elements, not edges", "quotient"),
                  ("nets", "one node per class", "renumbered, never stored", "face"),
                  ("check", "pairwise contact rules", "obstructions drawn", "face"),
                  ("project", "→ lattice / transport", "nets → shared incidence", "transport")])
    left = panel("GElectrical, QET and KiCad agree: nets are derived", p + table(["pattern", "reference", "the CAD"], [
        ["node identity", "GElectrical: (page,x,y) keys unioned by connected components; QET: DFS over terminal-conductor adjacency at query time; KiCad: CONNECTION_SUBGRAPH per sheet path, one driver resolved by PRIORITY (PIN &lt; SHEET_PIN &lt; HIER_LABEL &lt; LOCAL_LABEL &lt; … &lt; GLOBAL)", "a net is a face of port coincidence + declared links; never authored, never stored as truth; the naming driver is a declared priority lattice, not a first-come rule"],
        ["cross-sheet identity", "QET next/previous report; GElectrical Reference adds its code as a coordinate-less port; KiCad global labels + sheet pins", "a membrane's ports and a global label are the only cross-sheet contacts"],
        ["a wire", "GElectrical: element whose two ports are one node; QET: Conductor between two terminal uuids with properties; KiCad: SCH_LINE", "a passage with both boundary maps — glue at the net level, a carrier at the transport level"],
        ["checks", "KiCad ERC pin matrix; GElectrical rules (self / upstream / downstream_node) over the derived graph", "Library 0 contact rules + rules-as-data over the derived graph; obstructions drawn on the net"],
        ["results", "GElectrical: DisplayElementNode per (page, gnode), typed like inputs", "probe faces are elements in the drawing, typed like data"],
        ["numbering", "QET formula %f-%l%c propagated over the potential; GElectrical lexsort with freeze", "names are faces derived from kind and position; explicit freezing"],
    ]), "flex: 1 1 auto")
    right = panel("boundary", box("lean", "co-presence is not contact: a crossing of drawn wires is contact only through a junction component; contact requires a declared interaction (AGENTS.md ownership; TABLET_THE_CAUSAL_PROFILE:153)") +
                  box("carried", "the derived net becomes typed shared incidence in the lattice face and a shared node in the carrier's B — one object, three faces") +
                  box("obstructed", "an all-receiver net reads nothing; two emissions without a junction have no law — refused at check, kept visible") + box("hyp", grade("interpretation") + " the derivation is proposed; the three reference mechanisms are source-inspected"), "flex: 0 0 360px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("Schematic → nets", "port coincidence and declared links derive nets by connected components; checks are contact rules; results are typed elements", 1400, 820, body,
                    "sources: GElectrical model/networkmodel.py:93-188 · QET terminal.cpp:963-987 · KiCad connection graph / ERC docs · canon on contact and junctions")

@board("MachRecompute.dc.html", "Machinery 6 — the document DAG and recompute", 1400, 820, "page-machinery")
def mach_recompute():
    p = pipeline([("touch", "a property or program span changed", "Touched bit; fine-grained DepEdge", ""),
                  ("dependency list", "out-links → DAG", "topological sort; cycles → SCC", "construction"),
                  ("expressions (in)", "bindings evaluated with units", "before the kernel step", "transport"),
                  ("execute", "re-elaborate / re-project", "Lean check as a world event", "transport"),
                  ("expressions (out)", "output bindings", "after execute", "transport"),
                  ("error as data", "Which, Why on the node", "InList skipped, drawn", "face"),
                  ("commit", "transaction snapshot", "undo = replay copies", "construction")])
    left = panel("FreeCAD's recompute, retyped as circulation over the document", p + table(["pattern", "FreeCAD", "the CAD"], [
        ["node", "DocumentObject with typed Property members; PropertyLink with scope (Child/Global/Hidden)", "an occurrence with typed fields; links carry scope and lineage"],
        ["order", "buildDependencyList → boost topological_sort; two passes for dependency inversion", "the derivation circuit (derivation_atlas.rs: 0-cells declarations, 1-cells recruitment) is the DAG; re-elaborate touched frames only"],
        ["step", "expressions(non-output) → execute() → expressions(output); StdReturn or DocumentObjectExecReturn {Why, Which}", "project → check → return; a kernel refusal is data on the node and its InList waits, drawn"],
        ["names", "IndexedName Face1 vs MappedName (history-hashed) — the topological naming problem", "references into generated structure keyed by provenance: occurrence id = (birth, rank), alias union"],
        ["undo", "Transaction snapshots (Property::Copy/Paste); LibreCAD: deleted flag on immortal undoables", "append-only occurrences with active flags (MorphoHDL) — undo is implicit; history is never lost"],
        ["expressions", "AST with units; ObjectIdentifier paths; HIDDENREF opts out of dependency", "bindings are typed swings; a hidden reference is refused (every dependency is lineage)"],
    ]), "flex: 1 1 auto")
    right = panel("boundary", box("lean", "a file store is an exterior chart, never the runtime topology; mount broad material incrementally (AGENTS.md ownership)") +
                  box("carried", "every recompute carries an outer time bound; one that cannot return inside it is factored into resumable sections (AGENTS.md validation cadence)") +
                  box("obstructed", grade("open") + " exact incremental extraction from Lean: paperproof refetches everything; DerivationAtlas exports whole files — a per-frame delta exporter is absent"), "flex: 0 0 360px")
    body = row([left, right], "flex: 1 1 auto; min-height: 0")
    return artboard("The document DAG and recompute", "typed nodes, links with scope, topological recompute, errors as data, undo without loss", 1400, 820, body,
                    "sources: FreeCAD main 3b2c969 src/App/Document.cpp:2843 recompute, DocumentObject.h, PropertyLinks.h · LibreCAD rs_undo · MorphoHDL append-only cells · derivation_atlas.rs")
