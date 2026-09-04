# Holonic CAD design testimony — export for Sol (2026-08-30)

[definition] Everything here is design testimony under `archive/plans/THE_PRESENTATION_ORGAN.md`. It schedules nothing, asserts no engine capability, and is not canon. CONS1 / the UAR freeze are untouched. Files are exported verbatim from the Claude session scratchpad (session `deaf7379`), with the published artifact URLs recorded so the online copies can be compared.

## The two artifacts

| artifact | URL | latest label | export |
|---|---|---|---|
| Holonic Expression Manipulator (pass 1: low-fidelity CAD wireframes, 46 artboards on 7 pages) | https://claude.ai/code/artifact/c6ef8191-7b8c-4a12-b2da-6ad596d9bef5 | v1.1 (second-look corrections) | `expression-manipulator/` |
| Holonic Render Codec (passes 2–4: exact rendering codec + internal JS library, 10 scenes) | https://claude.ai/code/artifact/21f8b9d6-280d-45e8-940d-32f1e5f1b727 | render-codec-v2.1-intaglio-b | `render-codec/` |

## render-codec/
- `holonic-render-codec.html` — the published single file (224 kB, no external libraries). Open in a browser; every scene prints receipts and runs the gauge falsifier; “show svg” emits the vector face with `data-source` exact values on every mark.
- `src/` — the library. `bash build.sh` rebuilds `../holonic-render-codec.html` byte-for-byte (verified). `node test_*.js` runs the Node tests (all pass).
  - `core.js` Rat (BigInt), orient2d, segIntersect (collinear touch vs overlap), angleCmp, PlanarMap (dart faces, Euler, face-dual), FourColor (exact search)
  - `colour.js` dimensional_wave transduction (P₀,P₁,P₂; κ; α+τ=1) — the only colour law
  - `quadfield.js` ℚ(√Δ) carrier; Pythagorean speeds; readStaticSite (retarded time, aberration, Doppler)
  - `poly.js` exact multivariate polynomials (eval, gradient, Hessian)
  - `fields.js` Navier–Stokes (vorticity–streamfunction, spectral) and Klein–Gordon on the periodic lattice; `dissipation()` = ν|∇ω|²
  - `models.js` ℤ⁴/ℤ³ lattices, Chart (oblique / perspective), exact visibility, depth traces, renderPlan
  - `glyphs.js` rigid symbol library (19 symbols; hands not arrowheads; D4 orientations; placeAlong = exact similarity onto a projected edge; rational circle points)
  - `regions.js` band regions + dual-lattice boundaries (Float64 fields)
  - `brackets.js` levelBrackets (dual lattice) and **isolate** (exact bisection on grid edges; saddle cells decided by centre sign)
  - `hatch.js` principal directions in ℚ(√Δ) from I, II; sign of K; foreshortening predicate for cross-hatch
  - `receivers.js` Affine2 over ℚ; Receiver tree (grain, seam-aware address, Gram, hand); cycleDeficit (layout curvature); atlas (exact ≤4-class chart colouring)
  - `minkowski.js` events, worldlines, cone, Pythagorean boost, proper-time ticks, rational γ and Doppler
  - `circuit.js` ℚ(i) Gauss–Jordan; ℤ³ Kirchhoff G = BᵀMB; KCL receipt; hypergraph incidence; schematic plan (width ⌈|I|/unit⌉ via integer ceil-sqrt, hands, under-strand gaps)
  - `bord.js` Leinster p.8 cells as exact polynomial level sets; isolated slices; wall traces; hatch stations
  - `polygraph.js` n-polygraph with globular checks on chains; ℤ³ → 27/54/36/8, Euler 1; planar map → 2-polygraph
  - `codec.js` holonic-render-v2 document schema, generators, mounts, canonical digest
  - `paper.js` Canvas presentation face + SVG vector face; structuralResidue (gauge falsifier)
  - `app.js`, `app3.js` the ten scenes
- `reports/` — Sonnet/Opus extraction reports with page-cited quotes and `*.structures.json` records (relativistic rendering, discrete fields, holonic rendering owners, polygraphs low/high, Leinster structures, Brown–Porter/Leinster-rough/MathWorld, Dorn–Douglas manifold diagrams, Akleman weaving). `SOURCE_PDFS.txt` lists the PDFs read (not copied; arXiv/author URLs in the page notes).

## expression-manipulator/
- `holonic-expression-manipulator.html` — the published design canvas (3.1 MB; contains the Claude Design editor payload + the 46 artboards).
- `artboards/` — the artboards extracted from that file (`*.dc.html` + `canvas.json`); the six non-Holonic boards (AlgebraGeometry, NumberShapes, RubikBoard, SolverBoard, TheBands, TheDescentAtFive) are the earlier archive the canvas preserved, not part of the CAD design.
- `generator/` — the Python that seeded the boards (`gen.py`, `lib.py`, `boards_*.py`) and `check.js`.
- `reports/` — pass-1 reference extractions (paperproof, MorphoHDL, OpenSCAD, SolveSpace, KiCad, FreeCAD/LibreCAD, GElectrical/QET/circuitikz) and the holonics types/canon extractions.

## Points Sol should check first
1. Colour doctrine: the page mirrors `dimensional_wave.rs` and keeps “NO FOUR-COLOR GOVERNOR”; the ≤4-class colouring is used only to distinguish charts (tint + D4 cell-mark direction). Confirm this reading of `research/records/2026-07-25` and `2026-07-30`.
2. Isolation law: contour vertices are midpoints of exact isolating intervals (bisection on grid edges); saddle cells decided by the exact centre sign. Compare with `certified_face.rs` (Sturm count → isolate) and `model_surface.rs` (certified sign change) — the page has no Sturm counting; obstructions are only the saddle decisions.
3. Intaglio: principal directions in ℚ(√Δ) per station; K sign = sign det II; cross-hatch predicate (n·v)² ≤ τ(n·n)(v·v). Is “tone as a predicate” the right presentation-gauge reading?
4. Dilated expressions: measurements as rest quantity × named exact factors (γ⁻¹, f/(f+z), k, s, DPR; D = n/m for Pythagorean u). Is this the right codec type for “compressed transformations between frames”?
5. Receiver tree: Affine2 relations, seam addressing, Gram with hand kept apart, cycle deficit as layout curvature; the browser’s vectors admitted as exact dyadics. Map onto `receiver_atlas.rs` / `TABLET_THE_CHART.md` / `layout_curvature_consumption.rs`.
6. Findings recorded on the page: OpenRelativity applies D⁻³ to a wavelength-parametrised spectrum (D² residual); Brower et al. internal factor-of-2; Brown–Porter has no “local-to-global”/“interchange” in its prose; the Polygraphs book writes P₀…Pₙ not Σ; 2208.13758 is Dorn–Douglas (manifold diagrams), not a hatching paper.
7. Open: exact ℚ carrier for field ticks stays engine-side; Sturm-certified feature counting for curves; Bord slices drawn without painter’s order; NS entropy production vs the semi-Lagrangian scheme’s numerical diffusion (stated in the receipt).

Provenance: cursor OBJ-28933086-1ece-46d2-8cdc-99b69124e695 (“Holonic Graphics Source Cartographer”) carries the intent/completion messages for passes 2–4 (latest OBJ-8c2cfad2-0443-4fe4-8448-ca5cc7ed5bf2); released.
