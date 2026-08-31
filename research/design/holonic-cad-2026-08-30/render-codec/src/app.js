// ===== app.js — scenes bound to codec documents; every pixel traces to a generator parameter =====
(function (HR) {
  const { R, Rat } = HR;
  const $ = (s, el = document) => el.querySelector(s); const $$ = (s, el = document) => [...el.querySelectorAll(s)];
  const state = { scene: null, paper: null, doc: null, inst: null, playing: false, raf: 0, history: [] };
  const fmt = (x, d = 3) => (typeof x === 'number' ? (Math.abs(x) >= 1000 ? x.toFixed(0) : x.toFixed(d)) : String(x));
  const GAUGES = [{ name: 'declared', ink: '#101214', paper: '#f6f7f4' }, { name: 'permuted-gauge-b', ink: '#3a2a10', paper: '#fbf8f1' }];
  function setReceipts(rows) { const el = $('#receipts'); el.innerHTML = rows.map(([k, v, cls]) => `<div class="rk">${k}</div><div class="rv ${cls || ''}">${v}</div>`).join(''); }
  function gaugeReceipt(p) { const a = p.svg(GAUGES[0]), b = p.svg(GAUGES[1]); const ok = HR.structuralResidue(a) === HR.structuralResidue(b); state.lastSvg = a; return ['gauge falsifier', `${ok ? 'residues identical' : 'STRUCTURE MOVED'} under two gauges (${GAUGES[0].name} / ${GAUGES[1].name}) · ${p.marks.length} marks · ${(a.length / 1024).toFixed(0)} kB vector face`, ok ? 'ok' : 'bad']; }
  function setDoc(doc) { state.doc = doc; $('#doc').value = JSON.stringify(doc, null, 1); const errs = HR.Codec.validate(doc); $('#docstate').textContent = errs.length ? 'refused: ' + errs.join('; ') : 'admitted · digest ' + HR.Codec.receipt(doc).digest; $('#docstate').className = 'docstate ' + (errs.length ? 'bad' : 'ok'); return errs.length === 0; }
  function paperFor(unit, origin) { const cv = $('#canvas'); const w = cv.parentElement.clientWidth, h = cv.parentElement.clientHeight; state.paper = new HR.Paper(cv, { width: w, height: h, unit, origin }); return state.paper; }
  const rgb = (resp) => HR.Colour.css(HR.Colour.toRGB(resp));
  // ---------- scene: symbols ----------
  const SCENES = {};
  SCENES.symbols = {
    title: 'Symbols', doc: () => ({ schema: HR.Codec.SCHEMA, scene: 'symbols', generators: { sheet: { use: 'symbol.place', params: { symbol: 'parametron', at: ['0', '0'], orient: 'r0', scale: 1 } } }, gauge: { stroke: { hairline: 1, unit: '1/2' }, hand: { length: '1/8' } },
      schematic: { instances: [{ symbol: 'pump', at: [1, 4], quantity: '1' }, { symbol: 'parametron', at: [4, 4], scale: 2, quantity: '3/2' }, { symbol: 'junction', at: [7, 5], orient: 'r0' }, { symbol: 'receiver', at: [9, 5], orient: 'r180' }, { symbol: 'membrane', at: [8, 2], scale: 2 }, { symbol: 'exterior', at: [4, 7], orient: 'r90' }, { symbol: 'deposit', at: [1, 1] }],
        wires: [[['3/2', 4], [3, 4], [3, '7/2']], [[5, '7/2'], [5, 3], [7, 3], [7, 2]], [['13/2', 5], [4, 5], [4, '9/2']], [['15/2', 5], ['17/2', 5]], [[4, '13/2'], [4, 5]]] } }),
    render(doc) {
      const p = paperFor(44, [40, 40]); p.clear(); const unit = R(doc.gauge.stroke.unit);
      const names = Object.keys(HR.Glyphs.SYMBOLS); const gy = 9.6;
      HR.App.chartGround(p, { x0: -0.2, x1: 14.2, y0: gy - 3.7, y1: gy + 0.7 }, { cls: 1, step: 1, label: 'library receiver · unit cells' }); HR.App.chartGround(p, { x0: -0.2, x1: 11.2, y0: -0.7, y1: 5.6 }, { cls: 2, step: 1, label: 'schematic receiver · lattice cells' });
      names.forEach((n, i) => { const at = [0.5 + (i % 7) * 2, gy - Math.floor(i / 7) * 1.6]; drawGlyph(p, HR.Glyphs.place(n, at, 'r0', 1), { unit, labels: true }); p.text([at[0] - 0.5, at[1] - 0.62], n, { size: 9, color: '#5d6470' }); });
      p.text([0, gy + 0.9], 'library — anchors ringed, hands ticked on the + side, hairline unless a quantity is declared (the stroke law is the gauge\'s)', { size: 10, color: '#5d6470' });
      const a = HR.Glyphs.assemble(doc.schematic);
      for (const w of a.wires) p.line(w.points, { width: 1, role: 'passage' });
      for (const { inst, glyph } of a.placed) drawGlyph(p, glyph, { unit, q: inst.quantity });
      for (const c of a.crossings) p.ring(c.point, 3, '#8a4b6a');
      p.text([0, -0.3], 'schematic — nets by exact anchor coincidence; a crossing without a junction is co-presence, not contact', { size: 10, color: '#5d6470' });
      const rows = [['symbols', names.length], ['instances', a.placed.length], ['terminals', a.terminals.length], ['nets', a.nets.length], ['crossings', a.crossings.length]];
      a.checks.forEach((c, i) => rows.push([`net ${i}`, `${c.kinds.join(' + ')} → ${c.findings.length ? c.findings.join('; ') : 'ok'}`, c.findings.some((f) => f.startsWith('refused')) ? 'bad' : (c.findings.length ? 'warn' : 'ok')]));
      rows.push(['stroke law (gauge)', `hairline 1 px; declared quantity q → ⌈q / ${unit}⌉ px`], ['orientation', 'D4 only; hand = tick on the + side; no arrowheads'], gaugeReceipt(p)); setReceipts(rows);
    },
  };
  function drawGlyph(p, g, opts = {}) { const w = HR.Glyphs.widthPx(opts.q ?? null, opts.unit); for (const s of g.strokes) p.line(s, { width: g.quantity && opts.q != null ? w : 1, role: 'symbol' }); for (const s of g.dashed) p.line(s, { width: 1, dash: [3, 3], role: 'membrane' }); for (const d of g.dots) p.dot(d, 2); for (const h of g.hands) p.line(h, { width: 1, role: 'hand' });
    if (opts.labels) for (const [k, a] of Object.entries(g.anchors)) { p.ring(a, 2.5, '#3c6ea5'); p.text(a, k, { size: 8, color: '#3c6ea5', dx: 4, dy: -4 }); } }
  // ---------- field helpers ----------
  function fieldPaper(N) { const cv = $('#canvas'); return paperFor(Math.min(cv.parentElement.clientWidth, cv.parentElement.clientHeight) / (N + 2), [8, 8]); }
  function bandBoundaries(p, field, N, levels, wrap = true) { const rg = HR.Regions.regions(field, N, levels, { wrap }); for (const [a, b] of HR.Regions.boundaries(rg, N, { wrap })) p.line([a, b], { width: 1, role: 'level-bracket' }); return rg; }
  // ---------- scene: Navier–Stokes ----------
  SCENES.ns = {
    title: 'Field · Navier–Stokes', doc: () => ({ schema: HR.Codec.SCHEMA, scene: 'ns', generators: { flow: { use: 'field.navier-stokes', params: { N: 64, nu: 0.001, dt: 0.5, vortices: [{ x: 20, y: 32, gamma: 1, r: 4 }, { x: 44, y: 32, gamma: -1, r: 4 }, { x: 32, y: 12, gamma: 0.6, r: 3 }] } } },
      colour: { current: 'u_x + i u_y (the 1-form ⋆dψ read at the site)', aperture: 0.5 }, traces: { levels: ['-0.6', '-0.3', '-0.1', '0.1', '0.3', '0.6'], transportTime: 12, seedStride: 6 }, receiver: { site: [32, 32], causal: 'L1', retarded: false } }),
    init(doc) { state.inst = HR.Codec.instantiate(doc); state.history = []; },
    step() { const f = state.inst.flow.value; f.step(); state.history.push(Float64Array.from(f.omega)); if (state.history.length > 96) state.history.shift(); },
    render(doc) {
      const f = state.inst.flow.value; const N = f.N; const p = fieldPaper(N); p.clear();
      let seen = f.omega; if (doc.receiver.retarded && state.history.length) { const [ri, rj] = doc.receiver.site; seen = new Float64Array(N * N); for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { let di = Math.abs(i - ri), dj = Math.abs(j - rj); di = Math.min(di, N - di); dj = Math.min(dj, N - dj); const h = state.history.length - 1 - (di + dj); seen[i * N + j] = h >= 0 ? state.history[h][i * N + j] : state.history[0][i * N + j]; } }
      const kappa = doc.colour.aperture; p.raster(N, (k) => HR.Colour.toRGB(HR.Colour.transduce([{ re: f.ux[k], im: f.uy[k] }], kappa))); HR.App.chartGround(p, { x0: 0, x1: N, y0: 0, y1: N }, { cls: 1, step: 8, frameOnly: true, label: `flow receiver · ${N}×${N} cells · c = 1 cell/tick` });
      // entropy production: ε = ν|∇ω|² per site (a Float64 face); its band boundaries show where the arrow of time is being paid for
      const dis = f.dissipation(); let emax = 0; for (const v of dis.eps) emax = Math.max(emax, v); const erg = HR.Regions.regions(dis.eps, N, [emax * 0.2, emax * 0.5]); for (const [a, b] of HR.Regions.boundaries(erg, N)) p.line([a, b], { width: 1, color: '#8a4b6a', role: 'entropy-bracket', alpha: 0.8 });
      let lo = Infinity, hi = -Infinity; for (const v of seen) { if (v < lo) lo = v; if (v > hi) hi = v; } const m = Math.max(Math.abs(lo), Math.abs(hi)) || 1;
      const levels = doc.traces.levels.map((s) => R(s).toNumber() * m); const rg = bandBoundaries(p, seen, N, levels);
      const st = doc.traces.seedStride, T = doc.traces.transportTime; for (let i = 0; i < N; i += st) for (let j = 0; j < N; j += st) { const path = HR.Traces.transportPath((x, y) => f.velocity(x, y), [i, j], T, 0.5); p.dot([i, j], 1.2); p.line(unwrap(path, N), { width: 1, color: '#1d3f6e', role: 'transport' }); }
      const [ri, rj] = doc.receiver.site; p.ring([ri, rj], 5, '#8a4b6a'); p.ring([ri, rj], 2, '#8a4b6a');
      const r = f.receipts(); setReceipts([['tick', r.tick], ['t', fmt(r.t, 2)], ['circulation Σω', fmt(r.circulation, 6)], ['enstrophy ½Σω²', fmt(r.enstrophy)], ['energy ½Σ|u|²', fmt(r.energy)], ['ν · Δt', `${f.nu} · ${f.dt}`], ['colour', `receiver transduction of A = u_x + i u_y per site, κ = ${kappa}; P₀=Re², P₁=Im², P₂=(Re+Im)²; quantized once`], ['level brackets', `${rg.count} band regions of ω; boundaries drawn on the dual lattice, no interpolated point`], ['transport paths', `RK4 for T = ${T} from ${Math.ceil(N / st) ** 2} sites — a Float64 face of the 1-form, not a witnessed statement`], ['entropy production', `ε = ν|∇ω|² summed = ${dis.total.toExponential(3)} per tick (plum brackets at 20 % and 50 % of max); enstrophy actually falls at ${(-(state.history.length > 1 ? (r.enstrophy - 0.5 * state.history[state.history.length - 2].reduce((a, w) => a + w * w, 0)) / f.dt : 0)).toExponential(3)} per tick — the scheme's numerical diffusion dominates ν: the arrow of time here is mostly the integrator's, and the page says so`, 'warn'], ['receiver', `site (${ri},${rj}) · ${doc.receiver.retarded ? 'retarded by the L1 cone (c = 1 site/tick)' : 'simultaneous face'}`], ['exact', 'incidence, cone delays, region labels · Float64 faces: ω, ψ, u'], gaugeReceipt(p)]);
    },
  };
  function unwrap(path, N) { const out = [path[0]]; for (let k = 1; k < path.length; k++) { const a = out[out.length - 1], b = path[k]; if (Math.abs(b[0] - a[0]) > N / 2 || Math.abs(b[1] - a[1]) > N / 2) break; out.push(b); } return out; }
  // ---------- scene: Klein–Gordon fluctuation ----------
  SCENES.kg = {
    title: 'Field · vacuum fluctuation', doc: () => ({ schema: HR.Codec.SCHEMA, scene: 'kg', generators: { field: { use: 'field.klein-gordon', params: { N: 64, m: 0.3, dt: 0.2, seed: 7 } } }, colour: { current: 'φ + i π (field and conjugate momentum at the site)', aperture: 1.5 }, traces: { levels: ['-0.6', '-0.2', '0.2', '0.6'] }, probe: { site: [32, 32] } }),
    init(doc) { state.inst = HR.Codec.instantiate(doc); },
    step() { state.inst.field.value.step(); },
    render(doc) {
      const f = state.inst.field.value; const N = f.N; const p = fieldPaper(N); p.clear();
      const kappa = doc.colour.aperture; p.raster(N, (k) => HR.Colour.toRGB(HR.Colour.transduce([{ re: f.phi[k], im: f.pi[k] }], kappa))); HR.App.chartGround(p, { x0: 0, x1: N, y0: 0, y1: N }, { cls: 2, step: 8, frameOnly: true, label: `field receiver · ${N}×${N} cells` });
      const levels = doc.traces.levels.map((s) => R(s).toNumber()); const rg = bandBoundaries(p, f.phi, N, levels);
      const [pi, pj] = doc.probe.site; p.ring([pi, pj], 5, '#8a4b6a');
      let v = 0; for (const x of f.phi) v += x * x; v /= N * N; let ex = 0; for (const l of f.eig) ex += 1 / (2 * Math.sqrt(f.m * f.m + l)); ex /= N * N;
      setReceipts([['tick', f.tick], ['t', fmt(f.t, 2)], ['m · Δt', `${f.m} · ${f.dt}`], ['energy (sample)', fmt(f.energy())], ['seed', doc.generators.field.params.seed], ['⟨φ²⟩ sample vs exact', `${fmt(v, 4)} vs ${fmt(ex, 4)} = (1/N²)Σ 1/(2ω_k) — cutoff-dominated, not physical`], ['colour', `receiver transduction of A = φ + iπ per site, κ = ${kappa}`], ['level brackets', `${rg.count} band regions on the torus; boundaries on the dual lattice`], ['what this is', 'ONE sample of the free vacuum (Gaussian, covariance 1/(2ω_k)) evolved by leapfrog; the vacuum is a state, not a configuration'], ['exact', 'incidence, dispersion structure ω_k² = m² + Σ4sin²(k/2), region labels · Float64: φ, π'], gaugeReceipt(p)]);
    },
  };
  // ---------- scene: Z^4 through a chart ----------
  SCENES.z4 = {
    title: 'Model · ℤ⁴ through a receiver', doc: () => ({ schema: HR.Codec.SCHEMA, scene: 'z4', generators: { lattice: { use: 'lattice.Z4', params: { g: 2, wrap: false } }, chart: { use: 'chart.split3+1', params: { shown: [0, 1, 2], folded: 3, fold: ['1/3', '1/5', '1/4'], law: { kind: 'oblique', a: '1/2', b: '1/3' } } } }, colour: { current: 'exact depth gradient of the visible 2-cell in the receiver chart', aperture: '1/2' }, traces: { depthSpacing: '1/4', hatch: true, fills: true, hidden: 'dashed' } }),
    init(doc) { state.inst = HR.Codec.instantiate(doc); },
    render(doc) {
      const L = state.inst.lattice.value, C = state.inst.chart.value; const t0 = performance.now();
      const plan = HR.Models.renderPlan(L, C, { delta: doc.traces.depthSpacing, hatch: doc.traces.hatch, aperture: doc.colour.aperture });
      let minx = Infinity, maxx = -Infinity, miny = Infinity, maxy = -Infinity; for (const q of plan.projection.points) { const x = q.xy[0].toNumber(), y = q.xy[1].toNumber(); minx = Math.min(minx, x); maxx = Math.max(maxx, x); miny = Math.min(miny, y); maxy = Math.max(maxy, y); }
      const W = $('#canvas').parentElement.clientWidth, H = $('#canvas').parentElement.clientHeight; const unit = Math.min((W - 80) / (maxx - minx || 1), (H - 80) / (maxy - miny || 1)); const p = paperFor(unit, [40 - minx * unit, 40 - miny * unit]); p.clear();
      const map = plan.map; HR.App.chartGround(p, { x0: minx - 0.3, x1: maxx + 0.3, y0: miny - 0.3, y1: maxy + 0.3 }, { cls: 1, step: 1, label: `chart receiver · ${C.law.kind}` });
      if (doc.traces.fills) for (const f of map.faces) { if (!f.bounded) continue; const fill = plan.fills.get(f.id); const cyc = f.darts.map((d) => map.nodes[map.darts[d].from].p); if (fill) p.fill(cyc, rgb(fill.response)); const v = plan.visible.get(f.id); if (v && v.open) p.line([...cyc, cyc[0]], { width: 1, dash: [1, 2], color: '#8a4b6a', role: 'open-occlusion' }); }
      for (const tr of plan.traces) p.line([tr.a, tr.b], { width: 1, alpha: 0.85, role: 'depth-level' });
      for (const e of plan.edgePieces) { if (e.hidden) { if (doc.traces.hidden === 'dashed') p.line([e.a, e.b], { width: 1, dash: [2, 3], alpha: 0.5, role: 'hidden-edge' }); } else p.line([e.a, e.b], { width: 1, role: 'edge' }); }
      for (const q of plan.projection.points) p.dot(q.xy, 1.5);
      for (const c of map.crossings) if (c.over !== null) p.ring(c.point, 2.5, '#8a4b6a');
      const ms = performance.now() - t0; const distinct = new Set([...plan.fills.values()].map((f) => `${f.current.re},${f.current.im}`)).size;
      setReceipts([['lattice', `ℤ⁴ · g = ${L.g} · ${L.V.length} sites · ${L.E.length} edges · ${L.F.length} 2-cells`], ['chart', `${C.law.kind} · shown ${C.shown.join('')} · folded ${C.folded} by (${doc.generators.chart.params.fold.join(', ')})`], ['planar map', `${map.nodes.length} nodes · ${map.edges.length} edges · ${map.faces.length} faces (Euler: F = E − V + 2 → ${map.edges.length - map.nodes.length + 2})`, map.faces.length === map.edges.length - map.nodes.length + 2 ? 'ok' : 'warn'], ['crossings', `${map.crossings.length}, over/under by exact depth`], ['discriminants', map.discriminants.length ? map.discriminants.map((d) => d.kind).join(', ') : 'none', map.discriminants.length ? 'warn' : 'ok'], ['occlusion', `${plan.openFaces} open (equal depth, no winner invented; dotted) · ${plan.edgePieces.filter((e) => e.hidden).length}/${plan.edgePieces.length} edge pieces hidden`, plan.openFaces ? 'warn' : 'ok'], ['depth traces', `${plan.traces.length} exact level lines at spacing ${doc.traces.depthSpacing}`], ['colour', `transduction of each visible face's exact depth gradient (${distinct} distinct currents; faces parallel to the receiver stay paper), κ = ${doc.colour.aperture}`], ['face-dual testimony', `the receiver's map admits ${plan.classes.chromatic} classes${plan.classes.exact ? '' : ' (greedy)'} — testimony, not a colour law`], ['exact', 'coordinates, crossings, depths, faces, gradients, level lines, responses: ℚ'], ['time', `${ms.toFixed(0)} ms`], gaugeReceipt(p)]);
    },
  };
  // ---------- scene: receiver in motion (exact Q(√Δ) light cone) ----------
  SCENES.rx = {
    title: 'Receiver · past cone at β', doc: () => ({ schema: HR.Codec.SCHEMA, scene: 'rx', generators: { slab: { use: 'lattice.Z3', params: { g: 2, offset: ['0', '0', '7'] } } }, receiver: { beta: '3/5', axis: 2, focal: '2', subdivide: 4 }, modal: { step: ['3/5', '4/5'], omega: 0.6 }, colour: { aperture: '1/2' } }),
    init(doc) { state.inst = HR.Codec.instantiate(doc); },
    render(doc) {
      const L = state.inst.slab.value; const beta = R(doc.receiver.beta), axis = doc.receiver.axis, focal = doc.receiver.focal, sub = doc.receiver.subdivide; const g = HR.Relativity.gamma(beta);
      const W = $('#canvas').parentElement.clientWidth, H = $('#canvas').parentElement.clientHeight; const p = paperFor(Math.min(W / 2, H) / 3.2, [0, 0]); p.clear();
      const halves = [{ ox: W / 4, beta: Rat.ZERO, label: 'simultaneous face (β = 0)' }, { ox: 3 * W / 4, beta, label: `receiver at β = ${beta} along axis ${axis}, γ = ${g}` }];
      const step = [R(doc.modal.step[0]), R(doc.modal.step[1])]; let Dmin = null, Dmax = null, fields = new Set();
      for (const hv of halves) {
        p.origin = [hv.ox, H / 2]; HR.App.chartGround(p, { x0: -1.5, x1: 1.5, y0: -1.5, y1: 1.5 }, { cls: hv.beta.isZero() ? 1 : 2, step: 0.5, label: hv.beta.isZero() ? 'receiver at rest' : 'receiver in motion' });
        const readSite = (c) => HR.Relativity.readStaticSite(c, hv.beta, axis, focal);
        for (const e of L.E) { const a = L.V[e.from].coords, b = L.V[e.to].coords; const pts = []; for (let k = 0; k <= sub; k++) { const t = R(k).div(sub); const c = a.map((ai, i) => ai.add(b[i].sub(ai).mul(t))); const rd = readSite(c); if (!rd || rd.behind) { if (pts.length > 1) p.line(pts.map((s) => s.map((q) => q.toNumber())), { width: 1, role: 'edge' }); pts.length = 0; continue; } pts.push(rd.screen); fields.add(rd.delta.toString()); }
          if (pts.length > 1) p.line(pts.map((s) => s.map((q) => q.toNumber())), { width: 1, role: 'edge' }); }
        for (const v of L.V) { const rd = readSite(v.coords); if (!rd || rd.behind) continue; const i = v.ints[0];
          // modal current at the site: an exact Pythagorean rotation per lattice step along x, received with Doppler D (exact) and a phase advance ω·t_ret (float face)
          let A = [Rat.ONE, Rat.ZERO]; const rot = [step[0], step[1]]; const n = ((i % 8) + 8) % 8; for (let k = 0; k < n; k++) A = [A[0].mul(rot[0]).sub(A[1].mul(rot[1])), A[0].mul(rot[1]).add(A[1].mul(rot[0]))];
          const D = rd.D.toNumber(); const w = Math.pow(D, -2); const ph = doc.modal.omega * rd.tRet.toNumber(); const re = A[0].toNumber(), im = A[1].toNumber(); const Ar = w * (re * Math.cos(ph) - im * Math.sin(ph)), Ai = w * (re * Math.sin(ph) + im * Math.cos(ph));
          const col = HR.Colour.css(HR.Colour.toRGB(HR.Colour.transduce([{ re: Ar, im: Ai }], R(doc.colour.aperture).toNumber())));
          p.dot(rd.screen.map((q) => q.toNumber()), 3, col); if (!hv.beta.isZero()) { if (Dmin === null || D < Dmin) Dmin = D; if (Dmax === null || D > Dmax) Dmax = D; } }
        p.text([-1.4, -1.45], hv.label, { size: 10, color: '#5d6470' });
      }
      setReceipts([['slab', `ℤ³ [−${L.g},${L.g}]³ at offset (${doc.generators.slab.params.offset.join(', ')}) · ${L.V.length} sites · ${L.E.length} edges`], ['receiver', `β = ${beta} (Pythagorean ⇒ γ = ${g} exact) · focal ${focal} · c = 1`], ['light cone', `per site t_ret = −√Δ, Δ = r·r; ${fields.size} distinct quadratic fields ℚ(√Δ) across the read points`], ['aberration', 'r′_∥ = γ(r_∥ + |β| n), r′_⊥ = r_⊥ — exact in ℚ(√Δ); edges subdivided ×' + sub + ' because the map is nonlinear'], ['Doppler', Dmin !== null ? `D = n / (γ(n + β·r)) exact in ℚ(√Δ); float face ${fmt(Dmin)} … ${fmt(Dmax)}` : '—'], ['searchlight', 'amplitude × D⁻² (intensity D⁻⁴, band-integrated) before transduction'], ['colour', `transduction of the received modal current (exact rotation (${doc.modal.step.join(', ')})ⁱ per site; phase advance ω·t_ret is a float face), κ = ${doc.colour.aperture}`], ['crossing analysis', 'refused: read points lie in mixed quadratic fields (the Rust owner refuses the radical chart the same way)', 'warn'], ['exact', 'Δ, n, r′, D, screen point: ℚ(√Δ) · Float64: cos/sin of the phase advance, pixels'], gaugeReceipt(p)]);
    },
  };
  // ---------- scene: receiver on the lattice (causal cone over a field) ----------
  SCENES.cone = {
    title: 'Receiver · causal cone', doc: () => ({ schema: HR.Codec.SCHEMA, scene: 'cone', generators: { flow: { use: 'field.navier-stokes', params: { N: 64, nu: 0.001, dt: 0.5, vortices: [{ x: 16, y: 32, gamma: 1, r: 3 }, { x: 48, y: 32, gamma: -1, r: 3 }] } } }, receiver: { site: [32, 32], causal: 'L1', c: 1 }, colour: { aperture: 0.5 }, traces: { levels: ['-0.5', '-0.2', '0.2', '0.5'] } }),
    init(doc) { state.inst = HR.Codec.instantiate(doc); state.history = []; },
    step() { const f = state.inst.flow.value; f.step(); state.history.push({ w: Float64Array.from(f.omega), ux: Float64Array.from(f.ux), uy: Float64Array.from(f.uy) }); if (state.history.length > 128) state.history.shift(); },
    render(doc) {
      const f = state.inst.flow.value; const N = f.N; const p = fieldPaper(N); p.clear();
      const [ri, rj] = doc.receiver.site; const H = state.history.length; const seen = new Float64Array(N * N), sux = new Float64Array(N * N), suy = new Float64Array(N * N); const delay = new Int32Array(N * N); let outside = 0;
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { let di = Math.abs(i - ri), dj = Math.abs(j - rj); di = Math.min(di, N - di); dj = Math.min(dj, N - dj); const d = doc.receiver.causal === 'Linf' ? Math.max(di, dj) : di + dj; delay[i * N + j] = d; const h = H - 1 - Math.round(d / doc.receiver.c); const k = i * N + j; const src = h >= 0 ? state.history[h] : null; if (src) { seen[k] = src.w[k]; sux[k] = src.ux[k]; suy[k] = src.uy[k]; } else { outside++; } }
      p.raster(N, (k) => (delay[k] >= H ? [246, 247, 244] : HR.Colour.toRGB(HR.Colour.transduce([{ re: sux[k], im: suy[k] }], doc.colour.aperture)))); HR.App.chartGround(p, { x0: 0, x1: N, y0: 0, y1: N }, { cls: 1, step: 8, frameOnly: true, label: `receiver at rest · ${N}×${N} cells · past cone` });
      let m = 0; for (const v of seen) m = Math.max(m, Math.abs(v)); m = m || 1; const rg = bandBoundaries(p, seen, N, doc.traces.levels.map((s) => R(s).toNumber() * m));
      const hor = new Float64Array(N * N); for (let k = 0; k < N * N; k++) hor[k] = delay[k] >= H ? 1 : 0; const hrg = HR.Regions.regions(hor, N, [0.5]); for (const [a, b] of HR.Regions.boundaries(hrg, N)) p.line([a, b], { width: 1, color: '#8a4b6a', role: 'horizon' });
      p.ring([ri, rj], 5, '#8a4b6a'); p.ring([ri, rj], 2, '#8a4b6a');
      setReceipts([['tick', f.tick], ['receiver', `site (${ri},${rj}) at rest on the lattice`], ['cone', `${doc.receiver.causal} graph distance · c = ${doc.receiver.c} site/tick · delay is an exact integer`], ['horizon', `${H} ticks retained → radius ${Math.max(0, H - 1)} · ${outside} sites outside the reach (paper, bounded by the plum bracket)`], ['what is seen', 'ω(x, t − d(x, r)) and u(x, t − d): the past cone, not a simultaneous slice'], ['colour', `transduction of the retarded current u_x + i u_y, κ = ${doc.colour.aperture}`], ['level brackets', `${rg.count} band regions of the retarded ω`], ['moving receiver', 'see “Receiver · past cone at β” for aberration and Doppler in ℚ(√Δ)'], gaugeReceipt(p)]);
    },
  };
  // ---------- shell ----------
  function loadScene(name) {
    state.scene = SCENES[name]; state.playing = false; cancelAnimationFrame(state.raf); $('#play').textContent = 'play'; const doc = state.scene.doc(); setDoc(doc); if (state.scene.init) state.scene.init(doc); state.scene.render(doc);
    $$('#tabs button').forEach((b) => b.classList.toggle('on', b.dataset.scene === name)); $('#play').style.display = state.scene.step ? '' : 'none'; $('#stepbtn').style.display = state.scene.step ? '' : 'none'; $('#svgout').value = '';
  }
  function applyDoc() { try { const doc = JSON.parse($('#doc').value); if (!setDoc(doc)) return; if (state.scene.init) state.scene.init(doc); state.scene.render(doc); } catch (e) { $('#docstate').textContent = 'refused: ' + e.message; $('#docstate').className = 'docstate bad'; } }
  function loop() { if (!state.playing) return; state.scene.step(); state.scene.render(state.doc); state.raf = requestAnimationFrame(loop); }
  window.addEventListener('DOMContentLoaded', () => {
    $('#tabs').innerHTML = Object.entries(SCENES).map(([k, s]) => `<button data-scene="${k}">${s.title}</button>`).join('');
    $('#tabs').addEventListener('click', (e) => { const b = e.target.closest('button'); if (b) loadScene(b.dataset.scene); });
    $('#apply').addEventListener('click', applyDoc); $('#reset').addEventListener('click', () => loadScene(Object.keys(SCENES).find((k) => SCENES[k] === state.scene)));
    $('#play').addEventListener('click', () => { state.playing = !state.playing; $('#play').textContent = state.playing ? 'pause' : 'play'; if (state.playing) loop(); });
    $('#stepbtn').addEventListener('click', () => { state.scene.step(); state.scene.render(state.doc); });
    $('#showsvg').addEventListener('click', () => { $('#svgout').value = state.lastSvg || state.paper.svg(GAUGES[0]); });
    window.addEventListener('resize', () => state.scene && state.scene.render(state.doc));
    loadScene('z4');
  });
  HR.App = { SCENES, state, paperFor, setReceipts, gaugeReceipt, drawGlyph, rgb, fmt, GAUGES, $ };
})(HR);
