// ===== codec.js — holonic-render-v1: a rigid document whose generators programmatically produce renderings =====
// A document is data only: exact rationals as strings ("p/q"), integers, enums, names. Rendering is a pure function of the document.
(function (HR) {
  const { Rat, R } = HR;
  const SCHEMA = 'holonic-render-v2'; const SCHEMAS = ['holonic-render-v1', SCHEMA]; // v1 documents stay admitted: a v1 document has one implicit receiver
  // FNV-1a 64-bit over the canonical serialization: a receipt (digest is testimony, never identity)
  function fnv1a64(str) { let h = 0xcbf29ce484222325n; const P = 0x100000001b3n; for (let i = 0; i < str.length; i++) { h ^= BigInt(str.charCodeAt(i)); h = (h * P) & 0xffffffffffffffffn; } return h.toString(16).padStart(16, '0'); }
  function canonical(obj) { // sorted keys, no whitespace, rationals normalised through Rat
    if (obj === null || typeof obj !== 'object') { if (typeof obj === 'string' && /^-?\d+(\/\d+)?$/.test(obj)) return JSON.stringify(R(obj).toString()); return JSON.stringify(obj); }
    if (Array.isArray(obj)) return '[' + obj.map(canonical).join(',') + ']';
    return '{' + Object.keys(obj).sort().map((k) => JSON.stringify(k) + ':' + canonical(obj[k])).join(',') + '}';
  }
  // generator registry: name -> {params: {name: {type, default}}, kind, make(params) }
  const GENERATORS = {
    'lattice.Z4': { kind: 'complex', params: { g: { type: 'int', default: 2, min: 1, max: 3 }, wrap: { type: 'bool', default: false } }, make: (p) => HR.Models.Lattice4(p.g, { wrap: p.wrap }) },
    'lattice.Z3': { kind: 'complex', params: { g: { type: 'int', default: 2, min: 1, max: 4 }, offset: { type: 'rat3', default: ['0', '0', '6'] } }, make: (p) => HR.Models.Lattice3(p.g, p.offset) },
    'chart.split3+1': { kind: 'chart', params: { shown: { type: 'axes', default: [0, 1, 2] }, folded: { type: 'int', default: 3 }, fold: { type: 'rat3', default: ['1/3', '1/5', '1/4'] }, law: { type: 'law', default: { kind: 'oblique', a: '1/2', b: '1/3' } } }, make: (p) => HR.Models.Chart(p) },
    'field.navier-stokes': { kind: 'field', params: { N: { type: 'pow2', default: 64 }, nu: { type: 'float-face', default: 0.001 }, dt: { type: 'float-face', default: 0.5 }, vortices: { type: 'list', default: [{ x: 20, y: 32, gamma: 1, r: 4 }, { x: 44, y: 32, gamma: -1, r: 4 }] } }, make: (p) => { const f = new HR.NavierStokes(p.N, { nu: p.nu, dt: p.dt }); f.seedVortices(p.vortices); return f; } },
    'field.klein-gordon': { kind: 'field', params: { N: { type: 'pow2', default: 64 }, m: { type: 'float-face', default: 0.3 }, dt: { type: 'float-face', default: 0.2 }, seed: { type: 'int', default: 7 } }, make: (p) => { const f = new HR.KleinGordon(p.N, { m: p.m, dt: p.dt, seed: p.seed }); f.sampleVacuum(); return f; } },
    'symbol.place': { kind: 'glyph', params: { symbol: { type: 'enum', default: 'parametron' }, at: { type: 'rat2', default: [0, 0] }, orient: { type: 'enum', default: 'r0', options: Object.keys(HR.Glyphs ? HR.Glyphs.D4 : { r0: 1 }) }, scale: { type: 'rat', default: 1 } }, make: (p) => HR.Glyphs.place(p.symbol, p.at, p.orient, p.scale) },
    // ---- v2: receivers, Minkowski charts, exact circuits, Bord cells ----
    'receiver.tree': { kind: 'receiver', params: { elements: { type: 'list', default: ['header', '#tabs', '.sheet', '#doc', '#receipts'] }, probe: { type: 'rat3', default: ['1', '1', '1'] }, marksAcross: { type: 'int', default: 16 } }, make: (p) => ({ declared: p, note: 'the platform supplies the grains and relations at render; they are recorded in the receipt, never authored here' }) },
    'chart.minkowski': { kind: 'chart', params: { window: { type: 'window', default: { t0: '-2', t1: '6', x0: '-4', x1: '4' } }, receiver: { type: 'rat2', default: ['5', '0'] }, beta: { type: 'rat', default: '3/5' }, objects: { type: 'list', default: [{ name: 'A', at: ['0', '0'], u: '0' }, { name: 'B', at: ['0', '1'], u: '3/5' }] }, hyperbolae: { type: 'list', default: ['1', '2'] }, grid: { type: 'int', default: 32 }, bisections: { type: 'int', default: 6 }, properStep: { type: 'rat', default: '1' } }, make: (p) => HR.Minkowski.plan(p) },
    'circuit.lattice': { kind: 'complex', params: { g: { type: 'int', default: 3, min: 2, max: 4 }, admittance: { type: 'record', default: { x: '1', y: '1/2', z: { re: '0', im: '1/3' } } }, sources: { type: 'list', default: [{ node: [0, 0, 0], current: { re: '1', im: '0' } }, { node: [2, 2, 2], current: { re: '-1', im: '0' } }] }, ground: { type: 'int3', default: [2, 2, 2] } }, make: (p) => HR.Circuit.LatticeCircuit(p) },
    'bord.cell': { kind: 'complex', params: { kind: { type: 'enum', default: 'saddle', options: ['pants', 'saddle', 'cylinder', 'cap'] }, slices: { type: 'int', default: 24, min: 1, max: 64 }, grid: { type: 'int', default: 32, min: 8, max: 96 }, bisections: { type: 'int', default: 7, min: 0, max: 12 }, params: { type: 'record', default: {} } }, make: (p) => HR.Bord.slices(p.kind, { slices: p.slices, grid: p.grid, bisections: p.bisections, params: p.params }) },
  };
  function validate(doc) {
    const errors = [];
    if (!SCHEMAS.includes(doc.schema)) errors.push('schema must be one of ' + SCHEMAS.join(', '));
    // v2 mounts: an object is mounted into a named receiver through a chart generator; every name must resolve
    for (const m of doc.mounts || []) { if (!doc.generators || !doc.generators[m.object]) errors.push(`mount: unknown object ${m.object}`); if (!doc.generators || !doc.generators[m.chart]) errors.push(`mount: unknown chart ${m.chart}`); if (typeof m.receiver !== 'string') errors.push('mount: receiver must be named'); }
    for (const [k, g] of Object.entries(doc.generators || {})) { const spec = GENERATORS[g.use]; if (!spec) { errors.push(`generator ${k}: unknown ${g.use}`); continue; }
      for (const [pn, pd] of Object.entries(spec.params)) { const v = (g.params || {})[pn]; if (v === undefined) continue; if (pd.type === 'int' && !Number.isInteger(v)) errors.push(`${k}.${pn}: int`); if (pd.type === 'rat' && (() => { try { R(v); return false; } catch { return true; } })()) errors.push(`${k}.${pn}: rational`); if (pd.type === 'pow2' && (v & (v - 1))) errors.push(`${k}.${pn}: power of two`); if (pd.type === 'float-face' && typeof v !== 'number') errors.push(`${k}.${pn}: number (declared float face)`); } }
    return errors;
  }
  function instantiate(doc) { const out = {}; for (const [k, g] of Object.entries(doc.generators || {})) { const spec = GENERATORS[g.use]; const p = {}; for (const [pn, pd] of Object.entries(spec.params)) p[pn] = (g.params && g.params[pn] !== undefined) ? g.params[pn] : pd.default; out[k] = { use: g.use, params: p, value: spec.make(p) }; } return out; }
  function receipt(doc) { const c = canonical(doc); return { schema: doc.schema, digest: fnv1a64(c), bytes: c.length }; }
  HR.Codec = { SCHEMA, SCHEMAS, GENERATORS, validate, instantiate, canonical, receipt, fnv1a64 };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
