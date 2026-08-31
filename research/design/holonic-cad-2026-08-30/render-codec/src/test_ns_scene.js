const HR = require('./core.js'); require('./fields.js'); require('./models.js'); require('./glyphs.js'); require('./regions.js'); require('./codec.js');
const doc = { schema: 'holonic-render-v1', generators: { flow: { use: 'field.navier-stokes', params: { N: 64, nu: 0.001, dt: 0.5, vortices: [{ x: 20, y: 32, gamma: 1, r: 4 }, { x: 44, y: 32, gamma: -1, r: 4 }, { x: 32, y: 12, gamma: 0.6, r: 3 }] } } }, traces: { levels: ['-0.6', '-0.3', '-0.1', '0.1', '0.3', '0.6'], transportTime: 12, seedStride: 6 } };
let t0 = Date.now(); const inst = HR.Codec.instantiate(doc); const f = inst.flow.value; const N = f.N; console.log('instantiate ms', Date.now() - t0);
let lo = Infinity, hi = -Infinity; for (const v of f.omega) { if (v < lo) lo = v; if (v > hi) hi = v; } const m = Math.max(Math.abs(lo), Math.abs(hi)) || 1;
const levels = doc.traces.levels.map((s) => parseFloat(HR.R(s).toNumber())).map((x) => x * m); console.log('levels', levels);
t0 = Date.now(); const ls = HR.Traces.levelSets(f.omega, N, levels); console.log('levelsets ms', Date.now() - t0, ls.map(l => l.segments.length));
t0 = Date.now(); let n = 0; for (let i = 0; i < N; i += 6) for (let j = 0; j < N; j += 6) { const path = HR.Traces.transportPath((x, y) => f.velocity(x, y), [i, j], 12, 0.5); n += path.length; } console.log('paths ms', Date.now() - t0, 'pts', n);
