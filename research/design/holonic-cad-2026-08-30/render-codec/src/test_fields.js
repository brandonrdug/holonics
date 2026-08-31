const HR = require('./core.js'); require('./fields.js');
const N = 64; const ns = new HR.NavierStokes(N, { nu: 0.001, dt: 0.5 });
ns.seedVortices([{ x: 20, y: 32, gamma: 1, r: 4 }, { x: 44, y: 32, gamma: -1, r: 4 }]);
const r0 = ns.receipts(); for (let k = 0; k < 20; k++) ns.step(); const r1 = ns.receipts();
console.log('NS circulation', r0.circulation.toFixed(6), '->', r1.circulation.toFixed(6), 'enstrophy', r0.enstrophy.toFixed(3), '->', r1.enstrophy.toFixed(3), 'energy', r0.energy.toFixed(3), '->', r1.energy.toFixed(3));
const ls = HR.Traces.levelSets(ns.omega, N, [0.5, -0.5, 0.1, -0.1]); console.log('level sets', ls.map(l => l.segments.length).join(' '));
const p = HR.Traces.transportPath((x, y) => ns.velocity(x, y), [20, 36], 40); console.log('path pts', p.length, p[p.length - 1].map(v => v.toFixed(2)).join(','));
const kg = new HR.KleinGordon(N, { m: 0.3, dt: 0.2, seed: 7 }); kg.sampleVacuum(); const e0 = kg.energy(); let mean = 0, var_ = 0; for (const v of kg.phi) mean += v; mean /= N * N; for (const v of kg.phi) var_ += (v - mean) ** 2; var_ /= N * N;
for (let k = 0; k < 50; k++) kg.step(); console.log('KG energy', e0.toFixed(3), '->', kg.energy().toFixed(3), 'phi mean', mean.toFixed(4), 'var', var_.toFixed(4));
// the exact lattice variance of φ at a site: (1/N²) Σ_k 1/(2ω_k)
let ex = 0; const eig = (() => { const L = []; for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const a = Math.sin(Math.PI * i / N), b = Math.sin(Math.PI * j / N); L.push(4 * a * a + 4 * b * b); } return L; })(); for (const l of eig) ex += 1 / (2 * Math.sqrt(0.09 + l)); ex /= N * N; console.log('expected var', ex.toFixed(4));
