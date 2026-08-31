const HR = require('./core.js'); require('./colour.js'); require('./quadfield.js'); require('./fields.js'); require('./regions.js');
const { R } = HR;
const e = HR.Colour.transduceExact([{ re: '3/4', im: '1/4' }, { re: '-1/2', im: '1/2' }], '1/2'); console.log('exact', e.primaries.map(String).join(' '), 'α', String(e.alpha), 'τ', String(e.transmittance), HR.Colour.toRGB(e));
console.log('zero current → paper', HR.Colour.toRGB(HR.Colour.transduce([{ re: 0, im: 0 }], 1)));
console.log('gamma 3/5 =', String(HR.Relativity.gamma('3/5')), ' 4/5 =', String(HR.Relativity.gamma('4/5')), ' 1/2 =', HR.Relativity.gamma('1/2'));
const rd = HR.Relativity.readStaticSite([R(3), R(4), R(12)], '3/5', 2, 8); console.log('Δ', String(rd.delta), 'n', String(rd.n), 'D', String(rd.D), '=', rd.D.toNumber().toFixed(4), 'screen', rd.screen.map((s) => s.toString() + '=' + s.toNumber().toFixed(4)).join(' , '), 'tRet', rd.tRet.toNumber());
// check D against the float formula D = n/(γ(n+β r_z)) with n=13: 13/(1.25*(13+0.6*12)) = 13/(1.25*20.2)
console.log('D float check', (13 / (1.25 * (13 + 0.6 * 12))).toFixed(4));
const q = new HR.QF('1', '1', '2'); console.log('sign(1−√2)', new HR.QF('1', '-1', '2').sign(), 'sign(3−2√2)', new HR.QF('3', '-2', '2').sign(), '(1+√2)(1−√2) =', String(q.mul(q.conj()).a));
const N = 32; const kg = new HR.KleinGordon(N, { m: 0.3, dt: 0.2, seed: 3 }); kg.sampleVacuum(); const rg = HR.Regions.regions(kg.phi, N, [-0.3, 0.3]); console.log('boundaries', HR.Regions.boundaries(rg, N).length);
