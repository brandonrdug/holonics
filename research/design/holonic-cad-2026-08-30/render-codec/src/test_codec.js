const HR = require('./core.js'); require('./fields.js'); require('./models.js'); require('./glyphs.js'); require('./codec.js');
const doc = { schema: 'holonic-render-v1', generators: { L: { use: 'lattice.Z4', params: { g: 2 } }, C: { use: 'chart.split3+1', params: { law: { kind: 'oblique', a: '2/4', b: '1/3' } } }, P: { use: 'symbol.place', params: { symbol: 'pump', at: ['0', '0'] } } } };
console.log('errors', HR.Codec.validate(doc)); const r = HR.Codec.receipt(doc); console.log('receipt', r);
const doc2 = JSON.parse(JSON.stringify(doc)); doc2.generators.C.params.law.a = '1/2'; console.log('same digest after rational normalisation?', HR.Codec.receipt(doc2).digest === r.digest);
const inst = HR.Codec.instantiate(doc); console.log(Object.entries(inst).map(([k, v]) => k + ':' + v.use + ':' + (v.value.V ? v.value.V.length + 'V' : v.value.kind || 'chart')).join(' '));
// correct schematic doc: pump.out (1/2,0) -> wire -> parametron n1 ; parametron at (3,0) r0 scale 2 => n1 = (3-1, 0-1/2) = (2,-1/2)
const sd = { instances: [{ symbol: 'pump', at: [0, 0] }, { symbol: 'parametron', at: [3, 0], scale: 2 }, { symbol: 'receiver', at: [6, 0], orient: 'r180' }], wires: [[['1/2', 0], [2, 0], [2, '-1/2']], [[4, '-1/2'], ['11/2', 0]]] };
const a = HR.Glyphs.assemble(sd); console.log('nets', a.nets.length, a.checks.map(c => `${c.terminals}:${c.kinds.join('+')}:${c.findings.join('|') || 'ok'}`).join(' ; '));
