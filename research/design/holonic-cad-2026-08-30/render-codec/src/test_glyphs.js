const HR = require('./core.js'); require('./glyphs.js');
const g = HR.Glyphs.place('parametron', [2, 2], 'r90', 2); console.log('parametron anchors', Object.entries(g.anchors).map(([k, p]) => k + '=' + p[0] + ',' + p[1]).join(' '), 'hands', g.hands.length, 'strokes', g.strokes.length);
console.log('width law', HR.Glyphs.widthPx('3/2', '1/2'), HR.Glyphs.widthPx(null), HR.Glyphs.widthPx('1/10', 1));
const doc = { instances: [{ symbol: 'pump', at: [0, 0] }, { symbol: 'parametron', at: [3, 0], orient: 'r270', scale: 2 }, { symbol: 'receiver', at: [6, 0], orient: 'r180' }, { symbol: 'exterior', at: [3, 3], orient: 'r90' }],
  wires: [[['1/2', 0], [2, 0]], [[4, 0], ['11/2', 0]], [[3, 1], [3, 2], [4, 2], [4, -2]]] };
const a = HR.Glyphs.assemble(doc); console.log('nets', a.nets.length, a.checks.map(c => `${c.terminals}:${c.kinds.join('+')}:${c.findings.join('|') || 'ok'}`).join(' ; '), 'crossings', a.crossings.length);
