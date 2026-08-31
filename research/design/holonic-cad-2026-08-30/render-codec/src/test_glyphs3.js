const HR = require('./core.js'); require('./glyphs.js'); const { R } = HR;
for (const n of ['cup', 'cap', 'circle', 'hyperedge', 'event']) { const g = HR.Glyphs.place(n, [0, 0], 'r0', 1); console.log(n, 'strokes', g.strokes.length, 'pts', g.strokes[0].length, 'first', g.strokes[0][0].join(','), 'last', g.strokes[0][g.strokes[0].length - 1].join(','), 'hands', g.hands.length); }
// exactness of circle points: x² + y² = r² for every point
const c = HR.Glyphs.circle(0, 0, '1/4', 16); console.log('on circle', c.every(([x, y]) => x.mul(x).add(y.mul(y)).eq(R('1/16'))), c.length);
const pa = HR.Glyphs.placeAlong('transport', [R(0), R(0)], [R(2), R(1)], '1/2'); console.log('placeAlong anchors', Object.entries(pa.anchors).map(([k, v]) => k + '=' + v.join(',')).join(' '));
