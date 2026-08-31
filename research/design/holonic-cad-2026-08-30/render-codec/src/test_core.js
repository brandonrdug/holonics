const HR = require('./core.js'); const { Rat, R } = HR;
// rationals
console.log('rat', R('1/3').add(R('1/6')).toString(), R(0.75).toString(), R('2.5').mul(2).toString(), R(-3).div(R('3/7')).toString());
// a 2x2 grid of squares as segments (5 nodes across): 4 faces bounded + 1 outer
const segs = [];
const g = 2; for (let i = 0; i <= g; i++) { segs.push({ a: [R(i), R(0)], b: [R(i), R(g)] }); segs.push({ a: [R(0), R(i)], b: [R(g), R(i)] }); }
// add a diagonal crossing edge with depths
segs.push({ a: [R(0), R(0)], b: [R(2), R(2)], depthA: R(0), depthB: R(2) });
const m = HR.PlanarMap.build(segs);
console.log('nodes', m.nodes.length, 'edges', m.edges.length, 'faces', m.faces.length, 'bounded', m.faces.filter(f => f.bounded).length, 'crossings', m.crossings.length, 'disc', m.discriminants.length);
console.log('areas', m.faces.map(f => f.signedDoubleArea.toString()).join(' '));
const c = HR.FourColor.colour(m.faces.length, m.adjacency);
console.log('colours', c.colours.join(''), 'chromatic', c.chromatic, 'exact', c.exact, 'steps', c.steps);
// a cube projected obliquely: 8 vertices, 12 edges; expect crossings and correct over/under
const V = []; for (const z of [0, 1]) for (const y of [0, 1]) for (const x of [0, 1]) V.push([R(x), R(y), R(z)]);
const E = []; for (let i = 0; i < 8; i++) for (let j = i + 1; j < 8; j++) { let dif = 0; for (let k = 0; k < 3; k++) if (!V[i][k].eq(V[j][k])) dif++; if (dif === 1) E.push([i, j]); }
const proj = (v) => [v[0].add(v[2].mul(R('1/2'))), v[1].add(v[2].mul(R('1/3')))];
const cs = E.map(([i, j]) => ({ a: proj(V[i]), b: proj(V[j]), depthA: V[i][2], depthB: V[j][2] }));
const cm = HR.PlanarMap.build(cs);
console.log('cube: nodes', cm.nodes.length, 'edges', cm.edges.length, 'faces', cm.faces.length, 'crossings', cm.crossings.length, cm.crossings.map(x => `over=${x.over} s=${x.orientationSign}`).join(' | '));
const cc = HR.FourColor.colour(cm.faces.length, cm.adjacency); console.log('cube colours', cc.colours.join(''), cc.chromatic, cc.exact);
// interior points
for (const f of cm.faces.filter(f => f.bounded).slice(0, 3)) { const p = HR.PlanarMap.interiorPoint(cm, f); console.log('interior', p[0].toString(), p[1].toString(), HR.PlanarMap.pointInCycle(f.darts.map(d => cm.nodes[cm.darts[d].from].p), p)); }
