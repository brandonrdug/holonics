const HR = require('./core.js'); require('./colour.js'); require('./quadfield.js'); require('./poly.js'); require('./models.js'); require('./brackets.js'); require('./hatch.js'); require('./receivers.js'); require('./minkowski.js'); require('./circuit.js'); require('./bord.js'); require('./polygraph.js');
const { R, Rat } = HR; const t0 = Date.now();
// brackets: hyperbola x² − t² = ±1 on a 1/4 grid has exact stations at (γ, γβ) = (5/4, 3/4)
const br = HR.Brackets.levelBrackets((t, x) => x.mul(x).sub(t.mul(t)), { x0: -3, x1: 3, y0: -3, y1: 3 }, 24, ['-1', '1']);
console.log('brackets', br.segs.length, 'stations', br.stations.length, br.stations.slice(0, 4).map((s) => s.p.join(',') + '@' + s.level).join(' '));
// receivers: tree, seam address, holonomy
const A2 = HR.Affine2; const dev = new HR.Receiver('device', { w: 3840, h: 2160 }); const css = new HR.Receiver('monitor-css', { w: 2560, h: 1440 }, A2.scale('3/2'), dev);
const win = new HR.Receiver('viewport', { w: 1900, h: 1000 }, A2.translate(100, 80), css); const el = new HR.Receiver('canvas', { w: 900, h: 560 }, A2.translate('213/2', '150'), win);
const paper = new HR.Receiver('paper', { w: 20, h: 12 }, A2.translate(40, 520).compose(A2.scale(40, -40)), el);
const toDev = paper.toRoot(); console.log('paper→device', toDev.toString(), 'gram', toDev.gram().map((r) => r.join(',')).join(';'), 'hand', toDev.hand());
console.log('address of (1,1) in device', dev.address(toDev.apply([1, 1])).map((c) => c.join(':')).join(' '), '| seam probe', dev.address([2, 3]).length, dev.address(['5/2', 3]).length, dev.address(['5/2', '7/2']).length);
const cyc = HR.Receivers.cycleDeficit([el.toParent, win.toParent, css.toParent, paper.toParent.compose(A2.identity()), el.toRoot().inverse(), paper.toParent.inverse()]); console.log('cycle flat?', cyc.flat, cyc.map.toString());
const at = HR.Receivers.atlas([css, win, el, paper]); console.log('atlas classes', at.classes.join(','), 'chromatic', at.chromatic, 'adjacent pairs', at.edges);
// minkowski
const mp = HR.Minkowski.plan({ window: { t0: -2, t1: 6, x0: -4, x1: 4 }, receiver: [5, 0], beta: '3/5', objects: [{ at: [0, 0], u: '0', name: 'A' }, { at: [0, 1], u: '3/5', name: 'B' }], hyperbolae: ['1'], grid: 32 });
console.log('mink lines', mp.lines.length, 'contours', mp.contours.length, 'boost calib', mp.boost.calibration.toString(), 'retarded B', mp.retarded[1].map((r) => r.event.join(',') + ' null? ' + r.check.kind).join(' | '), 'interval AB', mp.interval.kind, mp.interval.s2.toString());
// circuit
const circ = HR.Circuit.LatticeCircuit({ g: 3, admittance: { x: '1', y: '1/2', z: { re: '0', im: '1/3' } }, sources: [{ node: [0, 0, 0], current: { re: '1', im: '0' } }, { node: [2, 2, 2], current: { re: '-1', im: '0' } }], ground: [2, 2, 2] });
console.log('circuit', circ.nodes.length, circ.edges.length, 'unknowns', circ.unknowns, 'solve ms', circ.solveMs, 'KCL worst |r|²', circ.kclWorst.toString(), 'power', circ.power.toString(), 'phi(0)', circ.phi[0].toString().slice(0, 60));
const chart = HR.Models.Chart({ shown: [0, 1, 2], folded: 3, fold: ['0', '0', '0'], law: { kind: 'oblique', a: '2/5', b: '2/7' } });
const sp = HR.Circuit.schematicPlan(circ, chart, { unit: '1/4' }); console.log('schematic crossings', sp.crossings, 'open', sp.openCrossings, 'widths', [...new Set(sp.edges.map((e) => e.width))].join(','), 'cut edges', sp.edges.filter((e) => e.cuts).length);
// bord
for (const k of ['pants', 'saddle']) { const s = HR.Bord.slices(k, { slices: 8, grid: 32 }); const pr = HR.Bord.project(s, chart); console.log(k, 'bottom comps', s.components.bottom, 'top comps', s.components.top, 'segs', pr.segs.length); }
// polygraph
const pg = HR.Polygraphs.fromLattice3(3); console.log('polygraph', pg.polygraph.counts().join('/'), 'euler', pg.polygraph.euler(), 'cubes', pg.cubes, 'unresolved', pg.unresolved, 'obstructions', pg.polygraph.obstructions.length);
const pm = HR.Polygraphs.fromPlanarMap(sp.map); console.log('map polygraph', pm.polygraph.counts().join('/'), 'obstructions', pm.polygraph.obstructions.length, 'euler V-E+F', sp.map.nodes.length - sp.map.edges.length + sp.map.faces.length, 'discr', sp.discriminants.length);
console.log('total ms', Date.now() - t0);
