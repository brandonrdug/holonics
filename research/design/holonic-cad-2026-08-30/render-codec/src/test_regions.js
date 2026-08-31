const HR = require('./core.js'); require('./fields.js'); require('./regions.js');
const N = 64; const kg = new HR.KleinGordon(N, { m: 0.3, dt: 0.2, seed: 7 }); kg.sampleVacuum();
const rg = HR.Regions.regions(kg.phi, N, [-0.6, -0.2, 0.2, 0.6]); const c = HR.FourColor.colour(rg.count, rg.adjacency, { budget: 300000 });
console.log('regions', rg.count, 'chromatic', c.chromatic, 'exact', c.exact, 'steps', c.steps);
const rg2 = HR.Regions.regions(kg.phi, N, [-0.6, -0.2, 0.2, 0.6], { wrap: false }); const c2 = HR.FourColor.colour(rg2.count, rg2.adjacency, { budget: 300000 });
console.log('disk (no wrap) regions', rg2.count, 'chromatic', c2.chromatic, 'exact', c2.exact, 'steps', c2.steps);
