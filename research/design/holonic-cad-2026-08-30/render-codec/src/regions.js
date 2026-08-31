// ===== regions.js — level-band regions of a lattice 0-form (exact integer labels) and their adjacency: the colour law's input =====
(function (HR) {
  // band(v) = index of the band between consecutive levels; regions = connected components of equal band (4-neighbour); adjacency across lattice edges
  function regions(field, N, levels, opts = {}) {
    const wrap = opts.wrap !== false; const band = new Int32Array(N * N);
    for (let k = 0; k < N * N; k++) { let b = 0; while (b < levels.length && field[k] > levels[b]) b++; band[k] = b; }
    const label = new Int32Array(N * N).fill(-1); let count = 0; const stack = [];
    const nb = (i, j) => { const out = []; const push = (a, b) => { if (wrap) out.push([(a + N) % N, (b + N) % N]); else if (a >= 0 && a < N && b >= 0 && b < N) out.push([a, b]); }; push(i + 1, j); push(i - 1, j); push(i, j + 1); push(i, j - 1); return out; };
    for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const k = i * N + j; if (label[k] >= 0) continue; const id = count++; label[k] = id; stack.push([i, j]);
      while (stack.length) { const [a, b] = stack.pop(); for (const [c, d] of nb(a, b)) { const kk = c * N + d; if (label[kk] < 0 && band[kk] === band[k]) { label[kk] = id; stack.push([c, d]); } } } }
    const adjacency = new Map(); const add = (a, b) => { if (a === b) return; if (!adjacency.has(a)) adjacency.set(a, new Set()); adjacency.get(a).add(b); };
    for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const k = i * N + j; for (const [c, d] of nb(i, j)) { const kk = c * N + d; add(label[k], label[kk]); add(label[kk], label[k]); } }
    const bandOf = new Int32Array(count); for (let k = 0; k < N * N; k++) bandOf[label[k]] = band[k];
    return { label, band, count, adjacency, bandOf };
  }
  HR.Regions = { regions };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
// witnessed level boundaries: the dual-lattice edges separating sites of different band — no interpolated point
(function (HR) {
  function boundaries(rg, N, opts = {}) {
    const wrap = opts.wrap !== false; const segs = [];
    for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) {
      const k = i * N + j; const ii = i + 1, jj = j + 1;
      if (ii < N || wrap) { const kk = ((ii) % N) * N + j; if (rg.band[k] !== rg.band[kk]) segs.push([[i + 0.5, j - 0.5], [i + 0.5, j + 0.5]]); }
      if (jj < N || wrap) { const kk = i * N + (jj % N); if (rg.band[k] !== rg.band[kk]) segs.push([[i - 0.5, j + 0.5], [i + 0.5, j + 0.5]]); }
    }
    return segs;
  }
  HR.Regions.boundaries = boundaries;
})(HR);
