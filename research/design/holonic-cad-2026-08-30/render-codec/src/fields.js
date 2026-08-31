// ===== fields.js — DEC on a periodic square lattice; Float64 is declared a rendering face =====
// Topology (incidence) is exact and integer; field values are Float64 faces of the exact carrier.
(function (HR) {
  // --- exact incidence of the N×N periodic square lattice (0-cells, 1-cells, 2-cells) ---
  function Lattice2(N) {
    const V = N * N, E = 2 * V, F = V;
    const vid = (i, j) => ((i + N) % N) * N + ((j + N) % N);
    const eid = (i, j, dir) => 2 * vid(i, j) + dir; // dir 0: (i,j)->(i+1,j) [x]; dir 1: (i,j)->(i,j+1) [y]
    const fid = (i, j) => vid(i, j);                 // face with lower-left corner (i,j)
    // d0: edge = target - source ; d1: face boundary = e_x(i,j) + e_y(i+1,j) - e_x(i,j+1) - e_y(i,j)
    const d0 = (e) => { const v = e >> 1, dir = e & 1, i = Math.floor(v / N), j = v % N; return [[vid(i, j), -1], [dir === 0 ? vid(i + 1, j) : vid(i, j + 1), +1]]; };
    const d1 = (f) => { const i = Math.floor(f / N), j = f % N; return [[eid(i, j, 0), +1], [eid(i + 1, j, 1), +1], [eid(i, j + 1, 0), -1], [eid(i, j, 1), -1]]; };
    return { N, V, E, F, vid, eid, fid, d0, d1, hodge: { star0: 1, star1: 1, star2: 1 } }; // unit lattice: all dual measures are 1 (rational, exact)
  }
  // --- 2-D FFT (radix-2, N power of two), complex arrays as separate re/im Float64Array ---
  function fft1(re, im, inv) {
    const n = re.length; for (let i = 1, j = 0; i < n; i++) { let bit = n >> 1; for (; j & bit; bit >>= 1) j ^= bit; j ^= bit; if (i < j) { [re[i], re[j]] = [re[j], re[i]]; [im[i], im[j]] = [im[j], im[i]]; } }
    for (let len = 2; len <= n; len <<= 1) { const ang = 2 * Math.PI / len * (inv ? 1 : -1); const wr = Math.cos(ang), wi = Math.sin(ang);
      for (let i = 0; i < n; i += len) { let cr = 1, ci = 0; for (let k = 0; k < len / 2; k++) { const ur = re[i + k], ui = im[i + k]; const vr = re[i + k + len / 2] * cr - im[i + k + len / 2] * ci, vi = re[i + k + len / 2] * ci + im[i + k + len / 2] * cr; re[i + k] = ur + vr; im[i + k] = ui + vi; re[i + k + len / 2] = ur - vr; im[i + k + len / 2] = ui - vi; const nr = cr * wr - ci * wi; ci = cr * wi + ci * wr; cr = nr; } } }
    if (inv) for (let i = 0; i < n; i++) { re[i] /= n; im[i] /= n; }
  }
  function fft2(re, im, N, inv) {
    const tr = new Float64Array(N), ti = new Float64Array(N);
    for (let i = 0; i < N; i++) { fft1(re.subarray(i * N, i * N + N), im.subarray(i * N, i * N + N), inv); }
    for (let j = 0; j < N; j++) { for (let i = 0; i < N; i++) { tr[i] = re[i * N + j]; ti[i] = im[i * N + j]; } fft1(tr, ti, inv); for (let i = 0; i < N; i++) { re[i * N + j] = tr[i]; im[i * N + j] = ti[i]; } }
  }
  // lattice eigenvalue of -Δ0 for mode (kx, ky): 4 sin²(π kx/N) + 4 sin²(π ky/N)
  function lapEig(N) { const L = new Float64Array(N * N); for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const a = Math.sin(Math.PI * i / N), b = Math.sin(Math.PI * j / N); L[i * N + j] = 4 * a * a + 4 * b * b; } return L; }
  // --- Navier–Stokes, vorticity–streamfunction, periodic, spectral Poisson + spectral diffusion + semi-Lagrangian advection ---
  class NavierStokes {
    constructor(N, opts = {}) {
      this.L = Lattice2(N); this.N = N; this.nu = opts.nu ?? 0.002; this.dt = opts.dt ?? 0.5;
      this.omega = new Float64Array(N * N); this.psi = new Float64Array(N * N); this.ux = new Float64Array(N * N); this.uy = new Float64Array(N * N);
      this.eig = lapEig(N); this.t = 0; this.tick = 0; this.re = new Float64Array(N * N); this.im = new Float64Array(N * N);
    }
    seedVortices(spec) { // spec: [{x,y,gamma,r}] in lattice units — Gaussian vortex blobs
      const N = this.N; this.omega.fill(0);
      for (const v of spec) for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { let dx = i - v.x, dy = j - v.y; dx -= N * Math.round(dx / N); dy -= N * Math.round(dy / N); this.omega[i * N + j] += v.gamma * Math.exp(-(dx * dx + dy * dy) / (2 * v.r * v.r)); }
      this.solvePsi();
    }
    solvePsi() { // -Δψ = ω  ⇒  ψ_k = ω_k / λ_k, λ_0 := 0 mode removed (mean ψ = 0)
      const N = this.N; this.re.set(this.omega); this.im.fill(0); fft2(this.re, this.im, N, false);
      for (let k = 0; k < N * N; k++) { const l = this.eig[k]; if (l === 0) { this.re[k] = 0; this.im[k] = 0; } else { this.re[k] /= l; this.im[k] /= l; } }
      fft2(this.re, this.im, N, true); this.psi.set(this.re);
      // velocity as the 1-form ⋆dψ read at vertices by centred differences (a rendering face of the edge 1-form)
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const ip = (i + 1) % N, im = (i + N - 1) % N, jp = (j + 1) % N, jm = (j + N - 1) % N;
        this.ux[i * N + j] = 0.5 * (this.psi[i * N + jp] - this.psi[i * N + jm]);      // u = ∂ψ/∂y
        this.uy[i * N + j] = -0.5 * (this.psi[ip * N + j] - this.psi[im * N + j]); }   // v = -∂ψ/∂x
    }
    sample(arr, x, y) { const N = this.N; x = ((x % N) + N) % N; y = ((y % N) + N) % N; const i = Math.floor(x), j = Math.floor(y), fx = x - i, fy = y - j; const i1 = (i + 1) % N, j1 = (j + 1) % N; return (1 - fx) * (1 - fy) * arr[i * N + j] + fx * (1 - fy) * arr[i1 * N + j] + (1 - fx) * fy * arr[i * N + j1] + fx * fy * arr[i1 * N + j1]; }
    velocity(x, y) { return [this.sample(this.ux, x, y), this.sample(this.uy, x, y)]; }
    step() { // one tick: advect ω along u for dt (RK2 backward trace), then diffuse spectrally
      const N = this.N, dt = this.dt; const next = new Float64Array(N * N);
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { let [u, v] = this.velocity(i, j); const xm = i - 0.5 * dt * u, ym = j - 0.5 * dt * v; [u, v] = this.velocity(xm, ym); next[i * N + j] = this.sample(this.omega, i - dt * u, j - dt * v); }
      this.re.set(next); this.im.fill(0); fft2(this.re, this.im, N, false);
      for (let k = 0; k < N * N; k++) { const f = Math.exp(-this.nu * this.eig[k] * dt); this.re[k] *= f; this.im[k] *= f; }
      fft2(this.re, this.im, N, true); this.omega.set(this.re); this.solvePsi(); this.t += dt; this.tick++;
    }
    // entropy production of the flow: enstrophy dissipation ν|∇ω|² per site (central differences on the torus; a Float64 face)
    dissipation() { const N = this.N, w = this.omega; const eps = new Float64Array(N * N); let total = 0; for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const ip = (i + 1) % N, im = (i + N - 1) % N, jp = (j + 1) % N, jm = (j + N - 1) % N; const gx = 0.5 * (w[ip * N + j] - w[im * N + j]), gy = 0.5 * (w[i * N + jp] - w[i * N + jm]); const e = this.nu * (gx * gx + gy * gy); eps[i * N + j] = e; total += e; } return { eps, total }; }
    receipts() { // kinematic receipts: circulation (sum ω), enstrophy, energy face
      let circ = 0, ens = 0, en = 0; for (let k = 0; k < this.N * this.N; k++) { circ += this.omega[k]; ens += this.omega[k] * this.omega[k]; en += this.ux[k] * this.ux[k] + this.uy[k] * this.uy[k]; }
      return { circulation: circ, enstrophy: ens, energy: 0.5 * en, tick: this.tick, t: this.t };
    }
  }
  // --- free scalar field (Klein–Gordon) on the periodic lattice: one vacuum fluctuation sample and its evolution ---
  class KleinGordon {
    constructor(N, opts = {}) { this.N = N; this.m = opts.m ?? 0.3; this.dt = opts.dt ?? 0.25; this.phi = new Float64Array(N * N); this.pi = new Float64Array(N * N); this.eig = lapEig(N); this.t = 0; this.tick = 0; this.seed = opts.seed ?? 1; }
    rng() { // deterministic mulberry32 — the sample is a situated occurrence with a recorded seed
      let a = (this.seed += 0x6D2B79F5); a = Math.imul(a ^ (a >>> 15), a | 1); a ^= a + Math.imul(a ^ (a >>> 7), a | 61); return ((a ^ (a >>> 14)) >>> 0) / 4294967296; }
    gauss() { const u = 1 - this.rng(), v = this.rng(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); }
    sampleVacuum() { // φ_k ~ N(0, 1/(2ω_k)) per mode with ω_k² = m² + λ_k ; π_k ~ N(0, ω_k/2); hermitian symmetry for a real field
      const N = this.N; const re = new Float64Array(N * N), im = new Float64Array(N * N), pre = new Float64Array(N * N), pim = new Float64Array(N * N);
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const k = i * N + j; const w = Math.sqrt(this.m * this.m + this.eig[k]); const s = Math.sqrt(1 / (2 * w)) * N / Math.SQRT2; const sp = Math.sqrt(w / 2) * N / Math.SQRT2; re[k] = s * this.gauss(); im[k] = s * this.gauss(); pre[k] = sp * this.gauss(); pim[k] = sp * this.gauss(); }
      // enforce φ(-k) = conj φ(k)
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const k = i * N + j, kk = ((N - i) % N) * N + ((N - j) % N); if (kk < k) { re[k] = re[kk]; im[k] = -im[kk]; pre[k] = pre[kk]; pim[k] = -pim[kk]; } else if (kk === k) { im[k] = 0; pim[k] = 0; } }
      fft2(re, im, N, true); fft2(pre, pim, N, true); this.phi.set(re); this.pi.set(pre); this.t = 0; this.tick = 0;
    }
    step() { // leapfrog: π += dt (Δφ − m²φ); φ += dt π   (exact lattice dispersion ω_k² = m² + λ_k)
      const N = this.N, dt = this.dt, m2 = this.m * this.m;
      for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const k = i * N + j; const lap = this.phi[((i + 1) % N) * N + j] + this.phi[((i + N - 1) % N) * N + j] + this.phi[i * N + (j + 1) % N] + this.phi[i * N + (j + N - 1) % N] - 4 * this.phi[k]; this.pi[k] += dt * (lap - m2 * this.phi[k]); }
      for (let k = 0; k < N * N; k++) this.phi[k] += dt * this.pi[k];
      this.t += dt; this.tick++;
    }
    correlator(i0, j0) { // ⟨φ(x0)φ(x)⟩ read from ONE sample is not the vacuum correlator; return the sample product face and label it so
      const N = this.N, out = new Float64Array(N * N), c = this.phi[i0 * N + j0]; for (let k = 0; k < N * N; k++) out[k] = c * this.phi[k]; return out; }
    energy() { let e = 0; const N = this.N; for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) { const k = i * N + j; const dx = this.phi[((i + 1) % N) * N + j] - this.phi[k], dy = this.phi[i * N + (j + 1) % N] - this.phi[k]; e += 0.5 * (this.pi[k] * this.pi[k] + dx * dx + dy * dy + this.m * this.m * this.phi[k] * this.phi[k]); } return e; }
  }
  HR.Lattice2 = Lattice2; HR.fft2 = fft2; HR.NavierStokes = NavierStokes; HR.KleinGordon = KleinGordon;
})(HR);

// ===== traces.js — topological traces: level sets, transported paths; no arrowheads =====
(function (HR) {
  // marching squares on a periodic N×N 0-form; returns polylines in lattice coordinates (may wrap)
  function levelSets(field, N, levels, opts = {}) {
    const out = [];
    const at = (i, j) => field[((i % N + N) % N) * N + ((j % N + N) % N)];
    const cellsWrap = opts.wrap === false ? N - 1 : N;
    for (const c of levels) {
      const segs = [];
      for (let i = 0; i < cellsWrap; i++) for (let j = 0; j < cellsWrap; j++) {
        const a = at(i, j) - c, b = at(i + 1, j) - c, d = at(i + 1, j + 1) - c, e = at(i, j + 1) - c; // corners: (i,j),(i+1,j),(i+1,j+1),(i,j+1)
        const idx = (a > 0 ? 1 : 0) | (b > 0 ? 2 : 0) | (d > 0 ? 4 : 0) | (e > 0 ? 8 : 0); if (idx === 0 || idx === 15) continue;
        const lerp = (p, q, va, vb) => { const t = va / (va - vb); return [p[0] + t * (q[0] - p[0]), p[1] + t * (q[1] - p[1])]; };
        const P = [[i, j], [i + 1, j], [i + 1, j + 1], [i, j + 1]], vals = [a, b, d, e];
        const edgePt = (k) => lerp(P[k], P[(k + 1) % 4], vals[k], vals[(k + 1) % 4]);
        const table = { 1: [[3, 0]], 2: [[0, 1]], 3: [[3, 1]], 4: [[1, 2]], 5: [[3, 0], [1, 2]], 6: [[0, 2]], 7: [[3, 2]], 8: [[2, 3]], 9: [[0, 2]], 10: [[0, 1], [2, 3]], 11: [[1, 2]], 12: [[1, 3]], 13: [[0, 1]], 14: [[3, 0]] };
        for (const [u, v] of table[idx]) segs.push([edgePt(u), edgePt(v)]);
      }
      out.push({ level: c, segments: segs });
    }
    return out;
  }
  // transported path: integrate a velocity sampler from a seed for a fixed proper time T (the length is the causal datum, not an arrowhead)
  function transportPath(vel, seed, T, h = 0.25, maxSteps = 4000) {
    const pts = [[seed[0], seed[1]]]; let x = seed[0], y = seed[1], t = 0, steps = 0;
    while (t < T && steps++ < maxSteps) { const k1 = vel(x, y); const k2 = vel(x + 0.5 * h * k1[0], y + 0.5 * h * k1[1]); const k3 = vel(x + 0.5 * h * k2[0], y + 0.5 * h * k2[1]); const k4 = vel(x + h * k3[0], y + h * k3[1]);
      x += h / 6 * (k1[0] + 2 * k2[0] + 2 * k3[0] + k4[0]); y += h / 6 * (k1[1] + 2 * k2[1] + 2 * k3[1] + k4[1]); t += h; pts.push([x, y]); }
    return pts;
  }
  HR.Traces = { levelSets, transportPath };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
