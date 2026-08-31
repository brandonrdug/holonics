// ===== colour.js — colour is a receiver's kernel: the dimensional_wave transduction, mirrored =====
// Owner mirrored: crates/holonic-engine/src/dimensional_wave.rs:235-267 (ExactPremultipliedReceiverResponse, transduce).
// Law (research/records/2026-07-30, 2026-08-05): currents of ONE mode are added before response; then three exact
// nonnegative phase responses P0 = Σ(Re A)², P1 = Σ(Im A)², P2 = Σ(Re A + Im A)²; for a declared positive aperture κ,
// D = κ + P0 + P1 + P2; premultiplied (R,G,B,α) = (P0/D, P1/D, P2/D, ΣP/D), transmittance τ = κ/D; R+G+B = α, α+τ = 1.
// Quantize to u8 ONCE, last. No constituent owns a palette; chroma occurs only where the modal population produces it.
(function (HR) {
  const { Rat, R } = HR;
  // exact form over Rat: modes = [{re: Rat, im: Rat}] already superposed per mode
  function transduceExact(modes, aperture) {
    let P0 = Rat.ZERO, P1 = Rat.ZERO, P2 = Rat.ZERO;
    for (const m of modes) { const re = R(m.re), im = R(m.im); P0 = P0.add(re.mul(re)); P1 = P1.add(im.mul(im)); const d = re.add(im); P2 = P2.add(d.mul(d)); }
    const total = P0.add(P1).add(P2); const D = R(aperture).add(total);
    const out = { primaries: [P0.div(D), P1.div(D), P2.div(D)], alpha: total.div(D), transmittance: R(aperture).div(D) };
    // the two identities the Rust owner debug_asserts
    if (!out.primaries[0].add(out.primaries[1]).add(out.primaries[2]).eq(out.alpha)) throw new Error('transduce: ΣP/D ≠ α');
    if (!out.alpha.add(out.transmittance).eq(Rat.ONE)) throw new Error('transduce: α + τ ≠ 1');
    return out;
  }
  // float face of the same law (fields whose values are already declared Float64 faces)
  function transduce(modes, aperture) {
    let P0 = 0, P1 = 0, P2 = 0; for (const m of modes) { P0 += m.re * m.re; P1 += m.im * m.im; const d = m.re + m.im; P2 += d * d; }
    const total = P0 + P1 + P2, D = aperture + total; return { primaries: [P0 / D, P1 / D, P2 / D], alpha: total / D, transmittance: aperture / D };
  }
  // the single quantization: premultiplied response over the paper ground, rounded once
  function octet(x) { return Math.max(0, Math.min(255, Math.round(x * 255))); }
  function toRGB(resp, paper = [246, 247, 244]) {
    const [r, g, b] = resp.primaries.map((p) => (p instanceof Rat ? p.toNumber() : p)); const tau = resp.transmittance instanceof Rat ? resp.transmittance.toNumber() : resp.transmittance;
    // premultiplied composite over the paper: channel = response·255 + τ·paper  (α = 1 − τ already inside the responses)
    return [octet(r + tau * paper[0] / 255), octet(g + tau * paper[1] / 255), octet(b + tau * paper[2] / 255)];
  }
  const css = (rgb) => `rgb(${rgb[0]},${rgb[1]},${rgb[2]})`;
  HR.Colour = { transduceExact, transduce, toRGB, css };
})(HR);
if (typeof module !== 'undefined') module.exports = HR;
