"""Phase 1 -- the controls, which precede the reading.

Two frames are required before any invariant may be called one (CLAUDE.md section 0, lesson 4).

CONTROL A (gauge orbit, within-head GL). The head-space gauge is
    W_V -> M W_V ,  W_O -> W_O M^-1      for any invertible M
which leaves W_OV = W_O W_V EXACTLY unchanged while moving W_O and W_V individually. So:
    - the singular values of the RAW projection W_V MUST move  (a coordinate)
    - the spectrum of the COMPOSED circuit W_OV MUST NOT move  (an invariant)
If the raw reading does not move, the gauge is vacuous on this material and the test proves
nothing (CLAUDE.md section 8: a gauge whose group acts trivially is not a gauge).

CONTROL B (bus gauge, orthogonal). The tie reduces the residual gauge to O(2560). Under
    E -> E M^T ,  W -> M W M^T
the induced map Phi_S = E_S W E_S^T is invariant elementwise.

CONTROL C (null). A matched-shape random matrix. Marchenko-Pastur is the null; a species that
also appears here is not a finding.

Efficiency note that is also what makes this scale: W_OV = Wo @ Wv has rank <= d, and
eig(AB) and eig(BA) share their nonzero spectrum, so the spectrum of the 2560x2560 circuit is
computed from the d x d matrix Wv @ Wo. The bus-sized matrix is never formed.
"""
import numpy as np

from read_map import (
    Map,
    participation_ratio,
    projectivised_spectrum,
    winding_census,
)

rng = np.random.default_rng(20260813)


def ov_spectrum(Wo, Wv):
    """Nonzero spectrum of W_OV = Wo @ Wv, via the small side. Exact identity, not an
    approximation: eig(AB) and eig(BA) agree off zero."""
    return np.linalg.eigvals((Wv @ Wo).astype(np.float64))


def report(tag, evals):
    z = projectivised_spectrum(evals)
    w = winding_census(evals)
    return {
        "tag": tag,
        "projectivised_top8": np.round(np.abs(z[:8]), 6),
        "pairs": w["conjugate_pairs"],
        "real_pos": w["real_positive"],
        "real_neg": w["real_negative"],
        "pr": round(participation_ratio(np.abs(evals)), 3),
    }


def main():
    m = Map()
    species = m.layer_species()
    L, H = 5, 0  # a global-attention layer, head 0
    Wo, Wv = m.ov(L, H)
    print(f"layer {L} ({species[L]}), head {H}: Wo {Wo.shape}  Wv {Wv.shape}")
    d = Wv.shape[0]

    base = ov_spectrum(Wo, Wv)

    # ---- CONTROL A: within-head GL gauge --------------------------------
    M = rng.standard_normal((d, d))
    while abs(np.linalg.det(M)) < 1e-6:
        M = rng.standard_normal((d, d))
    Minv = np.linalg.inv(M)
    Wv_g = M @ Wv
    Wo_g = Wo @ Minv
    gauged = ov_spectrum(Wo_g, Wv_g)

    raw_before = np.linalg.svd(Wv.astype(np.float64), compute_uv=False)
    raw_after = np.linalg.svd(Wv_g.astype(np.float64), compute_uv=False)
    raw_pr_before = participation_ratio(raw_before)
    raw_pr_after = participation_ratio(raw_after)

    zb = np.sort_complex(projectivised_spectrum(base))
    zg = np.sort_complex(projectivised_spectrum(gauged))
    inv_drift = float(np.max(np.abs(np.sort(np.abs(zb)) - np.sort(np.abs(zg)))))

    print("\n=== CONTROL A -- within-head GL gauge ===")
    print(f"  raw W_V participation ratio   before {raw_pr_before:.3f}  after {raw_pr_after:.3f}"
          f"   -> MOVED by {abs(raw_pr_after-raw_pr_before):.3f}")
    print(f"  raw W_V top singular value    before {raw_before[0]:.4f}  after {raw_after[0]:.4f}")
    print(f"  composed W_OV projectivised spectrum max drift: {inv_drift:.3e}")
    print(f"  winding census before {winding_census(base)['conjugate_pairs']} pairs, "
          f"after {winding_census(gauged)['conjugate_pairs']} pairs")
    a_ok = abs(raw_pr_after - raw_pr_before) > 1.0 and inv_drift < 1e-6
    print(f"  VERDICT: {'PASS' if a_ok else 'FAIL'} "
          f"(raw must move, composed must not)")

    # ---- CONTROL B: bus orthogonal gauge on the induced map -------------
    ids = [236778, 13498, 236812, 19025, 236862, 13779, 1282, 236784]  # 2 two 4 four + plus add =
    E = m.rows("model.language_model.embed_tokens.weight", ids).astype(np.float64)
    Phi = (E @ Wo.astype(np.float64)) @ (Wv.astype(np.float64) @ E.T)
    Q, _ = np.linalg.qr(rng.standard_normal((Wo.shape[0], Wo.shape[0])))
    Phi_g = ((E @ Q.T) @ (Q @ Wo.astype(np.float64))) @ ((Wv.astype(np.float64) @ Q.T) @ (Q @ E.T))
    drift = float(np.max(np.abs(Phi - Phi_g)) / max(np.max(np.abs(Phi)), 1e-30))
    print("\n=== CONTROL B -- bus orthogonal gauge on Phi_S ===")
    print(f"  Phi_S relative max drift under O(2560): {drift:.3e}")
    print(f"  VERDICT: {'PASS' if drift < 1e-9 else 'FAIL'}")

    # ---- CONTROL C: matched-shape null ----------------------------------
    print("\n=== CONTROL C -- matched-shape null ===")
    sv = float(np.std(Wv.astype(np.float64)))
    so = float(np.std(Wo.astype(np.float64)))
    Nv = rng.standard_normal(Wv.shape) * sv
    No = rng.standard_normal(Wo.shape) * so
    null = ov_spectrum(No, Nv)
    for r in (report("real  W_OV", base), report("null  W_OV", null)):
        print(f"  {r['tag']}: pairs={r['pairs']:4} real+={r['real_pos']:4} real-={r['real_neg']:4} "
              f"PR={r['pr']:8.3f}  top|z|={r['projectivised_top8'][:5]}")


if __name__ == "__main__":
    main()
