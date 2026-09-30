"""Exterior float model of the receiving bank on the declared order-2 field, with exact first-order
sensitivities (eigen-derivative of the executed monodromy's spectral radius; the face's quadratic).

Validated against the exact owner (bank_causes dump-read): placement, E_0, member growths.
"""
import numpy as np
from fractions import Fraction

D = 60          # receiving ring period (nodes, turn ticks)
N_REQ = 40      # request cells
M_ST = 8        # stations
CLASSES = 5     # 4 symbols + termination
SYMBOLS = 4
TERM = 4
Y = 16.0
A0 = 2 + 1 / Y + 0.5   # M_t = A0 I - p R(c)
V = (3 + 4j) / 5
ZETA = np.conj(V) ** 2


def nu_hat(n, L=None):
    """The population chart nu(n) (dyadic nearest 1/n); L_nu from the declared field."""
    if n == 0:
        return 0.0
    L = L or NU_EXP
    scale = 1 << L
    return ((2 * scale + n) // (2 * n)) / scale


NU_EXP = 21  # read from the dump: nu(3) = 699051/2^21


# ---------------------------------------------------------------------------------------------
# terrains (synthetic, exact truth routines only generate data)

def order2(rng, count, n=N_REQ, m=M_ST):
    out = []
    for _ in range(count):
        req = list(rng.integers(0, SYMBOLS, n))
        seq = req[:]
        for _ in range(m):
            seq.append((seq[-2] + 1) % SYMBOLS)
        out.append((req, seq[n:]))
    return out


def alternation(rng, count, n=N_REQ, m=M_ST):
    """Period-2 alternation: x_t = x_(t-2) over request and continuation."""
    out = []
    for _ in range(count):
        a, b = rng.integers(0, SYMBOLS, 2)
        seq = [a if t % 2 == 0 else b for t in range(n + m)]
        out.append((seq[:n], seq[n:]))
    return out


def spectral_line(rng, count, n=N_REQ, m=M_ST):
    """A single spectral line: x_t = x_0 + s t (mod 4), s drawn per request."""
    out = []
    for _ in range(count):
        x0, s = rng.integers(0, SYMBOLS, 2)
        seq = [int((x0 + s * t) % SYMBOLS) for t in range(n + m)]
        out.append((seq[:n], seq[n:]))
    return out


def order2_random_lag2(rng, count, n=N_REQ, m=M_ST):
    """Uniform request, continuation x_t = x_(t-2) (the order-2 rule without its +1)."""
    out = []
    for _ in range(count):
        req = list(rng.integers(0, SYMBOLS, n))
        seq = req[:]
        for _ in range(m):
            seq.append(seq[-2])
        out.append((req, seq[n:]))
    return out


# ---------------------------------------------------------------------------------------------
# placements: C[b, r, x] = weight of class x at rotation r (a datum of age r)

# The source navigator's transport modulus rho (the owner's `ConstitutionRead::transport`): one at
# the founding; the fits set it.
DECAY = [1.0]


def placement_counts(request, placed, station, cand):
    """One candidate's placement on the passage read from its station (the owner's
    `BankPlacement::storage`, the station-framed law of September 30): request cells at rotations
    39..0 and the placed stations and the candidate at rotation 59 - j, each datum at its
    transported weight rho^r / sum rho^r over the span, r its two-sided distance from the station
    read (n + j - k for request cell k, |i - j| for station i); at rho = 1 the one population
    nu(n + v), v the placed count (candidate included)."""
    C = np.zeros((D, CLASSES))
    cells = dict(placed)
    if station is not None:
        cells[station] = cand
    n = len(request)
    r = DECAY[0]
    if r == 1.0:
        w = nu_hat(n + len(cells))
        for k, x in enumerate(request):
            C[(n - 1 - k) % D, x] += w
        for j, x in cells.items():
            C[(D - 1 - j) % D, x] += w
        return C
    if station is None:
        raise ValueError('below modulus one a placement is read from a station')
    distances = [n + station - k for k in range(n)] + [abs(i - station) for i in cells]
    raw = [r ** a for a in distances]
    total = sum(raw)
    for k, x in enumerate(request):
        C[(n - 1 - k) % D, x] += raw[k] / total
    for i, (j, x) in enumerate(cells.items()):
        C[(D - 1 - j) % D, x] += raw[n + i] / total
    return C


def candidates_counts(request, placed, station):
    return np.stack([placement_counts(request, placed, station, y) for y in range(CLASSES)])


def storage_nodes(C, E):
    """z_node[b] = sum_x conv(C[b,:,x], E[:,x]) (circular), C (B, D, X), E (D, X) complex."""
    FC = np.fft.fft(C, axis=1)                  # (B, D, X)
    FE = np.fft.fft(E, axis=0)                  # (D, X)
    return np.fft.ifft((FC * FE[None]).sum(axis=2), axis=1)


def to_turn(z_node):
    return z_node[:, ::-1]                      # tick t reads node d-1-t


def grad_E_from_node(C, G_node):
    """dF = Re sum_b sum_n conj(G_node[b,n]) dz_node[b,n] -> G_E (D, X) with dF = Re sum conj(G_E) dE."""
    FC = np.fft.fft(C, axis=1)                  # (B, D, X)
    FG = np.fft.fft(G_node, axis=1)             # (B, D)
    # cross-correlation: G_E[m, x] = sum_b sum_r C[b,r,x] G[b, m + r]
    FGE = (np.conj(FC) * FG[:, :, None]).sum(axis=0)
    return np.fft.ifft(FGE, axis=0)


# ---------------------------------------------------------------------------------------------
# the executed growth and its exact first-order sensitivity

R_RE = np.array([[1.0, 0.0], [0.0, -1.0]])
R_IM = np.array([[0.0, 1.0], [1.0, 0.0]])


def _ticks(c, p):
    """Per tick executed maps and their derivatives in Re c, Im c. c (B, d) complex."""
    re, im = c.real, c.imag
    det = A0 ** 2 - p ** 2 * (re ** 2 + im ** 2)
    X = np.empty(c.shape + (2, 2))
    X[..., 0, 0] = (A0 + p * re) / det
    X[..., 1, 1] = (A0 - p * re) / det
    X[..., 0, 1] = (p * im) / det
    X[..., 1, 0] = (p * im) / det
    K = np.empty(c.shape + (2, 2))
    K[..., 0, 0] = 1 - 2 * p * re
    K[..., 1, 1] = 1 + 2 * p * re
    K[..., 0, 1] = -2 * p * im
    K[..., 1, 0] = -2 * p * im
    I2 = np.eye(2)
    XK = X @ K
    T = np.empty(c.shape + (4, 4))
    T[..., :2, :2] = I2 - XK
    T[..., :2, 2:] = 2 * X
    T[..., 2:, :2] = -2 * XK
    T[..., 2:, 2:] = 4 * X - I2
    dTs = []
    for dR in (R_RE, R_IM):
        dX = p * (X @ dR @ X)
        dK = -2 * p * dR
        dXK = dX @ K + X @ dK
        dT = np.empty(c.shape + (4, 4))
        dT[..., :2, :2] = -dXK
        dT[..., :2, 2:] = 2 * dX
        dT[..., 2:, :2] = -2 * dXK
        dT[..., 2:, 2:] = 4 * dX
        dTs.append(dT)
    return T, dTs, det


def member_growth(zturn, member, p, want_grad=False):
    B, d = zturn.shape
    phase = 1j ** ((member * np.arange(d)) % 4)
    c = zturn * phase[None]
    T, dTs, det = _ticks(c, p)
    Mon = np.broadcast_to(np.eye(4), (B, 4, 4)).copy()
    for t in range(d):
        Mon = T[:, t] @ Mon
    w, Vr = np.linalg.eig(Mon)
    k = np.abs(w).argmax(axis=1)
    mu = w[np.arange(B), k]
    rho = np.abs(mu)
    certified = (det > 0).all(axis=1) & (A0 - 0.5 - p * np.abs(c) > 0).all(axis=1)
    if not want_grad:
        return rho, None, certified
    Linv = np.linalg.inv(Vr)
    r = Vr[np.arange(B), :, k]                 # (B, 4)
    l = Linv[np.arange(B), k, :]               # (B, 4): l^T r = 1
    # forward vectors rho_t = P_t r, backward lam_t^T = l^T S_t
    fwd = np.empty((B, d, 4), complex)
    v = r.copy()
    for t in range(d):
        fwd[:, t] = v
        v = np.einsum('bij,bj->bi', T[:, t], v)
    bwd = np.empty((B, d, 4), complex)
    u = l.copy()
    for t in range(d - 1, -1, -1):
        bwd[:, t] = u
        u = np.einsum('bi,bij->bj', u, T[:, t])
    dmu_re = np.einsum('bti,btij,btj->bt', bwd, dTs[0], fwd)
    dmu_im = np.einsum('bti,btij,btj->bt', bwd, dTs[1], fwd)
    scale = np.conj(mu)[:, None] / rho[:, None]
    g_re = (scale * dmu_re).real
    g_im = (scale * dmu_im).real
    G_c = g_re + 1j * g_im                      # d rho = Re(conj(G_c) dc)
    G_z = np.conj(phase)[None] * G_c            # dc = phase dz  ->  d rho = Re(conj(conj(phase) G_c) dz)
    # careful: Re(conj(G_c) phase dz) = Re(conj(conj(phase) G_c) dz)
    return rho, G_z, certified


def joint_growth(zturn, p, want_grad=False, members=(0, 1, 2, 3)):
    """Joint growth = max over members; its (sub)gradient is the attaining member's."""
    ps = p if np.ndim(p) else [p] * len(members)
    rhos, grads, certs = [], [], []
    for mi, m in enumerate(members):
        rho, G, cert = member_growth(zturn, m, ps[mi], want_grad)
        rhos.append(rho)
        grads.append(G)
        certs.append(cert)
    rhos = np.stack(rhos, axis=1)
    which = rhos.argmax(axis=1)
    joint = rhos.max(axis=1)
    cert = np.stack(certs, axis=1).all(axis=1)
    if not want_grad:
        return joint, None, rhos, cert
    G = np.stack(grads, axis=1)[np.arange(len(joint)), which]
    return joint, G, rhos, cert


# ---------------------------------------------------------------------------------------------
# the face (kicked chart's second order at each member's resonance and its mirror)

def face_weights(d=D, members=(0, 1, 2, 3)):
    t = np.arange(d)
    rows = []
    for m in members:
        base = 1j ** ((m * t) % 4)
        rows.append(base * ZETA ** t)
        rows.append(base * np.conj(ZETA) ** t)
    return np.array(rows)


FW = face_weights()


def face(zturn, p, want_grad=False):
    W = zturn @ FW.T                            # (B, 8)
    A = p ** 2 * (np.abs(W) ** 2).sum(axis=1)
    if not want_grad:
        return A, None
    # dA = 2 p^2 Re sum_k conj(W_k) sum_t FW[k,t] dz_t = Re sum_t conj(G_t) dz_t, G_t = 2p^2 sum_k W_k conj(FW[k,t])
    G = 2 * p ** 2 * (W @ np.conj(FW))
    return A, G
