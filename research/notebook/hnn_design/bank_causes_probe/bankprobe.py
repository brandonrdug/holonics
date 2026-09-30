"""Exterior float probe of the receiving bank (hnn::ring::ReceivingBank, hnn::prediction).

Float64 only as an exterior probe; every reading used as evidence is validated against the exact
Rust owner (bank_dump) or certified there.

The bank: one node C = I, K = I, D = 0, port Y = 16, h = 1; members m = 0..3 (axis 1, step i^m),
strength p. Tick for member m at turn tick t: c_t = i^(m t) z_t, K_t = I - 2p R(c_t),
M_t = 2I + I/Y + K_t/2, X_t = M_t^-1, T_t = [[I - X K, 2X], [-2 X K, 4X - I]].
Monodromy = T_(d-1)...T_0; growth = spectral radius; joint = max over members.
Face: v = (3+4i)/5, zeta = conj(v)^2, W^+-_m = sum_t i^(m t) zeta^(+-t) z_t,
A = p^2 sum_m (|W+|^2 + |W-|^2).
"""
import numpy as np

Y = 16.0
H = 1.0
V = (3 + 4j) / 5
ZETA = np.conj(V) ** 2


def R(c):
    return np.array([[c.real, c.imag], [c.imag, -c.real]])


def tick_maps(zturn, member, p):
    """Executed tick maps for one member over a turn (array of complex amplitudes)."""
    d = len(zturn)
    I2 = np.eye(2)
    maps = []
    for t in range(d):
        c = (1j ** ((member * t) % 4)) * zturn[t]
        K = I2 - 2 * p * R(c)
        M = 2 * I2 + I2 / Y + 0.5 * K
        X = np.linalg.inv(M)
        T = np.block([[I2 - X @ K, 2 * X], [-2 * X @ K, 4 * X - I2]])
        maps.append(T)
    return maps


def batched_growth(zturns, p, members=(0, 1, 2, 3)):
    """Vectorized: zturns (B, d) complex -> member growths (B, len(members))."""
    B, d = zturns.shape
    out = np.zeros((B, len(members)))
    for mi, m in enumerate(members):
        phase = (1j ** ((m * np.arange(d)) % 4))
        c = zturns * phase[None, :]  # (B, d)
        # K = I - 2p R(c); M = (2 + 1/Y) I + K/2 = (2 + 1/Y + 1/2) I - p R(c)
        a0 = 2 + 1 / Y + 0.5
        re, im = c.real, c.imag
        # M = [[a0 - p re, -p im], [-p im, a0 + p re]]; det = a0^2 - p^2 |c|^2
        det = a0 ** 2 - p ** 2 * (re ** 2 + im ** 2)
        X = np.empty((B, d, 2, 2))
        X[..., 0, 0] = (a0 + p * re) / det
        X[..., 1, 1] = (a0 - p * re) / det
        X[..., 0, 1] = (p * im) / det
        X[..., 1, 0] = (p * im) / det
        K = np.empty((B, d, 2, 2))
        K[..., 0, 0] = 1 - 2 * p * re
        K[..., 1, 1] = 1 + 2 * p * re
        K[..., 0, 1] = -2 * p * im
        K[..., 1, 0] = -2 * p * im
        XK = X @ K
        I2 = np.eye(2)
        T = np.empty((B, d, 4, 4))
        T[..., :2, :2] = I2 - XK
        T[..., :2, 2:] = 2 * X
        T[..., 2:, :2] = -2 * XK
        T[..., 2:, 2:] = 4 * X - I2
        Mon = np.broadcast_to(np.eye(4), (B, 4, 4)).copy()
        for t in range(d):
            Mon = T[:, t] @ Mon
        ev = np.linalg.eigvals(Mon)
        out[:, mi] = np.abs(ev).max(axis=1)
    return out


def growth(zturn, p):
    return batched_growth(np.asarray(zturn)[None, :], p)[0]


def face_weights(d, members=(0, 1, 2, 3)):
    t = np.arange(d)
    rows = []
    for m in members:
        base = 1j ** ((m * t) % 4)
        rows.append(base * ZETA ** t)
        rows.append(base * np.conj(ZETA) ** t)
    return np.array(rows)  # (2*members, d)


def face_reading(zturns, p):
    """A = p^2 sum |W|^2 for (B, d)."""
    Wt = face_weights(zturns.shape[1])
    W = zturns @ Wt.T
    return p ** 2 * (np.abs(W) ** 2).sum(axis=1)


# ---------------------------------------------------------------------------------------------
# the declared sign sequence (hnn::constitution::declared_sign)

MASK64 = (1 << 64) - 1


def splitmix(state):
    z = (state + 0x9E3779B97F4A7C15) & MASK64
    z = ((z ^ (z >> 30)) * 0xBF58476D1CE4E5B9) & MASK64
    z = ((z ^ (z >> 27)) * 0x94D049BB133111EB) & MASK64
    return z ^ (z >> 31)


def declared_sign(locus, i, j):
    z = splitmix(0)
    for x in (locus, i, j):
        z = splitmix(z ^ x)
    return 1 if z & 1 else -1


def E0(d=60, classes=5):
    """E_0 = sign sequence / 2 on 2d real rows; returned complex (d, classes)."""
    real = np.array([[declared_sign(0, i, j) * 0.5 for j in range(classes)] for i in range(2 * d)])
    return real[0::2] + 1j * real[1::2], real
