"""Ruler: the return on the clock of news against a plain drop, on made data.

A softmax reader over K symbols codes N places whose news is skewed as the line's fifths are
(most places near zero). The full deposit is G = sum_t J_t^T g_t with g_t = p_t - q_t. Two
partitions at a tolerance sigma are compared with it:
  drop:  sum over places with c_t >= sigma (the dark places' covectors released);
  clock: S_t = sum c_k, a place returned Delta_t = floor(S_t/sigma) - floor(S_(t-1)/sigma) times
         at weight w_t = sigma*Delta_t/c_t, the region's end closing the last stride at r/c.
News is held on an integer grain (2^-24 nats), so the identity sum w_t c_t = S_T is checked on
integers. Every check is an assert; the printed figures are readings.
"""
import numpy as np

GRAIN = 1 << 24
rng = np.random.default_rng(20261115)
K, D = 16, 12


def region(n, temp, W):
    # a reader whose logits are sharpened by `temp` against the law that writes the symbols
    X = rng.normal(size=(n, D)) * rng.choice([0.4, 3.0], size=(n, 1), p=[0.4, 0.6])
    logits = X @ W.T
    pt = np.exp(logits - logits.max(1, keepdims=True)); pt /= pt.sum(1, keepdims=True)
    u = np.array([rng.choice(K, p=row) for row in pt])          # written by the true law
    pl = np.exp(temp * (logits - logits.max(1, keepdims=True))); pl /= pl.sum(1, keepdims=True)
    q = np.eye(K)[u]
    g = pl - q
    rest = pl.sum(1) - pl[np.arange(n), u]           # 1 - p(u), summed from the other symbols
    rest = np.array([np.delete(pl[t], u[t]).sum() for t in range(n)])
    g[np.arange(n), u] = -rest                       # the written symbol's entry without cancellation
    c = -np.log1p(-rest)
    J = X  # the covector reaches W through x: dW = g x^T
    return g, c, J


def deposit(g, J, w):
    return (g * w[:, None]).T @ J


def clock(c_int, sigma_int):
    S = np.cumsum(c_int)
    prev = np.concatenate([[0], S[:-1]])
    delta = S // sigma_int - prev // sigma_int
    r = S[-1] - (S[-1] // sigma_int) * sigma_int
    return S, delta, r


out = []
for temp in (1.0, 1.3, 0.8):
    for sig_bits in (1 / 16, 1 / 4):
        sigma = sig_bits * np.log(2)
        one_d, one_c, acc_d, acc_c, shares, shares_drop = [], [], [], [], [], []
        for reader in range(10):
            W = rng.normal(size=(K, D))
            F = Dr = C = 0
            for _ in range(40):
                n = 2000
                g, c, J = region(n, temp, W)
                c_int = np.maximum(np.rint(c * GRAIN).astype(np.int64), 1)
                s_int = int(round(sigma * GRAIN))
                S, delta, r = clock(c_int, s_int)
                w_num = s_int * delta
                last = n - 1
                w_num = w_num.copy(); w_num[last] += r            # the region's end closes the last stride
                assert int(w_num.sum()) == int(S[-1])             # sum w_t c_t = S_T, on integers
                w = w_num / c_int
                assert np.all(np.abs(g).sum(1) <= 2 * c * (1 + 1e-9))   # ||g||_1 <= 2c
                assert np.all(np.abs(g * w[:, None]).sum(1) <= 2 * w * c * (1 + 1e-9))
                returned = int((w_num > 0).sum())
                bright = int((c_int >= s_int).sum())
                assert bright <= returned <= S[-1] // s_int + 1   # every bright place, at most one return a section and the end
                full = deposit(g, J, np.ones(n))
                dropw = (c_int >= s_int).astype(float)
                dd, dc = deposit(g, J, dropw), deposit(g, J, w)
                one_d.append(np.linalg.norm(dd - full) / np.linalg.norm(full))
                one_c.append(np.linalg.norm(dc - full) / np.linalg.norm(full))
                F, Dr, C = F + full, Dr + dd, C + dc
                shares.append(returned / n); shares_drop.append(dropw.mean())
            acc_d.append(np.linalg.norm(Dr - F) / np.linalg.norm(F))
            acc_c.append(np.linalg.norm(C - F) / np.linalg.norm(F))
        out.append((temp, sig_bits, np.median(shares), np.median(shares_drop), np.median(one_c), np.median(one_d),
                    np.median(acc_c), np.median(acc_d), np.mean(np.array(acc_c) < np.array(acc_d))))

print("reader  sigma  returned      one region's error   40 regions summed     summed: clock<drop")
print("temp    bits   clock  drop   clock    drop        clock    drop")
for row in out:
    print("%.1f     %-5s  %.3f  %.3f  %.4f   %.4f      %.4f   %.4f      %.1f" % (row[0], row[1], *row[2:]))
