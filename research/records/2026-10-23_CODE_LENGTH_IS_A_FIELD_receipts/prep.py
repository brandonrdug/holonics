# Regions of the rendered training passage ("question\nanswer\n\n" per problem) and the primes' signs.
# usage: python3 -I prep.py TRAIN_JSONL PARTITION_JSON PASSAGE OUTDIR NMAX
# Writes OUTDIR/{roles.u8, fine.u8, prob.u32, Q.bin, P.bin, N.bin, M.bin, mu.bin, lam.bin}.
# Coarse regions (every byte in one): 0 Q question (with its newline), 1 P answer text outside the
# calculations except digits (with the closing blank line), 2 N answer digits outside the calculations,
# 3 M calculation markup <<...>>. Fine roles as in classify_partition.py.
import json, re, sys, numpy as np
rows = [json.loads(l) for l in open(sys.argv[1], encoding="utf-8")]
idx = json.load(open(sys.argv[2]))["train_indices"]
passage = open(sys.argv[3], "rb").read()
out, nmax = sys.argv[4], int(sys.argv[5])
FINE = ["question prose", "question digit", "separator", "answer prose", "answer digit (prose)",
        "calc markup", "calc operand digit", "calc result digit", "digit after >> (repeat of result)",
        "#### marker", "final answer digit"]
F = {k: i for i, k in enumerate(FINE)}
buf, coarse, fine, prob = bytearray(), [], [], []
for pi, ri in enumerate(idx):
    r = rows[ri]
    q, a = r["question"].encode(), r["answer"].encode()
    buf += q + b"\n" + a + b"\n\n"
    coarse += [0] * (len(q) + 1)
    fine += [F["question digit"] if 48 <= c <= 57 else F["question prose"] for c in q] + [F["separator"]]
    ac = [2 if 48 <= c <= 57 else 1 for c in a]
    af = [F["answer digit (prose)"] if 48 <= c <= 57 else F["answer prose"] for c in a]
    for m in re.finditer(rb"<<([^=>]*)=([^>]*)>>", a):
        for i in range(m.start(), m.end()): ac[i] = 3; af[i] = F["calc markup"]
        for i in range(m.start(1), m.end(1)):
            if 48 <= a[i] <= 57: af[i] = F["calc operand digit"]
        for i in range(m.start(2), m.end(2)):
            if 48 <= a[i] <= 57: af[i] = F["calc result digit"]
        j = m.end()
        while j < len(a) and (48 <= a[j] <= 57 or a[j] in b".,"):
            if 48 <= a[j] <= 57: af[j] = F["digit after >> (repeat of result)"]
            j += 1
    h = a.rfind(b"#### ")
    if h >= 0:
        for i in range(h, h + 5): af[i] = F["#### marker"]
        for i in range(h + 5, len(a)):
            if 48 <= a[i] <= 57: af[i] = F["final answer digit"]
    coarse += ac + [1, 1]
    fine += af + [F["separator"], F["separator"]]
    prob += [pi] * (len(q) + 1 + len(a) + 2)
assert bytes(buf) == passage, "rendering differs from the passage"
coarse, fine, prob = np.array(coarse, np.uint8), np.array(fine, np.uint8), np.array(prob, np.uint32)
coarse.tofile(out + "/roles.u8"); fine.tofile(out + "/fine.u8"); prob.tofile(out + "/prob.u32")
pb = np.frombuffer(passage, np.uint8)
for k, name in enumerate("QPNM"):
    pb[coarse == k].tofile(out + "/%s.bin" % name)
    print(name, int((coarse == k).sum()), "bytes")
# Moebius and Liouville by sieve over n = 1..nmax
mu = np.ones(nmax + 1, np.int8); lam = np.ones(nmax + 1, np.int8)
isp = np.ones(nmax + 1, bool); isp[:2] = False
for p in range(2, int(nmax ** 0.5) + 1):
    if isp[p]: isp[p * p::p] = False
primes = np.nonzero(isp)[0]
omega_big = np.zeros(nmax + 1, np.int8)  # Omega(n) mod 2 by prime powers
for p in primes:
    mu[p::p] *= -1
    mu[p * p::p * p] = 0
    pk = p
    while pk <= nmax:
        omega_big[pk::pk] ^= 1
        pk *= p
lam = np.where(omega_big == 1, -1, 1).astype(np.int8)
mu, lam = mu[1:], lam[1:]
(mu + 1).astype(np.uint8).tofile(out + "/mu.bin")
((lam + 1) // 2).astype(np.uint8).tofile(out + "/lam.bin")
print("n <=", nmax, "M =", int(mu.astype(np.int64).sum()), "L =", int(lam.astype(np.int64).sum()), "squarefree", int((mu != 0).sum()))
