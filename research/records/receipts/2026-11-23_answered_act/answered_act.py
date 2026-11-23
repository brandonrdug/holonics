#!/usr/bin/env python3
"""A host ruler for the record of November 23 on an act answered in kind. Standard library only, one fixed seed, no state of the line.

  A  an unanswered act: the least code of a target that does not depend on the act, at a reader holding the act as context
  B  a reader that cannot tell a draft from the passage: what the passage's places pay, by the drafts' share
  C  a probe reads its loop and a slope (the identities of Lean `HNN/AnsweredAct`, on drawn numbers)
  D  one propagation at every quality: a medium's turn and fade from its quality, the sea for sound and for a slow electric
     field (a diffusion's wavelength, phase speed and front), and a fluid's shear beside its compression
  E  a boundary's ports: a star's spokes from three ports, two ports and one number, the count n(n-1)/2
  F  a follower and a carried period on a beat that changes its tempo
  G  a turn handed along a line of members that each carry it: one law at two frictions, a train and a diffusion

Every number of part D that is a constant of a medium is from the literature (from training) and is named where it is used.
"""
import math
import random

rng = random.Random(20261123)


def dist(n):
    v = [rng.random() ** 3 + 1e-3 for _ in range(n)]
    s = sum(v)
    return [x / s for x in v]


def ent(p):
    return -sum(x * math.log(x) for x in p if x > 0)


def part_a_b():
    C, R, X = 3, 5, 6
    D = R
    mu = dist(C)
    rho = [dist(R) for _ in range(C)]            # the passage's hidden continuation, from the context
    pi = [dist(D) for _ in range(C)]             # the reader's own act, from the context
    q = [[dist(X) for _ in range(R)] for _ in range(C)]   # the target, from the context and the hidden continuation
    qbar = [[sum(rho[c][r] * q[c][r][x] for r in range(R)) for x in range(X)] for c in range(C)]

    worst = 0.0
    for c in range(C):
        for d in range(D):
            num = [sum(mu[c] * pi[c][d] * rho[c][r] * q[c][r][x] for r in range(R)) for x in range(X)]
            z = sum(num)
            worst = max(worst, max(abs(num[x] / z - qbar[c][x]) for x in range(X)))
    h_blind = sum(mu[c] * ent(qbar[c]) for c in range(C))
    h_seen = sum(mu[c] * rho[c][r] * ent(q[c][r]) for c in range(C) for r in range(R))
    h_act = sum(mu[c] * ent(pi[c]) for c in range(C))
    print("A  an unanswered act (contexts 3, hidden continuations 5, targets 6, acts 5; laws drawn)")
    print(f"   the target's law given the context and the act, against its law given the context alone: largest difference {worst:.1e}")
    print(f"   least code with the hidden continuation shown {h_seen:.4f} nats; with the act shown in its place {h_blind:.4f}; the difference {h_blind - h_seen:.4f} = I(target; continuation | context)")
    print(f"   news of the act in the target: 0.0000 nats. An answer that is a one-to-one function of the act holds all of it: {h_act:.4f} nats (the act's own entropy)")
    print()
    print("B  one reader for the passage and for drafts it cannot tell from the passage: what a passage place pays, by the drafts' share")
    print("   share     nats a passage place     over share      over share squared")
    for lam in (0.0037, 0.0142, 0.06, 0.236, 0.5):
        cost = 0.0
        for c in range(C):
            for s in range(R):
                wp, wd = (1 - lam) * rho[c][s], lam * pi[c][s]
                p = [(wp * q[c][s][x] + wd * qbar[c][x]) / (wp + wd) for x in range(X)]
                cost += mu[c] * rho[c][s] * sum(q[c][s][x] * math.log(q[c][s][x] / p[x]) for x in range(X))
        print(f"   {lam:6.4f}    {cost:12.6f}            {cost / lam:8.4f}        {cost / lam ** 2:8.3f}")
    print("   the cost is never negative and zero only at no drafts; across this range it stands near first order in the share, because a draft")
    print("   stands where the passage seldom does and the drafts' comparison takes those states over (second order only under the share at which")
    print("   a state's drafts outnumber its passages)")
    print("   the lead's two reads on the theory's held code: +0.0112 and +0.0442 nats a place at 92 and 354 drafted places a section (ratio 3.95 at 3.85 times the dose)")
    print()


def part_c():
    eps, loop = 0.25, 0.37
    print("C  a probe reads its loop (a world of memory 0.97 and spread 4.1, a balanced probe of size 0.25, a loop of gain 0.37)")
    for n in (4096, 65536, 1048576):
        w, x = [], 0.0
        for _ in range(n):
            x = 0.97 * x + rng.gauss(0, 1)
            w.append(x)
        signs = [1] * (n // 2) + [-1] * (n // 2)
        rng.shuffle(signs)
        a = [eps * s for s in signs]
        r = [w[t] + loop * a[t] for t in range(n)]
        saa = sum(v * v for v in a)
        swa = sum(w[t] * a[t] for t in range(n))
        est = sum(r[t] * a[t] for t in range(n)) / saa
        print(f"   {n:8d} ticks: the reading demodulated against the probe {est:.4f}; its whole error is the world's correlation with the probe, {swa / saa:+.4f} (spread 4.1/(0.25 sqrt n) = {4.1 / (eps * math.sqrt(n)):.4f})")
    print(f"   at the last dwell the reading's power {sum(v * v for v in r):.1f} = the world's {sum(v * v for v in w):.1f} + the loop's {loop * loop * saa:.1f} + the cross term {2 * loop * swa:+.1f}")
    f0, g, h, u = 3.0, -0.8, 0.5, 0.2
    probe = [0.05, -0.05] * 32
    f = lambda v: f0 + g * v + h * v * v
    mean = sum(f(u + p) for p in probe) / len(probe)
    slope = sum(f(u + p) * p for p in probe) / sum(p * p for p in probe)
    print(f"   a response 3 - 0.8u + 0.5u^2 at u = 0.2 under a probe of +-0.05: the mean moves by {mean - f(u):+.6f} (the curvature times the probe's power, {h * 0.05 ** 2:.6f})")
    print(f"   demodulated against the probe it returns {slope:+.4f}, the slope there ({g + 2 * h * u:+.4f})")
    print()


def fade(qual):
    t = -qual + math.sqrt(qual * qual + 1)       # t/(1 - t^2) = 1/(2Q)
    return t, math.exp(-2 * math.pi * t), 0.5 * math.degrees(math.atan2(1.0, qual))


def thorp(f_khz):
    f2 = f_khz * f_khz
    return 0.11 * f2 / (1 + f2) + 44 * f2 / (4100 + f2) + 2.75e-4 * f2 + 0.003   # dB a km (Thorp 1967)


def part_d():
    print("D  one propagation at every quality: k = a + ib turns at a and fades at b; t = b/a, t/(1 - t^2) = 1/(2Q)")
    print("   Q is the reader's clock over the medium's relaxation (omega tau); the wavenumber's angle is half the loss angle,")
    print("   and the medium at that clock is a diffusion whose diffusivity stands at the angle arctan Q")
    print("   quality Q      t            kept over one wavelength     angle of k (degrees)     angle of the diffusivity (degrees)")
    for qual in (1e-9, 0.1, 1.0, 10.0, 1e3, 1e7):
        t, kept, ang = fade(qual)
        print(f"   {qual:8.1e}     {t:.6f}     {kept:.6f}                     {ang:7.4f}                  {math.degrees(math.atan(qual)):10.6f}")
    print(f"   the slow end: t = 1, e^(-2 pi) = {math.exp(-2 * math.pi):.6f} of the amplitude a wavelength, 45 degrees; it still turns once in every wavelength")
    print()
    c_air, rho_air, c_sea, rho_sea = 343.0, 1.2, 1500.0, 1025.0
    z1, z2 = rho_air * c_air, rho_sea * c_sea
    tr = 4 * z1 * z2 / (z1 + z2) ** 2
    print("   sound: air 343 m/s and 1.2 kg/m^3, sea 1,500 m/s and 1,025 kg/m^3")
    print(f"   power handed across a flat face between them: {tr:.5f} ({10 * math.log10(tr):.1f} dB); a tone keeps its frequency and its wavelength grows {c_sea / c_air:.2f} times")
    print(f"   a bubble's own tone (Minnaert 1933) at the surface: {3.26 / 1e-3:.0f} Hz at 1 mm radius, {3.26 / 5e-3:.0f} Hz at 5 mm")
    print("   frequency      wavelength     absorbed (dB a km)     km to lose 20 dB to absorption     Q            wavelengths to 1/e")
    for f in (20.0, 100.0, 1e3, 1e4, 1e5):
        al_db = thorp(f / 1e3)
        al_np = al_db / 8.686 / 1e3
        lam = c_sea / f
        qual = math.pi * f / (c_sea * al_np)
        print(f"   {f:9.0f} Hz   {lam:9.3f} m    {al_db:10.4f}             {20 / al_db:12.1f}                    {qual:9.2e}    {qual / math.pi:10.2e}")
    print()
    nu_air, nu_sea = 1.5e-5, 1.0e-6
    print("   the same fluid's shear (its vorticity) at the same clocks: k^2 = i omega/nu, 45 degrees, depth sqrt(2 nu/omega) (Stokes 1851)")
    print("   frequency      depth in air (nu 1.5e-5 m^2/s)     depth in the sea (nu 1.0e-6)     sound's wavelength in air, in the sea")
    for f in (1.0, 10.0, 100.0, 1e3):
        om = 2 * math.pi * f
        print(f"   {f:9.0f} Hz   {1e3 * math.sqrt(2 * nu_air / om):8.3f} mm                        {1e3 * math.sqrt(2 * nu_sea / om):8.3f} mm                      {c_air / f:9.3f} m, {c_sea / f:9.2f} m")
    print()
    sigma, eps = 4.0, 80 * 8.854e-12
    mu0 = 4e-7 * math.pi
    c_light = 2.998e8
    front = c_light / math.sqrt(80)
    print("   a slow electric field in the sea: conductivity 4 S/m, relative permittivity 80")
    print(f"   the store's relaxation eps/sigma = {eps / sigma:.2e} s; the reader's clock passes it (Q = 1) at {sigma / (2 * math.pi * eps) / 1e9:.2f} GHz")
    print(f"   the front's speed at every frequency, c/sqrt(80): {front:.3e} m/s")
    print("   frequency      depth delta     wavelength 2 pi delta     phase speed omega delta     Q = omega eps/sigma     kept over one wavelength")
    for f in (1.0, 10.0, 76.0, 1e3, 1e6):
        om = 2 * math.pi * f
        delta = math.sqrt(2 / (mu0 * sigma * om))
        qual = om * eps / sigma
        print(f"   {f:9.0f} Hz   {delta:9.3f} m     {2 * math.pi * delta:10.2f} m              {om * delta:12.1f} m/s           {qual:9.2e}               {fade(qual)[1]:.6f}")
    moment, thr = 8e-6 * 0.05, 5e-7
    reach = (moment / (2 * math.pi * sigma * thr)) ** (1 / 3)
    delta1 = math.sqrt(2 / (mu0 * sigma * 2 * math.pi))
    print(f"   a dipole of 8 microamperes over 5 cm against a threshold of 5 nV a cm (Kalmijn 1971, 1982): read on its axis to {reach:.2f} m")
    print(f"   over that distance the front passes in {reach / front * 1e9:.1f} ns and the current's pattern settles in about mu sigma r^2 = {mu0 * sigma * reach ** 2 * 1e6:.2f} microseconds")
    print(f"   a plane disturbance of 1 Hz has then turned r/delta = {reach / delta1 * 1e3:.2f} thousandths of a radian and faded by the same share: the reader stands inside its first turn,")
    print(f"   {reach / (2 * math.pi * delta1) * 1e3:.3f} thousandths of a wavelength from the source (a dipole's near terms cancel the first order and leave (r/delta)^2 = {(reach / delta1) ** 2:.1e} radians)")
    mob = 5.19e-8
    print(f"   the carriers at the threshold field: a sodium ion (mobility 5.19e-8 m^2/(V s)) drifts at {mob * thr:.1e} m/s, and the pattern of their motion crosses at the front's speed")
    print(f"   a body moving at 1 m/s across a field of 50 microtesla meets v B = {1.0 * 5e-5 * 1e9 / 100:.0f} nV a cm, {1.0 * 5e-5 / thr:.0f} times that threshold")
    print()


def part_e():
    n = 5
    g = [0.3 + rng.random() * 2 for _ in range(n)]
    s = sum(g)
    lam = [[(g[i] - g[i] * g[i] / s) if i == j else -g[i] * g[j] / s for j in range(n)] for i in range(n)]
    rec = lam[0][0] - lam[0][1] * lam[0][2] / lam[1][2]
    rows = max(abs(sum(row)) for row in lam)
    print("E  a boundary's ports")
    print(f"   a star of 5 spokes: its rows sum to {rows:.1e}; spoke 0 is {g[0]:.6f} and three ports read {rec:.6f}")
    print(f"   two spokes in series read at two ports: (1, 1) gives {1 * 1 / (1 + 1):.4f} and (3/4, 3/2) gives {0.75 * 1.5 / (0.75 + 1.5):.4f}")
    print("   ports n and the numbers a reciprocal boundary of n ports carries, n(n-1)/2: " + ", ".join(f"{k}: {k * (k - 1) // 2}" for k in (2, 3, 4, 8, 16)))
    print()


def part_f():
    alpha, beta = 0.5, 0.2
    print("F  a beat of period 1 that takes period 0.9 at beat 20 (phase gain 0.5; the carried period moves by 0.2 of the error)")
    for name, b in (("a follower, its own period 1", 0.0), ("a carried period", beta)):
        t_hat, p, e_log, beat = 0.0, 1.0, [], 0.0
        for k in range(80):
            e = beat - t_hat
            e_log.append(e)
            t_hat += p + alpha * e
            p += b * e
            beat += 1.0 if k < 19 else 0.9
        print(f"   {name}: error at beats 19, 25, 40, 79: {e_log[19]:+.4f}, {e_log[25]:+.4f}, {e_log[40]:+.4f}, {e_log[79]:+.4f}; its period at the end {p:.4f}")
    print(f"   the follower's standing error is the detuning over its gain, (0.9 - 1)/0.5 = {(0.9 - 1) / alpha:+.4f}")


def arrival(eta, dist, dt=0.05, chi=1.0, j=1.0):
    n = max(dist) + 48
    phi, vel = [0.0] * n, [0.0] * n
    phi[0] = 1.0
    left, out, t = sorted(dist), {}, 0.0
    while left:
        for i in range(1, n - 1):
            force = j * (phi[i - 1] - 2 * phi[i] + phi[i + 1])
            vel[i] = (vel[i] + dt * force / chi) / (1 + dt * eta / chi)
        vel[n - 1] = (vel[n - 1] + dt * j * (phi[n - 2] - phi[n - 1]) / chi) / (1 + dt * eta / chi)
        for i in range(1, n):
            phi[i] += dt * vel[i]
        t += dt
        while left and phi[left[0]] >= 0.5:
            out[left.pop(0)] = t
    return out


def part_g():
    print("G  a turn handed along a line of members: chi phi'' + eta phi' = J (phi[i-1] - 2 phi[i] + phi[i+1]), chi = J = 1, member 0 held turned")
    print("   the time at which member d has taken half the turn")
    dist = (2, 4, 8, 16)
    for eta, name in ((0.02, "each member keeps its turn for 50 hand-overs (eta 0.02)"), (20.0, "each member loses its turn inside a hand-over (eta 20)")):
        got = arrival(eta, dist)
        times = ", ".join(f"d = {d}: {got[d]:9.2f}" for d in dist)
        ratios = ", ".join(f"{got[dist[k + 1]] / got[dist[k]]:.2f}" for k in range(len(dist) - 1))
        print(f"   {name}: {times}; each doubling of the distance multiplies the time by {ratios}")
    print("   a mode of the contacts' eigenvalue lam travels where 4 chi J lam > eta^2 and settles without turning below it; a line of N members' coarsest")
    print(f"   mode has lam = (pi/N)^2: at eta 0.02 every mode travels in a line of fewer than {2 * math.pi / 0.02:.0f} members; at eta 20 the bound is lam > {20.0 ** 2 / 4:.0f},")
    print("   above the largest a line holds (4), and no mode travels: one law, read at two frictions")


if __name__ == "__main__":
    part_a_b()
    part_c()
    part_d()
    part_e()
    part_f()
    print()
    part_g()
