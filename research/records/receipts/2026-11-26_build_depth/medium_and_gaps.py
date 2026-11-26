#!/usr/bin/env -S python3 -I
"""Arithmetic beside the build-depth record: a medium's speed of sound from its contents, a free reed's note from its two cuts,
the gaps two coprime periods leave, and the least joins that reach a count. A host ruler on public constants; it holds no law.

    medium_and_gaps.py
"""
import math

R, T = 8.314462618, 293.15  # J/(mol K), 20 C
GASES = {"air": (1.400, 0.028964), "carbon dioxide": (1.289, 0.044010), "helium": (1.667, 0.0040026)}


def cents(ratio):
    return 1200 * math.log2(ratio)


def chain_length(n, limit=12):
    """The least count of additions that reaches n from 1 with every sum kept (an addition chain), by search to `limit`."""
    best = [None]

    def go(chain, depth):
        if chain[-1] == n:
            best[0] = depth
            return True
        if depth == bound or chain[-1] << (bound - depth) < n:
            return False
        for i in range(len(chain) - 1, -1, -1):
            for j in range(i, -1, -1):
                s = chain[i] + chain[j]
                if chain[-1] < s <= n and go(chain + [s], depth + 1):
                    return True
        return False

    for bound in range(limit + 1):
        if go([1], 0):
            return best[0]
    return None


def main():
    c_air = math.sqrt(GASES["air"][0] * R * T / GASES["air"][1])
    for name, (gamma, molar) in GASES.items():
        c = math.sqrt(gamma * R * T / molar)
        print(f"MEDIUM gas={name!r} c={c:.1f} m/s tube_pitch_against_air={c / c_air:.3f} cents={cents(c / c_air):+.0f}")
    c_water, z_air, z_water = 1481.0, 1.204 * c_air, 998.0 * 1481.0
    t = 4 * z_air * z_water / (z_air + z_water) ** 2
    print(f"MEDIUM water c={c_water:.0f} m/s index_against_air={c_air / c_water:.3f} impedance_ratio={z_water / z_air:.0f} power_across_the_surface={t:.5f} ({10 * math.log10(t):.1f} dB)")
    e, rho = 100e9, 8500.0  # brass
    for h_mm, l_mm in ((0.20, 15.0), (0.20, 15.0 * math.sqrt(4 / 5)), (0.20, 15.0 * math.sqrt(4 / 6))):
        f = 0.16154 * (h_mm * 1e-3) / (l_mm * 1e-3) ** 2 * math.sqrt(e / rho)
        print(f"REED brass thickness={h_mm:.2f} mm length={l_mm:.2f} mm note={f:.0f} Hz")
    for a, b in ((3, 5), (4, 5), (5, 6), (2, 3)):
        reach = {a * i + b * j for i in range(b + 1) for j in range(a + 1)}
        gaps = [k for k in range(a * b) if k not in reach]
        print(f"GAPS periods={a},{b} count={len(gaps)} formula={(a - 1) * (b - 1) // 2} largest={max(gaps)} formula={a * b - a - b} gaps={gaps}")
    for n in (7, 15, 16, 23, 31, 32, 60, 64, 127):
        l = chain_length(n)
        print(f"JOINS count={n} least={l} floor={math.ceil(math.log2(n))} binary={n.bit_length() - 1 + bin(n).count('1') - 1}")


if __name__ == "__main__":
    main()
