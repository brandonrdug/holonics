"""A ruler for the pair amplitude of arXiv:2611.34924 (4.32)-(4.34), read on the host.

The connected overlap of a graviton pair made and taken back on one null cone is
    sum_k 2 (dq_k)^4 e^(-2ik/s),   (dq_k)^2 = 1/(2 s k),
that is sum_k e^(-2ik/s) / (2 s^2 k^2) = Li_2(e^(-2i/s)) / (2 s^2).
Summed with its turn: Re = (pi^2/6 - pi theta/2 + theta^2/4)/(2 s^2) at theta = 2/s (a Bernoulli
polynomial of the residue, 0 <= theta <= 2 pi), Im = -Cl_2(theta)/(2 s^2) ~ -(1 + ln(s/2))/s^3.
Expanded in 1/s first, the cubic term is -(i/s^3) sum_k 1/k, which grows as ln N without end.
Floats are a ruler's here; nothing of the machine reads them.
"""
import math

def clausen2(theta, n):
    return sum(math.sin(k * theta) / (k * k) for k in range(1, n + 1))

def main():
    n_modes = 2_000_000
    print("s  Re*2s^2(sum)  Bernoulli  Im*s^3(sum)  -(1+ln(s/2))  expanded-first Im*s^3 at N=2e5, 2e6")
    h_small = sum(1.0 / k for k in range(1, 200_001))
    h_large = h_small + sum(1.0 / k for k in range(200_001, n_modes + 1))
    for s in (10, 100, 1000):
        theta = 2.0 / s
        re_sum = sum(math.cos(k * theta) / (k * k) for k in range(1, n_modes + 1))
        bern = math.pi ** 2 / 6 - math.pi * theta / 2 + theta * theta / 4
        im_s3 = -clausen2(theta, n_modes) * s / 2
        pred = -(1 + math.log(s / 2))
        print(f"{s} {re_sum:.6f} {bern:.6f} {im_s3:.4f} {pred:.4f} {-h_small:.3f} {-h_large:.3f}")

if __name__ == "__main__":
    main()
