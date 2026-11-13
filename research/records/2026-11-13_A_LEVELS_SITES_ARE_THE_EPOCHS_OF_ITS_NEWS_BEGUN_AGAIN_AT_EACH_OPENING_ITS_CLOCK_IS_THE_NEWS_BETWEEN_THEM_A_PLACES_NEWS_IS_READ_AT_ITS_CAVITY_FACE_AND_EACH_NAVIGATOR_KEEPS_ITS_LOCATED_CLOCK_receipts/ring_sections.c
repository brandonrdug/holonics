/* ring_sections: a ladder of driven rings read once a turn (a host instrument for ring_cut.py; doubles, a ruler's arithmetic,
   never the machine's). Ring s turns one whole turn in 2^s samples and keeps 1 - 2^-(s + REACH) of its state a sample, so its reach
   is 2^REACH of its turns (REACH = 0: one turn; 2: four turns):
       z_n = (1 - 2^-(s + REACH)) e^(2 pi i / 2^s) z_(n-1) + x_n,   z = (w, u), free motion counterclockwise,
   the phase-carried moment of its drive (atlas navigator.source-moment, hnn.ring-moment-keys). Its lift is the dynamic section's
   (crates/holonics/src/hnn/dynamic_section.rs): the class of a point is its quadrant, a ray belonging to the class it starts, and
   between consecutive states the lift advances by the rays the straight chord passes, signed; a chord through the origin advances
   nothing and is counted. A place of ring s is one turn of it, 2^s samples (the samples whose index is a multiple of 2^s): at each the
   ring's octave (0 under one unit, else the bit length of the whole part of |z|) and its lift are written as two signed 32-bit
   little-endian words, s = FIRST..LAST, one file a ring. A free ring's lift advances 4 a place.
   usage: ring_sections IN.raw OUT_PREFIX REACH */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#define FIRST 2
#define LAST 7
static int cls(double w, double u) {
    if (w > 0 && u >= 0) return 0;
    if (w <= 0 && u > 0) return 1;
    if (w < 0 && u <= 0) return 2;
    if (w >= 0 && u < 0) return 3;
    return -1; /* the origin has no class */
}
int main(int argc, char **argv) {
    if (argc != 4) return 2;
    int reach = atoi(argv[3]);
    FILE *in = fopen(argv[1], "rb");
    if (!in) return 1;
    FILE *out[LAST + 1];
    char name[4096];
    double c[LAST + 1], d[LAST + 1], w[LAST + 1] = {0}, u[LAST + 1] = {0};
    int32_t lift[LAST + 1] = {0};
    long refused[LAST + 1] = {0};
    for (int s = FIRST; s <= LAST; s++) {
        snprintf(name, sizeof name, "%s.r%d", argv[2], s);
        out[s] = fopen(name, "wb");
        if (!out[s]) return 1;
        double rho = 1.0 - ldexp(1.0, -(s + reach)), th = 2.0 * M_PI / (double)(1 << s);
        c[s] = rho * cos(th);
        d[s] = rho * sin(th);
    }
    int16_t x;
    uint64_t t = 0;
    while (fread(&x, sizeof x, 1, in) == 1) {
        for (int s = FIRST; s <= LAST; s++) {
            double pw = w[s], pu = u[s];
            double qw = c[s] * pw - d[s] * pu + (double)x, qu = d[s] * pw + c[s] * pu;
            int a = cls(pw, pu), b = cls(qw, qu);
            if (a >= 0 && b >= 0) {
                double cross = pw * qu - pu * qw;
                if (cross > 0) lift[s] += (b - a + 4) % 4;
                else if (cross < 0) lift[s] -= (a - b + 4) % 4;
                else if (pw * qw + pu * qu < 0) refused[s]++;
            }
            w[s] = qw;
            u[s] = qu;
            if ((t & ((1ull << s) - 1)) == 0) {
                double m = hypot(qw, qu);
                int32_t rec[2];
                rec[0] = m < 1.0 ? 0 : (int32_t)ilogb(m) + 1;
                rec[1] = lift[s];
                fwrite(rec, sizeof rec, 1, out[s]);
            }
        }
        t++;
    }
    for (int s = FIRST; s <= LAST; s++) if (refused[s]) fprintf(stderr, "ring %d refused %ld\n", s, refused[s]);
    return 0;
}
