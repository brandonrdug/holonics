/* ring_arrivals: a ladder of driven rings read at every sample, each ring's places its own section arrivals (a host instrument for
   arrival_cut.py; doubles, a ruler's arithmetic, never the machine's). Ring s is ring_sections.c's:
       z_n = (1 - 2^-(s + REACH)) e^(2 pi i / 2^s) z_(n-1) + x_n,   z = (w, u), free motion counterclockwise,
   and its lift is the dynamic section's (crates/holonics/src/hnn/dynamic_section.rs), begun at the class of the first state off the
   origin, so the section is the ray u = 0, w > 0 under any start. An arrival is a sample at which the whole
   winding floor(lift / 4) passes its largest value so far (the state crossing the ray u = 0, w > 0 upward for the first time at that
   winding; a crossing back and its return are not arrivals). At an arrival four words are written, little-endian: the time of the
   crossing in samples and |z| at the crossing (the step from the sample before taken as a straight line of log z, which a free ring's
   is, and cut where it meets the ray), as 64-bit floats, then
   the count of crossings back since the last arrival and a zero, as signed 32-bit words. s = FIRST..LAST, one file a ring.
   usage: ring_arrivals IN.raw OUT_PREFIX REACH */
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
static long fdiv4(long l) { return l >= 0 ? l / 4 : -((-l + 3) / 4); }
int main(int argc, char **argv) {
    if (argc != 4) return 2;
    int reach = atoi(argv[3]);
    FILE *in = fopen(argv[1], "rb");
    if (!in) return 1;
    FILE *out[LAST + 1];
    char name[4096];
    double c[LAST + 1], d[LAST + 1], w[LAST + 1] = {0}, u[LAST + 1] = {0};
    long lift[LAST + 1] = {0}, top[LAST + 1] = {0};
    int32_t back[LAST + 1] = {0};
    for (int s = FIRST; s <= LAST; s++) {
        snprintf(name, sizeof name, "%s.a%d", argv[2], s);
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
            long before = fdiv4(lift[s]);
            if (a < 0 && b >= 0) {
                lift[s] = b; /* the lift begins at the first state's class, so the lift and the class agree in every quarter */
            } else if (a >= 0 && b >= 0) {
                double cross = pw * qu - pu * qw;
                if (cross > 0) lift[s] += (b - a + 4) % 4;
                else if (cross < 0) lift[s] -= (a - b + 4) % 4;
            }
            long after = fdiv4(lift[s]);
            if (after < before) back[s]++;
            if (after > top[s]) {
                /* the chord in the logarithmic chart: the step turns by del and scales evenly in the turn; the ray stands at -ap of it */
                double ap = atan2(pu, pw), del = atan2(pw * qu - pu * qw, pw * qw + pu * qu);
                double f = del > 0 ? -ap / del : 0.5;
                if (f < 0) f = 0;
                if (f > 1) f = 1;
                double when = (double)t - 1.0 + f, m = exp((1.0 - f) * log(hypot(pw, pu)) + f * log(hypot(qw, qu)));
                int32_t rec[2];
                rec[0] = back[s];
                rec[1] = 0;
                fwrite(&when, sizeof when, 1, out[s]);
                fwrite(&m, sizeof m, 1, out[s]);
                fwrite(rec, sizeof rec, 1, out[s]);
                top[s] = after;
                back[s] = 0;
            }
            w[s] = qw;
            u[s] = qu;
        }
        t++;
    }
    return 0;
}
