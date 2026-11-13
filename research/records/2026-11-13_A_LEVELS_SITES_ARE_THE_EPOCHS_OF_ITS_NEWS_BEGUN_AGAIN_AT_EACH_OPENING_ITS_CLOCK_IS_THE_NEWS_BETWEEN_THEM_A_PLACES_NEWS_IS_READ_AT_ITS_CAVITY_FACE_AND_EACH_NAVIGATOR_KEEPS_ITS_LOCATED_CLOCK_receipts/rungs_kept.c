/* rungs: the octave ladder's fading sums of a signed 16-bit stream, integer shifts only (a host instrument for band_ruler.py).
   y_0 is the sample; rung s keeps its sum a_s on 2^-s, a_s gaining x - (a_s >> s) at each sample, and y_s = a_s >> s, s = 1..RUNGS. Band s = y_s - y_(s+1), written every 2^s samples
   (the samples whose index is a multiple of 2^s), s = 0..RUNGS-1, as signed 32-bit little-endian, one file a band.
   usage: rungs IN.raw OUT_PREFIX */
#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#define RUNGS 7
int main(int argc, char **argv) {
    if (argc != 3) return 2;
    FILE *in = fopen(argv[1], "rb");
    if (!in) return 1;
    FILE *out[RUNGS];
    char name[4096];
    for (int s = 0; s < RUNGS; s++) {
        snprintf(name, sizeof name, "%s.b%d", argv[2], s);
        out[s] = fopen(name, "wb");
        if (!out[s]) return 1;
    }
    int64_t y[RUNGS + 1] = {0}, acc[RUNGS + 1] = {0};
    int16_t x;
    uint64_t t = 0;
    while (fread(&x, sizeof x, 1, in) == 1) {
        y[0] = x;
        for (int s = 1; s <= RUNGS; s++) { acc[s] += x - (acc[s] >> s); y[s] = acc[s] >> s; }   /* the sum kept on 2^-s: no remainder dropped */
        for (int s = 0; s < RUNGS; s++)
            if ((t & ((1ull << s) - 1)) == 0) {
                int32_t b = (int32_t)(y[s] - y[s + 1]);
                fwrite(&b, sizeof b, 1, out[s]);
            }
        t++;
    }
    return 0;
}
