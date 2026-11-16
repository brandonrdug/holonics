#include <stdint.h>
#include <stdio.h>
typedef unsigned __int128 u128;
static uint64_t umulh(uint64_t a, uint64_t b) { return (uint64_t)(((u128)a * b) >> 64); }
static uint64_t ref(uint64_t d) { return (uint64_t)((((u128)(~d)) << 64 | (u128)UINT64_MAX) / (u128)d); }
static uint64_t recip(uint64_t d) {
    const uint64_t d0 = d & 1, d9 = d >> 55, d40 = (d >> 24) + 1, d63 = (d >> 1) + d0;
    const uint64_t v0 = (uint32_t)((((uint32_t)1 << 19) - 3 * ((uint32_t)1 << 8)) / (uint32_t)d9);
    const uint64_t v1 = (v0 << 11) - ((v0 * v0 * d40) >> 40) - 1;
    const uint64_t v2 = (v1 << 13) + ((v1 * (((uint64_t)1 << 60) - v1 * d40)) >> 47);
    const uint64_t e = ((v2 >> 1) & (0 - d0)) - v2 * d63;
    const uint64_t v3 = (umulh(v2, e) >> 1) + (v2 << 31);
    const u128 p = (u128)v3 * d + d;
    return v3 - (uint64_t)(p >> 64) - d;
}
static uint64_t rs = 88172645463325252ull;
static uint64_t xr(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
int main(void) {
    uint64_t bad = 0, n = 0;
    uint64_t edges[] = {1ull << 63, ~0ull, (1ull << 63) + 1, ~0ull - 1};
    for (int i = 0; i < 4; i++) { n++; if (recip(edges[i]) != ref(edges[i])) { bad++; printf("edge %llx\n", (unsigned long long)edges[i]); } }
    for (uint64_t k = 1; k < (1ull << 24); k++) {
        const uint64_t d = k << __builtin_clzll(k); n++;
        if (recip(d) != ref(d)) { if (bad < 5) printf("k %llu\n", (unsigned long long)k); bad++; }
        const uint64_t k2 = k * k, d2 = k2 << __builtin_clzll(k2); n++;
        if (recip(d2) != ref(d2)) { if (bad < 5) printf("k2 %llu\n", (unsigned long long)k); bad++; }
    }
    for (uint64_t t = 0; t < 50000000ull; t++) { const uint64_t d = xr() | (1ull << 63); n++; if (recip(d) != ref(d)) { if (bad < 5) printf("r %llx\n", (unsigned long long)d); bad++; } }
    printf("checked=%llu unequal=%llu\n", (unsigned long long)n, (unsigned long long)bad);
    return bad != 0;
}
