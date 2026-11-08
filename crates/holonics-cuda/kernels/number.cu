// **The number header's parity kernels** (step 2 of the number record's build order): each operation of `number.cuh` on
// arrays of cases, one thread a case (one warp a case for the warp's add), for the host owner's parity
// (`crates/holonics-cuda/tests/number_parity.rs`).

#include "number.cuh"

// Each case's words: a and b (L limbs each); out: sum (L) and its carry, difference (L) and its borrow, the signed sum's
// winding, the unsigned product (2L), the signed product (2L), the release of k places' quotient and remainder (L each),
// the bottom inverse of (a | 1) (L) and its steps: 9L + 4 words a case.
template <int L>
__device__ void hn_parity_case(const uint32_t* a_in, const uint32_t* b_in, int k, uint32_t* out) {
    hn_word<L> a, b, s, d, q, r, x;
    hn_word<2 * L> p, ps;
#pragma unroll
    for (int i = 0; i < L; ++i) {
        a.w[i] = a_in[i];
        b.w[i] = b_in[i];
    }
    const uint32_t carry = hn_add<L>(s, a, b);
    const int winding = hn_signed_winding<L>(a, b, s);
    const uint32_t borrow = hn_sub<L>(d, a, b);
    hn_mul<L>(p, a, b);
    hn_mul_signed<L>(ps, a, b);
    hn_release_nearest<L>(q, r, a, k);
    hn_word<L> odd = a;
    odd.w[0] |= 1u;
    const int steps = hn_invert_bottom<L>(x, odd);
    int o = 0;
    for (int i = 0; i < L; ++i) out[o++] = s.w[i];
    out[o++] = carry;
    for (int i = 0; i < L; ++i) out[o++] = d.w[i];
    out[o++] = borrow;
    out[o++] = (uint32_t)winding;
    for (int i = 0; i < 2 * L; ++i) out[o++] = p.w[i];
    for (int i = 0; i < 2 * L; ++i) out[o++] = ps.w[i];
    for (int i = 0; i < L; ++i) out[o++] = q.w[i];
    for (int i = 0; i < L; ++i) out[o++] = r.w[i];
    for (int i = 0; i < L; ++i) out[o++] = x.w[i];
    out[o++] = (uint32_t)steps;
}

#define HN_PARITY(L)                                                                                                  \
    extern "C" __global__ void hn_parity_##L(const uint32_t* a, const uint32_t* b, const int* k, int n, uint32_t* out) { \
        const int c = blockIdx.x * blockDim.x + threadIdx.x;                                                          \
        if (c < n) hn_parity_case<L>(a + c * L, b + c * L, k[c], out + c * (9 * L + 4));                               \
    }

HN_PARITY(1)
HN_PARITY(2)
HN_PARITY(4)
HN_PARITY(8)

// The cut add on packed words, one thread a case.
extern "C" __global__ void hn_parity_cut(const uint32_t* x, const uint32_t* y, const uint32_t* h, int n, uint32_t* out) {
    const int c = blockIdx.x * blockDim.x + threadIdx.x;
    if (c < n) out[c] = hn_cut_add(x[c], y[c], h[c]);
}

// The warp's add of 1,024-place words, one warp a case: out holds each case's 32 limbs and its winding.
extern "C" __global__ void hn_parity_warp(const uint32_t* a, const uint32_t* b, int n, uint32_t* out) {
    const int c = (blockIdx.x * blockDim.x + threadIdx.x) >> 5;
    const int lane = threadIdx.x & 31;
    if (c >= n) return;
    uint32_t winding = 0;
    const uint32_t limb = hn_warp_add(a[c * 32 + lane], b[c * 32 + lane], winding);
    out[c * 33 + lane] = limb;
    if (lane == 0) out[c * 33 + 32] = winding;
}
