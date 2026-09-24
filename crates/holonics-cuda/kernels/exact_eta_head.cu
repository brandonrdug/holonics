// **The head of the eta jet, resident: `sum_(n<N) n^(-s)` and `-sum_(n<N) log(n) n^(-s)` at every
// boundary point of a receiver box at once, in exact fixed-point interval arithmetic.**
//
// Nothing here is a float. Every quantity is a signed 128-bit integer standing for a dyadic
// rational with ninety-six fractional bits, and every operation rounds its lower end down and its
// upper end up, so the pair `(lo, hi)` returned for each coordinate is a set that contains the
// true value — the same species of enclosure the serial owner in
// `relational_geometry::exact_analysis` returns, at the same grain, so the two can be intersected
// and neither can lie. The card is the apparatus; the law is the enclosure.
//
// Why the card, and why exactly this part. The Euler--Maclaurin start is derived from the height
// (the least `N` with certified remainder under the grain), which is `N ~ tau`; the head sum is
// then `O(N)` transcendental series per boundary point and there are dozens of boundary points per
// band. Measured 2026-08-27 on the CPU: ten milliseconds per `(point, term)` in `BigRational`, so a
// zero-free band at height two hundred is two minutes and a zero-bearing band at height sixty does
// not close under the process aperture. Every `(point, term)` is independent of every other, and
// the sum over terms is exact integer addition — commutative, so its order carries nothing. One
// lane per term, one block per point, a tree over the block.
//
// What stays on the CPU: the derived start, the tail at `N` (a single power), the Bernoulli
// corrections, the certified remainder disc, the `eta` factor `1 - 2^(1-s)`, the boundary
// certification law, and the winding. Those are `O(order)` per point and they are the semantics.
//
// Series, mirrored from the serial owner so the certificates agree:
//   exp(-x)   for x >= 0: halve until x <= 1/8, alternating series with the first omitted term as
//             the tail, square back;
//   sin, cos  at a point: halve until |c| <= 1/8, alternating series with the first omitted term
//             as the tail, double-angle back; then widen by the interval's radius, since both have
//             derivative of magnitude at most one.
// Logarithms of the integer bases are receiver-independent and arrive from the CPU as exact
// dyadic enclosures, computed once per start.

typedef __int128 i128;
typedef unsigned __int128 u128;

#define FRAC 96
#define BLOCK 128

struct Iv {
    i128 lo;
    i128 hi;
};

__device__ __forceinline__ i128 imin(i128 a, i128 b) { return a < b ? a : b; }
__device__ __forceinline__ i128 imax(i128 a, i128 b) { return a > b ? a : b; }
__device__ __forceinline__ i128 iabs(i128 a) { return a < 0 ? -a : a; }

// 128 x 128 -> 256, as four 64-bit limbs.
__device__ __forceinline__ void mul_u128(u128 a, u128 b, u128& hi, u128& lo) {
    unsigned long long a0 = (unsigned long long)a;
    unsigned long long a1 = (unsigned long long)(a >> 64);
    unsigned long long b0 = (unsigned long long)b;
    unsigned long long b1 = (unsigned long long)(b >> 64);
    u128 p00 = (u128)a0 * (u128)b0;
    u128 p01 = (u128)a0 * (u128)b1;
    u128 p10 = (u128)a1 * (u128)b0;
    u128 p11 = (u128)a1 * (u128)b1;
    u128 mid = (p00 >> 64) + (u128)(unsigned long long)p01 + (u128)(unsigned long long)p10;
    lo = (mid << 64) | (u128)(unsigned long long)p00;
    hi = p11 + (p01 >> 64) + (p10 >> 64) + (mid >> 64);
}

// |a·b| >> FRAC, with the dropped bits reported so the caller can round in a direction.
__device__ __forceinline__ u128 mul_mag(u128 a, u128 b, bool& sticky) {
    u128 hi, lo;
    mul_u128(a, b, hi, lo);
    const u128 mask = (((u128)1) << FRAC) - 1;
    sticky = (lo & mask) != 0;
    return (hi << (128 - FRAC)) | (lo >> FRAC);
}

// a·b rounded toward +inf (up) or -inf (!up).
__device__ __forceinline__ i128 mul_dir(i128 a, i128 b, bool up) {
    bool negative = (a < 0) != (b < 0);
    u128 ma = a < 0 ? (u128)(-a) : (u128)a;
    u128 mb = b < 0 ? (u128)(-b) : (u128)b;
    bool sticky;
    u128 m = mul_mag(ma, mb, sticky);
    if (negative) {
        return up ? -(i128)m : -(i128)(m + (sticky ? 1 : 0));
    }
    return up ? (i128)(m + (sticky ? 1 : 0)) : (i128)m;
}

__device__ __forceinline__ i128 div_dir(i128 a, unsigned k, bool up) {
    i128 q = a / (i128)k;
    i128 r = a - q * (i128)k;
    if (r != 0) {
        if (up && a > 0) q += 1;
        if (!up && a < 0) q -= 1;
    }
    return q;
}

__device__ __forceinline__ i128 floor_half(i128 a) {
    return a >= 0 ? (a >> 1) : -(((-a) + 1) >> 1);
}
__device__ __forceinline__ i128 ceil_half(i128 a) { return -floor_half(-a); }

__device__ __forceinline__ Iv iv_point(i128 v) { Iv r; r.lo = v; r.hi = v; return r; }
__device__ __forceinline__ Iv iv_add(Iv a, Iv b) { Iv r; r.lo = a.lo + b.lo; r.hi = a.hi + b.hi; return r; }
__device__ __forceinline__ Iv iv_neg(Iv a) { Iv r; r.lo = -a.hi; r.hi = -a.lo; return r; }
__device__ __forceinline__ Iv iv_sub(Iv a, Iv b) { return iv_add(a, iv_neg(b)); }
__device__ __forceinline__ Iv iv_half(Iv a) { Iv r; r.lo = floor_half(a.lo); r.hi = ceil_half(a.hi); return r; }
__device__ __forceinline__ Iv iv_double(Iv a) { Iv r; r.lo = a.lo << 1; r.hi = a.hi << 1; return r; }
__device__ __forceinline__ Iv iv_div(Iv a, unsigned k) { Iv r; r.lo = div_dir(a.lo, k, false); r.hi = div_dir(a.hi, k, true); return r; }
__device__ __forceinline__ i128 iv_mag(Iv a) { return imax(iabs(a.lo), iabs(a.hi)); }

__device__ __forceinline__ Iv iv_mul(Iv a, Iv b) {
    i128 l = imin(imin(mul_dir(a.lo, b.lo, false), mul_dir(a.lo, b.hi, false)),
                  imin(mul_dir(a.hi, b.lo, false), mul_dir(a.hi, b.hi, false)));
    i128 u = imax(imax(mul_dir(a.lo, b.lo, true), mul_dir(a.lo, b.hi, true)),
                  imax(mul_dir(a.hi, b.lo, true), mul_dir(a.hi, b.hi, true)));
    Iv r; r.lo = l; r.hi = u; return r;
}

// exp(-x) for an interval x with x.lo >= 0.
__device__ Iv exp_neg(Iv x, unsigned terms) {
    const i128 eighth = ((i128)1) << (FRAC - 3);
    const i128 one = ((i128)1) << FRAC;
    unsigned halvings = 0;
    while (x.hi > eighth) { x = iv_half(x); halvings++; }
    Iv negated = iv_neg(x);
    Iv sum = iv_point(one);
    Iv term = iv_point(one);
    for (unsigned j = 1; j < terms; j++) {
        term = iv_div(iv_mul(term, negated), j);
        sum = iv_add(sum, term);
    }
    // alternating with decreasing magnitudes once x <= 1/8: the tail is bounded by the next term
    i128 tail = div_dir(mul_dir(iv_mag(term), x.hi, true), terms, true) + 1;
    sum.lo -= tail;
    sum.hi += tail;
    if (sum.lo < 0) sum.lo = 0;
    for (unsigned k = 0; k < halvings; k++) sum = iv_mul(sum, sum);
    return sum;
}

// sin and cos of an interval angle: the series at its centre, widened by its radius.
__device__ void sin_cos(Iv theta, unsigned terms, Iv& sine_out, Iv& cosine_out) {
    const i128 eighth = ((i128)1) << (FRAC - 3);
    const i128 one = ((i128)1) << FRAC;
    i128 centre = floor_half(theta.lo + theta.hi);
    i128 radius = imax(centre - theta.lo, theta.hi - centre);
    Iv y = iv_point(centre);
    unsigned halvings = 0;
    while (iv_mag(y) > eighth) { y = iv_half(y); halvings++; }
    Iv square = iv_mul(y, y);
    Iv negated_square = iv_neg(square);
    Iv sine = y, sine_term = y;
    for (unsigned i = 1; i < terms; i++) {
        sine_term = iv_div(iv_mul(sine_term, negated_square), (2 * i) * (2 * i + 1));
        sine = iv_add(sine, sine_term);
    }
    i128 sine_tail = div_dir(mul_dir(iv_mag(sine_term), square.hi, true), (2 * terms) * (2 * terms + 1), true) + 1;
    Iv cosine = iv_point(one), cosine_term = iv_point(one);
    for (unsigned i = 1; i < terms; i++) {
        cosine_term = iv_div(iv_mul(cosine_term, negated_square), (2 * i - 1) * (2 * i));
        cosine = iv_add(cosine, cosine_term);
    }
    i128 cosine_tail = div_dir(mul_dir(iv_mag(cosine_term), square.hi, true), (2 * terms - 1) * (2 * terms), true) + 1;
    sine.lo -= sine_tail; sine.hi += sine_tail;
    cosine.lo -= cosine_tail; cosine.hi += cosine_tail;
    for (unsigned k = 0; k < halvings; k++) {
        Iv next_sine = iv_double(iv_mul(sine, cosine));
        Iv next_cosine = iv_sub(iv_mul(cosine, cosine), iv_mul(sine, sine));
        sine = next_sine;
        cosine = next_cosine;
    }
    sine.lo -= radius; sine.hi += radius;
    cosine.lo -= radius; cosine.hi += radius;
    sine_out = sine;
    cosine_out = cosine;
}

// points: 4 per point (sigma_lo, sigma_hi, tau_lo, tau_hi); logs: 2 per base, base = index + 1;
// out: 12 per point — value (re_lo, re_hi, im_lo, im_hi), first derivative (the same four), and
// second derivative (the same four): `n^-s`, `-log n · n^-s`, `log^2 n · n^-s`.
extern "C" __global__ void eta_head_jets(
    const i128* __restrict__ points,
    unsigned point_count,
    const i128* __restrict__ logs,
    unsigned start,
    unsigned exp_terms,
    unsigned trig_terms,
    i128* __restrict__ out)
{
    __shared__ i128 reduction[BLOCK][12];
    const unsigned point = blockIdx.x;
    if (point >= point_count) return;
    Iv sigma; sigma.lo = points[4 * point + 0]; sigma.hi = points[4 * point + 1];
    Iv tau;   tau.lo   = points[4 * point + 2]; tau.hi   = points[4 * point + 3];
    i128 acc[12];
    for (int i = 0; i < 12; i++) acc[i] = 0;
    for (unsigned base = 1 + threadIdx.x; base < start; base += BLOCK) {
        Iv logarithm; logarithm.lo = logs[2 * (base - 1)]; logarithm.hi = logs[2 * (base - 1) + 1];
        Iv amplitude = exp_neg(iv_mul(sigma, logarithm), exp_terms);
        Iv angle = iv_neg(iv_mul(tau, logarithm));
        Iv sine, cosine;
        sin_cos(angle, trig_terms, sine, cosine);
        Iv re = iv_mul(amplitude, cosine);
        Iv im = iv_mul(amplitude, sine);
        Iv dre = iv_neg(iv_mul(logarithm, re));
        Iv dim = iv_neg(iv_mul(logarithm, im));
        Iv ddre = iv_neg(iv_mul(logarithm, dre));
        Iv ddim = iv_neg(iv_mul(logarithm, dim));
        acc[0] += re.lo;   acc[1] += re.hi;
        acc[2] += im.lo;   acc[3] += im.hi;
        acc[4] += dre.lo;  acc[5] += dre.hi;
        acc[6] += dim.lo;  acc[7] += dim.hi;
        acc[8] += ddre.lo; acc[9] += ddre.hi;
        acc[10] += ddim.lo; acc[11] += ddim.hi;
    }
    for (int i = 0; i < 12; i++) reduction[threadIdx.x][i] = acc[i];
    __syncthreads();
    for (unsigned stride = BLOCK / 2; stride > 0; stride >>= 1) {
        if (threadIdx.x < stride) {
            for (int i = 0; i < 12; i++) reduction[threadIdx.x][i] += reduction[threadIdx.x + stride][i];
        }
        __syncthreads();
    }
    if (threadIdx.x == 0) {
        for (int i = 0; i < 12; i++) out[12 * point + i] = reduction[0][i];
    }
}
