// **The signed 128-bit word ring and its carrier refusal** (#12, #76).
//
// Ported from `13f8c734:crates/holonics-cuda/kernels/exact_resident_section.cu` (its `wide`
// carrier: the exact magnitude of the signed minimum, the product of two words, the refusal bit)
// and `13f8c734:crates/holonics-cuda/kernels/exact_integer.cuh` (the signed-magnitude carrier
// with an explicit overflow flag), rewritten against today's objects. The hnn_* API below is
// the original bounded ring and remains unchanged. The separate hnn_exact_* API at the end is
// runtime-width arithmetic for epoch consumers; it deliberately does not revive the old fixed
// template width or its constructors that indexed limbs beyond a narrow value's storage.
//
// [definition] **The ring.** A word is an element of Z/2^128 in two's complement: `uwide`
// addition and `wide` products of two signed 64-bit words are the ring's operations, and they
// wrap by definition (unsigned arithmetic; the signed reading of an unsigned word is modular in
// C++20). The **carrier** is the symmetric window W = (−2^127, 2^127), closed under negation; a
// word is read as an integer only on W.
//
// [definition] **The certificate is the l1 bound.** For integers p_1 … p_n with
// Σ_j |p_j| < 2^127, every partial sum, in every order and every tree of the reduction, has
// magnitude at most Σ_j |p_j|, so it lies in W, and the ring's sum read on W is the integer sum.
// A reduction therefore carries, beside its ring word, the sum of its terms' magnitudes,
// saturated at 2^127; the word is read only when that bound is below 2^127, and is refused
// otherwise, **whatever its value**. The refusal is a property of the exact terms alone, never of
// the realization's order: the device and any host reference refuse the same reads. It is the
// lattice rule's own quantity (`holonics::hnn::FieldDeclaration::lattice_by_rule`: `X_l`, the
// declared bound on the l1 norm of the operand one read of a locus sums), read at the carrier.
//
// A product of two signed 64-bit words has magnitude at most 2^126 (the signed minimum squared),
// so it is always a word of W and needs no refusal; the magnitude of the signed minimum is taken
// as `(uwide)0 − (uwide)v`, which is exact where a signed negation would overflow.
//
// [definition] **The certificate extended to products of two bounded operands.** A signed 64-bit
// word `a` times a certified carrier word `b` (`|b| < 2^127`, itself the read of a certified sum)
// can reach 2^190. Its magnitude is formed exactly from the limbs of `|b|`, and the product is a
// term of the ring only when `|a|·|b| < 2^127`; otherwise its magnitude enters the certificate
// saturated, so the sum it joins is refused whatever its value (`hnn_bounded_product`). The rule
// is again a property of the exact terms alone.
//
// [definition] **The nearest-point split** (`hnn_nearest`): Lean `HNN/LatticeDeposit.quot`/`rem`,
// the nearest multiple of `2^L`, ties upward, `s = q·2^L + r` with `−2^(L−1) ≤ r < 2^(L−1)`; at
// `L = 0` every integer is a lattice point and `r = 0`. It is read off the low bits and the
// arithmetic shift (the floor, C++20), with no addition that could leave the carrier.
//
// [definition] **The word boundary of a result.** A state or chart coordinate the split produces
// is kept only when it is a signed 64-bit word, the width every operand enters the card at;
// otherwise the entry is refused (`HNN_REFUSED_WORD`), never wrapped. An entry that reads a
// refused operand is refused in turn (`HNN_REFUSED_OPERAND`), so a refusal travels with the
// current and is reported where the word is released.
//
// [proved-derived; formal-checked] Lean `HNN/LatticeWord` §7: under the l1 certificate every
// partial sum lies in W and the ring's signed read is the integer sum (`carrier_partial_sum`,
// `carrier_ring_read`). The certificate's addition below is `min(a + b, 2^127)`
// (`certify_eq_branch`), commutative and associative (`certify_comm`, `certify_assoc`), so every
// tree over the same terms, the block tree here and the host's pass alike, carries
// `min(Σ|p_j|, 2^127)` and the same word (`Reduction.bound_eq`, `Reduction.order_free`): a read is
// refused exactly when `Σ|p_j|` reaches 2^127 (`Reduction.refused_iff`), and an admitted read is
// the integer sum (`Reduction.read_of_bound_lt`).

#pragma once
#include <stdint.h>
#include <stddef.h>

typedef __int128 wide;
typedef unsigned __int128 uwide;

// A read's status word: zero is exact; each refusal is one bit.
#define HNN_EXACT 0u
#define HNN_REFUSED_CARRIER 1u
#define HNN_REFUSED_MALFORMED 2u
#define HNN_REFUSED_WORD 4u
#define HNN_REFUSED_OPERAND 8u

// 2^127: the least magnitude outside the carrier.
#define HNN_CARRIER_BOUND (((uwide)1) << 127)

// |v| as an unsigned magnitude, exact for the signed minimum.
__device__ __forceinline__ uwide hnn_magnitude(wide v) {
    return v < 0 ? (uwide)0 - (uwide)v : (uwide)v;
}

// The product of two signed 64-bit words: exact, |p| ≤ 2^126.
__device__ __forceinline__ wide hnn_word_product(int64_t a, int64_t b) {
    return (wide)a * (wide)b;
}

// The certificate's addition: the l1 bounds of two parts, saturated at 2^127. Both operands are
// at most 2^127, so the sum of two unsaturated bounds stays below 2^128 and cannot wrap.
__device__ __forceinline__ uwide hnn_certify(uwide bound, uwide magnitude) {
    if (bound >= HNN_CARRIER_BOUND || magnitude >= HNN_CARRIER_BOUND) {
        return HNN_CARRIER_BOUND;
    }
    const uwide sum = bound + magnitude;
    return sum >= HNN_CARRIER_BOUND ? HNN_CARRIER_BOUND : sum;
}

// Read a ring word as an integer under its certificate, or refuse the carrier.
__device__ __forceinline__ wide hnn_certified(uwide word, uwide bound, uint32_t *status) {
    if (bound >= HNN_CARRIER_BOUND) {
        *status |= HNN_REFUSED_CARRIER;
        return 0;
    }
    return (wide)word;
}

// The product of a signed 64-bit word and a carrier word (|b| < 2^127): the exact product and its
// magnitude when |a·b| < 2^127; otherwise the magnitude saturates at 2^127 and the product is
// unread (zero). With |b| = h·2^64 + l: |a|·l < 2^127 and |a|·h < 2^126; |a|·h ≥ 2^63 already
// puts the product past 2^127, and below it (|a|·h)·2^64 + |a|·l < 2^128 cannot wrap.
__device__ __forceinline__ wide hnn_bounded_product(int64_t a, wide b, uwide *magnitude) {
    const uwide ma = hnn_magnitude((wide)a);
    const uwide mb = hnn_magnitude(b);
    const uwide limb = ((uwide)1 << 64) - 1;
    const uwide high = ma * (mb >> 64);
    if (high >= ((uwide)1 << 63)) {
        *magnitude = HNN_CARRIER_BOUND;
        return 0;
    }
    const uwide m = (high << 64) + ma * (mb & limb);
    if (m >= HNN_CARRIER_BOUND) {
        *magnitude = HNN_CARRIER_BOUND;
        return 0;
    }
    *magnitude = m;
    return ((a < 0) != (b < 0)) ? -(wide)m : (wide)m;
}

// The nearest-point split of a carrier word at 2^shift, ties upward (shift ≤ 127): returns q and
// writes r, s = q·2^shift + r, −2^(shift−1) ≤ r < 2^(shift−1).
__device__ __forceinline__ wide hnn_nearest(wide s, uint32_t shift, wide *remainder) {
    if (shift == 0) {
        *remainder = 0;
        return s;
    }
    const uwide unit = (uwide)1 << shift;
    const uwide low = (uwide)s & (unit - 1);
    const wide below = s >> shift;  // the floor of s / 2^shift
    if (low >= (unit >> 1)) {
        *remainder = (wide)(low - unit);  // in [−2^(shift−1), 0), read modularly
        return below + 1;
    }
    *remainder = (wide)low;
    return below;
}

// Whether an integer is a signed 64-bit word.
__device__ __forceinline__ bool hnn_is_word(wide v) {
    return v >= (wide)INT64_MIN && v <= (wide)INT64_MAX;
}

// The block's tree over its threads' ring words and certificates (blockDim.x a power of two):
// ring addition and the saturated certificate addition are associative and commutative, so the
// tree's order changes no value and no refusal (Lean `HNN/LatticeWord.Reduction.order_free`).
// Thread 0 holds the block's word and bound.
__device__ __forceinline__ void hnn_block_sum(uwide *ring, uwide *bound, uint32_t t) {
    for (uint32_t stride = blockDim.x >> 1; stride > 0; stride >>= 1) {
        if (t < stride) {
            ring[t] += ring[t + stride];
            bound[t] = hnn_certify(bound[t], bound[t + stride]);
        }
        __syncthreads();
    }
}

// Epoch arithmetic is deliberately a separate interface from the signed 128-bit HNN ring
// above. Values are signed magnitudes in caller-owned, little-endian 64-bit limb spans. `size`
// is the significant limb count (zero is represented by size=0 and negative=0); capacities
// are always supplied by the caller. There is no device allocation and no intrinsic word cap.
// The caller derives the first capacity from its lattice l1 bound and widens at a crossing.
struct HnnExactConst {
    const uint64_t *limb;
    size_t size;
    bool negative;
};
struct HnnExactMut {
    uint64_t *limb;
    size_t capacity;
    size_t size; // written only on HNN_XINT_OK
    bool negative; // written only on HNN_XINT_OK; zero is always nonnegative
};
struct HnnExactResult { uint32_t status; size_t required; };
struct HnnExactDivResult { uint32_t status; size_t quotient_required; size_t remainder_required; size_t scratch_required; };
struct HnnExactOrder { uint32_t status; int ordering; };
struct HnnExactCount { uint32_t status; uint64_t value; };
#define HNN_XINT_OK 0u
#define HNN_XINT_NEED_CAPACITY 1u
#define HNN_XINT_DIV_ZERO 2u
#define HNN_XINT_BAD_VIEW 3u
#define HNN_XINT_NONINTEGRAL_SHIFT 4u
// An exact reduction term pairs its signed value with the nonnegative l1 bound of the terms
// represented by it. The caller retains both spans and compares/adds the bound before release;
// when the derived carrier would be crossed it rebases into a wider caller-owned arena.
struct HnnExactCertified { HnnExactConst value; HnnExactConst l1_bound; };

// Workspace is caller-owned and must have at least the reported number of limbs. Operations
// stage their complete result here before touching the destination, so a short destination or
// workspace never commits a truncated value. Input/output/workspace overlap, including overlap
// between the quotient and remainder outputs, is unsupported. Mutating outputs are passed by
// pointer so successful limb and metadata writes reach the caller; failures leave both intact.
__device__ __forceinline__ size_t hnn_xtrim(const uint64_t *a, size_t n) {
    while (n && a[n - 1] == 0) --n;
    return n;
}
__device__ __forceinline__ int hnn_xcmp(const uint64_t *a, size_t an, const uint64_t *b, size_t bn) {
    an=hnn_xtrim(a,an); bn=hnn_xtrim(b,bn);
    if(an<bn)return -1; if(an>bn)return 1;
    while(an){--an;if(a[an]<b[an])return -1;if(a[an]>b[an])return 1;} return 0;
}
__device__ __forceinline__ bool hnn_xvalid(HnnExactConst a) {
    return a.size<=SIZE_MAX/64 && (!a.size || (a.limb && a.limb[a.size-1]!=0)) && (!a.negative || a.size!=0);
}
__device__ __forceinline__ bool hnn_exact_certified_valid(HnnExactCertified a) {
    return hnn_xvalid(a.value) && hnn_xvalid(a.l1_bound) && !a.l1_bound.negative &&
        hnn_xcmp(a.value.limb,a.value.size,a.l1_bound.limb,a.l1_bound.size)<=0;
}
__device__ __forceinline__ bool hnn_xmut_valid(const HnnExactMut *out) {
    return out && (out->capacity==0 || out->limb);
}
__device__ __forceinline__ bool hnn_xscratch_valid(const uint64_t *scratch,size_t capacity) {
    return capacity==0 || scratch!=nullptr;
}
__device__ __forceinline__ bool hnn_xsize_add(size_t a,size_t b,size_t *sum) {
    if (b>SIZE_MAX-a) return false; *sum=a+b; return true;
}
__device__ __forceinline__ void hnn_xcommit(HnnExactMut *out, const uint64_t *tmp, size_t n, bool neg) {
    for(size_t i=0;i<n;++i) out->limb[i]=tmp[i];
    out->size=n; out->negative=neg && n!=0;
}
__device__ __forceinline__ HnnExactResult hnn_xfinish(HnnExactMut *out, uint64_t *tmp, size_t tmpcap,
                                                       size_t n, bool neg) {
    n=hnn_xtrim(tmp,n);
    if(!hnn_xmut_valid(out))return {HNN_XINT_BAD_VIEW,0};
    if(tmpcap<n || out->capacity<n) return {HNN_XINT_NEED_CAPACITY,n};
    hnn_xcommit(out,tmp,n,neg); return {HNN_XINT_OK,n};
}

// Exact signed addition/subtraction; scratch needs max(a.size,b.size)+1 limbs.
__device__ __forceinline__ HnnExactResult hnn_xadd(HnnExactConst a,HnnExactConst b,bool subtract,
                                                    HnnExactMut *out,uint64_t *tmp,size_t tmpcap) {
    if(!hnn_xvalid(a)||!hnn_xvalid(b)||!hnn_xmut_valid(out)||!hnn_xscratch_valid(tmp,tmpcap))return {HNN_XINT_BAD_VIEW,0};
    const bool bn=b.negative!=subtract; size_t n=a.size>b.size?a.size:b.size;
    size_t scratch_need; if(!hnn_xsize_add(n,1,&scratch_need))return {HNN_XINT_BAD_VIEW,0};
    if(tmpcap<scratch_need)return {HNN_XINT_NEED_CAPACITY,scratch_need};
    if(a.negative==bn){ uint64_t carry=0; for(size_t i=0;i<n;++i){
        uint64_t av=i<a.size?a.limb[i]:0,bv=i<b.size?b.limb[i]:0;
        uint64_t s=av+bv,c1=s<av,t=s+carry,c2=t<s; tmp[i]=t; carry=c1|c2;
    } tmp[n]=carry; return hnn_xfinish(out,tmp,tmpcap,n+1,a.negative); }
    int cmp=hnn_xcmp(a.limb,a.size,b.limb,b.size); bool a_larger=cmp>=0;
    HnnExactConst x=a_larger?a:b,y=a_larger?b:a; bool neg=a_larger?a.negative:bn;
    uint64_t borrow=0; for(size_t i=0;i<x.size;++i){uint64_t xv=x.limb[i],yv=i<y.size?y.limb[i]:0;
        uint64_t t=xv-yv,b1=xv<yv,u=t-borrow,b2=t<borrow;tmp[i]=u;borrow=b1|b2;}
    return hnn_xfinish(out,tmp,tmpcap,x.size,neg);
}
__device__ __forceinline__ HnnExactResult hnn_xmul(HnnExactConst a,HnnExactConst b,HnnExactMut *out,
                                                    uint64_t *tmp,size_t tmpcap) {
    if(!hnn_xvalid(a)||!hnn_xvalid(b)||!hnn_xmut_valid(out)||!hnn_xscratch_valid(tmp,tmpcap))return {HNN_XINT_BAD_VIEW,0};
    size_t need=0; if(a.size&&b.size&&!hnn_xsize_add(a.size,b.size,&need))return {HNN_XINT_BAD_VIEW,0};
    if(tmpcap<need)return {HNN_XINT_NEED_CAPACITY,need};
    for(size_t i=0;i<need;++i)tmp[i]=0;
    for(size_t i=0;i<a.size;++i)for(size_t j=0;j<b.size;++j){
        size_t k=i+j; uint64_t lo=a.limb[i]*b.limb[j], hi=__umul64hi(a.limb[i],b.limb[j]);
        uint64_t s=tmp[k]+lo, c=s<tmp[k]; tmp[k]=s; ++k;
        if(k<need){ uint64_t t=tmp[k]+hi,c1=t<tmp[k],u=t+c,c2=u<t; tmp[k]=u;
            uint64_t carry=c1|c2; ++k; while(carry && k<need){uint64_t v=tmp[k]+1;carry=v==0;tmp[k++]=v;}
        }
    }
    return hnn_xfinish(out,tmp,tmpcap,need,a.negative!=b.negative);
}
__device__ __forceinline__ HnnExactResult hnn_xshift(HnnExactConst a,int64_t bits,HnnExactMut *out,
                                                      uint64_t *tmp,size_t tmpcap) {
    if(!hnn_xvalid(a)||!hnn_xmut_valid(out)||!hnn_xscratch_valid(tmp,tmpcap))return {HNN_XINT_BAD_VIEW,0};
    if(bits<0){uint64_t r=(uint64_t)(-(bits+1))+1, words=r/64, rem=r%64; size_t n=a.size>words?a.size-words:0;
        // A right shift is an exact dyadic rebase only when every discarded bit is zero.
        size_t whole=words<a.size?(size_t)words:a.size;
        for(size_t i=0;i<whole;++i)if(a.limb[i])return {HNN_XINT_NONINTEGRAL_SHIFT,0};
        if(rem && words<a.size && (a.limb[words]&((uint64_t(1)<<rem)-1)))return {HNN_XINT_NONINTEGRAL_SHIFT,0};
        if(tmpcap<n)return {HNN_XINT_NEED_CAPACITY,n};
        for(size_t i=0;i<n;++i){size_t ix=i+words;tmp[i]=a.limb[ix]>>rem;if(rem&&ix+1<a.size)tmp[i]|=a.limb[ix+1]<<(64-rem);}
        return hnn_xfinish(out,tmp,tmpcap,n,a.negative);
    }
    uint64_t s=(uint64_t)bits, words=s/64, rem=s%64; size_t n=0, extra;
    if(words>SIZE_MAX || !hnn_xsize_add((size_t)words,rem?1:0,&extra))return {HNN_XINT_BAD_VIEW,0};
    if(a.size&&!hnn_xsize_add(a.size,extra,&n))return {HNN_XINT_BAD_VIEW,0};
    if(tmpcap<n)return {HNN_XINT_NEED_CAPACITY,n};
    for(size_t i=0;i<n;++i)tmp[i]=0;
    for(size_t i=0;i<a.size;++i){tmp[i+words]|=a.limb[i]<<rem;if(rem)tmp[i+words+1]|=a.limb[i]>>(64-rem);}
    return hnn_xfinish(out,tmp,tmpcap,n,a.negative);
}

// Bitwise long division of magnitudes. Quotient truncates toward zero and remainder has the
// numerator's sign. Workspace is quotient.size + numerator.size + 1 limbs: q and rem.
__device__ __forceinline__ HnnExactDivResult hnn_xdivrem(HnnExactConst a,HnnExactConst b,HnnExactMut *q,
    HnnExactMut *r,uint64_t *tmp,size_t tmpcap) {
    if(!hnn_xvalid(a)||!hnn_xvalid(b)||!hnn_xmut_valid(q)||!hnn_xmut_valid(r)||!hnn_xscratch_valid(tmp,tmpcap))return {HNN_XINT_BAD_VIEW,0,0,0};
    if(!b.size)return {HNN_XINT_DIV_ZERO,0,0,0}; size_t n=a.size, m=b.size;
    size_t qneed=n, workneed; if(!hnn_xsize_add(qneed,n,&workneed)||!hnn_xsize_add(workneed,1,&workneed))return {HNN_XINT_BAD_VIEW,0,0,0};
    if(tmpcap<workneed)return {HNN_XINT_NEED_CAPACITY,0,0,workneed};
    uint64_t *qp=tmp,*rem=tmp+qneed;
    for(size_t i=0;i<qneed;++i)qp[i]=0; for(size_t i=0;i<n+1;++i)rem[i]=0;
    if(hnn_xcmp(a.limb,n,b.limb,m)>=0){
        size_t bitcount=n*64; while(bitcount && !(a.limb[(bitcount-1)/64]>>((bitcount-1)%64)&1))--bitcount;
        while(bitcount){--bitcount; uint64_t carry=(a.limb[bitcount/64]>>(bitcount%64))&1;
            for(size_t j=0;j<n+1;++j){uint64_t next=rem[j]>>63;rem[j]=(rem[j]<<1)|carry;carry=next;}
            if(hnn_xcmp(rem,n+1,b.limb,m)>=0){uint64_t borrow=0;for(size_t j=0;j<n+1;++j){uint64_t bv=j<m?b.limb[j]:0,t=rem[j]-bv,b1=rem[j]<bv,u=t-borrow,b2=t<borrow;rem[j]=u;borrow=b1|b2;}qp[bitcount/64]|=uint64_t(1)<<(bitcount%64);}
        }
    } else { for(size_t j=0;j<n;++j)rem[j]=a.limb[j]; }
    size_t qsize=hnn_xtrim(qp,qneed), rsize=hnn_xtrim(rem,n+1);
    if(qsize>q->capacity||rsize>r->capacity)return {HNN_XINT_NEED_CAPACITY,qsize,rsize,workneed};
    hnn_xcommit(q,qp,qsize,a.negative!=b.negative); hnn_xcommit(r,rem,rsize,a.negative); return {HNN_XINT_OK,qsize,rsize,workneed};
}

// Exact common trailing-power reduction for a signed numerator/denominator pair. The caller
// may then lower the shared dyadic exponent by the returned count. Zero has no sign and reports 0.
__device__ __forceinline__ uint64_t hnn_xcommon_trailing(HnnExactConst a,HnnExactConst b) {
    size_t an=hnn_xtrim(a.limb,a.size),bn=hnn_xtrim(b.limb,b.size); if(!an||!bn)return 0;
    uint64_t az=0,bz=0; while(az/64<an && ((a.limb[az/64]>>(az%64))&1)==0)++az;
    while(bz/64<bn && ((b.limb[bz/64]>>(bz%64))&1)==0)++bz;
    return az<bz?az:bz;
}

// Public epoch arithmetic spellings. For division the exact signed identity is
// a = b*q + r, |r| < |b|; q truncates toward zero and r has a's sign.
__device__ __forceinline__ HnnExactResult hnn_exact_add(HnnExactConst a,HnnExactConst b,HnnExactMut *out,uint64_t *tmp,size_t tmpcap) {
    return hnn_xadd(a,b,false,out,tmp,tmpcap);
}
__device__ __forceinline__ HnnExactResult hnn_exact_sub(HnnExactConst a,HnnExactConst b,HnnExactMut *out,uint64_t *tmp,size_t tmpcap) {
    return hnn_xadd(a,b,true,out,tmp,tmpcap);
}
__device__ __forceinline__ HnnExactResult hnn_exact_mul(HnnExactConst a,HnnExactConst b,HnnExactMut *out,uint64_t *tmp,size_t tmpcap) {
    return hnn_xmul(a,b,out,tmp,tmpcap);
}
__device__ __forceinline__ HnnExactResult hnn_exact_shift(HnnExactConst a,int64_t bits,HnnExactMut *out,uint64_t *tmp,size_t tmpcap) {
    return hnn_xshift(a,bits,out,tmp,tmpcap);
}
__device__ __forceinline__ HnnExactDivResult hnn_exact_divrem(HnnExactConst a,HnnExactConst b,HnnExactMut *q,HnnExactMut *r,uint64_t *tmp,size_t tmpcap) {
    return hnn_xdivrem(a,b,q,r,tmp,tmpcap);
}
__device__ __forceinline__ HnnExactOrder hnn_exact_compare(HnnExactConst a,HnnExactConst b) {
    if(!hnn_xvalid(a)||!hnn_xvalid(b))return {HNN_XINT_BAD_VIEW,0};
    if(a.negative!=b.negative)return {HNN_XINT_OK,a.negative?-1:1};
    int cmp=hnn_xcmp(a.limb,a.size,b.limb,b.size); return {HNN_XINT_OK,a.negative?-cmp:cmp};
}
__device__ __forceinline__ HnnExactCount hnn_exact_common_trailing(HnnExactConst a,HnnExactConst b) {
    if(!hnn_xvalid(a)||!hnn_xvalid(b))return {HNN_XINT_BAD_VIEW,0};
    return {HNN_XINT_OK,hnn_xcommon_trailing(a,b)};
}
