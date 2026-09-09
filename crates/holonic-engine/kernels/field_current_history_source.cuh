// Complete internal-current source geometry in an integral root-contact chart.
// Birth moments are exact on the numerical prefix representatives, with their existing
// uncertainty retained. C is the actual paired-junction covariance; no model update occurs here.
// A history pairing multiplies two complete wide current components.
using HistoryInteger = ExactInteger<2 * sizeof(wide) / sizeof(uint32_t)>;

__device__ __forceinline__ HistoryInteger history_integer(wide value) {
    uwide m = magnitude(value);
    ExactCoefficient coefficient{(uint64_t)m, (uint64_t)(m >> 64), (uint32_t)(value < 0), 0u};
    return HistoryInteger(coefficient);
}
__device__ __forceinline__ HistoryInteger history_read_integer(const int64_t *words, uint32_t *slot) {
    HistoryInteger value;
    for (uint32_t i=0; i<4; ++i) {
        uint64_t word=(uint64_t)words[i];
        value.limb[2*i]=(uint32_t)word;
        value.limb[2*i+1]=(uint32_t)(word>>32);
    }
    if (words[4]<0 || words[4]>1 || (words[4] && value.is_zero())) atomicOr(slot,REFUSED_MALFORMED);
    value.negative=words[4]!=0;
    return value;
}
__device__ __forceinline__ void history_write_integer(const HistoryInteger &value, int64_t *lo, int64_t *hi, uint32_t *slot) {
    if (value.overflow) { atomicOr(slot,REFUSED_CARRIER); return; }
    for (uint32_t i=0; i<4; ++i) {
        uint64_t word=(uint64_t)value.limb[2*i] | ((uint64_t)value.limb[2*i+1]<<32);
        lo[i]=hi[i]=(int64_t)word;
    }
    lo[4]=hi[4]=value.negative ? 1 : 0;
}
__device__ __forceinline__ wide history_narrow(const HistoryInteger &value, uint32_t *slot) {
    if (value.overflow || value.limb[4] || value.limb[5] || value.limb[6] || value.limb[7]) {
        atomicOr(slot,REFUSED_CARRIER); return 0;
    }
    uwide m=(uwide)value.limb[0] | ((uwide)value.limb[1]<<32) | ((uwide)value.limb[2]<<64) | ((uwide)value.limb[3]<<96);
    return of_magnitude(m,value.negative,slot);
}
__device__ wide history_norm_ceiling(const HistoryInteger &value, uint32_t *slot) {
    if (value.negative || value.overflow) { atomicOr(slot,REFUSED_CARRIER); return 0; }
    HistoryInteger root;
    for (int bit=127; bit>=0; --bit) {
        HistoryInteger candidate=root;
        candidate.limb[bit/32] |= (uint32_t)1u<<(bit%32);
        HistoryInteger square=candidate*candidate;
        if (!square.overflow && square<=value) root=candidate;
    }
    if (root*root!=value) root=root+1;
    return history_narrow(root,slot);
}
__device__ __forceinline__ void history_complex_add_product(
    HistoryInteger &real, HistoryInteger &imaginary, wide ar, wide ai, wide br, wide bi, bool conjugate_left=false
) {
    HistoryInteger a=history_integer(ar), b=history_integer(ai), c=history_integer(br), d=history_integer(bi);
    if (conjugate_left) b=-b;
    real=real+a*c-b*d;
    imaginary=imaginary+a*d+b*c;
}

// State: ell[D] as signed-128/S; kappa as signed-magnitude-256/S^2 (five words);
// next occurrence, grain, reserved zero. Feature: p[D], P[D], u[D] as signed-128/S;
// w complex and norm square as signed-magnitude-256/S^2; grain; radius128/S; trace C; occurrence;
// the upward-rounded representative norm as signed-128/S.
__device__ void field_current_history_source_prepare(
    const int64_t *query, const int64_t *origin, const int64_t *incoming,
    const int64_t *frame, const int64_t *origin_frame, const int64_t *covariance,
    const wide *before, const wide *current, const int64_t *state,
    uint32_t nodes, uint32_t linked, uint32_t grain, uint64_t occurrence,
    int64_t *next_lo, int64_t *next_hi, int64_t *source_lo, int64_t *source_hi,
    wide *scratch, uint32_t *slot,wide joint_radius=-1
) {
    if (!nodes || grain<1u || grain>120u || linked>1u || occurrence>=(uint64_t)INT64_MAX) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    const uint32_t D=6u*nodes;
    const size_t stride=(size_t)D+1u, matrix=(size_t)D*D;
    if (covariance[matrix]!=1 || state[2u*D+5u]!=(int64_t)occurrence
        || state[2u*D+6u]!=(int64_t)grain || state[2u*D+7u]!=0
        || before[4u*stride-1u]<0 || current[4u*stride-1u]<before[4u*stride-1u]
        || current[2u*stride-1u]<0) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    wide *face=scratch, *d=face+D;
    wide face_den, d_den;
    if (!field_paired_build_faces(query,origin,incoming,frame,origin_frame,nodes,linked,
        face,d,&face_den,&d_den,slot)) return;
    // Exact integral restriction of the contact representation, not a language rule.
    if (linked) for (uint32_t i=0; i<D; ++i) {
        if (d_den<=0 || d[i]%d_den!=0) { atomicOr(slot,REFUSED_MALFORMED); return; }
        d[i]/=d_den;
    }
    HistoryInteger cr, ci;
    if (linked) for (uint32_t i=0; i<D; i+=2)
        history_complex_add_product(cr,ci,d[i],d[i+1],before[3u*stride+i],before[3u*stride+i+1],true);
    wide c_real=history_narrow(cr,slot), c_imaginary=history_narrow(ci,slot);
    HistoryInteger square=history_read_integer(state+2u*D,slot);
    if (square.negative) atomicOr(slot,REFUSED_MALFORMED);
    square=square+cr*cr+ci*ci;
    wide *ell_lo=(wide *)next_lo, *ell_hi=(wide *)next_hi;
    const wide *ell_old=(const wide *)state;
    for (uint32_t i=0; i<D; i+=2) {
        HistoryInteger real=history_integer(ell_old[i]), imaginary=history_integer(ell_old[i+1]);
        if (linked) history_complex_add_product(real,imaginary,d[i],d[i+1],c_real,c_imaginary);
        ell_lo[i]=ell_hi[i]=history_narrow(real,slot);
        ell_lo[i+1]=ell_hi[i+1]=history_narrow(imaginary,slot);
    }
    history_write_integer(square,next_lo+2u*D,next_hi+2u*D,slot);
    next_lo[2u*D+5u]=next_hi[2u*D+5u]=(int64_t)(occurrence+1u);
    next_lo[2u*D+6u]=next_hi[2u*D+6u]=(int64_t)grain;
    next_lo[2u*D+7u]=next_hi[2u*D+7u]=0;
    if (*slot) return;
    wide *source=(wide *)source_lo, *source_upper=(wide *)source_hi;
    wide trace=0;
    for (uint32_t i=0; i<D; i+=2) {
        trace=add_checked(trace,(wide)covariance[(size_t)i*D+i],slot);
        HistoryInteger real=-history_integer(ell_lo[i]), imaginary=-history_integer(ell_lo[i+1]);
        for (uint32_t j=0; j<D; j+=2)
            history_complex_add_product(real,imaginary,(wide)covariance[(size_t)i*D+j],
                (wide)covariance[(size_t)(i+1u)*D+j],current[3u*stride+j],current[3u*stride+j+1]);
        source[2u*D+i]=source_upper[2u*D+i]=history_narrow(real,slot);
        source[2u*D+i+1]=source_upper[2u*D+i+1]=history_narrow(imaginary,slot);
    }
    HistoryInteger bottom_real=-square, bottom_imaginary;
    for (uint32_t i=0; i<D; i+=2)
        history_complex_add_product(bottom_real,bottom_imaginary,ell_lo[i],ell_lo[i+1],
            current[3u*stride+i],current[3u*stride+i+1],true);
    history_write_integer(bottom_real,source_lo+6u*D,source_hi+6u*D,slot);
    history_write_integer(bottom_imaginary,source_lo+6u*D+5u,source_hi+6u*D+5u,slot);
    HistoryInteger norm_real=-bottom_real, norm_imaginary=bottom_imaginary;
    for (uint32_t i=0; i<D; i+=2) {
        source[i]=source_upper[i]=current[stride+i];
        source[i+1]=source_upper[i+1]=current[stride+i+1];
        source[D+i]=source_upper[D+i]=current[3u*stride+i];
        source[D+i+1]=source_upper[D+i+1]=current[3u*stride+i+1];
        history_complex_add_product(norm_real,norm_imaginary,source[i],source[i+1],source[i],source[i+1],true);
        history_complex_add_product(norm_real,norm_imaginary,source[2u*D+i],source[2u*D+i+1],source[D+i],source[D+i+1],true);
    }
    if (norm_real.negative || !norm_imaginary.is_zero() || norm_imaginary.overflow || trace<0) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    history_write_integer(norm_real,source_lo+6u*D+10u,source_hi+6u*D+10u,slot);
    source_lo[6u*D+15u]=source_hi[6u*D+15u]=(int64_t)grain;
    wide trace_root=isqrt_floor(trace);
    if (trace_root*trace_root!=trace) trace_root=add_checked(trace_root,1,slot);
    wide radius=joint_radius>=0?joint_radius:add_checked(current[2u*stride-1u],product_checked(
        product_checked(2,current[4u*stride-1u],slot),trace_root,slot),slot);
    ((wide *)(source_lo+6u*D+16u))[0]=((wide *)(source_hi+6u*D+16u))[0]=radius;
    source_lo[6u*D+18u]=source_hi[6u*D+18u]=to_word(trace,slot);
    source_lo[6u*D+19u]=source_hi[6u*D+19u]=(int64_t)occurrence;
    ((wide *)(source_lo+6u*D+20u))[0]=((wide *)(source_hi+6u*D+20u))[0]=history_norm_ceiling(norm_real,slot);
}

extern "C" __global__ void section_field_current_history_source(
    const int64_t *query, const int64_t *origin, const int64_t *incoming,
    const int64_t *frame, const int64_t *origin_frame, const int64_t *covariance,
    const wide *before, const wide *current, const int64_t *state_lo, const int64_t *state_hi,
    uint32_t nodes, uint32_t linked, uint32_t grain, uint64_t occurrence,
    int64_t *next_lo, int64_t *next_hi, int64_t *source_lo, int64_t *source_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x || threadIdx.x) return;
    if (upstream_refused(census,lineage,lineage_count,slot)) return;
    if (!nodes || nodes>UINT32_MAX/6u) { atomicOr(slot,REFUSED_MALFORMED); return; }
    for (size_t i=0; i<12u*(size_t)nodes+8u; ++i)
        if (state_lo[i]!=state_hi[i]) { atomicOr(slot,REFUSED_MALFORMED); return; }
    extern __shared__ wide scratch[];
    field_current_history_source_prepare(query,origin,incoming,frame,origin_frame,covariance,
        before,current,state_lo,nodes,linked,grain,occurrence,next_lo,next_hi,source_lo,source_hi,scratch,slot);
}

__device__ void history_pairing_value(
    const int64_t *a_lo, const int64_t *b_lo, uint32_t D,
    HistoryInteger &real, HistoryInteger &imaginary, uint32_t *slot
) {
    bool reverse=a_lo[6u*D+19u]>b_lo[6u*D+19u];
    const int64_t *old=reverse?b_lo:a_lo, *now=reverse?a_lo:b_lo;
    const wide *x=(const wide *)old, *y=(const wide *)now;
    HistoryInteger internal_real=-history_read_integer(old+6u*D,slot);
    HistoryInteger internal_imaginary=history_read_integer(old+6u*D+5u,slot);
    for (uint32_t i=0; i<D; i+=2) {
        history_complex_add_product(real,imaginary,x[i],x[i+1],y[i],y[i+1],true);
        history_complex_add_product(internal_real,internal_imaginary,x[2u*D+i],x[2u*D+i+1],y[D+i],y[D+i+1],true);
    }
    bool negative=((uint64_t)old[6u*D+19u]+(uint64_t)now[6u*D+19u])&1u;
    real=real+(negative?-internal_real:internal_real);
    imaginary=imaginary+(negative?-internal_imaginary:internal_imaginary);
    if (reverse) imaginary=-imaginary;

}

extern "C" __global__ void section_field_current_history_pairing(
    const int64_t *a_lo, const int64_t *a_hi, const int64_t *b_lo, const int64_t *b_hi,
    uint32_t dimension, int64_t *out_lo, int64_t *out_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x || threadIdx.x) return;
    if (upstream_refused(census,lineage,lineage_count,slot)) return;
    const uint32_t D=dimension;
    if (!D || (D&1u)) { atomicOr(slot,REFUSED_MALFORMED); return; }
    for (size_t i=0; i<6u*(size_t)D+22u; ++i)
        if (a_lo[i]!=a_hi[i] || b_lo[i]!=b_hi[i]) { atomicOr(slot,REFUSED_MALFORMED); return; }
    if (a_lo[6u*D+15u]!=b_lo[6u*D+15u] || a_lo[6u*D+19u]<0 || b_lo[6u*D+19u]<0) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    HistoryInteger real, imaginary;
    history_pairing_value(a_lo,b_lo,D,real,imaginary,slot);
    history_write_integer(real,out_lo,out_hi,slot);
    history_write_integer(imaginary,out_lo+5,out_hi+5,slot);
    wide left_error=((const wide *)(a_lo+6u*D+16u))[0];
    wide right_error=((const wide *)(b_lo+6u*D+16u))[0];
    wide left_norm=((const wide *)(a_lo+6u*D+20u))[0];
    wide right_norm=((const wide *)(b_lo+6u*D+20u))[0];
    if (left_error<0 || right_error<0 || left_norm<0 || right_norm<0) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    HistoryInteger error=history_integer(left_error)*history_integer(right_norm)
        +history_integer(right_error)*history_integer(left_norm)
        +history_integer(left_error)*history_integer(right_error);
    history_write_integer(error,out_lo+10,out_hi+10,slot);
}
