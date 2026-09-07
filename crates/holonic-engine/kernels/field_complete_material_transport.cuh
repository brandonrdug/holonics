// Coercive material return on outgoing plus all born internal currents. Coefficients are
// represented by exact sums of numerical rank-one factors, with a separate physical-source
// error bound. M,A have grid S^2; a and unrounded forward currents have grid S^3.
__device__ __forceinline__ size_t complete_ball_words(uint32_t n) {return 12u*((size_t)2u*n+1u);}
__device__ __forceinline__ size_t complete_forward_at(uint32_t n) {return complete_ball_words(n)+4u*n;}
__device__ __forceinline__ size_t complete_source_at(uint32_t n) {return complete_forward_at(n)+10u*n;}
__device__ __forceinline__ size_t complete_extra_at(uint32_t n) {return complete_source_at(n)+36u*n+22u;}
__device__ __forceinline__ size_t complete_state_words(uint32_t n) {return (size_t)60u*n*n+22u*n+12u;}

__device__ HistoryInteger complete_power(uint32_t bit, uint32_t *slot) {
    HistoryInteger result;
    if (bit>=256u) {atomicOr(slot,REFUSED_CARRIER);return result;}
    result.limb[bit/32u]=(uint32_t)1u<<(bit%32u);return result;
}
__device__ wide complete_to_grid(const HistoryInteger &value, uint32_t shift, wide *rounds, uint32_t *slot) {
    HistoryInteger result;
    if (value.overflow || shift>=256u) {atomicOr(slot,REFUSED_CARRIER);return 0;}
    bool discarded=false;
    for (uint32_t bit=0;bit<256u;++bit) if ((value.limb[bit/32u]>>(bit%32u))&1u) {
        if (bit<shift) discarded=true;
        else result.limb[(bit-shift)/32u]|=(uint32_t)1u<<((bit-shift)%32u);
    }
    result.negative=value.negative && !result.is_zero();
    if (discarded) *rounds=add_checked(*rounds,1,slot);
    return history_narrow(result,slot);
}
__device__ HistoryInteger complete_divide(
    const HistoryInteger &numerator,const HistoryInteger &denominator,wide *rounds,uint32_t *slot
) {
    HistoryInteger result;
    if (numerator.overflow || denominator.overflow || denominator.negative || denominator.is_zero()) {
        atomicOr(slot,REFUSED_CARRIER);return result;
    }
    // The extra limb holds the doubled remainder even when the divisor fills all 256 bits.
    ExactInteger<9> remainder, divisor;
    for (uint32_t i=0;i<8u;++i) divisor.limb[i]=denominator.limb[i];
    for (int bit=255;bit>=0;--bit) {
        uint32_t carry=(numerator.limb[bit/32]>>(bit%32))&1u;
        for (uint32_t i=0;i<9u;++i) {uint32_t next=remainder.limb[i]>>31;remainder.limb[i]=(remainder.limb[i]<<1)|carry;carry=next;}
        if (compare_magnitude(remainder,divisor)>=0) {
            remainder=subtract_magnitude(remainder,divisor);
            result.limb[bit/32]|=(uint32_t)1u<<(bit%32);
        }
    }
    if (!remainder.is_zero()) *rounds=add_checked(*rounds,1,slot);
    result.negative=numerator.negative && !result.is_zero();return result;
}
__device__ __forceinline__ void complete_complex_product(
    const HistoryInteger &ar,const HistoryInteger &ai,const HistoryInteger &br,const HistoryInteger &bi,
    HistoryInteger &real,HistoryInteger &imaginary
) {real=ar*br-ai*bi;imaginary=ar*bi+ai*br;}
__device__ __forceinline__ wide complete_norm(const wide *values,uint32_t count,uint32_t *slot) {
    HistoryInteger sum;
    for(uint32_t i=0;i<count;++i) {HistoryInteger a=history_integer(values[i]);sum=sum+a*a;}
    return history_norm_ceiling(sum,slot);
}
__device__ wide complete_forward_error(wide et,wide nt,const int64_t *source,uint32_t D,uint32_t grain,wide rounding,uint32_t *slot) {
    wide ex=((const wide *)(source+6u*D+16u))[0], nx=((const wide *)(source+6u*D+20u))[0];
    if(et<0 || nt<0 || ex<0 || nx<0) {atomicOr(slot,REFUSED_MALFORMED);return 0;}
    return add_checked(rounding,add_checked(ft_ceil_product(et,add_checked(nx,ex,slot),grain,slot),
        ft_ceil_product(nt,ex,grain,slot),slot),slot);
}

// Evaluate the current coefficient expression at an older source. These are already-created
// immutable parameter factors, not repetitions of their original learning operations. Each row
// uses chronological addition order. No continuing parameter is written by this receiver.
extern "C" __global__ void section_complete_material_source_current(
    const int64_t *source_report,const int64_t *tail,uint32_t tail_count,uint32_t nodes,
    int64_t *out_lo,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x) return;
    if(upstream_refused(census,lineage,lineage_count,slot)) return;
    uint32_t D=6u*nodes;
    size_t forward=complete_forward_at(nodes), feature=complete_source_at(nodes), beta_at=complete_ball_words(nodes);
    for(uint32_t row=threadIdx.x;row<nodes;row+=blockDim.x) {
    HistoryInteger real=history_read_integer(source_report+forward+10u*row,slot);
    HistoryInteger imaginary=history_read_integer(source_report+forward+10u*row+5u,slot);
    for(uint32_t i=0;i<tail_count;++i) {
        const int64_t *increment=(const int64_t *)(uintptr_t)(uint64_t)tail[2u*i];
        const int64_t *origin=(const int64_t *)(uintptr_t)(uint64_t)tail[2u*i+1u];
        HistoryInteger kr,ki,dr,di;
        history_pairing_value(origin+feature,source_report+feature,D,kr,ki,slot);
        const wide *beta=(const wide *)(increment+beta_at);
        complete_complex_product(history_integer(beta[2u*row]),history_integer(beta[2u*row+1u]),kr,ki,dr,di);
        real=real+dr;imaginary=imaginary+di;
    }
    history_write_integer(real,out_lo+10u*row,out_hi+10u*row,slot);
    history_write_integer(imaginary,out_lo+10u*row+5u,out_hi+10u*row+5u,slot);
    }
}

extern "C" __global__ void section_complete_material_source_reading(
    const int64_t *state,const int64_t *source_report,const int64_t *refreshed,uint32_t nodes,uint32_t grain,
    wide *out_lo,wide *out_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x) return;
    if(upstream_refused(census,lineage,lineage_count,slot)) return;
    size_t extra=complete_state_words(nodes)-4u;
    const wide *bounds=(const wide *)(state+extra);
    const int64_t *exact=refreshed?refreshed:source_report+complete_forward_at(nodes);
    wide rounds=0;
    for(uint32_t i=0;i<2u*nodes;++i) out_lo[i]=out_hi[i]=complete_to_grid(history_read_integer(exact+5u*i,slot),2u*grain,&rounds,slot);
    out_lo[2u*nodes]=out_hi[2u*nodes]=complete_forward_error(bounds[0],bounds[1],source_report+complete_source_at(nodes),6u*nodes,grain,rounds,slot);
}

__device__ void complete_material_transport_prepare(
    const int64_t *state,const int64_t *origin_report,const int64_t *refreshed,
    const int64_t *query,const int64_t *origin,const int64_t *incoming,
    const int64_t *frame,const int64_t *origin_frame,const int64_t *covariance,
    const wide *before,const wide *current,uint32_t nodes,uint32_t linked,uint32_t grain,uint64_t occurrence,
    int64_t *proposal_lo,int64_t *proposal_hi,int64_t *report_lo,int64_t *report_hi,wide *scratch,uint32_t *slot
) {
    const uint32_t D=6u*nodes,R=2u*nodes;
    const size_t ga=2u*D+8u, coefficients=(size_t)R*(D/2u), matrix_words=5u*coefficients;
    const size_t m_at=ga,a_at=ga+matrix_words,offset_at=a_at+matrix_words;
    const size_t state_extra=offset_at+5u*R;
    const size_t stride=(size_t)R+1u, beta_at=complete_ball_words(nodes), forward_at=complete_forward_at(nodes);
    const size_t feature_at=complete_source_at(nodes),extra_at=complete_extra_at(nodes);
    for(size_t i=0;i<extra_at+10u;++i) report_lo[i]=report_hi[i]=0;
    field_current_history_source_prepare(query,origin,incoming,frame,origin_frame,covariance,before,current,
        state,nodes,linked,grain,occurrence,proposal_lo,proposal_hi,report_lo+feature_at,report_hi+feature_at,scratch,slot);
    if(*slot) return;
    for(size_t i=ga;i<complete_state_words(nodes);++i) proposal_lo[i]=proposal_hi[i]=state[i];
    wide old_et=((const wide *)(state+state_extra))[0],old_nt=((const wide *)(state+state_extra))[1];
    if(old_et<0 || old_nt<0 || (linked && !origin_report)) {atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *report=(wide *)report_lo,*upper=(wide *)report_hi;
    wide *observed=report+2u*stride;
    wide target_error=0;
    const wide scale=(wide)1<<grain;
    for(uint32_t i=0;i<R;++i) {
        const int64_t *input=incoming+3u*(i/2u);
        wide floor=signed_product_divide_2((wide)input[i%2u],scale/2,(wide)input[2],0,slot);
        wide ceil=signed_product_divide_2((wide)input[i%2u],scale/2,(wide)input[2],1,slot);
        observed[i]=input[i%2u]<0?ceil:floor;
        if(floor!=ceil) target_error=add_checked(target_error,1,slot);
    }
    observed[R]=target_error;
    wide target_norm=complete_norm(observed,R,slot),old_rounds=0,beta_rounds=0,new_rounds=0;
    wide *beta=(wide *)(report_lo+beta_at);
    wide next_et=old_et,next_nt=old_nt,numeric_error=0;
    if(linked) {
        const int64_t *source=origin_report+feature_at;
        const int64_t *exact=refreshed?refreshed:origin_report+forward_at;
        const wide *old_forward=(const wide *)origin_report;
        HistoryInteger denominator=history_read_integer(source+6u*D+10u,slot)+complete_power(2u*grain,slot);
        wide *current_source=report+stride;
        for(uint32_t i=0;i<R;++i)
            current_source[i]=complete_to_grid(history_read_integer(exact+5u*i,slot),2u*grain,&old_rounds,slot);
        current_source[R]=complete_forward_error(old_et,old_nt,source,D,grain,old_rounds,slot);
        for(uint32_t i=0;i<R;++i) {
            report[3u*stride+i]=sub_checked(observed[i],old_forward[i],slot);
            report[4u*stride+i]=sub_checked(current_source[i],old_forward[i],slot);
            report[5u*stride+i]=sub_checked(observed[i],current_source[i],slot);
            HistoryInteger numerator=history_integer(report[5u*stride+i])*complete_power(2u*grain,slot);
            beta[i]=history_narrow(complete_divide(numerator,denominator,&beta_rounds,slot),slot);
        }
        report[3u*stride+R]=add_checked(target_error,old_forward[R],slot);
        report[4u*stride+R]=add_checked(current_source[R],old_forward[R],slot);
        report[5u*stride+R]=add_checked(target_error,current_source[R],slot);
        wide source_error=((const wide *)(source+6u*D+16u))[0];
        wide source_norm=((const wide *)(source+6u*D+20u))[0];
        numeric_error=add_checked(div_ceil(old_rounds,2,slot),ft_ceil_product(beta_rounds,source_norm,grain,slot),slot);
        next_et=add_checked(old_et,add_checked(numeric_error,add_checked(div_ceil(target_error,2,slot),
            ft_ceil_product(add_checked(old_nt,target_norm,slot),source_error,grain,slot),slot),slot),slot);
        next_nt=add_checked(old_nt,ft_ceil_product(complete_norm(beta,R,slot),source_norm,grain,slot),slot);
        const wide *vectors=(const wide *)source;
        const bool phase=((uint64_t)source[6u*D+19u])&1u;
        for(uint32_t row=0;row<nodes;++row) {
            HistoryInteger br=history_integer(beta[2u*row]),bi=history_integer(beta[2u*row+1u]);
            for(uint32_t column=0;column<D/2u;++column) {
                size_t cell=2u*((size_t)row*(D/2u)+column);
                HistoryInteger dr,di;
                complete_complex_product(br,bi,history_integer(vectors[2u*column]),-history_integer(vectors[2u*column+1u]),dr,di);
                history_write_integer(history_read_integer(state+m_at+5u*cell,slot)+dr,proposal_lo+m_at+5u*cell,proposal_hi+m_at+5u*cell,slot);
                history_write_integer(history_read_integer(state+m_at+5u*(cell+1u),slot)+di,proposal_lo+m_at+5u*(cell+1u),proposal_hi+m_at+5u*(cell+1u),slot);
                complete_complex_product(br,bi,history_integer(vectors[2u*D+2u*column]),-history_integer(vectors[2u*D+2u*column+1u]),dr,di);
                if(phase) {dr=-dr;di=-di;}
                history_write_integer(history_read_integer(state+a_at+5u*cell,slot)+dr,proposal_lo+a_at+5u*cell,proposal_hi+a_at+5u*cell,slot);
                history_write_integer(history_read_integer(state+a_at+5u*(cell+1u),slot)+di,proposal_lo+a_at+5u*(cell+1u),proposal_hi+a_at+5u*(cell+1u),slot);
            }
            HistoryInteger dr,di;
            complete_complex_product(br,bi,history_read_integer(source+6u*D,slot),-history_read_integer(source+6u*D+5u,slot),dr,di);
            if(phase) {dr=-dr;di=-di;}
            history_write_integer(history_read_integer(state+offset_at+10u*row,slot)+dr,proposal_lo+offset_at+10u*row,proposal_hi+offset_at+10u*row,slot);
            history_write_integer(history_read_integer(state+offset_at+10u*row+5u,slot)+di,proposal_lo+offset_at+10u*row+5u,proposal_hi+offset_at+10u*row+5u,slot);
        }
    }
    ((wide *)(proposal_lo+state_extra))[0]=((wide *)(proposal_hi+state_extra))[0]=next_et;
    ((wide *)(proposal_lo+state_extra))[1]=((wide *)(proposal_hi+state_extra))[1]=next_nt;
    if(*slot) return;
    const wide *source=(const wide *)(report_lo+feature_at);
    for(uint32_t row=0;row<nodes;++row) {
        HistoryInteger real,imaginary,internal_real=-history_read_integer(proposal_lo+offset_at+10u*row,slot);
        HistoryInteger internal_imaginary=-history_read_integer(proposal_lo+offset_at+10u*row+5u,slot);
        for(uint32_t column=0;column<D/2u;++column) {
            size_t cell=2u*((size_t)row*(D/2u)+column);HistoryInteger dr,di;
            complete_complex_product(history_read_integer(proposal_lo+m_at+5u*cell,slot),history_read_integer(proposal_lo+m_at+5u*(cell+1u),slot),
                history_integer(source[2u*column]),history_integer(source[2u*column+1u]),dr,di);
            real=real+dr;imaginary=imaginary+di;
            complete_complex_product(history_read_integer(proposal_lo+a_at+5u*cell,slot),history_read_integer(proposal_lo+a_at+5u*(cell+1u),slot),
                history_integer(source[D+2u*column]),history_integer(source[D+2u*column+1u]),dr,di);
            internal_real=internal_real+dr;internal_imaginary=internal_imaginary+di;
        }
        if(occurrence&1u) {internal_real=-internal_real;internal_imaginary=-internal_imaginary;}
        real=real+internal_real;imaginary=imaginary+internal_imaginary;
        history_write_integer(real,report_lo+forward_at+10u*row,report_hi+forward_at+10u*row,slot);
        history_write_integer(imaginary,report_lo+forward_at+10u*row+5u,report_hi+forward_at+10u*row+5u,slot);
        report[2u*row]=complete_to_grid(real,2u*grain,&new_rounds,slot);
        report[2u*row+1u]=complete_to_grid(imaginary,2u*grain,&new_rounds,slot);
    }
    report[R]=complete_forward_error(next_et,next_nt,report_lo+feature_at,D,grain,new_rounds,slot);
    wide *extra=(wide *)(report_lo+extra_at);
    extra[0]=next_et;extra[1]=next_nt;extra[2]=numeric_error;extra[3]=old_rounds;extra[4]=new_rounds;
    // Exact-forward and geometry writes already set both endpoints. Finish the ordinary wide
    // report blocks and beta, without treating a numerical representative as an exact current.
    for(size_t i=0;i<complete_ball_words(nodes)+4u*nodes;++i) report_hi[i]=report_lo[i];
    for(size_t i=extra_at;i<extra_at+10u;++i) report_hi[i]=report_lo[i];
}
