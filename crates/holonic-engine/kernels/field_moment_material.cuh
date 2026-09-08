// The normalized homogeneous Hermitian source is generated from the COMPLETE current.
// k_Q(x,y)=|1+<x,y>|^2/((1+||x||^2)(1+||y||^2)). No matrix population is expanded.
// A 256-bit source value plus its reference needs 257 bits; the products need 514.
// Seventeen 32-bit limbs cover those products and the doubled division remainder.
using MomentInteger=ExactInteger<17>;
__device__ MomentInteger moment_lift(const HistoryInteger &a) {
    MomentInteger b;for(uint32_t j=0;j<8;++j)b.limb[j]=a.limb[j];b.negative=a.negative;b.overflow=a.overflow;return b;
}
__device__ MomentInteger moment_twice(const MomentInteger &a) {
    MomentInteger b=a;uint32_t carry=0;
    for(uint32_t j=0;j<17;++j){uint32_t next=b.limb[j]>>31;b.limb[j]=(b.limb[j]<<1)|carry;carry=next;}
    b.overflow=b.overflow || carry;return b;
}
__device__ void moment_pair(const int64_t *a,const int64_t *b,uint32_t D,uint32_t grain,
    MomentInteger &numerator,MomentInteger &denominator,uint32_t *slot) {
    if(grain<1 || grain>120 || a[6u*D+15u]!=(int64_t)grain || b[6u*D+15u]!=(int64_t)grain){atomicOr(slot,REFUSED_MALFORMED);return;}
    HistoryInteger re,im;history_pairing_value(a,b,D,re,im,slot);
    HistoryInteger na=history_read_integer(a+6u*D+10u,slot),nb=history_read_integer(b+6u*D+10u,slot);
    if(*slot || re.overflow || im.overflow || na.negative || nb.negative){atomicOr(slot,REFUSED_CARRIER);return;}
    MomentInteger unit=moment_lift(complete_power(2u*grain,slot));
    MomentInteger real=moment_lift(re)+unit,imaginary=moment_lift(im);
    numerator=real*real+imaginary*imaginary;
    denominator=(moment_lift(na)+unit)*(moment_lift(nb)+unit);
    if(numerator.overflow || denominator.overflow || denominator.is_zero() || numerator.negative || denominator.negative || denominator<numerator)
        atomicOr(slot,REFUSED_CARRIER);
}
__device__ wide moment_kernel_grid(const int64_t *a,const int64_t *b,uint32_t D,uint32_t grain,bool *remainder,uint32_t *slot) {
    MomentInteger n,d;moment_pair(a,b,D,grain,n,d,slot);if(*slot)return 0;
    wide q=0;
    if(n==d){*remainder=false;return (wide)((uwide)1u<<grain);}
    for(int bit=(int)grain-1;bit>=0;--bit){
        n=moment_twice(n);if(n.overflow){atomicOr(slot,REFUSED_CARRIER);return 0;}
        if(n>=d){n=n-d;q|=(wide)((uwide)1u<<bit);}
    }
    *remainder=!n.is_zero();return q;
}
__device__ __forceinline__ size_t moment_beta_at(uint32_t n){return 12u*(2u*(size_t)n+1u);}
__device__ __forceinline__ size_t moment_source_at(uint32_t n){return moment_beta_at(n)+4u*n;}
__device__ __forceinline__ size_t moment_raw_at(uint32_t n){return moment_source_at(n)+36u*n+22u;}
__device__ __forceinline__ size_t moment_remainder_at(uint32_t n){return moment_raw_at(n)+30u*n;}
__device__ __forceinline__ size_t moment_extra_at(uint32_t n){return moment_remainder_at(n)+2u*n;}
__device__ __forceinline__ size_t moment_state_words(uint32_t n){return 12u*(size_t)n+12u;}
__device__ wide moment_source_error(const int64_t *source,uint32_t D,uint32_t grain,uint32_t *slot){
    wide e=((const wide *)(source+6u*D+16u))[0],S=(wide)((uwide)1u<<grain);
    if(e<0){atomicOr(slot,REFUSED_MALFORMED);return 0;}
    return e>S ? 2*S : product_checked(2,e,slot);
}

// Oriented evaluation defect: the exact numerical kernel is at least its grid floor.
// Positive/negative beta sums bound its componentwise effect, in the S^2 chart.
__device__ void moment_evaluate_rows(const int64_t *table,uint32_t count,const int64_t *weights,
    const int64_t *base,const wide *new_beta,uint32_t nodes,int64_t *lo,int64_t *hi,uint32_t *slot) {
    uint32_t R=2u*nodes;
    for(uint32_t j=threadIdx.x;j<R;j+=blockDim.x){
        HistoryInteger sum=base?history_read_integer(base+5u*j,slot):HistoryInteger();
        HistoryInteger positive=base?history_read_integer(base+5u*(R+j),slot):HistoryInteger();
        HistoryInteger negative=base?history_read_integer(base+5u*(2u*R+j),slot):HistoryInteger();
        for(uint32_t i=0;i<count+(new_beta?1u:0u);++i){
            const wide *beta=i<count ? (const wide *)((const int64_t *)(uintptr_t)(uint64_t)table[2u*i]+moment_beta_at(nodes)) : new_beta;
            wide b=beta[j],k=((const wide *)(weights+4u*i))[0];
            sum=sum+history_integer(b)*history_integer(k);
            if(weights[4u*i+2u]){
                if(b>=0)positive=positive+history_integer(b);else negative=negative-history_integer(b);
            }
        }
        history_write_integer(sum,lo+5u*j,hi+5u*j,slot);
        history_write_integer(positive,lo+5u*(R+j),hi+5u*(R+j),slot);
        history_write_integer(negative,lo+5u*(2u*R+j),hi+5u*(2u*R+j),slot);
    }
}
__device__ wide moment_read_evaluation(const int64_t *raw,uint32_t R,uint32_t grain,wide *out,
    wide *dot_rounds,uint32_t *slot){
    wide error=0;
    for(uint32_t j=0;j<R;++j){
        out[j]=complete_to_grid(history_read_integer(raw+5u*j,slot),grain,dot_rounds,slot);
        HistoryInteger a=history_read_integer(raw+5u*(R+j),slot),b=history_read_integer(raw+5u*(2u*R+j),slot);
        if(a.negative || b.negative){atomicOr(slot,REFUSED_MALFORMED);return 0;}
        wide rounds=0,value=complete_to_grid(a>=b?a:b,grain,&rounds,slot);
        error=add_checked(error,add_checked(value,rounds,slot),slot);
    }
    return add_checked(error,*dot_rounds,slot);
}

extern "C" __global__ void section_moment_source_current(
    const int64_t *source,const int64_t *table,uint32_t count,uint32_t nodes,uint32_t grain,
    int64_t *weights,int64_t *lo,int64_t *hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    for(uint32_t i=threadIdx.x;i<count;i+=blockDim.x){
        const int64_t *origin=(const int64_t *)(uintptr_t)(uint64_t)table[2u*i+1u];
        bool remainder=false;wide k=moment_kernel_grid(origin+moment_source_at(nodes),source+moment_source_at(nodes),6u*nodes,grain,&remainder,slot);
        ((wide *)(weights+4u*i))[0]=k;weights[4u*i+2u]=remainder;weights[4u*i+3u]=0;
    }
    __syncthreads();if(*slot)return;
    moment_evaluate_rows(table,count,weights,source+moment_raw_at(nodes),nullptr,nodes,lo,hi,slot);
}

__device__ void moment_material_transport_prepare(
    const int64_t *state,const int64_t *origin_report,const int64_t *refreshed,const int64_t *table,uint32_t count,int64_t *weights,
    const int64_t *query,const int64_t *origin,const int64_t *incoming,const int64_t *frame,const int64_t *origin_frame,
    const int64_t *covariance,const wide *before,const wide *current,uint32_t nodes,uint32_t linked,uint32_t grain,uint64_t occurrence,
    int64_t *next_lo,int64_t *next_hi,int64_t *report_lo,int64_t *report_hi,wide *scratch,uint32_t *slot
) {
    uint32_t R=2u*nodes,D=6u*nodes,stride=R+1u;size_t ga=2u*D+8u;
    wide *report=(wide *)report_lo,*beta=(wide *)(report_lo+moment_beta_at(nodes));
    if(threadIdx.x==0){
        field_current_history_source_prepare(query,origin,incoming,frame,origin_frame,covariance,before,current,state,
            nodes,linked,grain,occurrence,next_lo,next_hi,report_lo+moment_source_at(nodes),report_hi+moment_source_at(nodes),scratch,slot);
        for(size_t i=0;i<moment_source_at(nodes);++i)report_lo[i]=report_hi[i]=0;
        for(uint32_t j=0;j<R;++j)report_lo[moment_remainder_at(nodes)+j]=report_hi[moment_remainder_at(nodes)+j]=0;
        const wide *bounds=(const wide *)(state+ga);wide et=bounds[0],nt=bounds[1],target_error=0;
        if(et<0 || nt<0 || (linked && !origin_report))atomicOr(slot,REFUSED_MALFORMED);
        wide S=(wide)((uwide)1u<<grain);
        for(uint32_t j=0;j<R && !*slot;++j){
            const int64_t *in=incoming+3u*(j/2u);
            wide lower=signed_product_divide_2(in[j%2u],S/2,in[2],0,slot),upper=signed_product_divide_2(in[j%2u],S/2,in[2],1,slot);
            report[2u*stride+j]=in[j%2u]<0?upper:lower;
            if(lower!=upper)target_error=add_checked(target_error,1,slot);
        }
        report[3u*stride-1u]=target_error;
        wide eval_error=0,dot_rounds=0,beta_halves=0;
        if(linked && !*slot){
            wide e=moment_source_error(origin_report+moment_source_at(nodes),D,grain,slot);
            eval_error=moment_read_evaluation(refreshed?refreshed:origin_report+moment_raw_at(nodes),R,grain,report+stride,&dot_rounds,slot);
            report[2u*stride-1u]=add_checked(et,add_checked(ft_ceil_product(nt,e,grain,slot),eval_error,slot),slot);
            const wide *old=(const wide *)origin_report;
            for(uint32_t j=0;j<R;++j){
                report[3u*stride+j]=sub_checked(report[2u*stride+j],old[j],slot);
                report[4u*stride+j]=sub_checked(report[stride+j],old[j],slot);
                wide r=sub_checked(report[2u*stride+j],report[stride+j],slot);report[5u*stride+j]=r;
                beta[j]=r/2;
                int64_t rem=-(int64_t)(r%2);report_lo[moment_remainder_at(nodes)+j]=report_hi[moment_remainder_at(nodes)+j]=rem;
                if(rem)++beta_halves;
            }
            report[4u*stride-1u]=add_checked(target_error,old[R],slot);
            report[5u*stride-1u]=add_checked(report[2u*stride-1u],old[R],slot);
            report[6u*stride-1u]=add_checked(target_error,report[2u*stride-1u],slot);
            wide y_norm=complete_norm(report+2u*stride,R,slot);
            et=add_checked(et,add_checked(div_ceil(add_checked(target_error,eval_error,slot),2,slot),
                add_checked(div_ceil(beta_halves,2,slot),ft_ceil_product(add_checked(nt,y_norm,slot),e,grain,slot),slot),slot),slot);
            // ||Mhat + beta g*||_F^2 = ||Mhat||_F^2
            //     + 2 Re <Mhat g,beta> + ||beta||^2, since ||g||_F=1.
            // Keep the signed cross-current before taking an upper square root.
            // The numerical source evaluation contributes at most 2 e_eval ||beta||.
            wide beta_norm=complete_norm(beta,R,slot);
            HistoryInteger square=history_integer(nt)*history_integer(nt)
                +HistoryInteger(2)*history_integer(eval_error)*history_integer(beta_norm);
            for(uint32_t j=0;j<R;++j){
                HistoryInteger b=history_integer(beta[j]);
                square=square+HistoryInteger(2)*history_integer(report[stride+j])*b+b*b;
            }
            wide energy_norm=history_norm_ceiling(square,slot);
            wide triangle_norm=add_checked(nt,beta_norm,slot);
            nt=energy_norm<triangle_norm?energy_norm:triangle_norm;
        }
        ((wide *)(next_lo+ga))[0]=((wide *)(next_hi+ga))[0]=et;
        ((wide *)(next_lo+ga))[1]=((wide *)(next_hi+ga))[1]=nt;
        wide *extra=(wide *)(report_lo+moment_extra_at(nodes));extra[0]=et;extra[1]=nt;extra[2]=eval_error;extra[3]=beta_halves;extra[4]=0;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t i=threadIdx.x;i<count+linked;i+=blockDim.x){
        const int64_t *source=i<count?(const int64_t *)(uintptr_t)(uint64_t)table[2u*i+1u]:origin_report;
        bool remainder=false;wide k=moment_kernel_grid(source+moment_source_at(nodes),report_lo+moment_source_at(nodes),D,grain,&remainder,slot);
        ((wide *)(weights+4u*i))[0]=k;weights[4u*i+2u]=remainder;weights[4u*i+3u]=0;
    }
    __syncthreads();if(*slot)return;
    moment_evaluate_rows(table,count,weights,nullptr,linked?beta:nullptr,nodes,report_lo+moment_raw_at(nodes),report_hi+moment_raw_at(nodes),slot);
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        wide rounds=0;wide error=moment_read_evaluation(report_lo+moment_raw_at(nodes),R,grain,report,&rounds,slot);
        const wide *bounds=(const wide *)(next_lo+ga);
        wide e=moment_source_error(report_lo+moment_source_at(nodes),D,grain,slot);
        report[R]=add_checked(bounds[0],add_checked(ft_ceil_product(bounds[1],e,grain,slot),error,slot),slot);
        ((wide *)(report_lo+moment_extra_at(nodes)))[4]=error;
        if(*slot)return;
        for(size_t i=0;i<moment_source_at(nodes);++i)report_hi[i]=report_lo[i];
        for(size_t i=moment_extra_at(nodes);i<moment_extra_at(nodes)+10u;++i)report_hi[i]=report_lo[i];
    }
}
