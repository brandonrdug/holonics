// A chronological word of paired reflections on actual contact joins. Only fresh carriers
// are written. The exact overlap and local before-current remain available for its adjoint.
// |g|^2 b uses two full overlap integers and one wide current, plus a guard limb for sums.
using PropagationInteger=ExactInteger<2*HistoryInteger::LIMBS+sizeof(wide)/sizeof(uint32_t)+1>;
constexpr size_t CP_WIDE_WORDS=sizeof(wide)/sizeof(int64_t);
constexpr size_t CP_HISTORY_WORDS=HistoryInteger::BITS/(sizeof(int64_t)*CHAR_BIT)+1;
constexpr size_t CP_BEFORE=2;
constexpr size_t CP_OVERLAP=CP_BEFORE+4*CP_WIDE_WORDS;
constexpr size_t CP_RADIUS=CP_OVERLAP+2*CP_HISTORY_WORDS;
constexpr size_t CP_OVERLAP_ERROR=CP_RADIUS+CP_WIDE_WORDS;
constexpr size_t CP_ROUNDS=(CP_OVERLAP_ERROR+CP_HISTORY_WORDS+CP_WIDE_WORDS-1)/CP_WIDE_WORDS*CP_WIDE_WORDS;
constexpr size_t CP_TRACE_WORDS=CP_ROUNDS+CP_WIDE_WORDS;

extern "C" __global__ void section_field_operative_input_current_add(
    const wide *before,const wide *delta,uint32_t count,wide *lo,wide *hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    size_t at=blockIdx.x*blockDim.x+threadIdx.x;
    if(at<2u*(size_t)count)lo[at]=hi[at]=add_checked(before[at],delta[at],slot);
    if(!count && !at){lo[0]=hi[0]=0;lo[1]=hi[1]=0;}
}

__device__ PropagationInteger cp_lift(const HistoryInteger &value){
    PropagationInteger out;for(int i=0;i<HistoryInteger::LIMBS;++i)out.limb[i]=value.limb[i];
    out.negative=value.negative;out.overflow=value.overflow;return out;
}
__device__ wide cp_quotient(const PropagationInteger &num,const PropagationInteger &den,wide *rounds,uint32_t *slot){
    bool omitted=false;PropagationInteger q=exact_divide_positive(num,den,&omitted);
    if(q.overflow){atomicOr(slot,REFUSED_CARRIER);return 0;}
    HistoryInteger small;
    for(int i=0;i<PropagationInteger::LIMBS;++i){
        if(i<HistoryInteger::LIMBS)small.limb[i]=q.limb[i];else if(q.limb[i])small.overflow=true;
    }
    small.negative=q.negative;
    if(omitted)*rounds=add_checked(*rounds,1,slot);
    return history_narrow(small,slot);
}
__device__ wide cp_family_radius(wide initial,const HistoryInteger &overlap_error,wide norm,
    const PropagationInteger &scale_squared,wide rounding,uint32_t *slot){
    wide omitted=0;
    wide difference=cp_quotient(PropagationInteger(2)*cp_lift(overlap_error)*cp_lift(history_integer(norm)),
        scale_squared,&omitted,slot);
    return add_checked(initial,add_checked(add_checked(difference,omitted,slot),rounding,slot),slot);
}

extern "C" __global__ void section_field_causal_contact_propagation(
    const int64_t *births,const int64_t *map_wire,const int64_t *input_wire,const int64_t *bounds_wire,
    uint32_t d,uint32_t count,uint32_t grain,
    int64_t *current_lo,int64_t *current_hi,int64_t *bounds_lo,int64_t *bounds_hi,
    int64_t *trace_lo,int64_t *trace_hi,int64_t *summary_lo,int64_t *summary_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x || threadIdx.x || upstream_refused(census,lineage,lineage_count,slot))return;
    const wide *D=(const wide *)map_wire,*input=(const wide *)input_wire,*bounds=(const wide *)bounds_wire;
    wide *current=(wide *)current_lo,*output_bounds=(wide *)bounds_lo;
    if(!d || (d&1u) || grain<1u || grain>120u || bounds[0]<0 || bounds[1]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide norm=0,rounds=0,joins=0;HistoryInteger errors;
    for(size_t i=0;i<2u*(size_t)(count?count:1u);++i){current[i]=count?input[i]:0;if(count)norm=add_checked(norm,of_magnitude(magnitude(input[i]),false,slot),slot);}
    for(size_t i=0;i<CP_TRACE_WORDS*(count?count:1u);++i)trace_lo[i]=trace_hi[i]=0;
    PropagationInteger unit=cp_lift(complete_power(2u*grain,slot)),unit_square=unit*unit;
    for(uint32_t after=0;after<count && !*slot;++after){
        int64_t source=births[2u*(size_t)after],receiving=births[2u*(size_t)after+1u];
        if(source<0 || source>=receiving || (after && births[2u*(size_t)(after-1u)+1u]>=receiving)){
            atomicOr(slot,REFUSED_MALFORMED);break;
        }
        int64_t *trace=trace_lo+CP_TRACE_WORDS*after;
        trace[0]=-1;trace[1]=receiving;
        // Find the exact joining occurrence inside the already admitted prefix on the device.
        uint32_t lo=0,hi=after;
        while(lo<hi){uint32_t mid=lo+(hi-lo)/2u;if(births[2u*(size_t)mid+1u]<source)lo=mid+1u;else hi=mid;}
        if(lo==after || births[2u*(size_t)lo+1u]!=source)continue;
        uint32_t before=lo;trace[0]=before;++joins;
        wide *prior=(wide *)(trace+CP_BEFORE);
        for(uint32_t j=0;j<2u;++j){prior[j]=current[2u*before+j];prior[2u+j]=current[2u*after+j];}
        ((wide *)(trace+CP_RADIUS))[0]=cp_family_radius(bounds[1],errors,norm,unit,rounds,slot);
        HistoryInteger re,im;wide contact_norm=0;
        for(uint32_t j=0;j<d;j+=2u){
            history_complex_add_product(re,im,D[(size_t)before*d+j],D[(size_t)before*d+j+1u],D[(size_t)after*d+j],D[(size_t)after*d+j+1u],true);
            for(uint32_t q=0;q<2u;++q){
                contact_norm=add_checked(contact_norm,of_magnitude(magnitude(D[(size_t)before*d+j+q]),false,slot),slot);
                contact_norm=add_checked(contact_norm,of_magnitude(magnitude(D[(size_t)after*d+j+q]),false,slot),slot);
            }
        }
        history_write_integer(re,trace+CP_OVERLAP,trace+CP_OVERLAP,slot);
        history_write_integer(im,trace+CP_OVERLAP+CP_HISTORY_WORDS,trace+CP_OVERLAP+CP_HISTORY_WORDS,slot);
        HistoryInteger local_error=history_integer(contact_norm)*history_integer(bounds[0])+history_integer(bounds[0])*history_integer(bounds[0]);
        history_write_integer(local_error,trace+CP_OVERLAP_ERROR,trace+CP_OVERLAP_ERROR,slot);errors=errors+local_error;
        PropagationInteger gr=cp_lift(re),gi=cp_lift(im),square=gr*gr+gi*gi;
        PropagationInteger den=unit_square+square,diagonal=unit_square-square,cross=PropagationInteger(2)*unit;
        PropagationInteger ar=cp_lift(history_integer(prior[0])),ai=cp_lift(history_integer(prior[1])),
            br=cp_lift(history_integer(prior[2])),bi=cp_lift(history_integer(prior[3]));
        wide omitted=0;
        current[2u*before]=cp_quotient(diagonal*ar-cross*(gr*br-gi*bi),den,&omitted,slot);
        current[2u*before+1u]=cp_quotient(diagonal*ai-cross*(gr*bi+gi*br),den,&omitted,slot);
        current[2u*after]=cp_quotient(cross*(gr*ar+gi*ai)+diagonal*br,den,&omitted,slot);
        current[2u*after+1u]=cp_quotient(cross*(gr*ai-gi*ar)+diagonal*bi,den,&omitted,slot);
        ((wide *)(trace+CP_ROUNDS))[0]=omitted;rounds=add_checked(rounds,omitted,slot);
    }
    output_bounds[0]=bounds[0];output_bounds[1]=cp_family_radius(bounds[1],errors,norm,unit,rounds,slot);
    ((wide *)summary_lo)[0]=joins;((wide *)summary_lo)[1]=rounds;
    if(*slot)return;
    for(size_t i=0;i<4u*(size_t)(count?count:1u);++i)current_hi[i]=current_lo[i];
    for(size_t i=0;i<4u;++i){bounds_hi[i]=bounds_lo[i];summary_hi[i]=summary_lo[i];}
    for(size_t i=0;i<CP_TRACE_WORDS*(count?count:1u);++i)trace_hi[i]=trace_lo[i];
}
