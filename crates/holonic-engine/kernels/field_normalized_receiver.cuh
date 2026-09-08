// A real receiver of two retained complex-current balls. The original carriers remain held.
// Each declared group retains its complete normalized exponential face. The returned current
// is q-p and its pullback J_p(q-p), without an inherited token target or terminal tanh/deposit.
// Output is an opaque exact-word report: ten signed-wide values per coordinate, with both
// word lanes identical. Each pair is an outward interval at the declared current grain.

__device__ void normalized_interval_product(wide a,wide b,wide c,wide d,uint32_t grain,
    wide *lo,wide *hi,uint32_t *slot) {
    wide lows[4]={product_shift(a,c,grain,0,slot),product_shift(a,d,grain,0,slot),
        product_shift(b,c,grain,0,slot),product_shift(b,d,grain,0,slot)};
    wide highs[4]={product_shift(a,c,grain,1,slot),product_shift(a,d,grain,1,slot),
        product_shift(b,c,grain,1,slot),product_shift(b,d,grain,1,slot)};
    *lo=lows[0];*hi=highs[0];
    for(uint32_t i=1;i<4;++i){if(lows[i]<*lo)*lo=lows[i];if(highs[i]>*hi)*hi=highs[i];}
}

__device__ void normalized_current_face(const wide *input,uint32_t nodes,uint32_t first,
    uint32_t width,uint32_t grain,uint32_t terms,wide *output,uint32_t offset,uint32_t *slot) {
    wide radius=input[2u*nodes],unit=(wide)1<<grain;
    if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide origin=add_checked(input[2u*first],radius,slot);
    for(uint32_t j=first+1;j<first+width;++j){
        wide hi=add_checked(input[2u*j],radius,slot);if(hi>origin)origin=hi;
    }
    wide total_lo=0,total_hi=0;
    for(uint32_t j=first;j<first+width;++j){
        wide low=sub_checked(sub_checked(input[2u*j],radius,slot),origin,slot);
        wide high=sub_checked(add_checked(input[2u*j],radius,slot),origin,slot);
        wide lo,hi,unused;
        if(*slot)return;
        exp_nonpositive(low,grain,terms,&lo,&unused,slot);
        exp_nonpositive(high,grain,terms,&unused,&hi,slot);
        output[10u*j+offset]=lo;output[10u*j+offset+1u]=hi;
        total_lo=add_checked(total_lo,lo,slot);total_hi=add_checked(total_hi,hi,slot);
    }
    if(*slot)return;
    if(total_hi<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=first;j<first+width;++j){
        wide lo=output[10u*j+offset],hi=output[10u*j+offset+1u];
        lo=signed_product_divide_2(lo,unit/2,total_hi,0,slot);
        hi=total_lo ? signed_product_divide_2(hi,unit/2,total_lo,1,slot) : unit;
        if(lo<0)lo=0;if(hi>unit)hi=unit;
        output[10u*j+offset]=lo;output[10u*j+offset+1u]=hi;
    }
}

extern "C" __global__ __launch_bounds__(512) void section_field_normalized_receiver(
    const int64_t *prediction,const int64_t *observation,uint32_t nodes,uint32_t group_width,
    uint32_t grain,uint32_t terms,int64_t *out_lo,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!nodes||!group_width||nodes%group_width||grain<1||grain>120||!terms||terms==UINT32_MAX){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    uint32_t first=blockIdx.x*group_width;if(first>=nodes)return;
    const wide *p=(const wide *)prediction;
    // Every material-report family retains its actual observed current in target block two.
    const wide *q=(const wide *)observation+2u*(2u*nodes+1u);
    wide *out=(wide *)out_lo;
    normalized_current_face(p,nodes,first,group_width,grain,terms,out,0,slot);
    normalized_current_face(q,nodes,first,group_width,grain,terms,out,2,slot);
    if(*slot)return;
    // For point currents, a common additive shift is exactly invisible even when 1/group_width
    // needs a numerical interval. This proves equality of faces, never identity of occurrences.
    bool same=p[2u*nodes]==0 && q[2u*nodes]==0;
    wide common=0;
    if(same){
        common=sub_checked(p[2u*first],q[2u*first],slot);
        for(uint32_t j=first+1;j<first+group_width;++j)
            same=same && sub_checked(p[2u*j],q[2u*j],slot)==common;
    }
    wide mean_lo=0,mean_hi=0,min_lo=0,max_hi=0;
    for(uint32_t j=first;j<first+group_width;++j){
        wide *o=out+10u*j;
        o[4]=same?0:sub_checked(o[2],o[1],slot);
        o[5]=same?0:sub_checked(o[3],o[0],slot);
        wide lo,hi;normalized_interval_product(o[0],o[1],o[4],o[5],grain,&lo,&hi,slot);
        mean_lo=add_checked(mean_lo,lo,slot);mean_hi=add_checked(mean_hi,hi,slot);
        if(j==first||o[4]<min_lo)min_lo=o[4];if(j==first||o[5]>max_hi)max_hi=o[5];
    }
    // The exact p is a simplex section, so its weighted mean lies in the residual's hull.
    if(mean_lo<min_lo)mean_lo=min_lo;if(mean_hi>max_hi)mean_hi=max_hi;
    for(uint32_t j=first;j<first+group_width;++j){
        wide *o=out+10u*j;
        o[8]=sub_checked(o[4],mean_hi,slot);o[9]=sub_checked(o[5],mean_lo,slot);
        normalized_interval_product(o[0],o[1],o[8],o[9],grain,o+6,o+7,slot);
    }
    if(*slot)return;
    for(uint32_t j=first*20u;j<(first+group_width)*20u;++j)out_hi[j]=out_lo[j];
}
