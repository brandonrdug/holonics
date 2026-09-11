// Exact source-plane map shared by producing comparison and conditional source attachment.
// ||(dc-dp,dc,dp)||² <= 3 (||dp||²+||dc||²), so 2r is an outward dyadic bound.
__device__ void normal_wave_source_lift(const wide *joint,uint32_t r,wide *source,uint32_t *slot){
    if(joint[2u*r]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=0;j<r;++j){
        source[j]=sub_checked(joint[r+j],joint[j],slot);
        source[r+j]=joint[r+j];source[2u*r+j]=joint[j];
    }
    source[3u*r]=product_checked(2,joint[2u*r],slot);
}
extern "C" __global__ void section_normal_wave_source(
    const int64_t *joint,const int64_t *joint_hi,uint32_t n,
    int64_t *source,int64_t *source_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!n || n>(UINT32_MAX-2u)/12u){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=0;j<2u*(4u*n+1u);++j)if(joint[j]!=joint_hi[j]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    normal_wave_source_lift((const wide *)joint,2u*n,(wide *)source,slot);
    if(*slot)return;
    for(uint32_t j=0;j<2u*(6u*n+1u);++j)source_hi[j]=source[j];
}
