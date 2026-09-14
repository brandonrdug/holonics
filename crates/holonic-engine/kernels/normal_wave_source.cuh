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
    const int64_t *joint,const int64_t *joint_hi,uint32_t n,uint32_t grain,uint32_t receiver,
    int64_t *source,int64_t *source_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!n || n>(UINT32_MAX-2u)/12u||receiver>1u||grain<1||grain>120){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=0;j<2u*(4u*n+1u);++j)if(joint[j]!=joint_hi[j]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    normal_wave_source_lift((const wide *)joint,2u*n,(wide *)source,slot);
    if(receiver&&! *slot){
        // UnitRealSum is an affine section of the orthogonal real-sum quotient
        // on each p,c block. Projection has norm one; the existing 2R bound
        // for phi still applies. Retain its constants and directed rounding.
        const wide *z=(const wide *)joint;wide *a=(wide *)source;
        wide ps=0,cs=0,S=(wide)1<<grain,rounding=0;
        for(uint32_t i=0;i<n;++i){ps=add_checked(ps,z[2u*i],slot);cs=add_checked(cs,z[2u*n+2u*i],slot);}
        for(uint32_t block=0;block<3u;++block)for(uint32_t i=0;i<n;++i){
            uint32_t at=block*2u*n+2u*i;
            wide offset=block==0?sub_checked(ps,cs,slot):sub_checked(S,block==1?cs:ps,slot);
            wide num=add_checked(product_checked(n,a[at],slot),offset,slot);
            if(*slot)return;
            wide lo=div_floor(num,n,slot),hi=div_ceil(num,n,slot);
            a[at]=num<0?hi:lo;rounding=add_checked(rounding,sub_checked(hi,lo,slot),slot);
        }
        a[6u*n]=add_checked(a[6u*n],rounding,slot);
    }
    if(*slot)return;
    for(uint32_t j=0;j<2u*(6u*n+1u);++j)source_hi[j]=source[j];
}
