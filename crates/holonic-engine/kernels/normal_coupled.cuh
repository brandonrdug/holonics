// Admission of a supported family is existence, not uniqueness or a confidence threshold.
extern "C" __global__ void section_normal_family_admit(
    const int64_t *report,const int64_t *hi,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(report[0]!=hi[0]||report[1]!=hi[1]){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide status=((const wide*)report)[0];
    if(status<0||status>2){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(status!=0){atomicOr(slot,REFUSED_BOUND);return;}
    out[0]=out_hi[0]=1;
}
// A separate actually observed point source must lie on the declared (c-p,c,p) plane.
// This checks its source relation, not equality to a projected latent current.
extern "C" __global__ void section_normal_source_plane(
    const int64_t *source,const int64_t *hi,uint32_t at,uint32_t den,uint32_t status,uint32_t n,
    int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    fibre_current_denominator(source,hi,den,status,slot);if(*slot)return;
    if(!n||n>UINT32_MAX/6u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t r=2u*n;
    for(uint32_t i=0;i<3u*r;++i)if(source[at+i]!=hi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<r;++i)if((wide)source[at+i]!=(wide)source[at+r+i]-(wide)source[at+2u*r+i]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    out[0]=out_hi[0]=1;
}
