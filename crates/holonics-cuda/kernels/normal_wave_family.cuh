// Initial anchored family: lambda=1, current joint=anchor, anchor constrained separately by
// the retained normal-wave ball. No coordinates of that ball are replaced by its centre.
extern "C" __global__ void section_normal_wave_family_seed(
    uint32_t n,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!n || n>(UINT32_MAX-7u)/8u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t a=4u*n,t=2u+2u*a,w=1u+t;
    size_t words=(size_t)w+4u+(size_t)t*t;
    for(size_t i=0;i<words;++i)out[i]=out_hi[i]=0;
    out[1]=out_hi[1]=1; // homogeneous complex unit, within the target coordinates
    out[w]=out_hi[w]=1;out[w+1u]=out_hi[w+1u]=2;
    out[w+2u]=out_hi[w+2u]=-1;out[w+3u]=out_hi[w+3u]=a;
    for(uint32_t i=0;i<a;++i){
        size_t row=(size_t)w+4u+(size_t)(2u+i)*t;
        out[row+2u+i]=out_hi[row+2u+i]=1;
        out[row+2u+a+i]=out_hi[row+2u+a+i]=1;
    }
}
