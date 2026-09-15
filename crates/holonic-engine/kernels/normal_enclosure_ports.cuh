// GPU receivers for contiguous complex-coordinate blocks and same-shape addition.
// Operands remain wide paired-int64 carriers throughout; no host numerical readout is used.
extern "C" __global__ void section_normal_enclosure_sum(
    const int64_t *left,const int64_t *left_hi,uint32_t la,
    const int64_t *right,const int64_t *right_hi,uint32_t ra,uint32_t width,
    int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!width||(width&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<2u*((size_t)width+1u);++i){
        if(left[la+i]!=left_hi[la+i]||right[ra+i]!=right_hi[ra+i]){
            atomicOr(slot,REFUSED_MALFORMED);return;
        }
    }
    const wide *a=(const wide *)(left+la),*b=(const wide *)(right+ra); wide *y=(wide *)out;
    if(a[width]<0||b[width]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<width;++i)y[i]=add_checked(a[i],b[i],slot);
    y[width]=add_checked(a[width],b[width],slot);
    if(*slot)return;
    for(size_t i=0;i<2u*((size_t)width+1u);++i)out_hi[i]=out[i];
}
