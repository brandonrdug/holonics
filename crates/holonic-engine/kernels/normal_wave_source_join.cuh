// Linear receivers of already-declared joint balls. The result is an outer enclosure;
// no centre is installed as the source and no independence of its components is asserted.
extern "C" __global__ void section_normal_enclosure_pair(
    const int64_t *left,const int64_t *left_hi,uint32_t la,uint32_t lw,
    const int64_t *right,const int64_t *right_hi,uint32_t ra,uint32_t rw,uint32_t kind,
    int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!lw||lw%2u||kind>2u||(kind&&(!rw||rw%2u))||(kind==2u&&lw!=rw)){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    for(uint32_t j=0;j<2u*(lw+1u);++j)if(left[la+j]!=left_hi[la+j]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    if(kind)for(uint32_t j=0;j<2u*(rw+1u);++j)if(right[ra+j]!=right_hi[ra+j]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    const wide *a=(const wide *)(left+la),*b=(const wide *)(right+ra);
    wide *v=(wide *)out;uint32_t width=kind==1u?lw+rw:lw;
    if(a[lw]<0||(kind&&b[rw]<0)){atomicOr(slot,REFUSED_MALFORMED);return;}
    bool same=kind==2u&&left==right&&la==ra;
    for(uint32_t j=0;j<lw;++j)v[j]=kind==2u?sub_checked(a[j],b[j],slot):a[j];
    if(kind==1u)for(uint32_t j=0;j<rw;++j)v[lw+j]=b[j];
    v[width]=same?0:kind?add_checked(a[lw],b[rw],slot):a[lw];
    if(*slot)return;
    for(uint32_t j=0;j<2u*(width+1u);++j)out_hi[j]=out[j];
}
