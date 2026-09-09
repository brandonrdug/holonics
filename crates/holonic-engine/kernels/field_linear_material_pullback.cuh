// M_source^* r for the finite complex operator. Later deposits are undone in reverse
// chronology with the exact same per-product projection that constructed them.
extern "C" __global__ void section_field_linear_material_pullback(
    const int64_t *state,const int64_t *journal,const int64_t *source_report,const int64_t *returned,
    uint32_t n,uint32_t targets,uint32_t contacts,uint32_t later,uint32_t grain,uint32_t metric,
    int64_t *lo,int64_t *hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t coordinate=blockIdx.x*blockDim.x+threadIdx.x;
    if(coordinate>=10u*n+2u*contacts)return;
    if(coordinate<4u*n || coordinate>=10u*n){for(uint32_t j=0;j<4;++j)lo[4u*coordinate+j]=hi[4u*coordinate+j]=0;return;}
    uint32_t j=coordinate-4u*n,column=j/2u;size_t stride=2u*(size_t)targets+1u;
    const wide *matrix=(const wide *)state,*r=(const wide *)returned;
    MaterialInterval sum={0,0};wide rn=0;
    for(uint32_t row=0;row<targets;++row){
        size_t at=2u*((size_t)row*3u*n+column);wide ar=matrix[at],ai=matrix[at+1u];
        for(uint32_t k=later;k>0;--k){
            if(!journal[2u*(k-1u)+1u])continue;
            const wide *entry=(const wide *)(uintptr_t)(uint64_t)journal[2u*(k-1u)];
            const wide *difference=entry+5u*stride,*gain=entry+6u*stride;
            wide dr,di,rounds=0;ft_complex_product(difference[2u*row],difference[2u*row+1u],gain[2u*column],gain[2u*column+1u],grain,&dr,&di,&rounds,slot);
            ar=sub_checked(ar,dr,slot);ai=sub_checked(ai,di,slot);
        }
        uint32_t offset=metric==2?4u*row:10u*row+(metric==0?4u:6u);
        MaterialInterval rr={r[offset],r[offset+1u]},ri=metric==2?MaterialInterval{r[offset+2u],r[offset+3u]}:mp_point(0);
        if(rr.lo>rr.hi || ri.lo>ri.hi){atomicOr(slot,REFUSED_MALFORMED);return;}
        auto norm=[&](MaterialInterval x){wide a=ft_abs(x.lo,slot),b=ft_abs(x.hi,slot);return a>b?a:b;};
        rn=add_checked(rn,add_checked(norm(rr),norm(ri),slot),slot);
        MaterialInterval value=(j&1u)?mp_add(mp_mul(mp_point(ar),ri,grain,slot),mp_neg(mp_mul(mp_point(ai),rr,grain,slot),slot),slot):
            mp_add(mp_mul(mp_point(ar),rr,grain,slot),mp_mul(mp_point(ai),ri,grain,slot),slot);
        sum=mp_add(sum,value,slot);
    }
    wide error=((const wide *)source_report)[6u*stride+6u*n+1u];
    if(error<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    error=ft_ceil_product(error,rn,grain,slot);
    wide *out=(wide *)lo;out[2u*coordinate]=sub_checked(sum.lo,error,slot);out[2u*coordinate+1u]=add_checked(sum.hi,error,slot);
    if(!*slot)for(uint32_t i=0;i<4;++i)hi[4u*coordinate+i]=lo[4u*coordinate+i];
}
