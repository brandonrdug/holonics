// The same local difference receiver for any supplied rational current path.
// Source=(c_j-c_{j-1}, c_j, c_{j-1}); observed=c_{j+1}-c_j.
// No exterior alphabet, sample codec or semantic identity enters this operator.
extern "C" __global__ void section_current_difference_section(
    const int64_t *lo,const int64_t *hi,uint32_t width,uint32_t stride,uint32_t rational,uint32_t rows,
    int64_t *source,int64_t *source_hi,int64_t *observed,int64_t *observed_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    size_t at=(size_t)blockIdx.x*blockDim.x+threadIdx.x;
    if(at>=(size_t)rows*width)return;
    uint32_t row=at/width,j=at%width;
    uint32_t a=row*stride,b=(row+1u)*stride,c=(row+2u)*stride;
    if(lo[a+j]!=hi[a+j]||lo[b+j]!=hi[b+j]||lo[c+j]!=hi[c+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide ad=fibre_current_denominator(lo,hi,rational?a+width:UINT32_MAX,UINT32_MAX,slot);
    wide bd=fibre_current_denominator(lo,hi,rational?b+width:UINT32_MAX,UINT32_MAX,slot);
    wide cd=fibre_current_denominator(lo,hi,rational?c+width:UINT32_MAX,UINT32_MAX,slot);
    if(*slot)return;
    wide sd=fibre_lcm(ad,bd,slot),yd=fibre_lcm(bd,cd,slot);
    wide av=product_checked(lo[a+j],sd/ad,slot),bv=product_checked(lo[b+j],sd/bd,slot);
    wide delta=sub_checked(bv,av,slot);
    wide later=sub_checked(product_checked(lo[c+j],yd/cd,slot),product_checked(lo[b+j],yd/bd,slot),slot);
    to_word(sd,slot);to_word(yd,slot);to_word(av,slot);to_word(bv,slot);to_word(delta,slot);to_word(later,slot);
    if(*slot)return;
    size_t s=(size_t)row*(3u*width+1u),y=(size_t)row*(width+1u);
    source[s+j]=source_hi[s+j]=(int64_t)delta;
    source[s+width+j]=source_hi[s+width+j]=(int64_t)bv;
    source[s+2u*width+j]=source_hi[s+2u*width+j]=(int64_t)av;
    observed[y+j]=observed_hi[y+j]=(int64_t)later;
    if(!j){source[s+3u*width]=source_hi[s+3u*width]=(int64_t)sd;observed[y+width]=observed_hi[y+width]=(int64_t)yd;}
}
