// Linear receivers of already-declared joint balls. The result is an outer enclosure;
// no centre is installed as the source and no independence of its components is asserted.
// At fixed h, F(a)=(a,h,h tensor a) is affine, with Lipschitz constant
// sqrt(1+||h||_2^2) <= 1+sum |h_j| over the real coordinates. Exact h is retained;
// only the returned numerical chart is rounded, with its error added to the ball.
extern "C" __global__ void section_normal_enclosure_features(
    const int64_t *source,const int64_t *source_hi,uint32_t at,uint32_t d,
    const int64_t *h,const int64_t *h_hi,uint32_t ha,uint32_t hd_at,uint32_t hs_at,uint32_t k,
    uint32_t grain,int64_t *output,int64_t *output_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t f64=(uint64_t)d+k+(uint64_t)d*(k/2u);
    if(!d||!k||(d&1u)||(k&1u)||(at&1u)||grain<1||grain>120||f64>=UINT32_MAX){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<2u*((size_t)d+1u);++i)if(source[at+i]!=source_hi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<k;++i)if(h[ha+i]!=h_hi[ha+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *x=(const wide *)(source+at);wide *out=(wide *)output;
    wide den=fibre_current_denominator(h,h_hi,hd_at,hs_at,slot),S=(wide)1<<grain;
    if(x[d]<0||den<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide N=S,rounding=0;
    for(uint32_t i=0;i<d;++i)out[i]=x[i];
    for(uint32_t i=0;i<k;++i){
        wide n=h[ha+i];
        wide lo=signed_product_divide_2(n,S/2,den,0,slot),hi=signed_product_divide_2(n,S/2,den,1,slot);
        if(*slot)return;
        out[d+i]=n<0?hi:lo;
        N=add_checked(N,n<0?sub_checked(0,lo,slot):hi,slot);
        rounding=add_checked(rounding,sub_checked(hi,lo,slot),slot);
    }
    wide twice_den=product_checked(2,den,slot);
    for(uint32_t j=0;j<k/2u;++j)for(uint32_t i=0;i<d/2u;++i){
        wide ar=x[2u*i],ai=x[2u*i+1u],hr=h[ha+2u*j],hi=h[ha+2u*j+1u];
        uint32_t p=d+k+j*d+2u*i;
        for(uint32_t q=0;q<2u;++q){
            wide u=q?ai:ar,v=q?ar:ai,hv=q?hi:sub_checked(0,hi,slot);
            wide lo=add_checked(signed_product_divide_2(u,hr,twice_den,0,slot),
                signed_product_divide_2(v,hv,twice_den,0,slot),slot);
            wide upper=add_checked(signed_product_divide_2(u,hr,twice_den,1,slot),
                signed_product_divide_2(v,hv,twice_den,1,slot),slot);
            if(*slot)return;
            out[p+q]=lo>=0?lo:upper<=0?upper:0;
            rounding=add_checked(rounding,sub_checked(upper,lo,slot),slot);
        }
    }
    out[(uint32_t)f64]=add_checked(signed_product_divide_2(N,x[d],2*S,1,slot),rounding,slot);
    if(*slot)return;
    for(size_t i=0;i<2u*(f64+1u);++i)output_hi[i]=output[i];
}
extern "C" __global__ void section_normal_enclosure_restrict(
    const int64_t *source,const int64_t *source_hi,uint32_t at,uint32_t width,uint32_t start,uint32_t count,
    int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!count||(at&1u)||(start&1u)||(count&1u)||(uint64_t)start+count>width){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t j=0;j<2u*((size_t)width+1u);++j)if(source[at+j]!=source_hi[at+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *x=(const wide *)(source+at);wide *v=(wide *)out;
    if(x[width]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=0;j<count;++j)v[j]=x[start+j];
    v[count]=x[width];
    for(size_t j=0;j<2u*((size_t)count+1u);++j)out_hi[j]=out[j];
}
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
