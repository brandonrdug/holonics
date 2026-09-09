// Partial real adjoint of the actual retained M[Q(s) tensor Q(c)] prediction.
// Historical factors are held fixed. Both the visible source and the full outgoing/internal
// query current return. Numerical intervals and the operator/source defect remain separate
// from a finite developmental displacement; this kernel does not select interval centres.
struct MaterialInterval { wide lo,hi; };
// Negative derivative of 1/2 ||observed-prediction||^2 in the complete complex
// current chart. Each real/imaginary coordinate carries its outward interval;
// the original joint balls remain retained by the field owner.
extern "C" __global__ void section_field_material_current_covector(
    const int64_t *prediction,const int64_t *observation,uint32_t targets,
    int64_t *out_lo,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t j=blockIdx.x*blockDim.x+threadIdx.x;if(j>=2u*targets)return;
    const wide *p=(const wide *)prediction,*q=(const wide *)observation+2u*(2u*targets+1u);
    if(p[2u*targets]<0 || q[2u*targets]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide error=add_checked(p[2u*targets],q[2u*targets],slot),value=sub_checked(q[j],p[j],slot);
    wide *out=(wide *)out_lo;out[2u*j]=sub_checked(value,error,slot);out[2u*j+1u]=add_checked(value,error,slot);
    if(!*slot)for(uint32_t i=0;i<4u;++i)out_hi[4u*j+i]=out_lo[4u*j+i];
}
__device__ MaterialInterval mp_point(wide x){return {x,x};}
__device__ MaterialInterval mp_add(MaterialInterval a,MaterialInterval b,uint32_t *slot){
    return {add_checked(a.lo,b.lo,slot),add_checked(a.hi,b.hi,slot)};
}
__device__ MaterialInterval mp_neg(MaterialInterval a,uint32_t *slot){
    return {sub_checked(0,a.hi,slot),sub_checked(0,a.lo,slot)};
}
__device__ MaterialInterval mp_mul(MaterialInterval a,MaterialInterval b,uint32_t g,uint32_t *slot){
    MaterialInterval r;normalized_interval_product(a.lo,a.hi,b.lo,b.hi,g,&r.lo,&r.hi,slot);return r;
}
// Signed 256-bit numerator / positive 256-bit denominator, at grid 2^g. The extra limb
// retains a doubled remainder; the shifted numerator never has to fit a 256-bit carrier.
__device__ MaterialInterval mp_ratio(HistoryInteger a,HistoryInteger b,uint32_t g,uint32_t *slot){
    if(a.overflow||b.overflow||b.negative||b.is_zero()){atomicOr(slot,REFUSED_CARRIER);return {0,0};}
    ExactInteger<9> rem,den;for(uint32_t i=0;i<8;++i)den.limb[i]=b.limb[i];
    wide value=0;
    for(int bit=255+(int)g;bit>=0;--bit){
        int source=bit-(int)g;uint32_t carry=source>=0?(a.limb[source/32]>>(source%32))&1u:0;
        for(uint32_t i=0;i<9;++i){uint32_t next=rem.limb[i]>>31;rem.limb[i]=(rem.limb[i]<<1)|carry;carry=next;}
        if(compare_magnitude(rem,den)>=0){
            rem=subtract_magnitude(rem,den);
            if(bit>=127){atomicOr(slot,REFUSED_CARRIER);return {0,0};}
            value|=(wide)((uwide)1<<bit);
        }
    }
    wide upper=add_checked(value,rem.is_zero()?0:1,slot);
    return a.negative?MaterialInterval{-upper,-value}:MaterialInterval{value,upper};
}
__device__ MaterialInterval mp_fraction(MomentInteger num,MomentInteger den,uint32_t g,uint32_t *slot){
    bool rem=false;wide lo=contextual_fraction(num,den,g,&rem,slot);return {lo,add_checked(lo,rem?1:0,slot)};
}
__device__ void mp_pair(const int64_t *a,const wide *ba,const int64_t *b,const wide *bb,
    uint32_t n,uint32_t g,bool visible,HistoryInteger &re,HistoryInteger &im,
    HistoryInteger &na,HistoryInteger &nb,uint32_t *slot){
    uint32_t d=visible?4u*n:6u*n;
    const wide *x=(const wide *)(visible?a+8u*n+2u:a),*y=(const wide *)(visible?b+8u*n+2u:b);
    for(uint32_t j=0;j<d;j+=2)history_complex_add_product(re,im,x[j],x[j+1],y[j],y[j+1],true);
    HistoryInteger unit=complete_power(2u*g,slot);re=re+unit;
    if(visible){na=history_read_integer(a+16u*n+2u,slot);nb=history_read_integer(b+16u*n+2u,slot);}
    else{
        int64_t ka=a[6u*d+18u],kb=b[6u*d+18u];
        if(ka<0||kb<0||(ka&&!ba)||(kb&&!bb)){atomicOr(slot,REFUSED_MALFORMED);return;}
        for(int64_t j=0;j<(ka<kb?ka:kb);++j)history_complex_add_product(re,im,ba[2*j],ba[2*j+1],bb[2*j],bb[2*j+1],true);
        na=unit+history_read_integer(a+6u*d+10u,slot);nb=unit+history_read_integer(b+6u*d+10u,slot);
    }
}
__device__ MaterialInterval mp_kernel(HistoryInteger re,HistoryInteger im,HistoryInteger na,HistoryInteger nb,
    uint32_t g,uint32_t *slot){
    MomentInteger r=moment_lift(re),i=moment_lift(im);
    return mp_fraction(r*r+i*i,moment_lift(na)*moment_lift(nb),g,slot);
}

extern "C" __global__ __launch_bounds__(512) void section_field_material_pullback_factors(
    const int64_t *table,const int64_t *returned,uint32_t source,uint32_t n,uint32_t targets,uint32_t g,uint32_t metric,
    int64_t *out_lo,int64_t *out_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t f=blockIdx.x,at=f/2u;if(at>source)return;
    wide *out=(wide *)out_lo+10u*f;for(uint32_t j=0;j<20u;++j)out_lo[20u*f+j]=out_hi[20u*f+j]=0;
    const int64_t *entry=contextual_at(table,at),*meta=entry+contextual_meta(n,targets);
    if(meta[1]<0)return;
    int64_t reference=meta[2];if(!at||reference<1||reference>(int64_t)at||meta[3]!=3){atomicOr(slot,REFUSED_MALFORMED);return;}
    if((f&1u)&&reference==(int64_t)at)return;
    uint32_t query=(f&1u)?(uint32_t)reference:at;
    const int64_t *basis=contextual_at(table,query),*now=contextual_at(table,source);
    const int64_t *s=basis+contextual_input_visible(n,targets),*c=contextual_at(table,query-1u)+contextual_context(n,targets);
    const int64_t *sq=now+contextual_output_visible(n,targets),*cq=now+contextual_context(n,targets);
    HistoryInteger sr,si,sn,sqn,cr,ci,cn,cqn;
    mp_pair(s,nullptr,sq,nullptr,n,g,true,sr,si,sn,sqn,slot);
    mp_pair(c,contextual_b_at(table,query-1u),cq,contextual_b_at(table,source),n,g,false,cr,ci,cn,cqn,slot);
    MaterialInterval ks=mp_kernel(sr,si,sn,sqn,g,slot),kc=mp_kernel(cr,ci,cn,cqn,g,slot),alpha={0,0};
    const wide *beta=(const wide *)(entry+contextual_beta(n,targets)),*r=(const wide *)returned;
    for(uint32_t j=0;j<targets;++j)for(uint32_t axis=0;axis<(metric==2?2u:1u);++axis){
        uint32_t coordinate=2u*j+axis;
        wide b=(f&1u)?sub_checked(0,beta[2u*targets+coordinate],slot):add_checked(beta[coordinate],beta[2u*targets+coordinate],slot);
        uint32_t offset=metric==2?2u*coordinate:10u*j+(metric==0?4u:6u);
        alpha=mp_add(alpha,mp_mul(mp_point(b),{r[offset],r[offset+1u]},g,slot),slot);
    }
    MaterialInterval as=mp_mul(alpha,kc,g,slot),ac=mp_mul(alpha,ks,g,slot);
    MaterialInterval coefficients[5]={mp_mul(as,mp_ratio(sr,sn,g,slot),g,slot),mp_mul(as,mp_ratio(si,sn,g,slot),g,slot),
        mp_mul(ac,mp_ratio(cr,cn,g,slot),g,slot),mp_mul(ac,mp_ratio(ci,cn,g,slot),g,slot),mp_mul(as,ks,g,slot)};
    for(uint32_t j=0;j<5;++j){out[2u*j]=coefficients[j].lo;out[2u*j+1u]=coefficients[j].hi;}
    if(!*slot)for(uint32_t j=0;j<20u;++j)out_hi[20u*f+j]=out_lo[20u*f+j];
}
__device__ wide mp_coordinate(const int64_t *table,uint32_t at,uint32_t n,uint32_t j,bool visible,bool output,uint32_t targets){
    const int64_t *r=contextual_at(table,at);
    if(visible)return ((const wide *)(r+(output?contextual_output_visible(n,targets):contextual_input_visible(n,targets))+8u*n+2u))[j];
    const int64_t *c=r+contextual_context(n,targets);if(j<6u*n)return ((const wide *)c)[j];
    j-=6u*n;return j<2u*(uint64_t)c[36u*n+18u]?contextual_b_at(table,at)[j]:0;
}
extern "C" __global__ __launch_bounds__(512) void section_field_material_pullback_return(
    const int64_t *table,const int64_t *factors,const int64_t *returned,uint32_t source,uint32_t n,uint32_t k,uint32_t targets,uint32_t g,uint32_t metric,
    int64_t *out_lo,int64_t *out_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t coordinate=blockIdx.x*blockDim.x+threadIdx.x;if(coordinate>=10u*n+2u*k)return;
    bool visible=coordinate<4u*n;uint32_t j=visible?coordinate:coordinate-4u*n;
    MaterialInterval sum={0,0},z={0,0};
    for(uint32_t f=0;f<2u*(source+1u);++f){
        uint32_t at=f/2u;const int64_t *entry=contextual_at(table,at),*meta=entry+contextual_meta(n,targets);if(meta[1]<0)continue;
        if((f&1u)&&meta[2]==(int64_t)at)continue;
        uint32_t q=(f&1u)?(uint32_t)meta[2]:at;
        const wide *a=(const wide *)factors+10u*f;uint32_t offset=visible?0u:4u;
        MaterialInterval ar={a[offset],a[offset+1]},ai={a[offset+2],a[offset+3]};
        wide x=mp_coordinate(table,visible?q:q-1u,n,j&~1u,visible,false,targets);
        wide y=mp_coordinate(table,visible?q:q-1u,n,(j&~1u)+1u,visible,false,targets);
        MaterialInterval value=(j&1u)?mp_add(mp_mul(ar,mp_point(y),g,slot),mp_mul(ai,mp_point(x),g,slot),slot):
            mp_add(mp_mul(ar,mp_point(x),g,slot),mp_neg(mp_mul(ai,mp_point(y),g,slot),slot),slot);
        sum=mp_add(sum,value,slot);z=mp_add(z,{a[8],a[9]},slot);
    }
    const int64_t *now=contextual_at(table,source),*s=now+contextual_output_visible(n,targets),*c=now+contextual_context(n,targets);
    wide x=mp_coordinate(table,source,n,j,visible,true,targets);
    sum=mp_add(sum,mp_neg(mp_mul(z,mp_point(x),g,slot),slot),slot);
    HistoryInteger unit=complete_power(2u*g,slot);
    HistoryInteger norm=visible?history_read_integer(s+16u*n+2u,slot):unit+history_read_integer(c+36u*n+10u,slot);
    sum=mp_mul(sum,mp_ratio(HistoryInteger(2)*unit,norm,g,slot),g,slot);
    // ||DQ||<=2, ||D²Q||<=20, and the other tensor factor changes by <=2*distance.
    // M's retained coefficient defect includes the immutable historical factor uncertainty.
    const wide *bounds=(const wide *)(now+contextual_extra(n,targets)),*r=(const wide *)returned;
    wide es=((const wide *)(s+16u*n+8u))[0],ec=((const wide *)(c+36u*n+16u))[0],rn=0;
    if(es<0||ec<0||bounds[0]<0||bounds[1]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<(metric==2?2u*targets:targets);++i){uint32_t off=metric==2?2u*i:10u*i+(metric==0?4u:6u);wide a=r[off],b=r[off+1];
        if(a>b){atomicOr(slot,REFUSED_MALFORMED);return;}wide m=a<0?sub_checked(0,a,slot):a;wide t=b<0?sub_checked(0,b,slot):b;
        rn=add_checked(rn,m>t?m:t,slot);
    }
    wide variation=add_checked(product_checked(20,visible?es:ec,slot),product_checked(4,visible?ec:es,slot),slot);
    wide error=ft_ceil_product(add_checked(product_checked(2,bounds[0],slot),ft_ceil_product(bounds[1],variation,g,slot),slot),rn,g,slot);
    sum.lo=sub_checked(sum.lo,error,slot);sum.hi=add_checked(sum.hi,error,slot);
    wide *out=(wide *)out_lo;out[2u*coordinate]=sum.lo;out[2u*coordinate+1u]=sum.hi;
    if(!*slot)for(uint32_t i=0;i<4;++i)out_hi[4u*coordinate+i]=out_lo[4u*coordinate+i];
}
