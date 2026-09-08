// Source-null contextual section at the ACTUAL fixed source s:
// D_s = { (dc,dy) | (0,dc,s tensor dc,dy) belongs to the retained relation }.
// The mixed terms remain tied to s. The resulting relation may be partial or vertical.
__device__ void context_section_joint(const int64_t *basis,uint32_t c,uint32_t y,
    int64_t *lo,int64_t *hi) {
    uint32_t j=c+y,w=1u+j,rank=0;
    for(size_t i=0;i<(size_t)w+4u+(size_t)j*j;++i)lo[i]=hi[i]=0;
    for(uint32_t p=0;p<j;++p){
        bool occupied=basis[(size_t)p*j+p]!=0;if(occupied)++rank;
        for(uint32_t k=0;k<j;++k)lo[w+4u+(size_t)p*j+k]=hi[w+4u+(size_t)p*j+k]=occupied?basis[(size_t)p*j+k]:0;
    }
    lo[w]=hi[w]=1;lo[w+1u]=hi[w+1u]=rank?2:0;
    lo[w+2u]=hi[w+2u]=-1;lo[w+3u]=hi[w+3u]=rank;
}

extern "C" __global__ void section_constitutive_context_section(
    const int64_t *basis,const int64_t *basis_hi,
    const int64_t *source,const int64_t *source_hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    uint32_t ns,uint32_t nc,uint32_t y,int64_t *graph,int64_t *graph_hi,
    int64_t *derived,int64_t *derived_hi,int64_t *joint,int64_t *joint_hi,
    int64_t *fixed,int64_t *fixed_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t sw64=2u*((uint64_t)ns+nc+(uint64_t)ns*nc),w64=sw64+y,k64=w64+2u*nc+y;
    if(!ns || !nc || !y || y%2u || k64>UINT32_MAX-4u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t sw=(uint32_t)sw64,w=(uint32_t)w64,c=2u*nc,j=c+y,k=(uint32_t)k64;
    for(size_t i=0;i<(size_t)w*w;++i)if(basis[i]!=basis_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide sd=fibre_current_denominator(source,source_hi,den_at,status_at,slot);if(*slot)return;
    for(uint32_t i=0;i<2u*ns;++i)if(source[at+i]!=source_hi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    extern __shared__ wide scratch[];wide *r=scratch,*row=r+w;
    for(size_t i=0;i<(size_t)k*k;++i)graph[i]=graph_hi[i]=0;
    uint32_t ignored=0,rank=0;
    for(uint32_t column=0;column<j;++column){
        for(uint32_t i=0;i<w;++i)r[i]=0;
        if(column<c){
            r[2u*ns+column]=sd;
            uint32_t mixed=2u*(ns+nc)+2u*(column/2u)*ns;
            for(uint32_t b=0;b<ns;++b){
                wide real=source[at+2u*b],imaginary=source[at+2u*b+1u];
                r[mixed+2u*b]=(column%2u)?-imaginary:real;
                r[mixed+2u*b+1u]=(column%2u)?real:imaginary;
            }
        }else r[sw+column-c]=sd;
        wide den=sd;
        fibre_query(basis,w,w,r,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
        for(uint32_t i=0;i<k;++i)row[i]=i<w?r[i]:(i-w==column?den:0);
        condition_stage_row(graph,graph_hi,k,row,slot);if(*slot)return;
    }
    // Kernel rows of the residual graph are the complete (dc,dy) relation. No model is fitted.
    for(uint32_t p=0;p<j;++p)for(uint32_t i=0;i<j;++i){
        int64_t value=graph[(size_t)(w+p)*k+w+p]?graph[(size_t)(w+p)*k+w+i]:0;
        derived[(size_t)p*j+i]=derived_hi[(size_t)p*j+i]=value;
    }
    context_section_joint(derived,c,y,joint,joint_hi);
    for(uint32_t i=0;i<2u*ns;++i)fixed[i]=fixed_hi[i]=source[at+i];
    fixed[2u*ns]=fixed_hi[2u*ns]=(int64_t)sd;
}

// Translate ONLY the condition origin of the derived homogeneous joint relation by an
// explicitly retained actual condition. The existing image-receive kernel then returns
// { c' | (c'-about, observed_difference) in D_s }, without installing a cause.
extern "C" __global__ void section_constitutive_context_translate(
    const int64_t *joint,const int64_t *joint_hi,
    const int64_t *about,const int64_t *about_hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    uint32_t c,uint32_t y,int64_t *out,int64_t *out_hi,int64_t *coverage,int64_t *coverage_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t j64=(uint64_t)c+y,w64=1u+j64;
    if(!c || !y || c%2u || y%2u || w64>UINT32_MAX-4u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t j=(uint32_t)j64,w=(uint32_t)w64;size_t words=(size_t)w+4u+(size_t)j*j;
    for(size_t i=0;i<words;++i)if(joint[i]!=joint_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(joint[w]!=1 || (joint[w+1u]!=0 && joint[w+1u]!=2)){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<w;++i)if(joint[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide den=fibre_current_denominator(about,about_hi,den_at,status_at,slot);if(*slot)return;
    for(uint32_t i=0;i<c;++i)if(about[at+i]!=about_hi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<words;++i)out[i]=out_hi[i]=joint[i];
    for(uint32_t i=0;i<c;++i)out[1u+i]=out_hi[1u+i]=about[at+i];
    out[w]=out_hi[w]=(int64_t)den;
    // Coverage is relative to the supplied joint relation's own supported context domain.
    coverage[0]=coverage_hi[0]=0;
}

// Affine output origin of an admitted context ray. All vertical directions and any outside
// source residual remain in the return. The origin is an actual retained reception.
extern "C" __global__ void section_context_output_origin(
    const int64_t *report,const int64_t *report_hi,const int64_t *base,const int64_t *base_hi,
    uint32_t c,uint32_t y,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t w64=(uint64_t)c+y;if(!c || !y || w64>UINT32_MAX-4u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t w=(uint32_t)w64;size_t words=(size_t)w+4u+(size_t)y*y;
    for(size_t i=0;i<words;++i)if(report[i]!=report_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<=y;++i)if(base[i]!=base_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(report[w]<=0 || base[y]<=0 || report[w+1u]<0 || report[w+1u]>2){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<words;++i)out[i]=out_hi[i]=report[i];
    if(report[w+1u]==1)return;
    extern __shared__ wide row[];wide den=fibre_lcm(report[w],base[y],slot);
    for(uint32_t i=0;i<w;++i){
        row[i]=product_checked(report[i],den/report[w],slot);
        if(i>=c)row[i]=add_checked(row[i],product_checked(base[i-c],den/base[y],slot),slot);
    }
    if(*slot)return;fibre_normalize(row,w,&den,slot);
    for(uint32_t i=0;i<w;++i)to_word(row[i],slot);to_word(den,slot);if(*slot)return;
    for(uint32_t i=0;i<w;++i)out[i]=out_hi[i]=(int64_t)row[i];out[w]=out_hi[w]=(int64_t)den;
}

extern "C" __global__ void section_context_return_difference(
    const int64_t *base,const int64_t *base_hi,
    const int64_t *observed,const int64_t *observed_hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    uint32_t y,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!y || y%2u || base[y]<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<=y;++i)if(base[i]!=base_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide od=fibre_current_denominator(observed,observed_hi,den_at,status_at,slot);if(*slot)return;
    for(uint32_t i=0;i<y;++i)if(observed[at+i]!=observed_hi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    extern __shared__ wide row[];wide den=fibre_lcm(od,base[y],slot);
    for(uint32_t i=0;i<y;++i)row[i]=sub_checked(product_checked(observed[at+i],den/od,slot),product_checked(base[i],den/base[y],slot),slot);
    if(*slot)return;fibre_normalize(row,y,&den,slot);
    for(uint32_t i=0;i<y;++i)to_word(row[i],slot);to_word(den,slot);if(*slot)return;
    for(uint32_t i=0;i<y;++i)out[i]=out_hi[i]=(int64_t)row[i];out[y]=out_hi[y]=(int64_t)den;
}
