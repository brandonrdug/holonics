// Direct current attachment to the existing unit-prior normal law. Source coordinates are the
// three declared complex port blocks; no field source handle or history table is an operand.
// The packed source ball and rational observed current are transient passage carriers.
__device__ void direct_normal_pack(
    const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,
    uint32_t roots,uint32_t targets,uint32_t grain,uint32_t observed,int64_t *input,uint32_t *slot){
    const uint32_t d=normal_source_components(roots);
    wide *current=(wide *)input;
    int64_t *incoming=input+NORMAL_WIDE_WORDS*2u*(d+1u);
        if(!roots||!targets||grain<1||grain>120||observed>1||xkind>1){atomicOr(slot,REFUSED_MALFORMED);}
        if(!*slot&&xkind==1){
            for(size_t j=0;j<NORMAL_WIDE_WORDS*(d+1u);++j)
                if(xlo[xa+j]!=xhi[xa+j])atomicOr(slot,REFUSED_MALFORMED);
            const wide *ball=(const wide *)(xlo+xa);
            if(ball[d]<0)atomicOr(slot,REFUSED_MALFORMED);
            if(!*slot)for(uint32_t j=0;j<=d;++j)current[d+1u+j]=ball[j];
        }
        if(!*slot&&xkind==0){
            wide den=fibre_current_denominator(xlo,xhi,xd,xs,slot),S=(wide)1<<grain;
            wide radius=0;
            for(uint32_t j=0;j<d&&! *slot;++j){
                if(xlo[xa+j]!=xhi[xa+j]){atomicOr(slot,REFUSED_MALFORMED);break;}
                wide lo=signed_product_divide_2(xlo[xa+j],S/2,den,0,slot);
                wide hi=signed_product_divide_2(xlo[xa+j],S/2,den,1,slot);
                current[d+1u+j]=xlo[xa+j]<0?hi:lo;
                if(lo!=hi)radius=add_checked(radius,1,slot);
            }
            current[2u*(d+1u)-1u]=radius;
        }
        if(!*slot){
            wide yden=observed?fibre_current_denominator(ylo,yhi,yd,ys,slot):1;
            for(uint32_t j=0;j<targets&&! *slot;++j){
                for(uint32_t q=0;q<2u;++q){
                    if(observed&&ylo[ya+2u*j+q]!=yhi[ya+2u*j+q])atomicOr(slot,REFUSED_MALFORMED);
                    incoming[3u*j+q]=observed?ylo[ya+2u*j+q]:0;
                }
                incoming[3u*j+2u]=(int64_t)yden;
            }
        }
}

// Parallel target rows, followed by their complete joint-radius bound.
__device__ void direct_normal_predict(const int64_t *old,const wide *current,
    uint32_t roots,uint32_t targets,uint32_t grain,wide *out,int64_t *work,bool full_report,uint32_t *slot){
    const uint32_t d=normal_source_components(roots),R=2u*targets;
    // Read the old operator using the same contraction and certified family bound as the field.
    const wide *M=(const wide *)old;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        wide norm=0;
        for(uint32_t j=0;j<d;++j)norm=add_checked(norm,ft_abs(M[(size_t)row*d+j],slot),slot);
        ((wide *)work)[2u*row]=norm;
        ((wide *)work)[2u*row+1u]=linear_material_row(M,nullptr,current+d+1u,row,
            normal_sources(roots),grain,out,slot);
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        wide norm=0,remainder=0;
        for(uint32_t row=0;row<targets;++row){
            norm=add_checked(norm,((wide *)work)[2u*row],slot);
            remainder=add_checked(remainder,((wide *)work)[2u*row+1u],slot);
        }
        wide error=M[(size_t)R*normal_sources(roots)];
        out[R]=ft_prediction_error(error,norm,current+d+1u,d,current[2u*(d+1u)-1u],remainder,grain,slot);
        if(full_report){
        size_t at=normal_metadata_at(roots,targets);
        out[at]=error;out[at+1u]=M[(size_t)R*normal_sources(roots)+1u];out[at+2u]=norm;
        const int64_t *errors=old+normal_state_words(roots,targets)-NORMAL_STATISTIC_COUNT*MOMENT_WIRE_WORDS;
        out[at+3u]=normal_grid(normal_read(errors,slot),grain,true,slot);
        out[at+4u]=normal_grid(normal_read(errors+MOMENT_WIRE_WORDS,slot),grain,true,slot);
        }
    }
    __syncthreads();if(*slot)return;
}

extern "C" __global__ __launch_bounds__(512) void section_direct_normal_material(
    const int64_t *old,
    const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,
    uint32_t roots,uint32_t targets,uint32_t grain,uint32_t observed,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
    if(blockIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t d=normal_source_components(roots),R=2u*targets;
    const size_t report_words=normal_report_words(roots,targets);
    wide *current=(wide *)input;
    int64_t *incoming=input+NORMAL_WIDE_WORDS*2u*(d+1u);
    wide *out=(wide *)before;
    for(size_t j=threadIdx.x;j<report_words;j+=blockDim.x)before[j]=before_hi[j]=0;
    for(size_t j=threadIdx.x;j<2u*(d+1u);j+=blockDim.x)current[j]=0;
    __syncthreads();
    if(!threadIdx.x){
        direct_normal_pack(xlo,xhi,xa,xd,xs,xkind,ylo,yhi,ya,yd,ys,
            roots,targets,grain,observed,input,slot);
    }
    __syncthreads();if(*slot)return;
    direct_normal_predict(old,current,roots,targets,grain,out,work,true,slot);
    if(*slot)return;
    for(size_t j=threadIdx.x;j<report_words;j+=blockDim.x)before_hi[j]=before[j];
    __syncthreads();
    if(observed)field_normal_material_prepare(old,current,(const wide *)before,current,incoming,
        roots,1,grain,next,next_hi,after,after_hi,work,targets,0,slot);
}
