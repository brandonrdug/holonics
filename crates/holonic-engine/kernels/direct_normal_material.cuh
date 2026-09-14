// Direct current attachment to the existing unit-prior normal law. Source coordinates are the
// three declared complex port blocks; no field source handle or history table is an operand.
// The packed source ball and rational observed current are transient passage carriers.
__device__ void direct_normal_source_ball(
    const int64_t *lo,const int64_t *hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    uint32_t kind,uint32_t d,uint32_t grain,wide *out,uint32_t *slot){
    if(!d||(d&1u)||grain<1||grain>120||kind>1){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(kind){
        for(size_t j=0;j<2u*((size_t)d+1u);++j)if(lo[at+j]!=hi[at+j]){
            atomicOr(slot,REFUSED_MALFORMED);return;
        }
        const wide *ball=(const wide *)(lo+at);
        if(ball[d]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
        for(uint32_t j=0;j<=d;++j)out[j]=ball[j];
    }else{
        wide den=fibre_current_denominator(lo,hi,den_at,status_at,slot),S=(wide)1<<grain;
        wide radius=0;
        for(uint32_t j=0;j<d&&! *slot;++j){
            if(lo[at+j]!=hi[at+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
            wide lower=signed_product_divide_2(lo[at+j],S/2,den,0,slot);
            wide upper=signed_product_divide_2(lo[at+j],S/2,den,1,slot);
            out[j]=lo[at+j]<0?upper:lower;
            if(lower!=upper)radius=add_checked(radius,1,slot);
        }
        out[d]=radius;
    }
}
extern "C" __global__ void section_normal_enclose_input(
    const int64_t *lo,const int64_t *hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    uint32_t kind,uint32_t d,uint32_t grain,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    direct_normal_source_ball(lo,hi,at,den_at,status_at,kind,d,grain,(wide *)out,slot);
    if(*slot)return;
    for(size_t j=0;j<2u*((size_t)d+1u);++j)out_hi[j]=out[j];
}
__device__ void direct_normal_pack_sources_with_target_kind(
    const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,uint32_t ykind,
    uint32_t m,uint32_t targets,uint32_t grain,uint32_t observed,int64_t *input,uint32_t *slot){
    const uint32_t d=NORMAL_QUADRATURES*m;
    wide *current=(wide *)input;
    int64_t *incoming=input+NORMAL_WIDE_WORDS*2u*(d+1u);
        if(!m||!targets||grain<1||grain>120||observed>1||xkind>1||ykind>1){atomicOr(slot,REFUSED_MALFORMED);}
        if(!*slot)direct_normal_source_ball(xlo,xhi,xa,xd,xs,xkind,d,grain,current+d+1u,slot);
        if(!*slot&&ykind==1){
            for(uint32_t j=0;j<2u*(2u*targets+1u);++j)
                if(ylo[ya+j]!=yhi[ya+j])atomicOr(slot,REFUSED_MALFORMED);
            const wide *ball=(const wide *)(ylo+ya);
            if(ball[2u*targets]<0)atomicOr(slot,REFUSED_MALFORMED);
            // The existing observation/normal owner consumes this original wide ball.
            // It is not narrowed into the transient rational-point packet.
        } else if(!*slot){
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

__device__ void direct_normal_pack_sources(
    const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,
    uint32_t m,uint32_t targets,uint32_t grain,uint32_t observed,int64_t *input,uint32_t *slot){
    direct_normal_pack_sources_with_target_kind(xlo,xhi,xa,xd,xs,xkind,ylo,yhi,ya,yd,ys,0,m,targets,grain,observed,input,slot);
}

__device__ void direct_normal_pack(
    const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,uint32_t ykind,
    uint32_t roots,uint32_t targets,uint32_t grain,uint32_t observed,int64_t *input,uint32_t *slot){
    direct_normal_pack_sources_with_target_kind(xlo,xhi,xa,xd,xs,xkind,ylo,yhi,ya,yd,ys,ykind,
        normal_sources(roots),targets,grain,observed,input,slot);
}

// Parallel target rows, followed by their complete joint-radius bound.
__device__ void direct_normal_predict_mode_sources(const int64_t *old,const wide *current,
    uint32_t m,uint32_t targets,uint32_t grain,wide *out,int64_t *work,bool full_report,
    bool reference,uint32_t *slot){
    const uint32_t d=NORMAL_QUADRATURES*m,R=2u*targets;
    // Read the old operator using the same contraction and certified family bound as the field.
    const wide *M=(const wide *)old;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        wide norm=0;
        for(uint32_t j=0;j<d;++j)norm=add_checked(norm,ft_abs(M[(size_t)row*d+j],slot),slot);
        ((wide *)work)[2u*row]=norm;
        ((wide *)work)[2u*row+1u]=linear_material_row(M,nullptr,current+d+1u,row,
            m,grain,out,slot);
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        wide norm=0,remainder=0;
        for(uint32_t row=0;row<targets;++row){
            norm=add_checked(norm,((wide *)work)[2u*row],slot);
            remainder=add_checked(remainder,((wide *)work)[2u*row+1u],slot);
        }
        // Reference transport pays the retained coefficient defect. Applied transport uses
        // the stored operator as the law, while retaining source enclosure and rounding.
        wide error=reference?M[(size_t)R*m]:0;
        out[R]=ft_prediction_error(error,norm,current+d+1u,d,current[2u*(d+1u)-1u],remainder,grain,slot);
        if(full_report){
        size_t at=normal_metadata_at_sources(m,targets);
        out[at]=M[(size_t)R*m];out[at+1u]=M[(size_t)R*m+1u];out[at+2u]=norm;
        const int64_t *errors=old+normal_state_words_sources(m,targets)-NORMAL_STATISTIC_COUNT*MOMENT_WIRE_WORDS;
        out[at+3u]=normal_diagnostic_upper(normal_read(errors,slot),grain,slot);
        out[at+4u]=normal_diagnostic_upper(normal_read(errors+MOMENT_WIRE_WORDS,slot),grain,slot);
        }
    }
    __syncthreads();if(*slot)return;
}

__device__ void direct_normal_predict_mode(const int64_t *old,const wide *current,
    uint32_t roots,uint32_t targets,uint32_t grain,wide *out,int64_t *work,bool full_report,
    bool reference,uint32_t *slot){
    direct_normal_predict_mode_sources(old,current,normal_sources(roots),targets,grain,out,work,full_report,reference,slot);
}

__device__ void direct_normal_predict_sources(const int64_t *old,const wide *current,
    uint32_t m,uint32_t targets,uint32_t grain,wide *out,int64_t *work,bool full_report,uint32_t *slot){
    direct_normal_predict_mode_sources(old,current,m,targets,grain,out,work,full_report,true,slot);
}

__device__ void direct_normal_predict(const int64_t *old,const wide *current,
    uint32_t roots,uint32_t targets,uint32_t grain,wide *out,int64_t *work,bool full_report,uint32_t *slot){
    direct_normal_predict_mode(old,current,roots,targets,grain,out,work,full_report,true,slot);
}

__device__ void direct_normal_material_execute(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,uint32_t ykind,
    uint32_t source_complex,uint32_t targets,uint32_t grain,uint32_t observed,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t d=NORMAL_QUADRATURES*source_complex;
    const size_t report_words=normal_report_words_sources(source_complex,targets);
    wide *current=(wide *)input; int64_t *incoming=input+NORMAL_WIDE_WORDS*2u*(d+1u);
    wide *out=(wide *)before;
    for(size_t j=threadIdx.x;j<report_words;j+=blockDim.x)before[j]=before_hi[j]=0;
    for(size_t j=threadIdx.x;j<2u*(d+1u);j+=blockDim.x)current[j]=0;
    __syncthreads();
    if(!threadIdx.x)direct_normal_pack_sources_with_target_kind(xlo,xhi,xa,xd,xs,xkind,ylo,yhi,ya,yd,ys,ykind,
        source_complex,targets,grain,observed,input,slot);
    __syncthreads();if(*slot)return;
    direct_normal_predict_mode_sources(old,current,source_complex,targets,grain,out,work,true,true,slot);
    if(*slot)return;
    for(size_t j=threadIdx.x;j<report_words;j+=blockDim.x)before_hi[j]=before[j];
    __syncthreads();
    if(observed){
        field_normal_material_prepare_sources_with_ball(old,current,(const wide *)before,current,incoming,
            source_complex,1,grain,next,next_hi,after,after_hi,work,targets,0,0,
            ykind?(const wide *)(ylo+ya):nullptr,slot);
    }
}

extern "C" __global__ __launch_bounds__(512) void section_direct_normal_material(
    const int64_t *old,
    const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,uint32_t ykind,
    uint32_t roots,uint32_t targets,uint32_t grain,uint32_t observed,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
    direct_normal_material_execute(old,xlo,xhi,xa,xd,xs,xkind,ylo,yhi,ya,yd,ys,ykind,normal_sources(roots),targets,grain,observed,next,next_hi,before,before_hi,after,after_hi,work,input,slot,census,lineage,lineage_count);
}

extern "C" __global__ __launch_bounds__(512) void section_direct_normal_material_sources(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xa,uint32_t xd,uint32_t xs,uint32_t xkind,
    const int64_t *ylo,const int64_t *yhi,uint32_t ya,uint32_t yd,uint32_t ys,uint32_t ykind,
    uint32_t source_complex,uint32_t targets,uint32_t grain,uint32_t observed,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
    direct_normal_material_execute(old,xlo,xhi,xa,xd,xs,xkind,ylo,yhi,ya,yd,ys,ykind,source_complex,targets,grain,observed,next,next_hi,before,before_hi,after,after_hi,work,input,slot,census,lineage,lineage_count);
}
