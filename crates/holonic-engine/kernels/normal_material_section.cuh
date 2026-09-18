// Integrate a supplied section into the existing normal geometry, fit once, and apply both
// actual operator cuts to the supplied source field. No record population enters the state.
extern "C" __global__ __launch_bounds__(512) void section_normal_material_enclosed_batch(
    const int64_t *old,const int64_t *table,uint32_t rows,uint32_t sources,uint32_t targets,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *work,int64_t *input,int64_t *report,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t d=2u*sources;size_t sw=normal_state_words_sources(sources,targets),rw=normal_report_words_sources(sources,targets);
    wide *current=(wide *)input;int64_t *incoming=input+4u*(d+1u);
    for(size_t j=threadIdx.x;j<sw;j+=blockDim.x)next[j]=old[j];
    for(size_t j=threadIdx.x;j<2u*(d+1u);j+=blockDim.x)current[j]=0;
    for(size_t j=threadIdx.x;j<rw;j+=blockDim.x)report[j]=0;
    __syncthreads();
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            const int64_t *entry=table+6u*(size_t)row;
            const int64_t *x=(const int64_t *)(uintptr_t)(uint64_t)entry[0],*xh=(const int64_t *)(uintptr_t)(uint64_t)entry[1];
            const int64_t *y=(const int64_t *)(uintptr_t)(uint64_t)entry[3],*yh=(const int64_t *)(uintptr_t)(uint64_t)entry[4];
            uint32_t xa=(uint32_t)entry[2],ya=(uint32_t)entry[5];
            direct_normal_pack_sources_with_target_kind(x,xh,xa,UINT32_MAX,UINT32_MAX,1,
                y,yh,ya,UINT32_MAX,UINT32_MAX,1,sources,targets,grain,1,input,slot);
            if(!*slot)normal_observation_frame_sources_with_ball(current,incoming,sources,targets,1,grain,0,0,report,slot,(const wide *)(y+ya));
        }
        __syncthreads();if(*slot)return;
        normal_increment_sources(next+normal_matrix_words_sources(sources,targets),
            (wide *)report+normal_source_at(targets),(wide *)report+NORMAL_OBSERVED*normal_ball_stride(targets),
            report+normal_report_base_sources(sources,targets),sources,targets,false,slot);
        if(*slot)return;
    }
    normal_fit_sources(next,sources,targets,grain,work,nullptr,slot);if(*slot)return;
    for(size_t j=threadIdx.x;j<sw;j+=blockDim.x)next_hi[j]=next[j];
}
__device__ void normal_material_section_execute(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xstride,uint32_t xrational,
    const int64_t *ylo,const int64_t *yhi,uint32_t ystride,uint32_t yrational,uint32_t rows,
    uint32_t source_complex,uint32_t targets,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,int64_t *report,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t d=NORMAL_QUADRATURES*source_complex;
    const size_t sw=normal_state_words_sources(source_complex,targets),rw=normal_report_words_sources(source_complex,targets);
    const size_t stride=normal_ball_stride(targets),field_words=NORMAL_WIDE_WORDS*stride*rows;
    wide *current=(wide *)input; int64_t *incoming=input+NORMAL_WIDE_WORDS*2u*(d+1u);
    for(size_t j=threadIdx.x;j<sw;j+=blockDim.x)next[j]=old[j];
    for(size_t j=threadIdx.x;j<2u*(d+1u);j+=blockDim.x)current[j]=0;
    for(size_t j=threadIdx.x;j<rw;j+=blockDim.x)report[j]=0;
    __syncthreads();
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            uint32_t xa=row*xstride,ya=row*ystride;
            direct_normal_pack_sources(xlo,xhi,xa,xrational?xa+d:UINT32_MAX,UINT32_MAX,0,
                ylo,yhi,ya,yrational?ya+2u*targets:UINT32_MAX,UINT32_MAX,
                source_complex,targets,grain,1,input,slot);
            if(!*slot)normal_observation_frame_sources(current,incoming,source_complex,targets,1,grain,0,0,report,slot);
        }
        __syncthreads();if(*slot)return;
        normal_increment_sources(next+normal_matrix_words_sources(source_complex,targets),
            (wide *)report+normal_source_at(targets),(wide *)report+NORMAL_OBSERVED*stride,
            report+normal_report_base_sources(source_complex,targets),source_complex,targets,false,slot);
        if(*slot)return;
    }
    normal_fit_sources(next,source_complex,targets,grain,work,nullptr,slot);if(*slot)return;
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            uint32_t xa=row*xstride;
            direct_normal_pack_sources(xlo,xhi,xa,xrational?xa+d:UINT32_MAX,UINT32_MAX,0,
                ylo,yhi,0,UINT32_MAX,UINT32_MAX,source_complex,targets,grain,0,input,slot);
        }
        __syncthreads();if(*slot)return;
        direct_normal_predict_mode_sources(old,current,source_complex,targets,grain,
            ((wide *)before)+row*stride,work,false,true,slot);
        if(*slot)return;
        direct_normal_predict_mode_sources(next,current,source_complex,targets,grain,
            ((wide *)after)+row*stride,work,false,true,slot);
        if(*slot)return;
    }
    for(size_t j=threadIdx.x;j<sw;j+=blockDim.x)next_hi[j]=next[j];
    for(size_t j=threadIdx.x;j<field_words;j+=blockDim.x){before_hi[j]=before[j];after_hi[j]=after[j];}
}

extern "C" __global__ __launch_bounds__(512) void section_normal_material_section(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xstride,uint32_t xrational,
    const int64_t *ylo,const int64_t *yhi,uint32_t ystride,uint32_t yrational,uint32_t rows,
    uint32_t roots,uint32_t targets,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,int64_t *report,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    normal_material_section_execute(old,xlo,xhi,xstride,xrational,ylo,yhi,ystride,yrational,rows,normal_sources(roots),targets,grain,next,next_hi,before,before_hi,after,after_hi,work,input,report,slot,census,lineage,lineage_count);
}

extern "C" __global__ __launch_bounds__(512) void section_normal_material_section_sources(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xstride,uint32_t xrational,
    const int64_t *ylo,const int64_t *yhi,uint32_t ystride,uint32_t yrational,uint32_t rows,
    uint32_t source_complex,uint32_t targets,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,int64_t *report,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    normal_material_section_execute(old,xlo,xhi,xstride,xrational,ylo,yhi,ystride,yrational,rows,source_complex,targets,grain,next,next_hi,before,before_hi,after,after_hi,work,input,report,slot,census,lineage,lineage_count);
}

// Apply one retained normal operator to every row of a resident source section.  The source
// section is a point or rational packet; the output retains one complete enclosure per row.
// No material state is changed and no row is read back between applications.
__device__ void normal_applied_material_section_execute(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xstride,
    uint32_t xrational,uint32_t rows,uint32_t source_complex,uint32_t targets,uint32_t grain,
    int64_t *out,int64_t *out_hi,int64_t *work,int64_t *input,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t d=NORMAL_QUADRATURES*source_complex;
    const size_t stride=normal_ball_stride(targets);
    const size_t field_words=NORMAL_WIDE_WORDS*stride*rows;
    for(size_t j=threadIdx.x;j<field_words;j+=blockDim.x)out[j]=0;
    __syncthreads();
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            const uint32_t xa=row*xstride;
            direct_normal_pack_sources(
                xlo,xhi,xa,xrational?xa+d:UINT32_MAX,UINT32_MAX,0,
                nullptr,nullptr,0,UINT32_MAX,UINT32_MAX,
                source_complex,targets,grain,0,input,slot);
        }
        __syncthreads();if(*slot)return;
        direct_normal_predict_mode_sources(
            old,(const wide *)input,source_complex,targets,grain,
            ((wide *)out)+row*stride,work,false,false,slot);
        if(*slot)return;
    }
    for(size_t j=threadIdx.x;j<field_words;j+=blockDim.x)out_hi[j]=out[j];
}

extern "C" __global__ __launch_bounds__(512) void section_normal_applied_material_section(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xstride,
    uint32_t xrational,uint32_t rows,uint32_t source_complex,uint32_t targets,uint32_t grain,
    int64_t *out,int64_t *out_hi,int64_t *work,int64_t *input,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    normal_applied_material_section_execute(old,xlo,xhi,xstride,xrational,rows,source_complex,targets,grain,
        out,out_hi,work,input,slot,census,lineage,lineage_count);
}
