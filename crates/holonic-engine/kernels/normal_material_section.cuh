// Integrate a supplied section into the existing normal geometry, fit once, and apply both
// actual operator cuts to the supplied source field. No record population enters the state.
extern "C" __global__ __launch_bounds__(512) void section_normal_material_section(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xstride,uint32_t xrational,
    const int64_t *ylo,const int64_t *yhi,uint32_t ystride,uint32_t yrational,uint32_t rows,
    uint32_t roots,uint32_t targets,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *before,int64_t *before_hi,
    int64_t *after,int64_t *after_hi,int64_t *work,int64_t *input,int64_t *report,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t d=normal_source_components(roots);
    const size_t sw=normal_state_words(roots,targets),rw=normal_report_words(roots,targets);
    const size_t stride=normal_ball_stride(targets),field_words=NORMAL_WIDE_WORDS*stride*rows;
    wide *current=(wide *)input;
    int64_t *incoming=input+NORMAL_WIDE_WORDS*2u*(d+1u);
    for(size_t j=threadIdx.x;j<sw;j+=blockDim.x)next[j]=old[j];
    for(size_t j=threadIdx.x;j<2u*(d+1u);j+=blockDim.x)current[j]=0;
    for(size_t j=threadIdx.x;j<rw;j+=blockDim.x)report[j]=0;
    __syncthreads();
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            uint32_t xa=row*xstride,ya=row*ystride;
            direct_normal_pack(xlo,xhi,xa,xrational?xa+d:UINT32_MAX,UINT32_MAX,0,
                ylo,yhi,ya,yrational?ya+2u*targets:UINT32_MAX,UINT32_MAX,
                roots,targets,grain,1,input,slot);
            if(!*slot)normal_observation_frame(current,incoming,roots,targets,1,grain,0,report,slot);
        }
        __syncthreads();if(*slot)return;
        normal_increment(next+normal_matrix_words(roots,targets),
            (wide *)report+normal_source_at(targets),(wide *)report+NORMAL_OBSERVED*stride,
            report+normal_report_base(roots,targets),roots,targets,false,slot);
        if(*slot)return;
    }
    normal_fit(next,roots,targets,grain,work,nullptr,slot);
    if(*slot)return;
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            uint32_t xa=row*xstride;
            direct_normal_pack(xlo,xhi,xa,xrational?xa+d:UINT32_MAX,UINT32_MAX,0,
                ylo,yhi,0,UINT32_MAX,UINT32_MAX,roots,targets,grain,0,input,slot);
        }
        __syncthreads();if(*slot)return;
        direct_normal_predict(old,current,roots,targets,grain,((wide *)before)+row*stride,work,false,slot);
        if(*slot)return;
        direct_normal_predict(next,current,roots,targets,grain,((wide *)after)+row*stride,work,false,slot);
        if(*slot)return;
    }
    for(size_t j=threadIdx.x;j<sw;j+=blockDim.x)next_hi[j]=next[j];
    for(size_t j=threadIdx.x;j<field_words;j+=blockDim.x){before_hi[j]=before[j];after_hi[j]=after[j];}
}
