// Until a successful report is published, its first high word records the current preparation
// stage. Success overwrites every high word with its matching low word. This is diagnostic
// evidence on refusal only and never participates in numerical conduct.
__device__ __forceinline__ void normal_receive_stage(int64_t *report_hi, int stage) {
    if (!threadIdx.x) report_hi[0]=stage;
    __syncthreads();
}
// One received point meets the preceding joint wave family. The normal source and target
// share the same current c: x=(c-p,c,p), y=received-c. No point port consumes an enclosure.
// `producing` is separate from `old` for the addressed comparison: SOURCE_FORWARD is
// produced by the material that caused the earlier report, while H/B/E are accumulated
// into the contemporary material copied from old.
__device__ void section_normal_wave_receive_impl(
    const int64_t *old,const int64_t *producing,const int64_t *joint,
    const int64_t *received_lo,const int64_t *received_hi,
    uint32_t received_at,uint32_t received_den,uint32_t received_disposition,
    uint32_t n,uint32_t grain,int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,
    int64_t *work,int64_t *input,bool producing_reference,bool updated_reference,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t r=2u*n,d=normal_source_components(n);
    size_t sw=normal_state_words(n,n),rw=normal_report_words(n,n),stride=normal_ball_stride(n);
    wide *out=(wide *)report,*frame=(wide *)input;const wide *pair=(const wide *)joint;
    for(size_t i=threadIdx.x;i<sw;i+=blockDim.x)next[i]=old[i];
    for(size_t i=threadIdx.x;i<rw;i+=blockDim.x)report[i]=report_hi[i]=0;
    for(size_t i=threadIdx.x;i<2u*(d+1u);i+=blockDim.x)frame[i]=0;
    __syncthreads();
    normal_receive_stage(report_hi,1);
    if(!threadIdx.x){
        wide *x=out+normal_source_at(n),*y=out+NORMAL_OBSERVED*stride;
        wide radius=pair[2u*r];
        normal_wave_source_lift(pair,r,x,slot);
        wide den=fibre_current_denominator(received_lo,received_hi,received_den,received_disposition,slot),S=(wide)1<<grain,rounds=0;
        for(uint32_t j=0;j<r&&! *slot;++j){
            if(received_lo[received_at+j]!=received_hi[received_at+j]){atomicOr(slot,REFUSED_MALFORMED);break;}
            wide v=received_lo[received_at+j],lo=signed_product_divide_2(v,S/2,den,0,slot),hi=signed_product_divide_2(v,S/2,den,1,slot);
            y[j]=sub_checked(v<0?hi:lo,pair[r+j],slot);if(lo!=hi)rounds=add_checked(rounds,1,slot);
        }
        y[r]=add_checked(radius,rounds,slot);
        for(uint32_t j=0;j<=d;++j)frame[d+1u+j]=x[j];
        if(!*slot)normal_observation_moments(x,y,n,n,report,slot);
    }
    __syncthreads();if(*slot)return;
    // The old response is retained before any newly fitted material is published.
    normal_receive_stage(report_hi,2);
    direct_normal_predict_mode(producing,frame,n,n,grain,out+NORMAL_SOURCE_FORWARD*stride,work,false,producing_reference,slot);
    if(*slot)return;
    normal_receive_stage(report_hi,3);
    normal_increment(next+normal_matrix_words(n,n),out+normal_source_at(n),out+NORMAL_OBSERVED*stride,
        report+normal_report_base(n,n),n,n,false,slot);
    if(*slot)return;
    normal_receive_stage(report_hi,4);
    normal_fit(next,n,n,grain,work,out+normal_metadata_at(n,n),slot);
    if(*slot)return;
    normal_receive_stage(report_hi,5);
    direct_normal_predict_mode(next,frame,n,n,grain,out,work,false,updated_reference,slot);
    if(*slot)return;
    normal_receive_stage(report_hi,6);
    if(!threadIdx.x){
        for(uint32_t j=0;j<r;++j){
            out[NORMAL_RETURNED_DIFFERENCE*stride+j]=sub_checked(out[NORMAL_OBSERVED*stride+j],out[NORMAL_SOURCE_FORWARD*stride+j],slot);
            out[NORMAL_CONTEMPORARY_DIFFERENCE*stride+j]=out[NORMAL_RETURNED_DIFFERENCE*stride+j];
        }
        out[NORMAL_RETURNED_DIFFERENCE*stride+r]=add_checked(out[NORMAL_OBSERVED*stride+r],out[NORMAL_SOURCE_FORWARD*stride+r],slot);
        out[NORMAL_CONTEMPORARY_DIFFERENCE*stride+r]=out[NORMAL_RETURNED_DIFFERENCE*stride+r];
    }
    __syncthreads();if(*slot)return;
    for(size_t i=threadIdx.x;i<sw;i+=blockDim.x)next_hi[i]=next[i];
    for(size_t i=threadIdx.x;i<rw;i+=blockDim.x)report_hi[i]=report[i];
}

extern "C" __global__ __launch_bounds__(512) void section_normal_wave_receive(
    const int64_t *old,const int64_t *joint,const int64_t *received_lo,const int64_t *received_hi,
    uint32_t received_at,uint32_t received_den,uint32_t received_disposition,
    uint32_t n,uint32_t grain,int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,
    int64_t *work,int64_t *input,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    section_normal_wave_receive_impl(old,old,joint,received_lo,received_hi,received_at,received_den,
        received_disposition,n,grain,next,next_hi,report,report_hi,work,input,true,true,slot,census,lineage,lineage_count);
}

extern "C" __global__ __launch_bounds__(512) void section_normal_wave_receive_applied(
    const int64_t *old,const int64_t *joint,const int64_t *received_lo,const int64_t *received_hi,
    uint32_t received_at,uint32_t received_den,uint32_t received_disposition,
    uint32_t n,uint32_t grain,int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,
    int64_t *work,int64_t *input,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    section_normal_wave_receive_impl(old,old,joint,received_lo,received_hi,received_at,received_den,
        received_disposition,n,grain,next,next_hi,report,report_hi,work,input,false,false,slot,census,lineage,lineage_count);
}

// Comparison variant: the contemporaneous material is updated and fitted, but the
// SOURCE_FORWARD report is evaluated with the separately supplied producing material.
extern "C" __global__ __launch_bounds__(512) void section_normal_wave_comparison(
    const int64_t *old,const int64_t *producing,const int64_t *joint,
    const int64_t *received_lo,const int64_t *received_hi,
    uint32_t received_at,uint32_t received_den,uint32_t received_disposition,
    uint32_t n,uint32_t grain,uint32_t producing_reference,uint32_t updated_reference,
    int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,
    int64_t *work,int64_t *input,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    section_normal_wave_receive_impl(old,producing,joint,received_lo,received_hi,received_at,received_den,
        received_disposition,n,grain,next,next_hi,report,report_hi,work,input,producing_reference!=0,updated_reference!=0,
        slot,census,lineage,lineage_count);
}
