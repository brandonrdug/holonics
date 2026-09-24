// Apply a retained normal map to rows that already carry complete enclosure packets.
// The source radius is transported through the same resident operation as its centre;
// no host centre selection or point conversion is permitted.
extern "C" __global__ __launch_bounds__(512) void section_normal_applied_enclosed_features(
    const int64_t *old,const int64_t *xlo,const int64_t *xhi,uint32_t xstride,
    uint32_t rows,uint32_t source_complex,uint32_t targets,uint32_t grain,uint32_t joint,
    int64_t *out,int64_t *out_hi,int64_t *work,int64_t *flags,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    const uint32_t row=blockIdx.x;if(row>=rows)return;
    uint32_t *status=(uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);
    if(!threadIdx.x)for(uint32_t i=0;i<SLOT_WORDS;++i)status[i]=0;
    __syncthreads();
    if(upstream_refused(census,lineage,lineage_count,status))return;
    const uint32_t d=2u*source_complex;
    const size_t stride=normal_ball_stride(targets);
    const int64_t *lo=xlo+(size_t)row*xstride,*hi=xhi+(size_t)row*xstride;
    int64_t *destination=out+2u*stride*row,*destination_hi=out_hi+2u*stride*row;
    int64_t *row_work=work+4u*(size_t)targets*row;
    if(!threadIdx.x){if(joint>1u)atomicOr(status,REFUSED_MALFORMED);ec_ball(lo,hi,d,status);}
    __syncthreads();if(*status)return;
    direct_normal_predict_ball_sources(old,(const wide *)lo,source_complex,targets,grain,
        (wide *)destination,row_work,false,false,status,joint!=0u);
    if(*status)return;
    for(size_t j=threadIdx.x;j<2u*stride;j+=blockDim.x)destination_hi[j]=destination[j];
}

// Append one homogeneous complex coordinate to each resident boundary row.
// The existing radius remains the joint radius of the enlarged packet.
extern "C" __global__ void section_enclosure_append_homogeneous(
    const int64_t *x,const int64_t *xh,uint32_t rows,uint32_t d,uint32_t grain,
    int64_t *out,int64_t *oh,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count){
    if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    const size_t in_stride=2u*((size_t)d+1u),out_stride=2u*((size_t)d+3u);
    const int64_t *a=x+in_stride*row,*ah=xh+in_stride*row;int64_t *b=out+out_stride*row,*bh=oh+out_stride*row;
    if(grain<1u||grain>120u){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(!ec_ball(a,ah,d,slot))return;
    const wide *input=(const wide*)a;wide *output=(wide*)b;
    for(uint32_t j=0;j<d;++j)output[j]=input[j];
    output[d]=(wide)((uwide)1u<<grain);output[d+1u]=0;
    output[d+2u]=input[d];ec_seal(b,bh,d+2u,slot);
}
