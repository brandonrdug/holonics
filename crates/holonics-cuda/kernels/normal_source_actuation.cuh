// A source section acts through its learned joined passages on the complete held joint current.
// Source rows are transient measured incidence. One section produces one successor ecology.
__device__ void section_normal_source_actuation_impl(
    const int64_t *material,const int64_t *joint,const int64_t *field_lo,const int64_t *field_hi,
    uint32_t rows,uint32_t rational,uint32_t n,uint32_t grain,
    int64_t *out,int64_t *out_hi,int64_t *anchors,int64_t *frame,int64_t *work,
    bool reference,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t r=2u*n,w=2u*r,d=3u*r,stride=r+rational;
    wide *q=(wide *)out,*x=(wide *)anchors,*y=x+w+1u,*delta=y+w+1u,*input=(wide *)frame;
    __shared__ bool exact_geometry,zero_response;
    for(uint32_t j=threadIdx.x;j<2u*(w+1u);j+=blockDim.x)out[j]=joint[j];
    for(uint32_t j=threadIdx.x;j<2u*(d+1u);j+=blockDim.x)input[j]=0;
    __syncthreads();
    // A certified common zero subspace: H e_j=e_j, B e_j=0, and applied M e_j=0.
    // This is exact invisibility for the present normal law, not absence of source current.
    // The first frame slot is otherwise unused by the direct normal predictor.
    const uint32_t m=normal_sources(n);
    const int64_t *H=material+normal_matrix_words(n,n),*B=H+COMPLEX_MOMENT_WIRE_WORDS*(size_t)m*m;
    const int64_t *errors=material+normal_state_words(n,n)-NORMAL_STATISTIC_COUNT*MOMENT_WIRE_WORDS;
    if(!threadIdx.x)exact_geometry=!reference||(normal_read(errors,slot).is_zero()&&normal_read(errors+MOMENT_WIRE_WORDS,slot).is_zero());
    __syncthreads();if(*slot)return;
    for(uint32_t j=threadIdx.x;j<m;j+=blockDim.x){
        bool invisible=exact_geometry;
        MomentInteger unit=normal_wide((wide)1<<grain)*normal_wide((wide)1<<grain);
        if(invisible&&reference){
            const int64_t *diagonal=H+COMPLEX_MOMENT_WIRE_WORDS*((size_t)j*m+j);
            invisible=normal_read(diagonal,slot)==unit&&normal_read(diagonal+MOMENT_WIRE_WORDS,slot).is_zero();
        }
        if(invisible&&reference)for(uint32_t i=0;i<m&&invisible;++i)if(i!=j){
            const int64_t *h=H+COMPLEX_MOMENT_WIRE_WORDS*((size_t)i*m+j);
            invisible=normal_read(h,slot).is_zero()&&normal_read(h+MOMENT_WIRE_WORDS,slot).is_zero();
        }
        if(invisible)for(uint32_t i=0;i<n&&invisible;++i){
            const int64_t *b=B+COMPLEX_MOMENT_WIRE_WORDS*((size_t)i*m+j);
            const wide *coefficient=(const wide *)material+2u*((size_t)i*m+j);
            invisible=(!reference||(normal_read(b,slot).is_zero()&&normal_read(b+MOMENT_WIRE_WORDS,slot).is_zero()))
                &&coefficient[0]==0&&coefficient[1]==0;
        }
        input[j]=invisible?0:1;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t row=1;row<rows;++row){
        if(!threadIdx.x){
            wide error=0,S=(wide)1<<grain;
            for(uint32_t side=0;side<2u&&! *slot;++side){
                uint32_t at=(row-1u+side)*stride;
                wide den=fibre_current_denominator(field_lo,field_hi,rational?at+r:UINT32_MAX,UINT32_MAX,slot);
                for(uint32_t j=0;j<r&&! *slot;++j){
                    if(field_lo[at+j]!=field_hi[at+j]){atomicOr(slot,REFUSED_MALFORMED);break;}
                    wide v=field_lo[at+j],lo=signed_product_divide_2(v,S/2,den,0,slot),hi=signed_product_divide_2(v,S/2,den,1,slot);
                    x[side*r+j]=v<0?hi:lo;if(lo!=hi)error=add_checked(error,1,slot);
                }
            }
            x[w]=error;
            for(uint32_t j=0;j<r&&! *slot;++j){
                input[d+1u+j]=sub_checked(x[r+j],x[j],slot);
                input[d+1u+r+j]=x[r+j];input[d+1u+2u*r+j]=x[j];
            }
            input[2u*(d+1u)-1u]=product_checked(2,error,slot);
            zero_response=exact_geometry&&error==0;
            for(uint32_t j=0;j<m&&zero_response;++j)
                if(input[j]&&(input[d+1u+2u*j]||input[d+1u+2u*j+1u]))zero_response=false;
        }
        __syncthreads();if(*slot)return;
        if(zero_response){for(uint32_t j=threadIdx.x;j<=r;j+=blockDim.x)delta[j]=0;}
        else direct_normal_predict_mode(material,input,n,n,grain,delta,work,false,reference,slot);
        __syncthreads();
        if(*slot)return;
        for(uint32_t j=threadIdx.x;j<r;j+=blockDim.x){y[j]=x[r+j];y[r+j]=add_checked(x[r+j],delta[j],slot);}
        if(!threadIdx.x)y[w]=add_checked(product_checked(2,x[w],slot),delta[r],slot);
        __syncthreads();if(*slot)return;
        passive_current_ball(x,y,q,q,w,grain,true,slot);
        if(*slot)return;
    }
    for(uint32_t j=threadIdx.x;j<2u*(w+1u);j+=blockDim.x)out_hi[j]=out[j];
}

extern "C" __global__ __launch_bounds__(512) void section_normal_source_actuation(
    const int64_t *material,const int64_t *joint,const int64_t *field_lo,const int64_t *field_hi,
    uint32_t rows,uint32_t rational,uint32_t n,uint32_t grain,
    int64_t *out,int64_t *out_hi,int64_t *anchors,int64_t *frame,int64_t *work,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    section_normal_source_actuation_impl(material,joint,field_lo,field_hi,rows,rational,n,grain,
        out,out_hi,anchors,frame,work,true,slot,census,lineage,lineage_count);
}

extern "C" __global__ __launch_bounds__(512) void section_normal_source_actuation_applied(
    const int64_t *material,const int64_t *joint,const int64_t *field_lo,const int64_t *field_hi,
    uint32_t rows,uint32_t rational,uint32_t n,uint32_t grain,
    int64_t *out,int64_t *out_hi,int64_t *anchors,int64_t *frame,int64_t *work,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    section_normal_source_actuation_impl(material,joint,field_lo,field_hi,rows,rational,n,grain,
        out,out_hi,anchors,frame,work,false,slot,census,lineage,lineage_count);
}
