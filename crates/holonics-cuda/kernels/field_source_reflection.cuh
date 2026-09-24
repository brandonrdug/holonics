// Immutable material application: (u,b) -> (v-u,D*v-b), with
// v=2(I+D D*)^-1(u+D b). The cached LDL is only a proposal; the exact
// residual against D supplies the output bound for every admitted input.
extern "C" __global__ __launch_bounds__(512) void section_field_source_factor(
    const int64_t *cov,const int64_t *cov_hi,uint32_t d,uint32_t grain,
    int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!d||(d&1u)||grain<1||grain>120){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *C=(const wide *)cov;wide *a=(wide *)out,*diag=a+(size_t)d*d,S=(wide)1<<grain;
    for(size_t i=threadIdx.x;i<(size_t)d*d;i+=blockDim.x)if(cov[i]!=cov_hi[i])atomicOr(slot,REFUSED_MALFORMED);
    __syncthreads();if(*slot)return;
    for(size_t ij=threadIdx.x;ij<(size_t)d*d;ij+=blockDim.x){
        uint32_t i=ij/d,j=ij%d;size_t at=2u*((size_t)(i/2u)*(d/2u)+j/2u);
        wide value=(i&1u)==(j&1u)?C[at]:(i&1u)?C[at+1u]:sub_checked(0,C[at+1u],slot);
        a[ij]=i==j?add_checked(value,S,slot):value;
    }
    __syncthreads();if(*slot)return;
    field_enclosed_factor(a,diag,d,grain,slot);if(*slot)return;
    for(size_t i=threadIdx.x;i<2u*((size_t)d*d+d);i+=blockDim.x)out_hi[i]=out[i];
}

// One implementation owns scalar, section and fixed-material-adjoint arithmetic.
// The exact residual against D certifies the cached factor's proposal in every case.
__device__ void field_source_apply(
    const wide *D,wide material_error,const wide *a,const wide *x,
    uint32_t d,uint32_t count,uint32_t grain,wide *work,int64_t *dots,
    int64_t *trace,int64_t *trace_hi,wide *y,uint32_t *slot){
    const uint32_t width=d+2u*count,m=d/2u;
    const wide *u=x,*b=x+d;
    wide *v=work,*rhs=v+d,*residual=rhs+d,*rounds=residual+d;
    for(uint32_t port=threadIdx.x;port<m;port+=blockDim.x){
        HistoryInteger re,im;wide omitted=0;
        for(uint32_t j=0;j<count;++j)history_complex_add_product(re,im,D[(size_t)j*d+2u*port],D[(size_t)j*d+2u*port+1u],b[2u*j],b[2u*j+1u],false);
        rhs[2u*port]=product_checked(2,add_checked(u[2u*port],operative_grid(re,grain,&omitted,slot),slot),slot);
        rhs[2u*port+1u]=product_checked(2,add_checked(u[2u*port+1u],operative_grid(im,grain,&omitted,slot),slot),slot);
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x)field_enclosed_solve(a,a+(size_t)d*d,d,grain,rhs,v,slot);
    __syncthreads();if(*slot)return;
    for(uint32_t j=threadIdx.x;j<count;j+=blockDim.x){
        HistoryInteger re,im;wide omitted=0;
        for(uint32_t port=0;port<d;port+=2u)history_complex_add_product(re,im,D[(size_t)j*d+port],D[(size_t)j*d+port+1u],v[port],v[port+1u],true);
        history_write_integer(re,dots+10u*j,dots+10u*j,slot);history_write_integer(im,dots+10u*j+5u,dots+10u*j+5u,slot);
        y[d+2u*j]=sub_checked(operative_grid(re,grain,&omitted,slot),b[2u*j],slot);
        y[d+2u*j+1u]=sub_checked(operative_grid(im,grain,&omitted,slot),b[2u*j+1u],slot);rounds[j]=omitted;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t port=threadIdx.x;port<m;port+=blockDim.x){
        MomentInteger re,im;operative_reflection_residual(D,u,v,b,dots,d,count,count,port,grain,re,im,slot);
        if(trace){operative_write_moment(re,trace+36u*port,trace_hi+36u*port,slot);operative_write_moment(im,trace+36u*port+18u,trace_hi+36u*port+18u,slot);}
        wide omitted=0;residual[2u*port]=operative_moment_grid(re,2u*grain,&omitted,slot);
        residual[2u*port+1u]=operative_moment_grid(im,2u*grain,&omitted,slot);rounds[count+port]=omitted;
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        HistoryInteger square,xnorm;wide error=0;
        for(uint32_t j=0;j<d;++j){square=square+history_integer(residual[j])*history_integer(residual[j]);y[j]=sub_checked(v[j],u[j],slot);}
        for(uint32_t j=0;j<width;++j)xnorm=xnorm+history_integer(x[j])*history_integer(x[j]);
        for(uint32_t j=0;j<count+m;++j)error=add_checked(error,rounds[j],slot);
        error=add_checked(error,history_norm_ceiling(square,slot),slot);
        error=add_checked(error,ft_ceil_product(product_checked(2,material_error,slot),history_norm_ceiling(xnorm,slot),grain,slot),slot);
        y[width]=add_checked(x[width],error,slot);
    }
    __syncthreads();if(*slot)return;
 }

__device__ void field_source_validate(
    const int64_t *map,const int64_t *map_hi,const int64_t *bounds,const int64_t *bounds_hi,
    const int64_t *factor,const int64_t *factor_hi,uint32_t d,uint32_t count,uint32_t grain,uint32_t *slot){
    if(!threadIdx.x){
        if(!d||(d&1u)||grain<1||grain>120||((const wide*)bounds)[0]<0)atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<2u*(size_t)d*count;++i)if(map[i]!=map_hi[i])atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<4;++i)if(bounds[i]!=bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<2u*((size_t)d*d+d);++i)if(factor[i]!=factor_hi[i])atomicOr(slot,REFUSED_MALFORMED);
    }
    __syncthreads();
}

extern "C" __global__ __launch_bounds__(512) void section_field_source_reflection(
    const int64_t *map,const int64_t *map_hi,const int64_t *bounds,const int64_t *bounds_hi,
    const int64_t *factor,const int64_t *factor_hi,
    const int64_t *input,const int64_t *input_hi,uint32_t at,
    uint32_t d,uint32_t count,uint32_t grain,int64_t *work,int64_t *dots,
    int64_t *trace,int64_t *trace_hi,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t width=d+2u*count;
    field_source_validate(map,map_hi,bounds,bounds_hi,factor,factor_hi,d,count,grain,slot);
    if(!threadIdx.x){
        if((at&1u)||((const wide*)(input+at))[width]<0)atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<2u*((size_t)width+1u);++i)if(input[at+i]!=input_hi[at+i])atomicOr(slot,REFUSED_MALFORMED);
    }
    __syncthreads();if(*slot)return;
    field_source_apply((const wide*)map,((const wide*)bounds)[0],(const wide*)factor,(const wide*)(input+at),d,count,grain,(wide*)work,dots,trace,trace_hi,(wide*)out,slot);
    if(*slot)return;
    for(size_t j=threadIdx.x;j<2u*((size_t)width+1u);j+=blockDim.x)out_hi[j]=out[j];
}

// A section shares its material and its producing internal branch. Row enclosures remain
// finer witnesses; this does not declare their sources statistically independent.
extern "C" __global__ __launch_bounds__(512) void section_field_source_reflection_section(
    const int64_t *map,const int64_t *map_hi,const int64_t *bounds,const int64_t *bounds_hi,
    const int64_t *factor,const int64_t *factor_hi,
    const int64_t *rows,const int64_t *rows_hi,uint32_t row_stride,uint32_t row_count,
    const int64_t *source,const int64_t *source_hi,uint32_t source_at,uint32_t d,uint32_t count,uint32_t grain,
    int64_t *work,int64_t *dots,int64_t *trace,int64_t *trace_hi,
    int64_t *joint_input,int64_t *joint_input_hi,int64_t *out,int64_t *out_hi,int64_t *flags,
    uint32_t *global_slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    uint32_t row=blockIdx.x;if(row>=row_count)return;uint32_t *slot=(uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);if(!threadIdx.x){for(uint32_t i=0;i<SLOT_WORDS;++i)slot[i]=0;upstream_refused(census,lineage,lineage_count,slot);}__syncthreads();if(slot[SLOT_REFUSED])return;(void)global_slot;
    const uint32_t width=d+2u*count;
    const wide *packed=(const wide*)(source+source_at);
    field_source_validate(map,map_hi,bounds,bounds_hi,factor,factor_hi,d,count,grain,slot);
    if(!threadIdx.x){
        if(!row_count||row_stride!=2u*(d+1u)||(source_at&1u)||packed[width]<0)atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<2u*((size_t)width+1u);++i)if(source[source_at+i]!=source_hi[source_at+i])atomicOr(slot,REFUSED_MALFORMED);
    }
    __syncthreads();if(*slot)return;
    {
        const size_t xa=(size_t)row*row_stride,oa=(size_t)row*2u*(width+1u);
        const wide *x=(const wide*)(rows+xa);
        wide *joined=(wide*)(joint_input+oa);
        if(!threadIdx.x){
            for(size_t i=0;i<row_stride;++i)if(rows[xa+i]!=rows_hi[xa+i])atomicOr(slot,REFUSED_MALFORMED);
            if(x[d]<0)atomicOr(slot,REFUSED_MALFORMED);
            for(uint32_t j=0;j<d;++j)joined[j]=x[j];
            for(uint32_t j=0;j<2u*count;++j)joined[d+j]=packed[d+j];
            joined[width]=add_checked(x[d],packed[width],slot);
        }
        __syncthreads();
        if(*slot)return;
        const size_t ta=(size_t)row*18u*d;
        field_source_apply((const wide*)map,((const wide*)bounds)[0],(const wide*)factor,joined,d,count,grain,(wide*)(work+(size_t)row*2u*(d*3u+count+d/2u)),dots+(size_t)row*count*10u,trace+ta,trace_hi+ta,(wide*)(out+oa),slot);
        if(*slot)return;
        for(size_t j=threadIdx.x;j<2u*((size_t)width+1u);j+=blockDim.x){joint_input_hi[oa+j]=joint_input[oa+j];out_hi[oa+j]=out[oa+j];}
    }
}

extern "C" __global__ __launch_bounds__(512) void section_field_source_reflection_joint_section(
    const int64_t *map,const int64_t *map_hi,const int64_t *bounds,const int64_t *bounds_hi,
    const int64_t *factor,const int64_t *factor_hi,
    const int64_t *rows,const int64_t *rows_hi,uint32_t row_stride,uint32_t row_count,
    uint32_t d,uint32_t count,uint32_t grain,int64_t *work,int64_t *dots,int64_t *out,int64_t *out_hi,int64_t *flags,
    uint32_t *global_slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    uint32_t row=blockIdx.x;if(row>=row_count)return;uint32_t *slot=(uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);if(!threadIdx.x){for(uint32_t i=0;i<SLOT_WORDS;++i)slot[i]=0;upstream_refused(census,lineage,lineage_count,slot);}__syncthreads();if(slot[SLOT_REFUSED])return;(void)global_slot;
    const uint32_t width=d+2u*count;
    field_source_validate(map,map_hi,bounds,bounds_hi,factor,factor_hi,d,count,grain,slot);
    if(!threadIdx.x&&(!row_count||row_stride!=2u*(width+1u)))atomicOr(slot,REFUSED_MALFORMED);
    __syncthreads();if(*slot)return;
    {
        const size_t at=(size_t)row*row_stride;
        const wide *x=(const wide*)(rows+at);
        if(!threadIdx.x){
            for(size_t i=0;i<row_stride;++i)if(rows[at+i]!=rows_hi[at+i])atomicOr(slot,REFUSED_MALFORMED);
            if(x[width]<0)atomicOr(slot,REFUSED_MALFORMED);
        }
        __syncthreads();
        if(*slot)return;
        field_source_apply((const wide*)map,((const wide*)bounds)[0],(const wide*)factor,x,d,count,grain,(wide*)(work+(size_t)row*2u*(d*3u+count+d/2u)),dots+(size_t)row*count*10u,nullptr,nullptr,(wide*)(out+at),slot);
        if(*slot)return;
        for(size_t j=threadIdx.x;j<row_stride;j+=blockDim.x)out_hi[at+j]=out[at+j];
    }
}
