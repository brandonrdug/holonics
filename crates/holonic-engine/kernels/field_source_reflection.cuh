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

extern "C" __global__ __launch_bounds__(512) void section_field_source_reflection(
    const int64_t *map,const int64_t *map_hi,const int64_t *bounds,const int64_t *bounds_hi,
    const int64_t *factor,const int64_t *factor_hi,
    const int64_t *input,const int64_t *input_hi,uint32_t at,
    uint32_t d,uint32_t count,uint32_t grain,int64_t *work,int64_t *dots,
    int64_t *trace,int64_t *trace_hi,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t width=d+2u*count,m=d/2u;
    const wide *D=(const wide *)map,*e=(const wide *)bounds,*x=(const wide *)(input+at),*a=(const wide *)factor;
    const wide *u=x,*b=x+d;wide *v=(wide *)work,*rhs=v+d,*residual=rhs+d,*rounds=residual+d;
    wide *y=(wide *)out;
    if(!threadIdx.x){
        if(!d||(d&1u)||(at&1u)||grain<1||grain>120||e[0]<0||x[width]<0)atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<2u*(size_t)d*count;++i)if(map[i]!=map_hi[i])atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<4;++i)if(bounds[i]!=bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<2u*((size_t)d*d+d);++i)if(factor[i]!=factor_hi[i])atomicOr(slot,REFUSED_MALFORMED);
        for(size_t i=0;i<2u*((size_t)width+1u);++i)if(input[at+i]!=input_hi[at+i])atomicOr(slot,REFUSED_MALFORMED);
    }
    __syncthreads();if(*slot)return;
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
        operative_write_moment(re,trace+36u*port,trace_hi+36u*port,slot);operative_write_moment(im,trace+36u*port+18u,trace_hi+36u*port+18u,slot);
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
        error=add_checked(error,ft_ceil_product(product_checked(2,e[0],slot),history_norm_ceiling(xnorm,slot),grain,slot),slot);
        y[width]=add_checked(x[width],error,slot);
    }
    __syncthreads();if(*slot)return;
    for(size_t j=threadIdx.x;j<2u*((size_t)width+1u);j+=blockDim.x)out_hi[j]=out[j];
}
