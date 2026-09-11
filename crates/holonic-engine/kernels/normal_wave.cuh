// A fixed learned normal response restricted to S(p,c)=(c-p,c,p).
// The top companion block is an exact join, not a learned approximation to c.
extern "C" __global__ void section_normal_wave_joint_seed(
    const int64_t *joint,const int64_t *joint_hi,uint32_t n,uint32_t grain,
    int64_t *previous,int64_t *previous_hi,int64_t *current,int64_t *current_hi,
    int64_t *power,int64_t *power_hi,int64_t *meta,int64_t *meta_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t r=2u*n,d=2u*n;size_t cells=2u*(size_t)d*d;
    const wide *z=(const wide *)joint;
    for(size_t j=threadIdx.x;j<2u*(2u*r+1u);j+=blockDim.x)
        if(joint[j]!=joint_hi[j])atomicOr(slot,REFUSED_MALFORMED);
    if(!threadIdx.x&&z[2u*r]<0)atomicOr(slot,REFUSED_MALFORMED);
    __syncthreads();if(*slot)return;
    for(uint32_t j=threadIdx.x;j<r;j+=blockDim.x){
        ((wide *)previous)[j]=z[j];((wide *)current)[j]=z[r+j];
    }
    if(!threadIdx.x){
        ((wide *)previous)[r]=((wide *)current)[r]=z[2u*r];
        ((wide *)meta)[0]=1;((wide *)meta)[1]=((wide *)meta)[2]=0;((wide *)meta)[3]=z[2u*r];
    }
    for(size_t j=threadIdx.x;j<cells;j+=blockDim.x)
        ((wide *)power)[j]=((j&1u)==0&&(j/2u)/d==(j/2u)%d)?(wide)1<<grain:0;
    __syncthreads();
    for(size_t j=threadIdx.x;j<2u*(r+1u);j+=blockDim.x){previous_hi[j]=previous[j];current_hi[j]=current[j];}
    for(size_t j=threadIdx.x;j<2u*cells;j+=blockDim.x)power_hi[j]=power[j];
    for(size_t j=threadIdx.x;j<8u;j+=blockDim.x)meta_hi[j]=meta[j];
}

__device__ void normal_wave_entry(const wide *M,uint32_t n,uint32_t row,uint32_t col,
    uint32_t grain,wide *re,wide *im,uint32_t *slot){
    *re=*im=0;
    if(row<n){if(col==n+row)*re=(wide)1<<grain;return;}
    uint32_t r=row-n,j=col%n;size_t at=2u*((size_t)r*3u*n+j);
    if(col<n){*re=sub_checked(M[at+4u*n],M[at],slot);*im=sub_checked(M[at+4u*n+1u],M[at+1u],slot);}
    else{*re=add_checked(M[at],M[at+2u*n],slot);*im=add_checked(M[at+1u],M[at+2u*n+1u],slot);
        if(r==j)*re=add_checked(*re,(wide)1<<grain,slot);}
}

extern "C" __global__ void section_normal_wave_seed(
    const int64_t *plo,const int64_t *phi,uint32_t pa,uint32_t pd,uint32_t ps,uint32_t previous_kind,
    const int64_t *clo,const int64_t *chi,uint32_t ca,uint32_t cd,uint32_t cs,
    uint32_t n,uint32_t grain,int64_t *seed,int64_t *seed_hi,int64_t *bound,int64_t *bound_hi,
    int64_t *previous,int64_t *previous_hi,int64_t *current,int64_t *current_hi,
    int64_t *power,int64_t *power_hi,int64_t *meta,int64_t *meta_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t r=2u*n,d=2u*n;size_t cells=2u*(size_t)d*d;
    for(size_t i=threadIdx.x;i<cells;i+=blockDim.x)((wide *)power)[i]=((i&1u)==0 && (i/2u)/d==(i/2u)%d)?(wide)1<<grain:0;
    __syncthreads();
    if(!threadIdx.x){
        wide S=(wide)1<<grain,total=0;
        if(previous_kind>1u){atomicOr(slot,REFUSED_MALFORMED);}
        uint32_t current_seed_at=previous_kind?2u*(r+1u):r+1u;
        if(previous_kind&&! *slot){
            for(uint32_t j=0;j<2u*(r+1u);++j){
                if(plo[pa+j]!=phi[pa+j])atomicOr(slot,REFUSED_MALFORMED);
                seed[j]=previous[j]=plo[pa+j];
            }
            const wide *v=(const wide *)(plo+pa);
            if(v[r]<0)atomicOr(slot,REFUSED_MALFORMED);
            for(uint32_t j=0;j<=r;++j)((wide *)bound)[j]=v[j];
            total=v[r];
        }else if(!*slot){
            wide den=fibre_current_denominator(plo,phi,pd,ps,slot),error=0;
            seed[r]=(int64_t)den;
            for(uint32_t j=0;j<r&&! *slot;++j){
                if(plo[pa+j]!=phi[pa+j]){atomicOr(slot,REFUSED_MALFORMED);break;}
                wide v=plo[pa+j];seed[j]=(int64_t)v;
                wide a=signed_product_divide_2(v,S/2,den,0,slot),b=signed_product_divide_2(v,S/2,den,1,slot);
                ((wide *)previous)[j]=v<0?b:a;((wide *)bound)[j]=((wide *)previous)[j];
                if(a!=b)error=add_checked(error,1,slot);
            }
            ((wide *)previous)[r]=error;total=error;
        }
        if(!*slot){
            wide den=fibre_current_denominator(clo,chi,cd,cs,slot),error=0;
            seed[current_seed_at+r]=(int64_t)den;
            for(uint32_t j=0;j<r&&! *slot;++j){
                if(clo[ca+j]!=chi[ca+j]){atomicOr(slot,REFUSED_MALFORMED);break;}
                wide v=clo[ca+j];seed[current_seed_at+j]=(int64_t)v;
                wide a=signed_product_divide_2(v,S/2,den,0,slot),b=signed_product_divide_2(v,S/2,den,1,slot);
                ((wide *)current)[j]=v<0?b:a;((wide *)bound)[r+j]=((wide *)current)[j];
                if(a!=b)error=add_checked(error,1,slot);
            }
            ((wide *)current)[r]=error;total=add_checked(total,error,slot);
        }
        ((wide *)bound)[2u*r]=total;
        ((wide *)meta)[0]=1;((wide *)meta)[1]=0;((wide *)meta)[2]=0;((wide *)meta)[3]=total;
    }
    __syncthreads();if(*slot)return;
    for(size_t i=threadIdx.x;i<2u*cells;i+=blockDim.x)power_hi[i]=power[i];
    for(size_t i=threadIdx.x;i<(previous_kind?3u:2u)*(r+1u);i+=blockDim.x)seed_hi[i]=seed[i];
    for(size_t i=threadIdx.x;i<2u*(r+1u);i+=blockDim.x){previous_hi[i]=previous[i];current_hi[i]=current[i];}
    for(size_t i=threadIdx.x;i<2u*(2u*r+1u);i+=blockDim.x)bound_hi[i]=bound[i];
    for(size_t i=threadIdx.x;i<8u;i+=blockDim.x)meta_hi[i]=meta[i];
}

extern "C" __global__ void section_normal_wave_power(const int64_t *material,const int64_t *prior,
    uint32_t n,uint32_t grain,int64_t *next,int64_t *next_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t d=2u*n;size_t at=(size_t)blockIdx.x*blockDim.x+threadIdx.x;
    if(at>=(size_t)d*d)return;uint32_t row=at/d,col=at%d;
    wide *out=(wide *)next;const wide *M=(const wide *)material,*Q=(const wide *)prior;
    if(row<n){out[2u*at]=Q[2u*((size_t)(row+n)*d+col)];out[2u*at+1u]=Q[2u*((size_t)(row+n)*d+col)+1u];}
    else{
        MomentInteger re,im;
        for(uint32_t k=0;k<d;++k){wide ar,ai;normal_wave_entry(M,n,row,k,grain,&ar,&ai,slot);
            size_t q=2u*((size_t)k*d+col);
            normal_product(re,im,normal_wide(ar),normal_wide(ai),normal_wide(Q[q]),normal_wide(Q[q+1u]),false);}
        out[2u*at]=normal_grid(re,grain,false,slot);out[2u*at+1u]=normal_grid(im,grain,false,slot);
    }
    if(*slot)return;for(uint32_t j=0;j<4u;++j)next_hi[4u*at+j]=next[4u*at+j];
}

__device__ wide normal_wave_multiply_upper(wide a,wide b,uint32_t grain,uint32_t *slot){
    return normal_grid(normal_wide(a)*normal_wide(b),grain,true,slot);
}
__device__ void section_normal_wave_evaluate_impl(const int64_t *material,const int64_t *power,
    const int64_t *seed_bound,const int64_t *old_meta,uint32_t n,uint32_t grain,uint64_t steps,
    int64_t *meta,int64_t *meta_hi,int64_t *joint,int64_t *joint_hi,int64_t *current,int64_t *current_hi,
    int64_t *work,bool reference,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t d=2u*n,r=2u*n;wide S=(wide)1<<grain;
    const wide *Q=(const wide *)power,*z=(const wide *)seed_bound;wide *out=(wide *)joint,*scratch=(wide *)work;
    for(uint32_t row=threadIdx.x;row<d;row+=blockDim.x){
        MomentInteger re,im;wide row_norm=0,col_norm=0;
        for(uint32_t k=0;k<d;++k){size_t a=2u*((size_t)row*d+k),b=2u*((size_t)k*d+row);
            normal_product(re,im,normal_wide(Q[a]),normal_wide(Q[a+1u]),normal_wide(z[2u*k]),normal_wide(z[2u*k+1u]),false);
            row_norm=add_checked(row_norm,add_checked(ft_abs(Q[a],slot),ft_abs(Q[a+1u],slot),slot),slot);
            col_norm=add_checked(col_norm,add_checked(ft_abs(Q[b],slot),ft_abs(Q[b+1u],slot),slot),slot);}
        wide rr=0,ri=0;
        out[2u*row]=operative_moment_grid(re,grain,&rr,slot);out[2u*row+1u]=operative_moment_grid(im,grain,&ri,slot);
        scratch[2u*d+row]=add_checked(rr,ri,slot);
        scratch[2u*row]=row_norm;scratch[2u*row+1u]=col_norm;
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        wide B=((const wide *)old_meta)[0];
        for(uint32_t j=0;j<2u*d;++j){wide v=scratch[j]/S+(scratch[j]%S!=0);if(v>B)B=v;}
        wide coefficient_error=reference?((const wide *)material)[6u*(size_t)n*n]:0;
        if(coefficient_error<0||B<1){atomicOr(slot,REFUSED_MALFORMED);}
        wide defect=add_checked(product_checked(product_checked(2,coefficient_error,slot),B,slot),(wide)2u*d,slot);
        wide base=add_checked(S,defect,slot),growth=S;uint64_t exponent=steps;
        while(exponent&&! *slot){if(exponent&1u)growth=normal_wave_multiply_upper(growth,base,grain,slot);
            exponent>>=1u;if(exponent)base=normal_wave_multiply_upper(base,base,grain,slot);}
        wide error=product_checked(B,sub_checked(growth,S,slot),slot),norm=0,rounds=0;
        for(uint32_t j=0;j<d;++j)rounds=add_checked(rounds,scratch[2u*d+j],slot);
        for(uint32_t j=0;j<2u*d;++j)norm=add_checked(norm,ft_abs(z[j],slot),slot);
        wide radius=add_checked(normal_wave_multiply_upper(error,add_checked(norm,z[2u*d],slot),grain,slot),
            add_checked(product_checked(B,z[2u*d],slot),rounds,slot),slot);
        out[2u*d]=radius;wide *m=(wide *)meta;m[0]=B;m[1]=defect;m[2]=error;m[3]=radius;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t j=threadIdx.x;j<r;j+=blockDim.x)((wide *)current)[j]=out[r+j];
    if(!threadIdx.x)((wide *)current)[r]=out[2u*r];
    __syncthreads();
    for(size_t j=threadIdx.x;j<2u*(2u*r+1u);j+=blockDim.x)joint_hi[j]=joint[j];
    for(size_t j=threadIdx.x;j<2u*(r+1u);j+=blockDim.x)current_hi[j]=current[j];
    for(size_t j=threadIdx.x;j<8u;j+=blockDim.x)meta_hi[j]=meta[j];
}

extern "C" __global__ void section_normal_wave_evaluate(const int64_t *material,const int64_t *power,
    const int64_t *seed_bound,const int64_t *old_meta,uint32_t n,uint32_t grain,uint64_t steps,
    int64_t *meta,int64_t *meta_hi,int64_t *joint,int64_t *joint_hi,int64_t *current,int64_t *current_hi,
    int64_t *work,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    section_normal_wave_evaluate_impl(material,power,seed_bound,old_meta,n,grain,steps,meta,meta_hi,joint,joint_hi,
        current,current_hi,work,true,slot,census,lineage,lineage_count);
}

extern "C" __global__ void section_normal_wave_evaluate_applied(const int64_t *material,const int64_t *power,
    const int64_t *seed_bound,const int64_t *old_meta,uint32_t n,uint32_t grain,uint64_t steps,
    int64_t *meta,int64_t *meta_hi,int64_t *joint,int64_t *joint_hi,int64_t *current,int64_t *current_hi,
    int64_t *work,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x)return;
    section_normal_wave_evaluate_impl(material,power,seed_bound,old_meta,n,grain,steps,meta,meta_hi,joint,joint_hi,
        current,current_hi,work,false,slot,census,lineage,lineage_count);
}
