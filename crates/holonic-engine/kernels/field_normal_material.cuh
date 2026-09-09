// Accumulated complex normal material. H=I+sum xx*, B=sum yx*, C=sum |y|².
// Exact moment numerators use the common scale S²; the material matrix uses S.
// Four retained scalar moments are EH, EB, C and EC. No floating-point arithmetic.
__device__ size_t normal_matrix_words(uint32_t n,uint32_t t){return 12u*(size_t)n*t+6u;}
__device__ size_t normal_stat_values(uint32_t n,uint32_t t){size_t m=3u*n;return 2u*m*m+2u*m*t+4u;}
__device__ size_t normal_state_words(uint32_t n,uint32_t t){return normal_matrix_words(n,t)+18u*normal_stat_values(n,t);}
__device__ size_t normal_report_base(uint32_t n,uint32_t t){return 24u*(size_t)t+12u*n+24u;}
__device__ size_t normal_report_words(uint32_t n,uint32_t t){return normal_report_base(n,t)+72u;}
__device__ MomentInteger normal_read(const int64_t *p,uint32_t *slot){
    MomentInteger a;
    for(uint32_t j=0;j<17u;++j){if(p[j]<0 || (uint64_t)p[j]>UINT32_MAX)atomicOr(slot,REFUSED_MALFORMED);a.limb[j]=(uint32_t)p[j];}
    if(p[17]!=0 && p[17]!=1)atomicOr(slot,REFUSED_MALFORMED);
    if(p[17] && a.is_zero())atomicOr(slot,REFUSED_MALFORMED);
    a.negative=p[17]!=0;return a;
}
__device__ MomentInteger normal_wide(wide x){return moment_lift(history_integer(x));}
__device__ MomentInteger normal_abs(MomentInteger x){x.negative=false;return x;}
__device__ wide normal_grid(MomentInteger x,uint32_t shift,bool ceiling,uint32_t *slot){
    wide omitted=0,value=operative_moment_grid(x,shift,&omitted,slot);
    if(ceiling && x.negative){atomicOr(slot,REFUSED_MALFORMED);return 0;}
    return ceiling?add_checked(value,omitted,slot):value;
}
__device__ void normal_product(MomentInteger &re,MomentInteger &im,
    const MomentInteger &ar,const MomentInteger &ai,const MomentInteger &br,const MomentInteger &bi,bool conjugate){
    if(conjugate){re=re+ar*br+ai*bi;im=im+ai*br-ar*bi;}
    else{re=re+ar*br-ai*bi;im=im+ar*bi+ai*br;}
}

// A rounded, strictly positive proposal is solved using the existing LDL owner. The
// residual is then evaluated against the EXACT H and B, not the proposal's normal system.
__device__ void normal_fit(int64_t *state,uint32_t n,uint32_t targets,uint32_t grain,
    int64_t *workspace,wide *diagnostic,uint32_t *slot){
    uint32_t m=3u*n,d=2u*m;size_t matrices=(size_t)m*m,coefficients=(size_t)m*targets;
    wide *M=(wide *)state,*a=(wide *)workspace,*diag=a+(size_t)d*d,*rhs=diag+d;
    int64_t *row_residual=(int64_t *)(rhs+(size_t)d*targets);
    wide *row_norm=(wide *)(row_residual+18u*targets);
    const int64_t *H=state+normal_matrix_words(n,targets),*B=H+36u*matrices,*scalars=B+36u*coefficients;
    for(size_t ij=threadIdx.x;ij<(size_t)d*d;ij+=blockDim.x){
        uint32_t i=ij/d,j=ij%d;const int64_t *h=H+36u*((size_t)(i/2u)*m+j/2u);
        wide value=normal_grid(normal_read(h+((i&1u)==(j&1u)?0u:18u),slot),grain,false,slot);
        if(!(i&1u) && (j&1u))value=sub_checked(0,value,slot);
        // Each real-block entry loses less than one grain unit. This diagonal majorant
        // makes the proposal positive; its difference from H is paid by the residual.
        a[ij]=i==j?add_checked(value,(wide)d,slot):value;
    }
    __syncthreads();if(*slot)return;
    field_enclosed_factor(a,diag,d,grain,slot);if(*slot)return;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        wide *r=rhs+(size_t)row*d,*out=M+(size_t)row*d;bool nonzero=false;
        for(uint32_t j=0;j<d;++j){MomentInteger b=normal_read(B+18u*((size_t)row*d+j),slot);nonzero=nonzero||!b.is_zero();r[j]=normal_grid((j&1u)?-b:b,grain,false,slot);out[j]=0;}
        if(nonzero){
            field_enclosed_solve(a,diag,d,grain,r,out,slot);
            for(uint32_t j=1;j<d;j+=2u)out[j]=sub_checked(0,out[j],slot);
        }
        MomentInteger residual;wide norm=0;
        for(uint32_t j=0;j<d;++j)norm=add_checked(norm,ft_abs(out[j],slot),slot);
        if(nonzero)for(uint32_t j=0;j<m;++j){
            MomentInteger re,im;
            for(uint32_t k=0;k<m;++k){const int64_t *h=H+36u*((size_t)k*m+j);
                normal_product(re,im,normal_wide(out[2u*k]),normal_wide(out[2u*k+1u]),normal_read(h,slot),normal_read(h+18u,slot),false);}
            const int64_t *b=B+36u*((size_t)row*m+j);MomentInteger S=moment_lift(complete_power(grain,slot));
            re=re-S*normal_read(b,slot);im=im-S*normal_read(b+18u,slot);
            residual=residual+normal_abs(re)+normal_abs(im);
        }
        operative_write_moment(residual,row_residual+18u*row,row_residual+18u*row,slot);row_norm[row]=norm;
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        MomentInteger residual;wide norm=0;
        for(uint32_t row=0;row<targets;++row){residual=residual+normal_read(row_residual+18u*row,slot);norm=add_checked(norm,row_norm[row],slot);}
        MomentInteger eh=normal_read(scalars,slot),eb=normal_read(scalars+18u,slot),S=moment_lift(complete_power(grain,slot));
        if(eh.negative||eb.negative)atomicOr(slot,REFUSED_MALFORMED);
        MomentInteger bound=residual+normal_wide(norm)*eh+S*eb;
        M[2u*coefficients]=normal_grid(bound,2u*grain,true,slot);
        M[2u*coefficients+1u]=normal_grid(residual,2u*grain,true,slot);M[2u*coefficients+2u]=norm;
        if(diagnostic){diagnostic[0]=M[2u*coefficients];diagnostic[1]=normal_grid(residual,2u*grain,true,slot);diagnostic[2]=norm;
            diagnostic[3]=normal_grid(eh,grain,true,slot);diagnostic[4]=normal_grid(eb,grain,true,slot);}
    }
    __syncthreads();
}

// Add/subtract an actual observation's exact sufficient-statistic increment.
__device__ void normal_increment(int64_t *stats,const wide *x,const wide *y,const int64_t *errors,
    uint32_t n,uint32_t targets,bool subtract,uint32_t *slot){
    size_t m=3u*n,hh=2u*m*m,bb=2u*m*targets;
    for(size_t at=threadIdx.x;at<hh+bb+4u;at+=blockDim.x){
        MomentInteger value;
        if(at<hh){size_t i=(at/2u)/m,j=(at/2u)%m;if((!x[2u*i]&&!x[2u*i+1u])||(!x[2u*j]&&!x[2u*j+1u]))continue;MomentInteger re,im;
            normal_product(re,im,normal_wide(x[2u*i]),normal_wide(x[2u*i+1u]),normal_wide(x[2u*j]),normal_wide(x[2u*j+1u]),true);value=(at&1u)?im:re;
        }else if(at<hh+bb){size_t ij=(at-hh)/2u,i=ij/m,j=ij%m;if((!y[2u*i]&&!y[2u*i+1u])||(!x[2u*j]&&!x[2u*j+1u]))continue;MomentInteger re,im;
            normal_product(re,im,normal_wide(y[2u*i]),normal_wide(y[2u*i+1u]),normal_wide(x[2u*j]),normal_wide(x[2u*j+1u]),true);value=(at&1u)?im:re;
        }else value=normal_read(errors+18u*(at-hh-bb),slot);
        if(value.overflow){atomicOr(slot,REFUSED_CARRIER);continue;}
        if(value.is_zero())continue;
        MomentInteger old=normal_read(stats+18u*at,slot);value=subtract?old-value:old+value;
        operative_write_moment(value,stats+18u*at,stats+18u*at,slot);
    }
    __syncthreads();
}

__device__ void field_normal_material_prepare(const int64_t *old,const wide *origin_current,const wide *origin_forward,
    const wide *current,const int64_t *incoming,uint32_t n,uint32_t linked,uint32_t grain,
    int64_t *next,int64_t *next_hi,int64_t *report,int64_t *report_hi,int64_t *workspace,
    uint32_t targets,uint32_t factor_width,uint32_t *slot){
    uint32_t d=6u*n,R=2u*targets;size_t stride=R+1u,gain=6u*stride,extra=gain+d+1u;
    size_t state_words=normal_state_words(n,targets),report_words=normal_report_words(n,targets);
    wide *out=(wide *)report;const wide *M=(const wide *)old;wide S=(wide)1<<grain;
    for(size_t i=threadIdx.x;i<state_words;i+=blockDim.x)next[i]=old[i];
    for(size_t i=threadIdx.x;i<report_words;i+=blockDim.x)report[i]=report_hi[i]=0;
    __syncthreads();
    if(!threadIdx.x){
        if(!n||!targets||!workspace||grain<1||grain>120||linked>1||(linked&&(!origin_current||!origin_forward)))atomicOr(slot,REFUSED_MALFORMED);
        wide *y=out+2u*stride,ey=0;
        if(!*slot && factor_width)contextual_tensor_target(incoming,n,factor_width,targets,grain,y,&ey,slot);
        else if(!*slot)for(uint32_t j=0;j<R;++j){const int64_t *v=incoming+3u*(j/2u);if(v[2]<=0){atomicOr(slot,REFUSED_MALFORMED);break;}
            wide lo=signed_product_divide_2(v[j%2u],S/2,v[2],0,slot),hi=signed_product_divide_2(v[j%2u],S/2,v[2],1,slot);y[j]=v[j%2u]<0?hi:lo;if(lo!=hi)ey=add_checked(ey,1,slot);}
        y[R]=ey;
        if(linked&&! *slot){
            const wide *x=origin_current+d+1u;for(uint32_t j=0;j<=d;++j)out[gain+j]=x[j];
            wide ex=x[d],nx=complete_norm(x,d,slot),ny=complete_norm(y,R,slot);
            if(ex<0)atomicOr(slot,REFUSED_MALFORMED);
            MomentInteger eh=(MomentInteger(2)*normal_wide(nx)+normal_wide(ex))*normal_wide(ex);
            MomentInteger eb=normal_wide(ny)*normal_wide(ex)+normal_wide(nx)*normal_wide(ey)+normal_wide(ex)*normal_wide(ey),cy;
            for(uint32_t j=0;j<R;++j)cy=cy+normal_wide(y[j])*normal_wide(y[j]);
            MomentInteger ec=(MomentInteger(2)*normal_wide(ny)+normal_wide(ey))*normal_wide(ey);
            int64_t *e=report+normal_report_base(n,targets);
            operative_write_moment(eh,e,e,slot);operative_write_moment(eb,e+18,e+18,slot);
            operative_write_moment(cy,e+36,e+36,slot);operative_write_moment(ec,e+54,e+54,slot);
        }
    }
    __syncthreads();if(*slot)return;
    if(linked){normal_increment(next+normal_matrix_words(n,targets),out+gain,out+2u*stride,report+normal_report_base(n,targets),n,targets,false,slot);
        if(*slot)return;normal_fit(next,n,targets,grain,workspace,out+extra,slot);}
    __syncthreads();if(*slot)return;
    // Prediction rows are independent; preserve the existing ordered complex products.
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        wide oldnorm=0,newnorm=0;for(uint32_t j=0;j<d;++j){oldnorm=add_checked(oldnorm,ft_abs(M[(size_t)row*d+j],slot),slot);newnorm=add_checked(newnorm,ft_abs(((wide *)next)[(size_t)row*d+j],slot),slot);}
        // Row scratch is separate from the eventual output and exact normal-fit residual.
        wide *scratch=(wide *)workspace;
        scratch[4u*row]=oldnorm;scratch[4u*row+1u]=newnorm;
        scratch[4u*row+2u]=linked?linear_material_row(M,nullptr,origin_current+d+1u,row,3u*n,grain,out+stride,slot):0;
        scratch[4u*row+3u]=linear_material_row((wide *)next,nullptr,current+d+1u,row,3u*n,grain,out,slot);
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        wide oldnorm=0,newnorm=0,ro=0,rn=0;wide *scratch=(wide *)workspace;
        for(uint32_t row=0;row<targets;++row){oldnorm=add_checked(oldnorm,scratch[4u*row],slot);newnorm=add_checked(newnorm,scratch[4u*row+1u],slot);ro=add_checked(ro,scratch[4u*row+2u],slot);rn=add_checked(rn,scratch[4u*row+3u],slot);}
        wide error=((wide *)next)[(size_t)R*3u*n];
        out[R]=ft_prediction_error(error,newnorm,current+d+1u,d,current[2u*(d+1u)-1u],rn,grain,slot);
        if(linked){
            wide pe=ft_prediction_error(M[(size_t)R*3u*n],oldnorm,origin_current+d+1u,d,origin_current[2u*(d+1u)-1u],ro,grain,slot);out[2u*stride-1u]=pe;
            for(uint32_t j=0;j<R;++j){out[3u*stride+j]=sub_checked(out[2u*stride+j],origin_forward[j],slot);out[4u*stride+j]=sub_checked(out[stride+j],origin_forward[j],slot);out[5u*stride+j]=sub_checked(out[2u*stride+j],out[stride+j],slot);}
            out[4u*stride-1u]=add_checked(out[3u*stride-1u],origin_forward[R],slot);out[5u*stride-1u]=add_checked(pe,origin_forward[R],slot);out[6u*stride-1u]=add_checked(out[3u*stride-1u],pe,slot);
        }else{out[extra]=error;out[extra+1u]=M[(size_t)R*3u*n+1u];out[extra+2u]=newnorm;const int64_t *e=next+normal_state_words(n,targets)-72u;out[extra+3u]=normal_grid(normal_read(e,slot),grain,true,slot);out[extra+4u]=normal_grid(normal_read(e+18u,slot),grain,true,slot);}
    }
    __syncthreads();if(*slot)return;
    for(size_t i=threadIdx.x;i<state_words;i+=blockDim.x)next_hi[i]=next[i];
    for(size_t i=threadIdx.x;i<report_words;i+=blockDim.x)report_hi[i]=report[i];
}

// Decode an older normal operator by subtracting exactly the later observed increments.
extern "C" __global__ __launch_bounds__(512) void section_field_normal_material_prefix(
    const int64_t *current,const int64_t *journal,uint32_t later,uint32_t n,uint32_t targets,uint32_t grain,
    int64_t *out,int64_t *hi,int64_t *workspace,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    size_t words=normal_state_words(n,targets);
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)out[j]=current[j];
    __syncthreads();
    for(uint32_t j=later;j>0;--j)if(journal[2u*(j-1u)+1u]){
        const int64_t *r=(const int64_t *)(uintptr_t)journal[2u*(j-1u)];const wide *v=(const wide *)r;size_t stride=2u*(size_t)targets+1u;
        normal_increment(out+normal_matrix_words(n,targets),v+6u*stride,v+2u*stride,r+normal_report_base(n,targets),n,targets,true,slot);if(*slot)return;
    }
    normal_fit(out,n,targets,grain,workspace,nullptr,slot);if(*slot)return;
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)hi[j]=out[j];
}
