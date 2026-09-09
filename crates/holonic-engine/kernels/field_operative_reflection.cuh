// Full-current operative reflection. The covariance is only an LDL proposal; the residual
// is recomputed from the actual retained numerical contact columns and entering currents.
__device__ wide operative_moment_grid(const MomentInteger &a,uint32_t shift,wide *rounds,uint32_t *slot){
    HistoryInteger q;bool omitted=false;
    if(a.overflow){atomicOr(slot,REFUSED_CARRIER);return 0;}
    for(uint32_t bit=0;bit<MomentInteger::BITS;++bit)if((a.limb[bit/MomentInteger::LIMB_BITS]>>(bit%MomentInteger::LIMB_BITS))&1u){
        if(bit<shift)omitted=true;
        else if(bit-shift>=HistoryInteger::BITS)atomicOr(slot,REFUSED_CARRIER);
        else q.limb[(bit-shift)/HistoryInteger::LIMB_BITS]|=(uint32_t)1u<<((bit-shift)%HistoryInteger::LIMB_BITS);
    }
    q.negative=a.negative && !q.is_zero();if(omitted)*rounds=add_checked(*rounds,1,slot);
    return history_narrow(q,slot);
}
__device__ void operative_write_moment(const MomentInteger &a,int64_t *lo,int64_t *hi,uint32_t *slot){
    if(a.overflow){atomicOr(slot,REFUSED_CARRIER);return;}
    for(uint32_t i=0;i<MomentInteger::LIMBS;++i)lo[i]=hi[i]=(int64_t)a.limb[i];
    lo[MomentInteger::LIMBS]=hi[MomentInteger::LIMBS]=a.negative && !a.is_zero()?1:0;
}

__device__ void field_operative_reflection_prepare(
    const int64_t *table,const int64_t *query,const int64_t *origin,const int64_t *incoming,
    const int64_t *frame,const int64_t *old_frame,const int64_t *raw_cov,const wide *before,
    uint32_t n,uint32_t linked,uint32_t grain,uint64_t at,
    int64_t *next_raw_lo,int64_t *next_raw_hi,wide *report,wide *report_hi,wide *workspace,uint32_t *slot
){
    const uint32_t d=6u*n,m=d/2u;const size_t stride=d+1u;
    const uint32_t old_count=(uint32_t)table[18],count=(uint32_t)table[19];
    const wide *old_map=(const wide *)(uintptr_t)table[0],*old_b=(const wide *)(uintptr_t)table[1],*old_e=(const wide *)(uintptr_t)table[2];
    int64_t *map_lo=(int64_t *)(uintptr_t)table[3],*map_hi=(int64_t *)(uintptr_t)table[4];
    int64_t *b_lo=(int64_t *)(uintptr_t)table[5],*b_hi=(int64_t *)(uintptr_t)table[6];
    int64_t *e_lo=(int64_t *)(uintptr_t)table[7],*e_hi=(int64_t *)(uintptr_t)table[8];
    int64_t *cov_lo=(int64_t *)(uintptr_t)table[9],*cov_hi=(int64_t *)(uintptr_t)table[10];
    int64_t *h_lo=(int64_t *)(uintptr_t)table[11],*h_hi=(int64_t *)(uintptr_t)table[12];
    int64_t *mb_lo=(int64_t *)(uintptr_t)table[13],*mb_hi=(int64_t *)(uintptr_t)table[14];
    int64_t *scratch=(int64_t *)(uintptr_t)table[15],*trace=(int64_t *)(uintptr_t)table[16],*trace_hi=(int64_t *)(uintptr_t)table[17];
    wide *map=(wide *)map_lo,*b=(wide *)b_lo,*e=(wide *)e_lo,*mb=(wide *)mb_lo;
    wide *moment_rounds=(wide *)scratch,*dot_rounds=moment_rounds+(size_t)m*m+m;
    int64_t *qraw=(int64_t *)(dot_rounds+count);
    wide *matrix=workspace,*u=matrix+(size_t)d*d,*birth=u+d,*rhs=birth+d,*v=rhs+d,*diagonal=v+d,*residual=diagonal+d;
    wide *extra=(wide *)(trace+18u*(size_t)d);
    if(threadIdx.x==0){
        for(size_t i=0;i<6u*stride;++i)report[i]=report_hi[i]=0;
        for(size_t i=0;i<18u*(size_t)d+12u;++i)trace[i]=trace_hi[i]=0;
        if(!n || grain<1u || grain>120u || linked>1u || count!=old_count+linked || old_e[0]<0 || old_e[1]<0 || before[4u*stride-1u]<0)
            atomicOr(slot,REFUSED_MALFORMED);
        wide ud=1,dd=1;
        if(!*slot && field_paired_build_faces(query,origin,incoming,frame,old_frame,n,linked,u,birth,&ud,&dd,slot)){
            // Keep the immutable birth moment for the existing fixed-map source codec.
            wide den=1;
            if(field_paired_build_covariance(raw_cov,d,linked,birth,dd,matrix,&den,slot)){
                for(size_t i=0;i<(size_t)d*d;++i)next_raw_lo[i]=next_raw_hi[i]=to_word(matrix[i],slot);
                next_raw_lo[(size_t)d*d]=next_raw_hi[(size_t)d*d]=to_word(den,slot);
            }
            wide eu=0,ed=0,S=(wide)((uwide)1u<<grain);
            for(uint32_t j=0;j<d;++j){
                u[j]=history_narrow(complete_divide(history_integer(u[j])*history_integer(S),history_integer(ud),&eu,slot),slot);
                if(linked)map[(size_t)old_count*d+j]=history_narrow(complete_divide(history_integer(birth[j])*history_integer(S),history_integer(dd),&ed,slot),slot);
            }
            e[0]=history_norm_ceiling(history_integer(old_e[0])*history_integer(old_e[0])+history_integer(ed)*history_integer(ed),slot);
            e[1]=old_e[1];extra[0]=eu;
            if(linked)b[2u*old_count]=b[2u*old_count+1u]=0;
            if(!count){for(uint32_t j=0;j<d;++j)map[j]=0;b[0]=b[1]=0;}
        }
    }
    __syncthreads();if(*slot)return;
    for(size_t i=threadIdx.x;i<(size_t)old_count*d;i+=blockDim.x)map[i]=old_map[i];
    for(size_t i=threadIdx.x;i<2u*(size_t)old_count;i+=blockDim.x)b[i]=old_b[i];
    __syncthreads();
    operative_moments_prepare(map_lo,b_lo,e_lo,d,count,grain,cov_lo,cov_hi,h_lo,h_hi,mb_lo,mb_hi,moment_rounds,slot);
    __syncthreads();if(*slot)return;
    const wide *C=(const wide *)cov_lo,*h=(const wide *)h_lo;
    wide S=(wide)((uwide)1u<<grain);
    for(size_t ij=threadIdx.x;ij<(size_t)d*d;ij+=blockDim.x){
        uint32_t i=ij/d,j=ij%d;size_t a=2u*((size_t)(i/2u)*m+j/2u);
        wide value=((i&1u)==(j&1u))?C[a]:((i&1u)?C[a+1u]:sub_checked(0,C[a+1u],slot));
        matrix[ij]=i==j?add_checked(value,S,slot):value;
    }
    __syncthreads();if(*slot)return;
    field_enclosed_factor(matrix,diagonal,d,grain,slot);if(*slot)return;
    if(threadIdx.x==0){
        HistoryInteger xnorm;
        for(uint32_t j=0;j<d;++j){rhs[j]=product_checked(2,add_checked(u[j],h[j],slot),slot);xnorm=xnorm+history_integer(u[j])*history_integer(u[j]);}
        for(size_t j=0;j<2u*(size_t)old_count;++j)xnorm=xnorm+history_integer(old_b[j])*history_integer(old_b[j]);
        extra[1]=history_norm_ceiling(xnorm,slot);
        if(!*slot)field_enclosed_solve(matrix,diagonal,d,grain,rhs,v,slot);
    }
    __syncthreads();if(*slot)return;
    for(uint64_t row=threadIdx.x;row<count;row+=blockDim.x){
        HistoryInteger re,im;wide omitted=0;
        for(uint32_t j=0;j<d;j+=2u)history_complex_add_product(re,im,map[row*d+j],map[row*d+j+1u],v[j],v[j+1u],true);
        history_write_integer(re,qraw+10u*row,qraw+10u*row,slot);history_write_integer(im,qraw+10u*row+5u,qraw+10u*row+5u,slot);
        wide br=operative_grid(re,grain,&omitted,slot),bi=operative_grid(im,grain,&omitted,slot);
        b[2u*row]=sub_checked(br,row<old_count?old_b[2u*row]:0,slot);
        b[2u*row+1u]=sub_checked(bi,row<old_count?old_b[2u*row+1u]:0,slot);dot_rounds[row]=omitted;
    }
    __syncthreads();if(*slot)return;
    // Exact numerator of (I+Dhat Dhat*)vhat-2(uhat+Dhat bhat), at scale S^3.
    for(uint32_t port=threadIdx.x;port<m;port+=blockDim.x){
        MomentInteger re=moment_lift(complete_power(2u*grain,slot))*moment_lift(history_integer(sub_checked(v[2u*port],product_checked(2,u[2u*port],slot),slot)));
        MomentInteger im=moment_lift(complete_power(2u*grain,slot))*moment_lift(history_integer(sub_checked(v[2u*port+1u],product_checked(2,u[2u*port+1u],slot),slot)));
        for(uint32_t row=0;row<count;++row){
            HistoryInteger qr=history_read_integer(qraw+10u*(size_t)row,slot),qi=history_read_integer(qraw+10u*(size_t)row+5u,slot);
            if(row<old_count){qr=qr-HistoryInteger(2)*history_integer(S)*history_integer(old_b[2u*row]);qi=qi-HistoryInteger(2)*history_integer(S)*history_integer(old_b[2u*row+1u]);}
            MomentInteger dr=moment_lift(history_integer(map[(size_t)row*d+2u*port])),di=moment_lift(history_integer(map[(size_t)row*d+2u*port+1u]));
            re=re+dr*moment_lift(qr)-di*moment_lift(qi);im=im+dr*moment_lift(qi)+di*moment_lift(qr);
        }
        operative_write_moment(re,trace+36u*port,trace_hi+36u*port,slot);operative_write_moment(im,trace+36u*port+18u,trace_hi+36u*port+18u,slot);
        wide omitted=0;residual[2u*port]=operative_moment_grid(re,2u*grain,&omitted,slot);
        residual[2u*port+1u]=operative_moment_grid(im,2u*grain,&omitted,slot);rhs[port]=omitted;
    }
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        wide eq=0,er=0;HistoryInteger square;
        for(uint32_t row=0;row<count;++row)eq=add_checked(eq,dot_rounds[row],slot);
        for(uint32_t j=0;j<d;++j)square=square+history_integer(residual[j])*history_integer(residual[j]);
        for(uint32_t j=0;j<m;++j)er=add_checked(er,rhs[j],slot);
        wide rn=add_checked(history_norm_ceiling(square,slot),er,slot);
        wide ec=add_checked(add_checked(old_e[1],extra[0],slot),add_checked(ft_ceil_product(product_checked(2,e[0],slot),extra[1],grain,slot),add_checked(rn,eq,slot),slot),slot);
        e[1]=ec;extra[2]=eq;extra[3]=er;extra[4]=rn;extra[5]=ec;
        wide ev=add_checked(ec,extra[0],slot),ep=add_checked(before[4u*stride-1u],ev,slot);
        for(uint32_t j=0;j<d;++j){
            report[j]=v[j];report[stride+j]=sub_checked(v[j],u[j],slot);
            report[3u*stride+j]=(at&1u)?sub_checked(before[3u*stride+j],v[j],slot):add_checked(before[3u*stride+j],v[j],slot);
            report[4u*stride+j]=u[j];report[5u*stride+j]=residual[j];
        }
        report[d]=ev;report[2u*stride-1u]=ec;report[4u*stride-1u]=ep;report[5u*stride-1u]=extra[0];report[6u*stride-1u]=1;
    }
    __syncthreads();if(*slot)return;
    // Reflection has changed b and its bound, while D and its bound are unchanged.
    // Keep the covariance and its exact numerical/error chart from the first preparation.
    operative_moments_prepare<false>(map_lo,b_lo,e_lo,d,count,grain,cov_lo,cov_hi,h_lo,h_hi,mb_lo,mb_hi,moment_rounds,slot);
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){for(uint32_t j=0;j<d;++j)report[2u*stride+j]=((const wide *)h_lo)[j];report[3u*stride-1u]=mb[1];}
    __syncthreads();if(*slot)return;
    operative_copy_point(map_lo,map_hi,2u*(size_t)(count?count:1u)*d);operative_copy_point(b_lo,b_hi,4u*(size_t)(count?count:1u));operative_copy_point(e_lo,e_hi,4);
    operative_copy_point((int64_t *)report,(int64_t *)report_hi,12u*stride);operative_copy_point(trace,trace_hi,18u*(size_t)d+12u);
}
