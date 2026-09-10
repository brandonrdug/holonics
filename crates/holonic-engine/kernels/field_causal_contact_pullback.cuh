// Return through the actual forward word. B_g=[1,g;-conj(g),1] has ||B_g^-1||<=1.
// x=B_g^-1 b, y=B_g^{-*} lambda, z=2(x_e conj(y_f)-y_e conj(x_f)).
// The input reaction is 2y-lambda. Keep the joint unitary error instead of multiplying the
// incoming uncertainty by a per-join gain. z supplies the sparse Hermitian morphology return.
extern "C" __global__ void section_field_operative_propagation_covector(
    const wide *paired,uint32_t d,uint32_t count,uint32_t old_count,wide *lo,wide *hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    size_t at=blockIdx.x*blockDim.x+threadIdx.x;
    if(old_count>count){if(!at)atomicOr(slot,REFUSED_MALFORMED);return;}
    if(at<2u*(size_t)old_count)lo[at]=hi[at]=paired[d+at];
    if(!at){wide error=paired[2u*(size_t)d+4u*(size_t)count+2u];if(error<0)atomicOr(slot,REFUSED_MALFORMED);lo[2u*(size_t)old_count]=hi[2u*(size_t)old_count]=error;}
}

extern "C" __global__ void section_field_operative_propagation_return(
    const wide *incoming,const wide *extra,uint32_t d,uint32_t count,uint32_t old_count,
    wide *paired_lo,wide *paired_hi,wide *bounds_lo,wide *bounds_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    size_t at=blockIdx.x*blockDim.x+threadIdx.x;
    if(old_count>count || extra[0]<0 || extra[1]<0){if(!at)atomicOr(slot,REFUSED_MALFORMED);return;}
    if(at<2u*(size_t)old_count)paired_lo[d+at]=paired_hi[d+at]=incoming[at];
    if(!at){size_t e=2u*(size_t)d+4u*(size_t)count;
        paired_lo[e+2u]=paired_hi[e+2u]=extra[0];
        paired_lo[e+5u]=paired_hi[e+5u]=add_checked(paired_lo[e+5u],extra[1],slot);
        bounds_lo[0]=bounds_hi[0]=add_checked(bounds_lo[0],extra[1],slot);
    }
}
__device__ void cp_inverse_pair(const PropagationInteger &gr,const PropagationInteger &gi,
    const PropagationInteger &unit,const PropagationInteger &den,const wide *b,wide *out,
    wide *rounds,uint32_t *slot){
    PropagationInteger ar=cp_lift(history_integer(b[0])),ai=cp_lift(history_integer(b[1])),
        br=cp_lift(history_integer(b[2])),bi=cp_lift(history_integer(b[3]));
    out[0]=cp_quotient(unit*(unit*ar-gr*br+gi*bi),den,rounds,slot);
    out[1]=cp_quotient(unit*(unit*ai-gr*bi-gi*br),den,rounds,slot);
    out[2]=cp_quotient(unit*(gr*ar+gi*ai+unit*br),den,rounds,slot);
    out[3]=cp_quotient(unit*(gr*ai-gi*ar+unit*bi),den,rounds,slot);
}
__device__ wide cp_l1(const wide *v,size_t count,uint32_t *slot){
    wide norm=0;for(size_t j=0;j<count;++j)norm=add_checked(norm,of_magnitude(magnitude(v[j]),false,slot),slot);
    return norm;
}
extern "C" __global__ void section_field_causal_contact_pullback(
    const int64_t *map_wire,const int64_t *bounds_wire,const int64_t *forward_wire,const int64_t *covector_wire,
    uint32_t d,uint32_t count,uint32_t grain,
    int64_t *incoming_lo,int64_t *incoming_hi,int64_t *overlap_lo,int64_t *overlap_hi,
    int64_t *error_lo,int64_t *error_hi,int64_t *bounds_lo,int64_t *bounds_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x || threadIdx.x || upstream_refused(census,lineage,lineage_count,slot))return;
    const wide *D=(const wide *)map_wire,*source_bounds=(const wide *)bounds_wire,*covector=(const wide *)covector_wire;
    wide *incoming=(wide *)incoming_lo,*overlaps=(wide *)overlap_lo,*errors=(wide *)error_lo;
    if(!d || (d&1u) || grain<1u || grain>120u || source_bounds[0]<0 || covector[2u*(size_t)count]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t j=0;j<2u*(size_t)(count?count:1u);++j){incoming[j]=count?covector[j]:0;overlaps[j]=0;}
    for(size_t j=0;j<(count?count:1u);++j)errors[j]=0;
    wide returning_error=covector[2u*(size_t)count],gradient_error=0;
    PropagationInteger unit=cp_lift(complete_power(2u*grain,slot)),unit_square=unit*unit;
    for(uint32_t index=count;index>0 && !*slot;--index){
        uint32_t after=index-1u;const int64_t *trace=forward_wire+CP_TRACE_WORDS*after;
        if(trace[0]==-1)continue;
        if(trace[0]<0 || (uint64_t)trace[0]>=after){atomicOr(slot,REFUSED_MALFORMED);break;}
        uint32_t before=(uint32_t)trace[0];const wide *b=(const wide *)(trace+CP_BEFORE);
        wide input_error=((const wide *)(trace+CP_RADIUS))[0];
        HistoryInteger gr_raw=history_read_integer(trace+CP_OVERLAP,slot),gi_raw=history_read_integer(trace+CP_OVERLAP+CP_HISTORY_WORDS,slot),
            overlap_error=history_read_integer(trace+CP_OVERLAP_ERROR,slot);
        if(input_error<0 || overlap_error.negative){atomicOr(slot,REFUSED_MALFORMED);break;}
        PropagationInteger gr=cp_lift(gr_raw),gi=cp_lift(gi_raw),den=unit_square+gr*gr+gi*gi;
        wide lambda[4]={incoming[2u*before],incoming[2u*before+1u],incoming[2u*after],incoming[2u*after+1u]},x[4],y[4];
        wide rx=0,ry=0,rg=0;
        cp_inverse_pair(gr,gi,unit,den,b,x,&rx,slot);
        cp_inverse_pair(-gr,-gi,unit,den,lambda,y,&ry,slot);
        wide eg=complete_to_grid(overlap_error,grain,&rg,slot);eg=add_checked(eg,rg,slot);
        wide nb=cp_l1(b,4,slot),nl=cp_l1(lambda,4,slot),nx=cp_l1(x,4,slot),ny=cp_l1(y,4,slot);
        wide ex=add_checked(input_error,add_checked(ft_ceil_product(eg,nb,grain,slot),rx,slot),slot);
        wide ey=add_checked(returning_error,add_checked(ft_ceil_product(eg,nl,grain,slot),ry,slot),slot);
        HistoryInteger r1,i1,r2,i2;wide rz=0;
        history_complex_add_product(r1,i1,y[2],y[3],x[0],x[1],true);
        history_complex_add_product(r2,i2,x[2],x[3],y[0],y[1],true);
        overlaps[2u*after]=operative_grid(HistoryInteger(2)*(r1-r2),grain,&rz,slot);
        overlaps[2u*after+1u]=operative_grid(HistoryInteger(2)*(i1-i2),grain,&rz,slot);
        wide ez=add_checked(product_checked(2,add_checked(ft_ceil_product(ex,add_checked(ny,ey,slot),grain,slot),
            ft_ceil_product(nx,ey,grain,slot),slot),slot),rz,slot);
        errors[after]=ez;
        wide nd=add_checked(cp_l1(D+(size_t)before*d,d,slot),cp_l1(D+(size_t)after*d,d,slot),slot);
        wide nz=cp_l1(overlaps+2u*after,2,slot);
        gradient_error=add_checked(gradient_error,add_checked(ft_ceil_product(source_bounds[0],add_checked(nz,ez,slot),grain,slot),
            ft_ceil_product(nd,ez,grain,slot),slot),slot);
        returning_error=add_checked(returning_error,product_checked(2,add_checked(ft_ceil_product(eg,nl,grain,slot),ry,slot),slot),slot);
        for(uint32_t j=0;j<2u;++j){
            incoming[2u*before+j]=sub_checked(product_checked(2,y[j],slot),lambda[j],slot);
            incoming[2u*after+j]=sub_checked(product_checked(2,y[2u+j],slot),lambda[2u+j],slot);
        }
    }
    ((wide *)bounds_lo)[0]=returning_error;((wide *)bounds_lo)[1]=gradient_error;
    if(*slot)return;
    for(size_t j=0;j<4u*(size_t)(count?count:1u);++j){incoming_hi[j]=incoming_lo[j];overlap_hi[j]=overlap_lo[j];}
    for(size_t j=0;j<2u*(size_t)(count?count:1u);++j)error_hi[j]=error_lo[j];
    for(size_t j=0;j<4u;++j)bounds_hi[j]=bounds_lo[j];
}
