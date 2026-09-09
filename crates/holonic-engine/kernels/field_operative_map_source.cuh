// Evaluate retained coefficient expressions, not the observations which produced them.
// A source-dependent return is Q(P k* + V ell* + D_source H), rounded once after the complete sum.
extern "C" __global__ void section_field_operative_join_return_bounds(
    const wide *ordinary,const wide *source,wide *lo,wide *hi,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x || threadIdx.x || upstream_refused(census,lineage,lineage_count,slot))return;
    if(ordinary[0]<0 || ordinary[1]<0 || source[0]<0 || source[1]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    lo[0]=hi[0]=add_checked(ordinary[0],source[1],slot);lo[1]=hi[1]=ordinary[1];
}
extern "C" __global__ void section_field_operative_map_anchor(
    const int64_t *anchor,const int64_t *births,uint32_t base_count,uint32_t count,uint32_t d,
    int64_t *lo,int64_t *hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!d || (d&1u) || base_count>count){if(!blockIdx.x&&!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
    size_t at=blockIdx.x*blockDim.x+threadIdx.x,width=2u*(size_t)d;
    if(at>=width*(count?count:1u))return;
    if(!count){lo[at]=hi[at]=0;return;}
    uint32_t row=at/width;size_t column=at%width;
    const int64_t *source=row<base_count?anchor+width*row:(const int64_t *)(uintptr_t)births[row-base_count];
    lo[at]=hi[at]=source[column];
}

extern "C" __global__ void __launch_bounds__(512) section_field_operative_map_expression(
    const int64_t *before_wire,const int64_t *source_wire,const int64_t *births,
    const int64_t *ports_wire,const int64_t *factors_wire,const int64_t *overlaps_wire,
    uint32_t count,uint32_t factor_count,uint32_t overlap_count,uint32_t d,uint32_t grain,
    int64_t *lo,int64_t *hi,int64_t *scratch,int64_t *round_lo,int64_t *round_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t port=blockIdx.x*blockDim.x+threadIdx.x,m=d/2u;
    if(!d || (d&1u) || factor_count>count || overlap_count>factor_count || grain<1u || grain>120u
        || (overlap_count && (!source_wire || !births || !overlaps_wire))){if(!port)atomicOr(slot,REFUSED_MALFORMED);return;}
    if(port>=m)return;
    const wide *before=(const wide *)before_wire,*source=(const wide *)source_wire,
        *p=(const wide *)ports_wire,*f=(const wide *)factors_wire,*h=(const wide *)overlaps_wire;
    constexpr size_t words=HistoryInteger::BITS/(sizeof(int64_t)*CHAR_BIT)+1;
    int64_t *column=scratch+2u*words*(size_t)port*(count?count:1u);
    for(uint32_t row=0;row<count;++row){
        HistoryInteger re,im;
        if(row<factor_count)for(uint32_t term=0;term<2u;++term)
            history_complex_add_product(re,im,f[2u*((size_t)term*factor_count+row)],f[2u*((size_t)term*factor_count+row)+1u],
                p[(size_t)term*d+2u*port],p[(size_t)term*d+2u*port+1u],true);
        history_write_integer(re,column+2u*words*row,column+2u*words*row,slot);
        history_write_integer(im,column+2u*words*row+words,column+2u*words*row+words,slot);
    }
    // One worker owns a complete root-port component. Join additions are chronological;
    // workers write disjoint components, including the overflow and omission receipts.
    for(uint32_t after=0;after<overlap_count && !*slot;++after){
        int64_t joined=births[2u*(size_t)after];uint32_t left=0,right=after;
        while(left<right){uint32_t mid=left+(right-left)/2u;if(births[2u*(size_t)mid+1u]<joined)left=mid+1u;else right=mid;}
        if(left==after || births[2u*(size_t)left+1u]!=joined)continue;
        uint32_t prior=left;
        for(uint32_t side=0;side<2u;++side){
            uint32_t row=side?after:prior,other=side?prior:after;
            HistoryInteger re=history_read_integer(column+2u*words*row,slot),im=history_read_integer(column+2u*words*row+words,slot);
            history_complex_add_product(re,im,h[2u*after],h[2u*after+1u],source[(size_t)other*d+2u*port],source[(size_t)other*d+2u*port+1u],!side);
            history_write_integer(re,column+2u*words*row,column+2u*words*row,slot);
            history_write_integer(im,column+2u*words*row+words,column+2u*words*row+words,slot);
        }
    }
    wide omitted=0;
    for(uint32_t row=0;row<count && !*slot;++row){
        wide re=operative_grid(history_read_integer(column+2u*words*row,slot),grain,&omitted,slot);
        wide im=operative_grid(history_read_integer(column+2u*words*row+words,slot),grain,&omitted,slot);
        size_t at=(size_t)row*d+2u*port;
        ((wide *)lo)[at]=add_checked(before[at],re,slot);((wide *)lo)[at+1u]=add_checked(before[at+1u],im,slot);
        for(uint32_t j=0;j<4u;++j)hi[2u*at+j]=lo[2u*at+j];
    }
    if(!count){((wide *)lo)[2u*port]=((wide *)hi)[2u*port]=0;((wide *)lo)[2u*port+1u]=((wide *)hi)[2u*port+1u]=0;}
    ((wide *)round_lo)[port]=((wide *)round_hi)[port]=omitted;
}

extern "C" __global__ void section_field_operative_expression_current(
    const int64_t *before_wire,const int64_t *bounds_wire,const int64_t *delta_wire,const int64_t *delta_bounds_wire,
    const int64_t *rounds_wire,uint32_t count,uint32_t ports,uint32_t exact_deposit,
    int64_t *lo,int64_t *hi,int64_t *bound_lo,int64_t *bound_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    size_t at=blockIdx.x*blockDim.x+threadIdx.x;
    const wide *before=(const wide *)before_wire,*bounds=(const wide *)bounds_wire,
        *delta=(const wide *)delta_wire,*de=(const wide *)delta_bounds_wire,*rounds=(const wide *)rounds_wire;
    if(bounds[0]<0 || bounds[1]<0 || de[0]<0 || de[1]<0 || exact_deposit>1u){if(!at)atomicOr(slot,REFUSED_MALFORMED);return;}
    if(at<2u*(size_t)count)((wide *)lo)[at]=((wide *)hi)[at]=delta?add_checked(before[at],delta[at],slot):before[at];
    if(!at){
        wide error=0;for(uint32_t p=0;p<ports;++p){if(rounds[p]<0)atomicOr(slot,REFUSED_MALFORMED);error=add_checked(error,rounds[p],slot);}
        ((wide *)bound_lo)[0]=((wide *)bound_hi)[0]=exact_deposit?bounds[0]:add_checked(bounds[0],add_checked(de[0],error,slot),slot);
        ((wide *)bound_lo)[1]=((wide *)bound_hi)[1]=add_checked(bounds[1],de[1],slot);
        if(!count)for(uint32_t j=0;j<2u;++j)((wide *)lo)[j]=((wide *)hi)[j]=0;
    }
}
