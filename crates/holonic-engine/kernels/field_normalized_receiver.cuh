// A real receiver of two retained complex-current balls. The original carriers remain held.
// Each declared group retains its complete normalized exponential face. The returned current
// is q-p and its pullback J_p(q-p), without an inherited token target or terminal tanh/deposit.
// Output is an opaque exact-word report: ten signed-wide values per coordinate, with both
// word lanes identical. Each pair is an outward interval at the declared current grain.

__device__ void normalized_interval_product(wide a,wide b,wide c,wide d,uint32_t grain,
    wide *lo,wide *hi,uint32_t *slot) {
    wide lows[4]={product_shift(a,c,grain,0,slot),product_shift(a,d,grain,0,slot),
        product_shift(b,c,grain,0,slot),product_shift(b,d,grain,0,slot)};
    wide highs[4]={product_shift(a,c,grain,1,slot),product_shift(a,d,grain,1,slot),
        product_shift(b,c,grain,1,slot),product_shift(b,d,grain,1,slot)};
    *lo=lows[0];*hi=highs[0];
    for(uint32_t i=1;i<4;++i){if(lows[i]<*lo)*lo=lows[i];if(highs[i]>*hi)*hi=highs[i];}
}

// Joint coordinate receiver of a material-current ball in a declared I/Q quadrature.
// Softmax preserves projected-potential
// ordering, so no exponential is needed to certify a unique maximum. All unexcluded
// coordinates are retained. For each i, project the real centre onto the closed cone
// x_i >= x_j for every j. Pool i with the descending coordinates above their pooled
// mean. Its exact squared distance is sum(x_j^2) - sum(x_j)^2/k. The cone intersects
// the joint Euclidean ball iff that distance is <= radius^2. The other quadrature
// stays unchanged at the minimizer; no independent coordinate-box relaxation is used.
extern "C" __global__ void section_field_material_packet_receiver(
    const int64_t *wire,uint32_t targets,uint32_t quadrature,int64_t *scratch,int64_t *lo,int64_t *hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!targets || quadrature>1u){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *v=(const wide *)wire;wide radius=v[2u*targets];
    if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *ordered=(wide *)scratch;
    for(uint32_t i=0;i<targets;++i){
        wide value=v[2u*i+quadrature];uint32_t j=i;
        while(j && ordered[j-1u]<value){ordered[j]=ordered[j-1u];--j;}
        ordered[j]=value;
    }
    MomentInteger r=moment_lift(history_integer(radius)),radius_square=r*r;
    int64_t count=0,selected=-1;
    for(uint32_t i=0;i<targets;++i){
        HistoryInteger sum=history_integer(v[2u*i+quadrature]);
        MomentInteger c=moment_lift(sum),squares=c*c;uint32_t k=1;
        for(uint32_t j=0;j<targets;++j){
            HistoryInteger next=history_integer(ordered[j]);
            if(next*HistoryInteger(k)<=sum)break;
            sum=sum+next;MomentInteger value=moment_lift(next);
            squares=squares+value*value;++k;
        }
        MomentInteger total=moment_lift(sum),distance=squares*MomentInteger(k)-total*total;
        MomentInteger bound=radius_square*MomentInteger(k);
        if(sum.overflow || distance.overflow || bound.overflow || distance.negative){atomicOr(slot,REFUSED_CARRIER);return;}
        bool candidate=distance<=bound;
        lo[2u+i]=hi[2u+i]=candidate?1:0;if(candidate){++count;selected=i;}}
    lo[0]=hi[0]=count;lo[1]=hi[1]=count==1?selected:-1;
}

__device__ void normalized_current_face(const wide *input,uint32_t nodes,uint32_t first,
    uint32_t width,uint32_t grain,uint32_t terms,wide *output,uint32_t offset,uint32_t *slot) {
    wide radius=input[2u*nodes],unit=(wide)1<<grain;
    if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide origin=add_checked(input[2u*first],radius,slot);
    for(uint32_t j=first+1;j<first+width;++j){
        wide hi=add_checked(input[2u*j],radius,slot);if(hi>origin)origin=hi;
    }
    wide total_lo=0,total_hi=0;
    for(uint32_t j=first;j<first+width;++j){
        wide low=sub_checked(sub_checked(input[2u*j],radius,slot),origin,slot);
        wide high=sub_checked(add_checked(input[2u*j],radius,slot),origin,slot);
        wide lo,hi,unused;
        if(*slot)return;
        exp_nonpositive(low,grain,terms,&lo,&unused,slot);
        exp_nonpositive(high,grain,terms,&unused,&hi,slot);
        output[10u*j+offset]=lo;output[10u*j+offset+1u]=hi;
        total_lo=add_checked(total_lo,lo,slot);total_hi=add_checked(total_hi,hi,slot);
    }
    if(*slot)return;
    if(total_hi<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=first;j<first+width;++j){
        wide lo=output[10u*j+offset],hi=output[10u*j+offset+1u];
        lo=signed_product_divide_2(lo,unit/2,total_hi,0,slot);
        hi=total_lo ? signed_product_divide_2(hi,unit/2,total_lo,1,slot) : unit;
        if(lo<0)lo=0;if(hi>unit)hi=unit;
        output[10u*j+offset]=lo;output[10u*j+offset+1u]=hi;
    }
}

__device__ void normalized_square_interval(wide lo,wide hi,uint32_t grain,wide *lower,wide *upper,uint32_t *slot){
    wide a=ft_abs(lo,slot),b=ft_abs(hi,slot),big=a>b?a:b,small=a<b?a:b;
    *upper=product_shift(big,big,grain,1,slot);
    *lower=lo<=0 && hi>=0?0:product_shift(small,small,grain,0,slot);
}
// The observed packet is a complete complex amplitude carrier. Its observed face is
// normalized squared modulus, not an exponentiated target logit. Zero total amplitude
// supplies no packet probability face and is an explicit receiver-domain obstruction.
__device__ void normalized_packet_face(const wide *input,uint32_t nodes,uint32_t first,
    uint32_t width,uint32_t grain,wide *output,uint32_t *slot){
    wide radius=input[2u*nodes],unit=(wide)1<<grain,total_lo=0,total_hi=0;
    if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=first;j<first+width;++j){
        wide lo=0,hi=0;
        for(uint32_t part=0;part<2;++part){wide a,b;normalized_square_interval(
            sub_checked(input[2u*j+part],radius,slot),add_checked(input[2u*j+part],radius,slot),grain,&a,&b,slot);
            lo=add_checked(lo,a,slot);hi=add_checked(hi,b,slot);}
        output[10u*j+2u]=lo;output[10u*j+3u]=hi;total_lo=add_checked(total_lo,lo,slot);total_hi=add_checked(total_hi,hi,slot);
    }
    if(!total_hi){atomicOr(slot,REFUSED_BOUND);return;}
    for(uint32_t j=first;j<first+width;++j){
        wide lo=signed_product_divide_2(output[10u*j+2u],unit/2,total_hi,0,slot);
        wide hi=total_lo?signed_product_divide_2(output[10u*j+3u],unit/2,total_lo,1,slot):unit;
        output[10u*j+2u]=lo;output[10u*j+3u]=hi<unit?hi:unit;
    }
}

extern "C" __global__ __launch_bounds__(512) void section_field_normalized_receiver(
    const int64_t *prediction,const int64_t *observation,uint32_t nodes,uint32_t group_width,
    uint32_t grain,uint32_t terms,uint32_t packet_observation,int64_t *out_lo,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!nodes||!group_width||nodes%group_width||grain<1||grain>120||!terms||terms==UINT32_MAX||packet_observation>1u){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    uint32_t first=blockIdx.x*group_width;if(first>=nodes)return;
    const wide *p=(const wide *)prediction;
    // Every material-report family retains its actual observed current in target block two.
    const wide *q=(const wide *)observation+2u*(2u*nodes+1u);
    wide *out=(wide *)out_lo;
    normalized_current_face(p,nodes,first,group_width,grain,terms,out,0,slot);
    if(packet_observation)normalized_packet_face(q,nodes,first,group_width,grain,out,slot);
    else normalized_current_face(q,nodes,first,group_width,grain,terms,out,2,slot);
    if(*slot)return;
    // For point currents, a common additive shift is exactly invisible even when 1/group_width
    // needs a numerical interval. This proves equality of faces, never identity of occurrences.
    bool same=!packet_observation && p[2u*nodes]==0 && q[2u*nodes]==0;
    wide common=0;
    if(same){
        common=sub_checked(p[2u*first],q[2u*first],slot);
        for(uint32_t j=first+1;j<first+group_width;++j)
            same=same && sub_checked(p[2u*j],q[2u*j],slot)==common;
    }
    wide mean_lo=0,mean_hi=0,min_lo=0,max_hi=0;
    for(uint32_t j=first;j<first+group_width;++j){
        wide *o=out+10u*j;
        o[4]=same?0:sub_checked(o[2],o[1],slot);
        o[5]=same?0:sub_checked(o[3],o[0],slot);
        wide lo,hi;normalized_interval_product(o[0],o[1],o[4],o[5],grain,&lo,&hi,slot);
        mean_lo=add_checked(mean_lo,lo,slot);mean_hi=add_checked(mean_hi,hi,slot);
        if(j==first||o[4]<min_lo)min_lo=o[4];if(j==first||o[5]>max_hi)max_hi=o[5];
    }
    // The exact p is a simplex section, so its weighted mean lies in the residual's hull.
    if(mean_lo<min_lo)mean_lo=min_lo;if(mean_hi>max_hi)mean_hi=max_hi;
    for(uint32_t j=first;j<first+group_width;++j){
        wide *o=out+10u*j;
        o[8]=sub_checked(o[4],mean_hi,slot);o[9]=sub_checked(o[5],mean_lo,slot);
        normalized_interval_product(o[0],o[1],o[8],o[9],grain,o+6,o+7,slot);
    }
    if(*slot)return;
    for(uint32_t j=first*20u;j<(first+group_width)*20u;++j)out_hi[j]=out_lo[j];
}
