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
    uint32_t width,uint32_t grain,wide *output,uint32_t offset,uint32_t *slot){
    wide radius=input[2u*nodes],unit=(wide)1<<grain,total_lo=0,total_hi=0;
    if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=first;j<first+width;++j){
        wide lo=0,hi=0;
        for(uint32_t part=0;part<2;++part){wide a,b;normalized_square_interval(
            sub_checked(input[2u*j+part],radius,slot),add_checked(input[2u*j+part],radius,slot),grain,&a,&b,slot);
            lo=add_checked(lo,a,slot);hi=add_checked(hi,b,slot);}
        output[10u*j+offset]=lo;output[10u*j+offset+1u]=hi;total_lo=add_checked(total_lo,lo,slot);total_hi=add_checked(total_hi,hi,slot);
    }
    if(!total_hi){atomicOr(slot,REFUSED_BOUND);return;}
    for(uint32_t j=first;j<first+width;++j){
        wide lo=signed_product_divide_2(output[10u*j+offset],unit/2,total_hi,0,slot);
        wide hi=total_lo?signed_product_divide_2(output[10u*j+offset+1u],unit/2,total_lo,1,slot):unit;
        output[10u*j+offset]=lo;output[10u*j+offset+1u]=hi<unit?hi:unit;
    }
}

// The shared residual return. With the normalized face p at [0,1] and a residual r at [4,5] of
// each coordinate's ten wides, subtract p's own weighted mean and return the centered residual
// at [8,9] and J_p r at [6,7], J_p = diag(p) - p p^T. p is a simplex section over the declared
// group, so its weighted mean lies in the hull of the residual intervals; intersecting those
// bounds is sound. The comparison receiver and the covector return use this one arithmetic.
__device__ void normalized_potential_pullback(wide *out,uint32_t first,uint32_t group_width,
    uint32_t grain,uint32_t *slot) {
    wide mean_lo=0,mean_hi=0,min_lo=0,max_hi=0;
    for(uint32_t j=first;j<first+group_width;++j){
        wide *o=out+10u*j;
        wide lo,hi;normalized_interval_product(o[0],o[1],o[4],o[5],grain,&lo,&hi,slot);
        mean_lo=add_checked(mean_lo,lo,slot);mean_hi=add_checked(mean_hi,hi,slot);
        if(j==first||o[4]<min_lo)min_lo=o[4];if(j==first||o[5]>max_hi)max_hi=o[5];
    }
    if(mean_lo<min_lo)mean_lo=min_lo;if(mean_hi>max_hi)mean_hi=max_hi;
    for(uint32_t j=first;j<first+group_width;++j){
        wide *o=out+10u*j;
        o[8]=sub_checked(o[4],mean_hi,slot);o[9]=sub_checked(o[5],mean_lo,slot);
        normalized_interval_product(o[0],o[1],o[8],o[9],grain,o+6,o+7,slot);
    }
}

__device__ void normalized_compare_faces(const wide *p,const wide *q,uint32_t nodes,uint32_t first,
    uint32_t group_width,uint32_t grain,uint32_t terms,uint32_t packet_observation,wide *out,uint32_t *slot) {
    normalized_current_face(p,nodes,first,group_width,grain,terms,out,0,slot);
    if(packet_observation)normalized_packet_face(q,nodes,first,group_width,grain,out,2u,slot);
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
    for(uint32_t j=first;j<first+group_width;++j){
        wide *o=out+10u*j;
        o[4]=same?0:sub_checked(o[2],o[1],slot);
        o[5]=same?0:sub_checked(o[3],o[0],slot);
    }
    normalized_potential_pullback(out,first,group_width,grain,slot);
    if(*slot)return;
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
    const wide *q=(const wide *)observation+2u*(2u*nodes+1u);
    normalized_compare_faces(p,q,nodes,first,group_width,grain,terms,packet_observation,(wide *)out_lo,slot);
    if(*slot)return;
    for(uint32_t j=first*20u;j<(first+group_width)*20u;++j)out_hi[j]=out_lo[j];
}

// One normalized comparison over the sum of two declared current balls. Offsets are in wide
// components. Typed producers supply the actual anchor/increment maps and retain their joint
// source; the sum's outer radius does not identify that joint source with an independent box.
extern "C" __global__ __launch_bounds__(512) void section_normalized_sum_receiver(
    const int64_t *anchor,uint32_t anchor_at,const int64_t *increment,uint32_t increment_at,
    const int64_t *observed_ball,
    uint32_t n,uint32_t group_width,uint32_t grain,uint32_t terms,
    int64_t *scratch,int64_t *out_lo,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!n||!group_width||n%group_width||grain<1||grain>120||!terms||terms==UINT32_MAX){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    const uint32_t r=2u*n;
    const wide *a=(const wide *)anchor+anchor_at;
    const wide *delta=(const wide *)increment+increment_at;
    wide *pred=(wide *)scratch;
    if(a[r]<0||delta[r]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t k=0;k<r;++k)pred[k]=add_checked(a[k],delta[k],slot);
    pred[r]=add_checked(a[r],delta[r],slot);
    if(*slot)return;
    for(uint32_t first=0;first<n;first+=group_width){
        normalized_compare_faces(pred,(const wide *)observed_ball,n,first,group_width,grain,terms,1u,(wide *)out_lo,slot);
        if(*slot)return;
    }
    for(uint32_t k=0;k<n*20u;++k)out_hi[k]=out_lo[k];
}

// ---------------------------------------------------------------------------------------------
// the row-sectioned face: one region row per block, its declared groups in order
// ---------------------------------------------------------------------------------------------
//
// The operands are resident enclosure sections. One row holds `2*nodes` real coordinates and one
// common outward radius, `2*(nodes*2+1)` words; that is exactly the ball the single-occurrence
// receiver already reads, so `normalized_compare_faces` runs unchanged over every row and no row
// is read back to the host between passages. Row `r` of the report is its own ten wides per
// coordinate at `20*nodes` words.
//
// Besides the report, a face is returned as an enclosure operand of the same chart: the real
// coordinate carries the interval centre `lo + ceil((hi-lo)/2)`, the imaginary coordinate is
// exactly zero, and the row radius is the sum of the half widths — an outward bound on their
// Euclidean length, so the returned ball contains the exact face's own box. A nonzero input
// radius therefore returns a nonzero radius; nothing is narrowed to a point.

// Every operand row is a sealed carrier: its two word lanes must agree before it is read.
__device__ bool normalized_row_is_point(const int64_t *lo,const int64_t *hi,size_t at,
    size_t words,uint32_t *slot) {
    for(size_t j=0;j<words;++j)if(lo[at+j]!=hi[at+j]){atomicOr(slot,REFUSED_MALFORMED);return false;}
    return true;
}

// One declared face of the report, written as the enclosure operand of a later call.
__device__ void normalized_face_ball(const wide *report,uint32_t nodes,uint32_t offset,
    wide *ball,uint32_t *slot) {
    wide radius=0;
    for(uint32_t j=0;j<nodes;++j){
        wide lo=report[10u*j+offset],hi=report[10u*j+offset+1u];
        if(hi<lo){atomicOr(slot,REFUSED_MALFORMED);return;}
        wide half=add_checked(sub_checked(hi,lo,slot),1,slot)>>1;
        ball[2u*j]=add_checked(lo,half,slot);ball[2u*j+1u]=0;
        radius=add_checked(radius,half,slot);
    }
    ball[2u*nodes]=radius;
}

// p, and with a comparison operand also q, q-p and J_p(q-p), over every row of a typed section.
// `compare` selects whether the second operand is read at all; `packet_face` selects the
// observed measure, normalized squared modulus rather than the normalized exponential of the
// real potentials. Grouping is the caller's receiver declaration, not native row topology.
extern "C" __global__ __launch_bounds__(512) void section_rows_normalized_receiver(
    const int64_t *prediction,const int64_t *prediction_hi,
    const int64_t *observation,const int64_t *observation_hi,uint32_t compare,
    uint32_t rows,uint32_t nodes,uint32_t group_width,uint32_t grain,uint32_t terms,
    uint32_t packet_face,int64_t *report_lo,int64_t *report_hi,
    int64_t *participation,int64_t *participation_hi,
    int64_t *difference,int64_t *difference_hi,int64_t *potential,int64_t *potential_hi,int64_t *flags,
    uint32_t *global_slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;uint32_t *slot=(uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);for(uint32_t i=0;i<SLOT_WORDS;++i)slot[i]=0;
    if(upstream_refused(census,lineage,lineage_count,slot))return;(void)global_slot;
    if(!rows||!nodes||!group_width||nodes%group_width||grain<1||grain>120||!terms||terms==UINT32_MAX
       ||packet_face>1u||compare>1u){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(row>=rows)return;
    const size_t ball_wides=2u*(size_t)nodes+1u,stride=2u*ball_wides;
    const size_t at=(size_t)row*stride,report_at=(size_t)row*20u*(size_t)nodes;
    if(!normalized_row_is_point(prediction,prediction_hi,at,stride,slot))return;
    if(compare&&!normalized_row_is_point(observation,observation_hi,at,stride,slot))return;
    const wide *p=(const wide *)(prediction+at),*q=(const wide *)(observation+at);
    wide *out=(wide *)(report_lo+report_at);
    for(size_t j=0;j<10u*(size_t)nodes;++j)out[j]=0;
    for(uint32_t first=0;first<nodes;first+=group_width){
        if(compare)normalized_compare_faces(p,q,nodes,first,group_width,grain,terms,packet_face,out,slot);
        else if(packet_face)normalized_packet_face(p,nodes,first,group_width,grain,out,0u,slot);
        else normalized_current_face(p,nodes,first,group_width,grain,terms,out,0u,slot);
        if(*slot)return;
    }
    normalized_face_ball(out,nodes,0u,(wide *)(participation+at),slot);
    for(size_t j=0;j<stride;++j){difference[at+j]=0;potential[at+j]=0;}
    if(compare){
        normalized_face_ball(out,nodes,4u,(wide *)(difference+at),slot);
        normalized_face_ball(out,nodes,6u,(wide *)(potential+at),slot);
    }
    if(*slot)return;
    for(size_t j=0;j<20u*(size_t)nodes;++j)report_hi[report_at+j]=report_lo[report_at+j];
    for(size_t j=0;j<stride;++j){
        participation_hi[at+j]=participation[at+j];
        difference_hi[at+j]=difference[at+j];
        potential_hi[at+j]=potential[at+j];
    }
}

// The return of a covector on the normalized face to the pre-normalization potentials: J_p g,
// row by row, with p read from the face report this covector was declared on. The face is the
// normalized exponential of the real coordinates alone, so the returned covector's imaginary
// coordinate is exactly zero — not omitted, and not a rounded small value.
extern "C" __global__ __launch_bounds__(512) void section_rows_normalized_pullback(
    const int64_t *face,uint32_t rows,uint32_t nodes,uint32_t group_width,uint32_t grain,
    const int64_t *covector,const int64_t *covector_hi,
    int64_t *report_lo,int64_t *report_hi,int64_t *potential,int64_t *potential_hi,int64_t *flags,
    uint32_t *global_slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;uint32_t *slot=(uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);for(uint32_t i=0;i<SLOT_WORDS;++i)slot[i]=0;
    if(upstream_refused(census,lineage,lineage_count,slot))return;(void)global_slot;
    if(!rows||!nodes||!group_width||nodes%group_width||grain<1||grain>120){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    if(row>=rows)return;
    const size_t ball_wides=2u*(size_t)nodes+1u,stride=2u*ball_wides;
    const size_t at=(size_t)row*stride,report_at=(size_t)row*20u*(size_t)nodes;
    if(!normalized_row_is_point(covector,covector_hi,at,stride,slot))return;
    const wide *g=(const wide *)(covector+at),*p=(const wide *)(face+report_at);
    wide radius=g[2u*nodes],unit=(wide)1<<grain;
    if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *out=(wide *)(report_lo+report_at);
    for(size_t j=0;j<10u*(size_t)nodes;++j)out[j]=0;
    for(uint32_t j=0;j<nodes;++j){
        wide lo=p[10u*j],hi=p[10u*j+1u];
        if(lo<0||hi>unit||hi<lo){atomicOr(slot,REFUSED_MALFORMED);return;}
        out[10u*j]=lo;out[10u*j+1u]=hi;
        out[10u*j+4u]=sub_checked(g[2u*j],radius,slot);
        out[10u*j+5u]=add_checked(g[2u*j],radius,slot);
    }
    if(*slot)return;
    for(uint32_t first=0;first<nodes;first+=group_width){
        normalized_potential_pullback(out,first,group_width,grain,slot);
        if(*slot)return;
    }
    normalized_face_ball(out,nodes,6u,(wide *)(potential+at),slot);
    if(*slot)return;
    for(size_t j=0;j<20u*(size_t)nodes;++j)report_hi[report_at+j]=report_lo[report_at+j];
    for(size_t j=0;j<stride;++j)potential_hi[at+j]=potential[at+j];
}
