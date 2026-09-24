// The source is J subset Anchor x Output, restricted by a retained anchor ball.
// With no vertical directions, output varies by A on the anchor tangent U.
// At the nearest admissible anchor, ||delta anchor|| <= R. Thus
// ||delta output|| <= ||A P_U||_2 R <= max(||A P_U||_1,||A P_U||_infty) R.
// Directed coefficient rounding increases that bound; centre rounding is added.
// Every signed coefficient and the original affine family remain at their source.
__device__ wide normal_family_enclosure_centre(
    const int64_t *report,const int64_t *report_hi,uint32_t a,uint32_t y,uint32_t grain,
    wide *out,uint32_t *slot){
    uint64_t count=4u+2u*(uint64_t)a+2u*(uint64_t)y;
    if(!a||!y||(a&1u)||(y&1u)||grain<1||grain>120||2u*count>UINT32_MAX){
        atomicOr(slot,REFUSED_MALFORMED);return 0;
    }
    for(size_t i=0;i<2u*count;++i)if(report[i]!=report_hi[i]){
        atomicOr(slot,REFUSED_MALFORMED);return 0;
    }
    const wide *r=(const wide *)report;
    if(r[0]!=0){atomicOr(slot,REFUSED_BOUND);return 0;}
    if(r[1]<=0||r[2u+a]<=0||r[3u+a+y]<=0){atomicOr(slot,REFUSED_MALFORMED);return 0;}
    wide S=(wide)1<<grain,rounding=0;
    for(uint32_t i=0;i<y;++i){
        wide flag=r[4u+2u*a+y+i];
        if(flag<0||flag>1){atomicOr(slot,REFUSED_MALFORMED);return 0;}
        if(flag){atomicOr(slot,REFUSED_BOUND);return 0;}
        wide n=r[3u+a+i];
        wide lo=signed_product_divide_2(n,S/2,r[2u+a],0,slot);
        wide hi=signed_product_divide_2(n,S/2,r[2u+a],1,slot);
        if(*slot)return 0;
        out[i]=n<0?hi:lo;
        rounding=add_checked(rounding,sub_checked(hi,lo,slot),slot);
    }
    return rounding;
}

extern "C" __global__ void section_normal_family_enclosure(
    const int64_t *report,const int64_t *report_hi,
    const int64_t *joint,const int64_t *joint_hi,
    const int64_t *ab,const int64_t *ab_hi,const int64_t *vertical,const int64_t *vertical_hi,
    const int64_t *anchor,const int64_t *anchor_hi,uint32_t anchor_at,uint32_t anchor_grain,
    uint32_t a,uint32_t y,uint32_t grain,int64_t *graph,int64_t *graph_hi,int64_t *workspace,
    int64_t *output,int64_t *output_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    wide *out=(wide *)output;
    wide rounding=normal_family_enclosure_centre(report,report_hi,a,y,grain,out,slot);
    if(*slot)return;
    uint64_t w64=(uint64_t)a+y;
    if(w64>UINT32_MAX||anchor_grain<1||anchor_grain>120||(anchor_at&1u)||
        (uint64_t)anchor_at+2u*((uint64_t)a+1u)>UINT32_MAX){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t w=(uint32_t)w64;
    for(size_t i=0;i<(size_t)w*w;++i)if(joint[i]!=joint_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<(size_t)a*a;++i)if(ab[i]!=ab_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<(size_t)y*y;++i){
        if(vertical[i]!=vertical_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
        if(vertical[i]){atomicOr(slot,REFUSED_BOUND);return;}
    }
    for(size_t i=0;i<2u*((size_t)a+1u);++i)if(anchor[anchor_at+i]!=anchor_hi[anchor_at+i]){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    const wide *ball=(const wide *)(anchor+anchor_at);
    if(ball[a]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *input=(wide *)workspace,*projected=input+a,*projection_query=projected+a;
    wide *joint_query=projection_query+2u*a,*row_sum=joint_query+2u*w;
    // The earlier receiver overwrote its projection scratch with the vertical graph.
    // Reconstruct P_U from the retained anchor basis, once for this bound.
    family_projection_graph(ab,a,graph,graph_hi,projection_query,slot);if(*slot)return;
    for(uint32_t r=0;r<y;++r)row_sum[r]=0;
    wide S=(wide)1<<grain,max_col=0;
    for(uint32_t c=0;c<a;++c){
        for(uint32_t i=0;i<a;++i)input[i]=i==c?1:0;
        wide den=1;
        family_project(ab,graph,a,input,&den,projected,projection_query,slot);if(*slot)return;
        for(uint32_t i=0;i<w;++i)joint_query[i]=i<a?projected[i]:0;
        uint32_t status=0,rank=0;
        fibre_query(joint,a,w,joint_query,&den,nullptr,-1,&status,&rank,slot);if(*slot)return;
        if(status!=0||den<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
        wide col=0;
        for(uint32_t r=0;r<y;++r){
            wide n=sub_checked(0,joint_query[a+r],slot);
            wide lo=signed_product_divide_2(n,S/2,den,0,slot);
            wide hi=signed_product_divide_2(n,S/2,den,1,slot);if(*slot)return;
            wide bound=n<0?sub_checked(0,lo,slot):hi;
            row_sum[r]=add_checked(row_sum[r],bound,slot);
            col=add_checked(col,bound,slot);
        }
        if(col>max_col)max_col=col;
    }
    wide N=max_col;
    for(uint32_t r=0;r<y;++r)if(row_sum[r]>N)N=row_sum[r];
    wide AS=(wide)1<<anchor_grain;
    out[y]=add_checked(signed_product_divide_2(N,ball[a],2*AS,1,slot),rounding,slot);
    if(*slot)return;
    for(size_t i=0;i<2u*((size_t)y+1u);++i)output_hi[i]=output[i];
}

extern "C" __global__ void section_normal_family_enclosure_point(
    const int64_t *report,const int64_t *report_hi,uint32_t a,uint32_t y,uint32_t grain,
    int64_t *output,int64_t *output_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    wide *out=(wide *)output;
    out[y]=normal_family_enclosure_centre(report,report_hi,a,y,grain,out,slot);
    if(*slot)return;
    for(size_t i=0;i<2u*((size_t)y+1u);++i)output_hi[i]=output[i];
}
