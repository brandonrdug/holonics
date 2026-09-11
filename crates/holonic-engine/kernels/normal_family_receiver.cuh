// Receiver of J subset Anchor x Joint, constrained by the retained anchor ball.
// Project m onto the admitted anchor affine space, then project zero onto the resulting
// joint fibre. These are receiver choices; the continuing source remains the whole family.
// A squared-norm comparison multiplies four wide factors and sums at most u32 coordinates.
using FamilyReceiverInteger = ExactInteger<(4*sizeof(wide)+sizeof(uint32_t))/sizeof(uint32_t)>;
__device__ FamilyReceiverInteger family_receiver_integer(wide x){
    uwide m=magnitude(x);return FamilyReceiverInteger(ExactCoefficient{(uint64_t)m,(uint64_t)(m>>64),(uint32_t)(x<0),0});
}

// Graph (V v_i, v_i) gives orthogonal projection onto row span V through the existing
// relation elimination, including zero-padded and nonorthogonal rows.
__device__ void family_projection_graph(const int64_t *v,uint32_t d,int64_t *g,int64_t *gh,wide *row,uint32_t *slot){
    uint32_t k=2u*d;
    for(size_t i=0;i<(size_t)k*k;++i)g[i]=gh[i]=0;
    for(uint32_t i=0;i<d;++i){
        for(uint32_t j=0;j<d;++j){
            row[j]=0;
            for(uint32_t n=0;n<d;++n)row[j]=add_checked(row[j],product_checked(v[(size_t)j*d+n],v[(size_t)i*d+n],slot),slot);
            row[d+j]=v[(size_t)i*d+j];
        }
        if(*slot)return;condition_stage_row(g,gh,k,row,slot);if(*slot)return;
    }
}
__device__ void family_project(const int64_t *v,const int64_t *graph,uint32_t d,
    const wide *input,wide *den,wide *output,wide *query,uint32_t *slot){
    for(uint32_t i=0;i<d;++i){
        query[i]=query[d+i]=0;
        for(uint32_t j=0;j<d;++j)query[i]=add_checked(query[i],product_checked(v[(size_t)i*d+j],input[j],slot),slot);
    }
    if(*slot)return;uint32_t status=0,rank=0;
    fibre_query(graph,d,2u*d,query,den,nullptr,-1,&status,&rank,slot);if(*slot)return;
    if(status!=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<d;++i)output[i]=sub_checked(0,query[d+i],slot);
}

// Report wide layout: status; anchor denominator + a values; joint denominator + a values;
// oriented (nearest anchor - m) denominator + a values; a flags for anchor-independent
// free joint coordinates. Status 0 supported, 1 empty affine relation, 2 misses anchor ball.
extern "C" __global__ void section_normal_family_receiver(
    const int64_t *pf,const int64_t *pf_hi,uint32_t ps,
    const int64_t *ball,const int64_t *ball_hi,uint32_t ball_at,uint32_t n,uint32_t grain,
    int64_t *joint,int64_t *joint_hi,int64_t *ab,int64_t *ab_hi,int64_t *vb,int64_t *vb_hi,
    int64_t *graph,int64_t *graph_hi,int64_t *report,int64_t *report_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t a64=4u*(uint64_t)n,t64=2u+2u*a64,w64=2u*a64,pk64=ps+t64;
    if(!n||grain<1||grain>120||pk64>UINT32_MAX-4u||4u+4u*a64>UINT32_MAX||(ball_at&1u)){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    uint32_t a=(uint32_t)a64,t=(uint32_t)t64,w=(uint32_t)w64,pk=(uint32_t)pk64;
    for(size_t i=0;i<(size_t)pk+4u+(size_t)t*t;++i)if(pf[i]!=pf_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<2u*(a+1u);++i)if(ball[ball_at+i]!=ball_hi[ball_at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *b=(const wide *)(ball+ball_at);wide fd=pf[pk],S=(wide)1<<grain;
    if(fd<=0||pf[pk+1u]<0||pf[pk+1u]>2||b[a]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *out=(wide *)report;uint32_t count=4u+4u*a;
    for(uint32_t i=0;i<count;++i)out[i]=0;
    out[0]=1;out[1]=out[2u+a]=out[3u+2u*a]=1;
    for(size_t i=0;i<(size_t)a*a;++i)vb[i]=vb_hi[i]=0;
    if(pf[pk+1u]==1){for(uint32_t i=0;i<2u*count;++i)report_hi[i]=report[i];return;}
    if(pf[ps]!=fd||pf[ps+1u]!=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    const int64_t *directions=pf+pk+4u;
    for(uint32_t i=0;i<t;++i)if(directions[(size_t)i*t]||directions[(size_t)i*t+1u]){atomicOr(slot,REFUSED_MALFORMED);return;}
    extern __shared__ wide scratch[];
    wide *row=scratch,*query=row+w,*delta=query+w,*projected=delta+a,*nearest=projected+a,*residual=nearest+a,*z=residual+a;
    for(size_t i=0;i<(size_t)w*w;++i)joint[i]=joint_hi[i]=0;
    for(size_t i=0;i<(size_t)a*a;++i)ab[i]=ab_hi[i]=vb[i]=vb_hi[i]=0;
    for(uint32_t i=0;i<t;++i){
        for(uint32_t j=0;j<w;++j)row[j]=directions[(size_t)i*t+2u+j];
        condition_stage_row(joint,joint_hi,w,row,slot);if(*slot)return;
    }
    for(uint32_t i=0;i<w;++i){
        for(uint32_t j=0;j<a;++j)row[j]=joint[(size_t)i*w+j];
        condition_stage_row(ab,ab_hi,a,row,slot);if(*slot)return;
    }
    for(uint32_t i=0;i<a;++i)for(uint32_t j=0;j<a;++j){
        int64_t v=joint[(size_t)(a+i)*w+a+i]?joint[(size_t)(a+i)*w+a+j]:0;
        vb[(size_t)i*a+j]=vb_hi[(size_t)i*a+j]=v;
    }
    family_projection_graph(ab,a,graph,graph_hi,row,slot);if(*slot)return;
    wide dd=fibre_lcm(S,fd,slot);
    for(uint32_t i=0;i<a;++i)delta[i]=sub_checked(product_checked(b[i],dd/S,slot),product_checked(pf[ps+2u+i],dd/fd,slot),slot);
    if(*slot)return;fibre_normalize(delta,a,&dd,slot);
    wide pd=dd;family_project(ab,graph,a,delta,&pd,projected,query,slot);if(*slot)return;
    wide nd=fibre_lcm(fd,pd,slot),ed=fibre_lcm(dd,pd,slot);
    for(uint32_t i=0;i<a;++i){
        nearest[i]=add_checked(product_checked(pf[ps+2u+i],nd/fd,slot),product_checked(projected[i],nd/pd,slot),slot);
        residual[i]=sub_checked(product_checked(projected[i],ed/pd,slot),product_checked(delta[i],ed/dd,slot),slot);
    }
    if(*slot)return;fibre_normalize(nearest,a,&nd,slot);fibre_normalize(residual,a,&ed,slot);if(*slot)return;
    FamilyReceiverInteger square;
    for(uint32_t i=0;i<a;++i){auto e=family_receiver_integer(residual[i]);square=square+e*e;}
    auto hs=family_receiver_integer(S),hr=family_receiver_integer(b[a]),he=family_receiver_integer(ed);
    auto left=square*hs*hs,right=hr*hr*he*he;
    if(left.overflow||right.overflow){atomicOr(slot,REFUSED_CARRIER);return;}
    out[0]=left<=right?0:2;out[1]=nd;out[3u+2u*a]=ed;
    for(uint32_t i=0;i<a;++i){
        out[2u+i]=nearest[i];out[4u+2u*a+i]=residual[i];
        for(uint32_t j=0;j<a;++j)if(vb[(size_t)j*a+i])out[4u+3u*a+i]=1;
    }
    if(out[0]==0){
        // Read the joint fibre over the projected anchor. Its point is only a receiver
        // witness; all vertical directions stay in vb and the original source relation.
        wide qd=fibre_lcm(nd,fd,slot);
        for(uint32_t i=0;i<w;++i)query[i]=i<a?sub_checked(product_checked(nearest[i],qd/nd,slot),product_checked(pf[ps+2u+i],qd/fd,slot),slot):0;
        if(*slot)return;uint32_t status=0,rank=0;
        fibre_query(joint,a,w,query,&qd,nullptr,-1,&status,&rank,slot);if(*slot)return;
        if(status==1){atomicOr(slot,REFUSED_MALFORMED);return;}
        wide zd=fibre_lcm(qd,fd,slot);
        for(uint32_t i=0;i<a;++i)z[i]=add_checked(product_checked(pf[ps+2u+a+i],zd/fd,slot),product_checked(sub_checked(0,query[a+i],slot),zd/qd,slot),slot);
        if(*slot)return;fibre_normalize(z,a,&zd,slot);
        family_projection_graph(vb,a,graph,graph_hi,row,slot);if(*slot)return;
        pd=zd;family_project(vb,graph,a,z,&pd,projected,query,slot);if(*slot)return;
        wide final_den=fibre_lcm(zd,pd,slot);
        for(uint32_t i=0;i<a;++i)z[i]=sub_checked(product_checked(z[i],final_den/zd,slot),product_checked(projected[i],final_den/pd,slot),slot);
        if(*slot)return;fibre_normalize(z,a,&final_den,slot);if(*slot)return;
        out[2u+a]=final_den;for(uint32_t i=0;i<a;++i)out[3u+a+i]=z[i];
    }
    for(uint32_t i=0;i<2u*count;++i)report_hi[i]=report[i];
}
