// Affine current-family image through a retained linear relation R subset X x Y.
// The joint carrier is {(x,y): x belongs to F and (x,y) belongs to R}. The same row
// calculus as condition_image retains correlation and exhibits unsupported source members.
extern "C" __global__ void section_constitutive_relation_image(
    const int64_t *basis,const int64_t *basis_hi,const int64_t *pf,const int64_t *pf_hi,
    uint32_t ps,uint32_t c,uint32_t y,
    int64_t *graph,int64_t *graph_hi,int64_t *rhs,int64_t *rhs_hi,int64_t *joint,int64_t *joint_hi,
    int64_t *domain_basis,int64_t *domain_basis_hi,int64_t *out_basis,int64_t *out_basis_hi,
    int64_t *domain,int64_t *domain_hi,int64_t *out,int64_t *out_hi,int64_t *coverage,int64_t *coverage_hi,
    int64_t *safe,int64_t *safe_hi,int64_t *workspace,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x || threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t w64=(uint64_t)c+y,k64=2u*w64,pk64=(uint64_t)ps+c;
    if(!c || !y || k64>UINT32_MAX-4u || pk64>UINT32_MAX-4u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t w=(uint32_t)w64,k=(uint32_t)k64,pk=(uint32_t)pk64;
    for(size_t i=0;i<(size_t)w*w;++i)if(basis[i]!=basis_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<(size_t)pk+4u+(size_t)c*c;++i)if(pf[i]!=pf_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(pf[pk]<=0 || pf[pk+1]<0 || pf[pk+1]>2){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *r=(wide *)workspace,*row=r+w,*q=row+k;
    for(size_t i=0;i<(size_t)k*k;++i)graph[i]=graph_hi[i]=0;
    for(uint32_t i=0;i<=w;++i)rhs[i]=rhs_hi[i]=0;rhs[w]=rhs_hi[w]=1;
    condition_empty_report(joint,joint_hi,w,w);condition_empty_report(domain,domain_hi,w,c);condition_empty_report(out,out_hi,w,y);
    for(uint32_t i=0;i<4u+c+w;++i)coverage[i]=coverage_hi[i]=0;
    coverage[1]=coverage_hi[1]=-1;coverage[2]=coverage_hi[2]=coverage[3u+c]=coverage_hi[3u+c]=1;
    for(uint32_t i=0;i<y+2u;++i)safe[i]=safe_hi[i]=0;safe[y]=safe_hi[y]=1;safe[y+1u]=safe_hi[y+1u]=1;
    // An outside-domain upstream return supplies no affine target family. Its original full
    // source remainder stays in the borrowed source object, not in an unrelated residual chart.
    if(pf[pk+1u]==1){coverage[0]=coverage_hi[0]=3;return;}
    uint32_t ignored=0,rank=0;
    for(uint32_t column=0;column<w;++column){
        for(uint32_t i=0;i<w;++i)r[i]=0;
        if(column<c)for(uint32_t i=0;i<c;++i)r[i]=pf[(size_t)pk+4u+(size_t)column*c+i];
        else r[column]=1;
        wide den=1;fibre_query(basis,w,w,r,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
        for(uint32_t i=0;i<k;++i)row[i]=i<w?r[i]:0;
        if(column<c)for(uint32_t i=0;i<c;++i)row[w+i]=product_checked(pf[(size_t)pk+4u+(size_t)column*c+i],den,slot);
        else row[w+column]=den;
        if(*slot)return;condition_stage_row(graph,graph_hi,k,row,slot);if(*slot)return;
    }
    wide cd=pf[pk],den=cd;
    for(uint32_t i=0;i<w;++i)r[i]=i<c?pf[ps+i]:0;
    fibre_query(basis,w,w,r,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
    for(uint32_t i=0;i<k;++i)q[i]=i<w?-r[i]:0;
    for(uint32_t i=0;i<w;++i)to_word(q[i],slot);to_word(den,slot);if(*slot)return;
    for(uint32_t i=0;i<w;++i)rhs[i]=rhs_hi[i]=(int64_t)q[i];rhs[w]=rhs_hi[w]=(int64_t)den;
    uint32_t status=0;fibre_query(graph,w,k,q,&den,nullptr,-1,&status,&rank,slot);if(*slot)return;
    for(uint32_t i=w;i<k;++i)q[i]=-q[i];
    if(status!=1){
        wide common=fibre_lcm(den,cd,slot);
        for(uint32_t i=0;i<k;++i)q[i]=product_checked(q[i],common/den,slot);
        for(uint32_t i=0;i<c;++i)q[w+i]=add_checked(q[w+i],product_checked(pf[ps+i],common/cd,slot),slot);
        den=common;fibre_normalize(q,k,&den,slot);
    }
    if(*slot)return;condition_store_report(graph,w,k,q,den,status,rank,joint,joint_hi,slot);if(*slot)return;
    condition_project(joint,w,w,0,c,domain_basis,domain_basis_hi,domain,domain_hi,row,slot);
    condition_project(joint,w,w,c,y,out_basis,out_basis_hi,out,out_hi,row,slot);if(*slot)return;
    if(status==1){
        for(uint32_t i=0;i<c;++i)row[i]=pf[ps+i];
        for(uint32_t i=0;i<w;++i)q[i]=joint[i];
        condition_coverage_write(2,-1,row,cd,c,q,joint[k],w,w,coverage,coverage_hi,slot);return;
    }
    wide dd=domain[w+c],rd=fibre_lcm(cd,dd,slot);
    for(uint32_t i=0;i<c;++i)q[i]=sub_checked(product_checked(pf[ps+i],rd/cd,slot),product_checked(domain[w+i],rd/dd,slot),slot);
    if(*slot)return;fibre_query(domain_basis,c,c,q,&rd,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
    int64_t failed=-1;bool partial=condition_nonzero(q,c);
    if(!partial)for(uint32_t p=0;p<c;++p){
        for(uint32_t i=0;i<c;++i)q[i]=pf[(size_t)pk+4u+(size_t)p*c+i];rd=1;
        fibre_query(domain_basis,c,c,q,&rd,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
        if(condition_nonzero(q,c)){partial=true;failed=p;break;}
    }
    if(partial){
        for(uint32_t i=0;i<c;++i)row[i]=add_checked(pf[ps+i],failed<0?0:product_checked(cd,pf[(size_t)pk+4u+(size_t)failed*c+i],slot),slot);
        if(*slot)return;condition_coverage_write(1,failed,row,cd,c,q,rd,c,w,coverage,coverage_hi,slot);
    }
    if(*slot)return;
    for(uint32_t i=0;i<y;++i)safe[i]=safe_hi[i]=out[w+i];
    safe[y]=safe_hi[y]=out[w+y];safe[y+1u]=safe_hi[y+1u]=partial?1:out[w+y+1u];
}
