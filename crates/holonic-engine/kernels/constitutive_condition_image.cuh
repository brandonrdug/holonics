// Joint affine image and condition-domain coverage, using the same native row calculus.
__device__ void condition_empty_report(int64_t *lo,int64_t *hi,uint32_t s,uint32_t t) {
    uint32_t w=s+t;size_t count=(size_t)w+4+(size_t)t*t;
    for(size_t i=0;i<count;++i) lo[i]=hi[i]=0;
    lo[w]=hi[w]=1;lo[w+1]=hi[w+1]=1;lo[w+2]=hi[w+2]=-1;
}
__device__ void condition_store_report(const int64_t *basis,uint32_t s,uint32_t w,
    const wide *q,wide den,uint32_t status,uint32_t rank,int64_t *lo,int64_t *hi,uint32_t *slot) {
    for(uint32_t i=0;i<w;++i) to_word(q[i],slot);to_word(den,slot);if(*slot)return;
    for(uint32_t i=0;i<w;++i)lo[i]=hi[i]=(int64_t)q[i];
    lo[w]=hi[w]=(int64_t)den;lo[w+1]=hi[w+1]=status;lo[w+2]=hi[w+2]=-1;lo[w+3]=hi[w+3]=rank;
    uint32_t t=w-s;
    for(uint32_t p=0;p<t;++p)for(uint32_t j=0;j<t;++j){
        int64_t v=basis[(size_t)(s+p)*w+s+p] ? basis[(size_t)(s+p)*w+s+j] : 0;
        size_t at=(size_t)w+4+(size_t)p*t+j;lo[at]=hi[at]=v;
    }
}
__device__ void condition_stage_row(int64_t *lo,int64_t *hi,uint32_t w,wide *row,uint32_t *slot){
    int64_t p=fibre_stage(lo,w,row,slot);for(uint32_t j=0;j<w;++j)to_word(row[j],slot);
    if(*slot)return;if(p>=0)for(uint32_t j=0;j<w;++j)lo[(size_t)p*w+j]=hi[(size_t)p*w+j]=(int64_t)row[j];
}
__device__ void condition_project(const int64_t *joint,uint32_t s,uint32_t joint_target,
    uint32_t start,uint32_t t,int64_t *basis_lo,int64_t *basis_hi,int64_t *lo,int64_t *hi,
    wide *row,uint32_t *slot){
    uint32_t jw=s+joint_target,w=s+t;
    for(size_t i=0;i<(size_t)t*t;++i)basis_lo[i]=basis_hi[i]=0;
    for(uint32_t p=0;p<joint_target;++p){
        for(uint32_t j=0;j<t;++j)row[j]=joint[(size_t)jw+4+(size_t)p*joint_target+start+j];
        condition_stage_row(basis_lo,basis_hi,t,row,slot);if(*slot)return;
    }
    uint32_t rank=0;for(uint32_t p=0;p<t;++p)if(basis_lo[(size_t)p*t+p])++rank;
    for(uint32_t j=0;j<s;++j)lo[j]=hi[j]=joint[j];
    for(uint32_t j=0;j<t;++j)lo[s+j]=hi[s+j]=joint[s+start+j];
    lo[w]=hi[w]=joint[jw];lo[w+1]=hi[w+1]=joint[jw+1]==1 ? 1 : (rank?2:0);
    lo[w+2]=hi[w+2]=-1;lo[w+3]=hi[w+3]=rank;
    for(size_t i=0;i<(size_t)t*t;++i)lo[w+4+i]=hi[w+4+i]=basis_lo[i];
}
__device__ bool condition_nonzero(const wide *v,uint32_t n){for(uint32_t j=0;j<n;++j)if(v[j])return true;return false;}
__device__ void condition_coverage_write(uint32_t kind,int64_t generator,wide *witness,wide wd,
    uint32_t c,wide *residual,wide rd,uint32_t rn,uint32_t w,int64_t *lo,int64_t *hi,uint32_t *slot){
    fibre_normalize(witness,c,&wd,slot);fibre_normalize(residual,rn,&rd,slot);
    for(uint32_t j=0;j<c;++j)to_word(witness[j],slot);
    for(uint32_t j=0;j<rn;++j)to_word(residual[j],slot);
    to_word(wd,slot);to_word(rd,slot);if(*slot)return;
    lo[0]=hi[0]=kind;lo[1]=hi[1]=generator;lo[2]=hi[2]=(int64_t)wd;
    for(uint32_t j=0;j<c;++j)lo[3+j]=hi[3+j]=(int64_t)witness[j];
    lo[3+c]=hi[3+c]=(int64_t)rd;
    for(uint32_t j=0;j<w;++j)lo[4+c+j]=hi[4+c+j]=j<rn?(int64_t)residual[j]:0;
}

extern "C" __global__ void section_constitutive_condition_image(
    const int64_t *basis,const int64_t *source_lo,const int64_t *source_hi,
    uint32_t source_at,uint32_t source_den_at,uint32_t source_status_at,
    const int64_t *pf,const int64_t *pf_hi,uint32_t ps,uint32_t ns,uint32_t nc,uint32_t y,
    int64_t *graph,int64_t *graph_hi,int64_t *rhs,int64_t *rhs_hi,int64_t *joint,int64_t *joint_hi,
    int64_t *domain_basis,int64_t *domain_basis_hi,int64_t *out_basis,int64_t *out_basis_hi,
    int64_t *domain,int64_t *domain_hi,int64_t *out,int64_t *out_hi,int64_t *coverage,int64_t *coverage_hi,
    int64_t *safe,int64_t *safe_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x || threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t sw64=2u*((uint64_t)ns+nc+(uint64_t)ns*nc),w64=sw64+y,k64=w64+2u*nc+y;
    if(!ns || !nc || !y || y%2 || k64>UINT32_MAX-4u || !ps || ps>w64){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t sw=(uint32_t)sw64,w=(uint32_t)w64,c=2u*nc,joint_target=c+y,k=(uint32_t)k64,pk=ps+c;
    size_t pf_words=(size_t)pk+4+(size_t)c*c;
    for(size_t i=0;i<pf_words;++i)if(pf[i]!=pf_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(pf[pk]<=0 || pf[pk+1]<0 || pf[pk+1]>2){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide sd=fibre_current_denominator(source_lo,source_hi,source_den_at,source_status_at,slot),cd=pf[pk];
    if(*slot)return;
    for(uint32_t i=0;i<2u*ns;++i)if(source_lo[source_at+i]!=source_hi[source_at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    extern __shared__ wide scratch[];wide *r=scratch,*row=r+w,*q=row+k;
    for(size_t i=0;i<(size_t)k*k;++i)graph[i]=graph_hi[i]=0;
    for(uint32_t i=0;i<=w;++i)rhs[i]=rhs_hi[i]=0;rhs[w]=rhs_hi[w]=1;
    condition_empty_report(joint,joint_hi,w,joint_target);condition_empty_report(domain,domain_hi,w,c);condition_empty_report(out,out_hi,w,y);
    for(uint32_t i=0;i<4u+c+w;++i)coverage[i]=coverage_hi[i]=0;coverage[1]=coverage_hi[1]=-1;
    coverage[2]=coverage_hi[2]=coverage[3+c]=coverage_hi[3+c]=1;
    for(uint32_t i=0;i<y+2;++i)safe[i]=safe_hi[i]=0;safe[y]=safe_hi[y]=1;safe[y+1]=safe_hi[y+1]=1;
    if(pf[pk+1]==1){
        coverage[0]=coverage_hi[0]=3;
        for(uint32_t i=0;i<ps;++i)joint[i]=joint_hi[i]=domain[i]=domain_hi[i]=out[i]=out_hi[i]=rhs[i]=rhs_hi[i]=pf[i];
        rhs[w]=rhs_hi[w]=pf[pk];
        joint[k]=joint_hi[k]=domain[w+c]=domain_hi[w+c]=out[w+y]=out_hi[w+y]=pf[pk];
        return;
    }
    // Build graph rows (P_R(variation), condition variation, output variation).
    uint32_t ignored=0,rank=0;
    for(uint32_t column=0;column<c+y;++column){
        for(uint32_t i=0;i<w;++i)r[i]=0;
        wide den=1;
        if(column<c){
            const int64_t *v=pf+pk+4+(size_t)column*c;den=sd;
            for(uint32_t i=0;i<c;++i)r[2u*ns+i]=product_checked(v[i],sd,slot);
            for(uint32_t a=0;a<nc;++a)for(uint32_t b=0;b<ns;++b){
                wide z[3];fibre_phase_product(source_lo[source_at+2*b],source_lo[source_at+2*b+1],1,v[2*a],v[2*a+1],1,z,slot);
                uint32_t at=2u*ns+c+2u*(a*ns+b);r[at]=z[0];r[at+1]=z[1];
            }
        }else r[sw+column-c]=1;
        if(*slot)return;fibre_query(basis,w,w,r,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
        for(uint32_t i=0;i<k;++i)row[i]=i<w?r[i]:0;
        if(column<c)for(uint32_t i=0;i<c;++i)row[w+i]=product_checked(pf[pk+4+(size_t)column*c+i],den,slot);
        else row[w+c+column-c]=den;
        if(*slot)return;condition_stage_row(graph,graph_hi,k,row,slot);if(*slot)return;
    }
    wide den=product_checked(sd,cd,slot);
    for(uint32_t i=0;i<w;++i)r[i]=0;
    for(uint32_t i=0;i<2u*ns;++i)r[i]=product_checked(source_lo[source_at+i],cd,slot);
    for(uint32_t i=0;i<c;++i)r[2u*ns+i]=product_checked(pf[ps+i],sd,slot);
    for(uint32_t a=0;a<nc;++a)for(uint32_t b=0;b<ns;++b){
        wide z[3];fibre_phase_product(source_lo[source_at+2*b],source_lo[source_at+2*b+1],1,pf[ps+2*a],pf[ps+2*a+1],1,z,slot);
        uint32_t at=2u*ns+c+2u*(a*ns+b);r[at]=z[0];r[at+1]=z[1];
    }
    if(*slot)return;fibre_query(basis,w,w,r,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
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
    condition_project(joint,w,joint_target,0,c,domain_basis,domain_basis_hi,domain,domain_hi,row,slot);
    condition_project(joint,w,joint_target,c,y,out_basis,out_basis_hi,out,out_hi,row,slot);if(*slot)return;
    if(status==1){
        for(uint32_t i=0;i<c;++i)row[i]=pf[ps+i];
        for(uint32_t i=0;i<w;++i)q[i]=joint[i];
        condition_coverage_write(2,-1,row,cd,c,q,joint[k],w,w,coverage,coverage_hi,slot);return;
    }
    // The supported condition domain is a subset of the input fibre. Check the reverse inclusion
    // on its affine origin and every retained direction, and exhibit the first failed member.
    wide dd=domain[w+c],rd=fibre_lcm(cd,dd,slot);
    for(uint32_t i=0;i<c;++i)q[i]=sub_checked(product_checked(pf[ps+i],rd/cd,slot),product_checked(domain[w+i],rd/dd,slot),slot);
    if(*slot)return;fibre_query(domain_basis,c,c,q,&rd,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
    int64_t failed=-1;bool partial=condition_nonzero(q,c);
    if(!partial)for(uint32_t p=0;p<c;++p){
        for(uint32_t i=0;i<c;++i)q[i]=pf[pk+4+(size_t)p*c+i];rd=1;
        fibre_query(domain_basis,c,c,q,&rd,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
        if(condition_nonzero(q,c)){partial=true;failed=p;break;}
    }
    if(partial){
        for(uint32_t i=0;i<c;++i)row[i]=add_checked(pf[ps+i],failed<0?0:product_checked(cd,pf[pk+4+(size_t)failed*c+i],slot),slot);
        if(*slot)return;condition_coverage_write(1,failed,row,cd,c,q,rd,c,w,coverage,coverage_hi,slot);
    }
    if(*slot)return;
    for(uint32_t i=0;i<y;++i)safe[i]=safe_hi[i]=out[w+i];
    safe[y]=safe_hi[y]=out[w+y];safe[y+1]=safe_hi[y+1]=partial?1:out[w+y+1];
}

// Restrict a complete-domain joint affine family by an actual later output. Homogenization
// pins the base-point coefficient to one, retaining absolute condition coordinates.
extern "C" __global__ void section_constitutive_condition_receive(
    const int64_t *joint,const int64_t *joint_hi,uint32_t js,uint32_t c,uint32_t y,
    const int64_t *coverage,const int64_t *coverage_hi,
    const int64_t *observed_lo,const int64_t *observed_hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    int64_t *graph,int64_t *graph_hi,int64_t *rhs,int64_t *rhs_hi,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x || threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t k64=1u+(uint64_t)c+y,jk64=(uint64_t)js+c+y;
    if(!c || !y || c%2 || y%2 || k64>UINT32_MAX-4u || jk64>UINT32_MAX-4u
        || coverage[0]!=coverage_hi[0] || coverage[0]!=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t j=c+y,jk=(uint32_t)jk64,k=(uint32_t)k64,s=1+y;
    for(size_t i=0;i<(size_t)jk+4+(size_t)j*j;++i)if(joint[i]!=joint_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(joint[jk]<=0 || (joint[jk+1]!=0 && joint[jk+1]!=2)){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide den=fibre_current_denominator(observed_lo,observed_hi,den_at,status_at,slot);if(*slot)return;
    for(uint32_t i=0;i<y;++i)if(observed_lo[at+i]!=observed_hi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    extern __shared__ wide scratch[];wide *row=scratch,*q=row+k;
    for(size_t i=0;i<(size_t)k*k;++i)graph[i]=graph_hi[i]=0;
    for(uint32_t p=0;p<=j;++p){
        row[0]=p==0?joint[jk]:0;
        for(uint32_t i=0;i<y;++i)row[1+i]=p==0?joint[js+c+i]:joint[(size_t)jk+4+(size_t)(p-1)*j+c+i];
        for(uint32_t i=0;i<c;++i)row[s+i]=p==0?joint[js+i]:joint[(size_t)jk+4+(size_t)(p-1)*j+i];
        condition_stage_row(graph,graph_hi,k,row,slot);if(*slot)return;
    }
    q[0]=den;for(uint32_t i=0;i<y;++i)q[1+i]=observed_lo[at+i];for(uint32_t i=s;i<k;++i)q[i]=0;
    for(uint32_t i=0;i<s;++i)rhs[i]=rhs_hi[i]=(int64_t)q[i];rhs[s]=rhs_hi[s]=(int64_t)den;
    uint32_t status=0,rank=0;fibre_query(graph,s,k,q,&den,nullptr,-1,&status,&rank,slot);if(*slot)return;
    for(uint32_t i=s;i<k;++i)q[i]=-q[i];
    condition_store_report(graph,s,k,q,den,status,rank,out,out_hi,slot);
}
