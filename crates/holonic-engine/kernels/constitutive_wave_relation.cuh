// Fixed-condition pullback. u=(lambda,anchor,p,c,eta), x=(lambda,anchor,p,c),
// y=(lambda,anchor,c,c+eta). Lambda is a complex homogenizing coordinate; the anchored
// family fixes lambda=1. This derives all of ker(residual_L E_h), including vertical rows.
extern "C" __global__ void section_constitutive_wave_relation(
    const int64_t *basis,const int64_t *basis_hi,
    const int64_t *condition,const int64_t *condition_hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    uint32_t n,uint32_t kc,uint32_t receiver,int64_t *graph,int64_t *graph_hi,
    int64_t *derived,int64_t *derived_hi,int64_t *fixed,int64_t *fixed_hi,int64_t *workspace,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint64_t f64=2u*(3u*(uint64_t)n+kc+3u*(uint64_t)n*kc),l64=f64+2u*n;
    uint64_t q64=2u+8u*(uint64_t)n,u64=2u+10u*(uint64_t)n,g64=l64+u64;
    if(!n||!kc||receiver>1u||g64>UINT32_MAX||2u*q64>UINT32_MAX){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t f=(uint32_t)f64,l=(uint32_t)l64,q=(uint32_t)q64,u=(uint32_t)u64,g=(uint32_t)g64;
    uint32_t a=4u*n,r=2u*n,source_width=6u*n,hwidth=2u*kc,z_at=2u+a,eta_at=z_at+2u*r;
    for(size_t i=0;i<(size_t)l*l;++i)if(basis[i]!=basis_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(receiver)for(uint32_t p=0;p<l;++p){
        wide sum=0;for(uint32_t i=0;i<n;++i)sum=add_checked(sum,basis[(size_t)p*l+f+2u*i],slot);
        if(*slot)return;if(sum){atomicOr(slot,REFUSED_MALFORMED);return;}
    }
    wide hd=fibre_current_denominator(condition,condition_hi,den_at,status_at,slot);if(*slot)return;
    for(uint32_t i=0;i<hwidth;++i)if(condition[at+i]!=condition_hi[at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide *residual=(wide *)workspace,*row=residual+l;
    for(size_t i=0;i<(size_t)g*g;++i)graph[i]=graph_hi[i]=0;
    for(size_t i=0;i<(size_t)(2u*q)*(2u*q);++i)derived[i]=derived_hi[i]=0;
    wide scale=product_checked(hd,receiver?n:1u,slot);if(*slot)return;
    for(uint32_t col=0;col<u;++col){
        for(uint32_t i=0;i<l;++i)residual[i]=0;
        if(col<2u){
            // The constant feature h becomes h*lambda; mixed features remain a*h.
            for(uint32_t j=0;j<kc;++j){
                wide hr=condition[at+2u*j],hi=condition[at+2u*j+1u];
                residual[source_width+2u*j]=product_checked(col? -hi:hr,receiver?n:1u,slot);
                residual[source_width+2u*j+1u]=product_checked(col?hr:hi,receiver?n:1u,slot);
            }
            if(receiver&&col==0)for(uint32_t j=0;j<n;++j){residual[r+2u*j]=hd;residual[2u*r+2u*j]=hd;}
        }else if(col>=z_at&&col<eta_at){
            uint32_t j=(col-z_at)%r;
            bool is_current=col>=z_at+r;
            residual[j]=is_current?scale:-scale;
            residual[(is_current?r:2u*r)+j]=scale;
            if(receiver&&!(j&1u))for(uint32_t i=0;i<n;++i){
                residual[2u*i]=add_checked(residual[2u*i],is_current?-hd:hd,slot);
                uint32_t at=(is_current?r:2u*r)+2u*i;
                residual[at]=sub_checked(residual[at],hd,slot);
            }
        }else if(col>=eta_at)residual[f+col-eta_at]=scale;
        for(uint32_t h=0;h<kc;++h)for(uint32_t b=0;b<3u*n;++b){
            // Source columns are integral unit coefficients, represented above at denominator hd.
            wide ar=residual[2u*b]/hd,ai=residual[2u*b+1u]/hd;
            wide hr=condition[at+2u*h],hi=condition[at+2u*h+1u];
            uint32_t j=source_width+hwidth+2u*(h*(3u*n)+b);
            residual[j]=sub_checked(product_checked(ar,hr,slot),product_checked(ai,hi,slot),slot);
            residual[j+1u]=add_checked(product_checked(ar,hi,slot),product_checked(ai,hr,slot),slot);
        }
        if(*slot)return;
        wide den=scale;uint32_t ignored=0,rank=0;
        fibre_query(basis,l,l,residual,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
        for(uint32_t i=0;i<g;++i)row[i]=i<l?residual[i]:(i-l==col?den:0);
        condition_stage_row(graph,graph_hi,g,row,slot);if(*slot)return;
    }
    // Residual-prefix-zero graph rows are exactly the kernel. Map them into the complete
    // input/output graph and eliminate dependent mapped rows with the existing relation owner.
    for(uint32_t pivot=0;pivot<u;++pivot){
        const int64_t *v=graph+(size_t)(l+pivot)*g+l;
        if(!v[pivot])continue;
        for(uint32_t i=0;i<2u*q;++i)row[i]=0;
        for(uint32_t i=0;i<q;++i)row[i]=v[i];
        for(uint32_t i=0;i<z_at;++i)row[q+i]=v[i];
        for(uint32_t i=0;i<r;++i){
            row[q+z_at+i]=v[z_at+r+i];
            row[q+z_at+r+i]=add_checked(v[z_at+r+i],v[eta_at+i],slot);
        }
        if(*slot)return;
        condition_stage_row(derived,derived_hi,2u*q,row,slot);if(*slot)return;
    }
    for(uint32_t i=0;i<hwidth;++i)fixed[i]=fixed_hi[i]=condition[at+i];
    to_word(hd,slot);if(*slot)return;
    fixed[hwidth]=fixed_hi[hwidth]=(int64_t)hd;
}
