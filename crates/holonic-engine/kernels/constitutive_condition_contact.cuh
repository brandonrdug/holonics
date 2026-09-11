// Unit-admittance contact with an affine condition family F=a+V, in the declared
// realified phase chart. P projects onto V, Q=I-P. The two-port exchange is
// (h,Qa) -> (Ph+Qa,Qh). It retains unconstrained current; it does not identify a cause.
extern "C" __global__ void section_constitutive_condition_current_found(
    const int64_t *lo, const int64_t *hi, uint32_t at, uint32_t den_at, uint32_t status_at,
    uint32_t c, int64_t *out, int64_t *out_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x || threadIdx.x) return;
    if (upstream_refused(census,lineage,lineage_count,slot)) return;
    wide den=fibre_current_denominator(lo,hi,den_at,status_at,slot);
    for(uint32_t j=0;j<c;++j) if(lo[at+j]!=hi[at+j]) atomicOr(slot,REFUSED_MALFORMED);
    to_word(den,slot); if(*slot) return;
    for(uint32_t j=0;j<5u*c;++j) out[j]=out_hi[j]=j<2u*c ? lo[at+j%c] : 0;
    out[5u*c]=out_hi[5u*c]=(int64_t)den;
    out[5u*c+1]=out_hi[5u*c+1]=0;
}

extern "C" __global__ void section_constitutive_condition_contact(
    const int64_t *lo, const int64_t *hi, uint32_t at, uint32_t den_at, uint32_t status_at,
    const int64_t *pf, const int64_t *pf_hi, uint32_t ps, uint32_t c,
    int64_t *graph, int64_t *graph_hi, int64_t *out, int64_t *out_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x || threadIdx.x) return;
    if (upstream_refused(census,lineage,lineage_count,slot)) return;
    uint32_t pk=ps+c,k=2u*c;
    size_t count=(size_t)pk+4+(size_t)c*c;
    for(size_t j=0;j<count;++j) if(pf[j]!=pf_hi[j]) atomicOr(slot,REFUSED_MALFORMED);
    if(pf[pk]<=0 || pf[pk+1]<0 || pf[pk+1]>2) atomicOr(slot,REFUSED_MALFORMED);
    wide hd=fibre_current_denominator(lo,hi,den_at,status_at,slot);
    for(uint32_t j=0;j<c;++j) if(lo[at+j]!=hi[at+j]) atomicOr(slot,REFUSED_MALFORMED);
    if(*slot) return;
    extern __shared__ wide scratch[];
    wide *row=scratch,*query=row+k,*values=query+k;
    for(uint32_t j=0;j<5u*c;++j) values[j]=j<2u*c ? lo[at+j%c] : 0;
    wide den=hd;
    // An empty compatible family makes no assertion about the actual retained current.
    // Preserve that current, return the family obstruction, and never publish a fabricated point.
    if(pf[pk+1]!=1) {
        const int64_t *directions=pf+pk+4;
        for(size_t j=0;j<(size_t)k*k;++j) graph[j]=graph_hi[j]=0;
        // Graph of V restricted to span(V^T): rows (V v_i, v_i). This also handles
        // zero-padded rows. Existing exact elimination supplies P, not a second solver.
        for(uint32_t i=0;i<c;++i) {
            for(uint32_t j=0;j<k;++j)row[j]=0;
            bool nonzero=false;
            // Same Gram sums, in the same per-coordinate order. Exact zero coefficients
            // contribute nothing; sparse/padded families need no dense cubic zero work.
            for(uint32_t n=0;n<c;++n){
                int64_t vi=directions[(size_t)i*c+n];if(!vi)continue;
                nonzero=true;row[c+n]=vi;
                for(uint32_t j=0;j<c;++j){int64_t vj=directions[(size_t)j*c+n];
                    if(vj)row[j]=add_checked(row[j],product_checked(vj,vi,slot),slot);
                }
            }
            if(*slot)return;
            if(nonzero){condition_stage_row(graph,graph_hi,k,row,slot);if(*slot)return;}
        }
        wide projection_den[2];
        for(uint32_t which=0;which<2;++which) {
            const int64_t *input=which ? pf+ps : lo+at;
            wide pd=which ? pf[pk] : hd;
            for(uint32_t j=0;j<c;++j) {
                query[j]=0; query[c+j]=0;
                for(uint32_t n=0;n<c;++n)
                    query[j]=add_checked(query[j],product_checked(directions[(size_t)j*c+n],input[n],slot),slot);
            }
            if(*slot) return;
            uint32_t disposition=0,rank=0;
            fibre_query(graph,c,k,query,&pd,nullptr,-1,&disposition,&rank,slot);
            if(*slot) return;
            // Gram positivity gives a unique projection for every input. Anything else is
            // an arithmetic/representation defect, not permission to select a free point.
            if(disposition!=0) { atomicOr(slot,REFUSED_MALFORMED); return; }
            for(uint32_t j=0;j<c;++j) values[(which+1u)*c+j]=sub_checked(0,query[c+j],slot);
            projection_den[which]=pd;
        }
        den=fibre_lcm(hd,pf[pk],slot);
        den=fibre_lcm(den,projection_den[0],slot);
        den=fibre_lcm(den,projection_den[1],slot);
        if(*slot) return;
        for(uint32_t j=0;j<c;++j) {
            wide h=product_checked(lo[at+j],den/hd,slot);
            wide ph=product_checked(values[c+j],den/projection_den[0],slot);
            wide pa=product_checked(values[2u*c+j],den/projection_den[1],slot);
            wide incoming=sub_checked(product_checked(pf[ps+j],den/pf[pk],slot),pa,slot);
            wide returned=sub_checked(h,ph,slot);
            values[j]=h;
            values[c+j]=add_checked(ph,incoming,slot);
            values[2u*c+j]=incoming;
            values[3u*c+j]=returned;
            values[4u*c+j]=sub_checked(incoming,returned,slot);
        }
    }
    fibre_normalize(values,5u*c,&den,slot);
    for(uint32_t j=0;j<5u*c;++j) to_word(values[j],slot);
    to_word(den,slot); if(*slot) return;
    // Only fresh output is written. The continuing current is transferred by its Rust owner
    // after the complete passage succeeds; no rollback copy of the ecology is made.
    for(uint32_t j=0;j<5u*c;++j) out[j]=out_hi[j]=(int64_t)values[j];
    out[5u*c]=out_hi[5u*c]=(int64_t)den;
    out[5u*c+1]=out_hi[5u*c+1]=pf[pk+1]==1 ? 1 : 0;
}
