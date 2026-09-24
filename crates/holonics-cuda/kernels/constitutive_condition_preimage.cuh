// Affine section of R at fixed source s and actual receiving current y:
// { c | (Phi(s,c),y) in R }. No coefficient model or preselected condition is supplied.
// The existing echelon reduction P_R has kernel R. Build the graph of
// D_s(c)=P_R(0,c,c tensor s,0), and query it at -P_R(s,0,0,y).
extern "C" __global__ void section_constitutive_condition_preimage(
    const int64_t *basis,
    const int64_t *source_lo, const int64_t *source_hi,
    uint32_t source_at, uint32_t source_denominator_at, uint32_t source_disposition_at,
    const int64_t *observed_lo, const int64_t *observed_hi,
    uint32_t observed_at, uint32_t observed_denominator_at, uint32_t observed_disposition_at,
    uint32_t source_complex, uint32_t condition_complex, uint32_t target_width,
    int64_t *graph_lo, int64_t *graph_hi, int64_t *rhs_lo, int64_t *rhs_hi,
    int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x!=0 || threadIdx.x!=0) return;
    if (upstream_refused(census,lineage,lineage_count,slot)) return;
    uint64_t source_width64=2u*((uint64_t)source_complex+condition_complex+(uint64_t)source_complex*condition_complex);
    uint64_t residual_width64=source_width64+target_width;
    uint64_t width64=residual_width64+2u*(uint64_t)condition_complex;
    if (!source_complex || !condition_complex || !target_width || target_width%2u || width64>UINT32_MAX-4u) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    uint32_t source_width=(uint32_t)source_width64, residual_width=(uint32_t)residual_width64;
    uint32_t conditions=2u*condition_complex, width=(uint32_t)width64;
    wide source_den=fibre_current_denominator(source_lo,source_hi,
        source_denominator_at,source_disposition_at,slot);
    wide observed_den=fibre_current_denominator(observed_lo,observed_hi,
        observed_denominator_at,observed_disposition_at,slot);
    if (*slot) return;
    for (uint32_t j=0;j<2u*source_complex;++j) if (source_lo[source_at+j]!=source_hi[source_at+j]) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    for (uint32_t j=0;j<target_width;++j) if (observed_lo[observed_at+j]!=observed_hi[observed_at+j]) {
        atomicOr(slot,REFUSED_MALFORMED); return;
    }
    extern __shared__ wide preimage_scratch[];
    wide *residual=preimage_scratch;
    wide *formed=residual+residual_width;
    wide *query=formed+width;
    // This is newly derived evidence, never the continuing learned basis.
    for (size_t j=0;j<(size_t)width*width;++j) graph_lo[j]=graph_hi[j]=0;
    uint32_t ignored_status=0,ignored_rank=0;
    for (uint32_t coordinate=0;coordinate<conditions;++coordinate) {
        for (uint32_t j=0;j<residual_width;++j) residual[j]=0;
        residual[2u*source_complex+coordinate]=source_den;
        uint32_t condition=coordinate/2u;
        uint32_t mixed_at=2u*(source_complex+condition_complex)+2u*condition*source_complex;
        for (uint32_t s=0;s<source_complex;++s) {
            wide real=source_lo[source_at+2u*s],imaginary=source_lo[source_at+2u*s+1u];
            residual[mixed_at+2u*s]=(coordinate%2u) ? -imaginary : real;
            residual[mixed_at+2u*s+1u]=(coordinate%2u) ? real : imaginary;
        }
        wide denominator=source_den;
        // Reduce through ALL pivots, including the original relation's vertical directions.
        fibre_query(basis,residual_width,residual_width,residual,&denominator,nullptr,-1,
            &ignored_status,&ignored_rank,slot);
        if (*slot) return;
        for (uint32_t j=0;j<width;++j)
            formed[j]=j<residual_width ? residual[j] : (j-residual_width==coordinate ? denominator : 0);
        int64_t inserted=fibre_stage(graph_lo,width,formed,slot);
        for (uint32_t j=0;j<width;++j) to_word(formed[j],slot);
        if (*slot) return;
        if (inserted>=0) for (uint32_t j=0;j<width;++j) {
            size_t at=(size_t)inserted*width+j;
            graph_lo[at]=graph_hi[at]=(int64_t)formed[j];
        }
    }
    // The affine constant includes the actual observed receiver coordinates, with their own
    // denominator. The source and observation are not reinterpreted as a guessed condition.
    wide denominator=fibre_lcm(source_den,observed_den,slot);
    for (uint32_t j=0;j<residual_width;++j) {
        residual[j]=0;
        if (j<2u*source_complex)
            residual[j]=product_checked(source_lo[source_at+j],denominator/source_den,slot);
        else if (j>=source_width)
            residual[j]=product_checked(observed_lo[observed_at+j-source_width],denominator/observed_den,slot);
    }
    if (*slot) return;
    fibre_query(basis,residual_width,residual_width,residual,&denominator,nullptr,-1,
        &ignored_status,&ignored_rank,slot);
    if (*slot) return;
    for (uint32_t j=0;j<residual_width;++j) {
        query[j]=-residual[j];
        to_word(query[j],slot);
    }
    to_word(denominator,slot);
    if (*slot) return;
    for (uint32_t j=0;j<residual_width;++j) rhs_lo[j]=rhs_hi[j]=(int64_t)query[j];
    rhs_lo[residual_width]=rhs_hi[residual_width]=(int64_t)denominator;
    for (uint32_t j=residual_width;j<width;++j) query[j]=0;
    uint32_t disposition=0,rank=0;
    fibre_query(graph_lo,residual_width,width,query,&denominator,nullptr,-1,&disposition,&rank,slot);
    if (*slot) return;
    for (uint32_t j=residual_width;j<width;++j) query[j]=-query[j];
    for (uint32_t j=0;j<width;++j) to_word(query[j],slot);
    to_word(denominator,slot);
    if (*slot) return;
    for (uint32_t j=0;j<width;++j) output_lo[j]=output_hi[j]=(int64_t)query[j];
    output_lo[width]=output_hi[width]=(int64_t)denominator;
    output_lo[width+1]=output_hi[width+1]=disposition;
    output_lo[width+2]=output_hi[width+2]=-1;
    output_lo[width+3]=output_hi[width+3]=rank;
    for (uint32_t p=0;p<conditions;++p) {
        bool occupied=graph_lo[(size_t)(residual_width+p)*width+residual_width+p]!=0;
        for (uint32_t j=0;j<conditions;++j) {
            size_t at=(size_t)width+4+(size_t)p*conditions+j;
            int64_t value=occupied ? graph_lo[(size_t)(residual_width+p)*width+residual_width+j] : 0;
            output_lo[at]=output_hi[at]=value;
        }
    }
}
