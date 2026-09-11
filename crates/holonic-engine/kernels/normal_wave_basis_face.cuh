// One unit-basis receiver of a complete joint Euclidean enclosure. Scores retain the shared
// radius; endpoints need not fit in one wide word. Their observer decoder uses exact rationals.
// Selection is native, and strict gap comparison uses the existing wider exact integer owner.
extern "C" __global__ __launch_bounds__(512) void section_normal_wave_basis_face(
    const int64_t *current_lo,const int64_t *current_hi,uint32_t current_at,uint32_t current_width,
    uint32_t n,uint32_t grain,const int64_t *permutation_lo,const int64_t *permutation_hi,
    int64_t *output,int64_t *output_hi,int64_t *report,int64_t *report_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!n||current_width!=2u*n||grain<1u||grain>120u||(current_at&1u)){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    for(uint32_t j=0;j<2u*(current_width+1u);++j)
        if(current_lo[current_at+j]!=current_hi[current_at+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *v=(const wide *)(current_lo+current_at);
    const wide radius=v[current_width];
    if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=0;j<n;++j){
        if(permutation_lo[j]!=permutation_hi[j]||permutation_lo[j]<0||permutation_lo[j]>=(int64_t)n){
            atomicOr(slot,REFUSED_MALFORMED);return;
        }
        for(uint32_t k=0;k<j;++k)if(permutation_lo[k]==permutation_lo[j]){
            atomicOr(slot,REFUSED_MALFORMED);return;
        }
    }
    wide winner=v[2u*(uint32_t)permutation_lo[0]];
    uint32_t selected=0,ties=1;
    for(uint32_t a=1;a<n;++a){
        wide score=v[2u*(uint32_t)permutation_lo[a]];
        if(score>winner){winner=score;selected=a;ties=1;}
        else if(score==winner)++ties;
    }
    bool robust=true;
    HistoryInteger twice_radius=HistoryInteger(2)*history_integer(radius);
    for(uint32_t a=0;a<n;++a)if(a!=selected){
        HistoryInteger gap=history_integer(winner)-history_integer(v[2u*(uint32_t)permutation_lo[a]]);
        if(gap<=twice_radius)robust=false;
    }
    for(uint32_t a=0;a<n;++a)((wide *)output)[a]=v[2u*(uint32_t)permutation_lo[a]];
    wide *r=(wide *)report;
    r[0]=(wide)selected;r[1]=winner;r[2]=(wide)ties;r[3]=robust?1:0;r[4]=radius;
    for(uint32_t j=0;j<2u*n;++j)output_hi[j]=output[j];
    for(uint32_t j=0;j<10u;++j)report_hi[j]=report[j];
}
