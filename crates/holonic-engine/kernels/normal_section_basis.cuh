// One simultaneous basis selection per consecutive section of one joint enclosure.
extern "C" __global__ __launch_bounds__(512) void section_normal_wave_basis_sections(
    const int64_t *current_lo,const int64_t *current_hi,uint32_t current_at,uint32_t current_width,
    uint32_t n,uint32_t sections,uint32_t grain,const int64_t *permutation_lo,const int64_t *permutation_hi,
    int64_t *scores,int64_t *scores_hi,int64_t *report,int64_t *report_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!n||!sections||current_width!=2u*n*sections||grain<1u||grain>120u||current_at&1u){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *v=(const wide *)(current_lo+current_at);
    for(uint32_t j=0;j<2u*(current_width+1u);++j)if(current_lo[current_at+j]!=current_hi[current_at+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide radius=v[current_width];if(radius<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t j=0;j<n;++j){
        if(permutation_lo[j]!=permutation_hi[j]||permutation_lo[j]<0||permutation_lo[j]>=(int64_t)n){atomicOr(slot,REFUSED_MALFORMED);return;}
        for(uint32_t k=0;k<j;++k)if(permutation_lo[k]==permutation_lo[j]){atomicOr(slot,REFUSED_MALFORMED);return;}
    }
    for(uint32_t section=0;section<sections;++section){
        uint32_t base=2u*n*section, selected=0,ties=1;wide winner=v[base+2u*(uint32_t)permutation_lo[0]];
        for(uint32_t a=1;a<n;++a){wide score=v[base+2u*(uint32_t)permutation_lo[a]];if(score>winner){winner=score;selected=a;ties=1;}else if(score==winner)++ties;}
        bool robust=true;HistoryInteger twice_radius=HistoryInteger(2)*history_integer(radius);
        for(uint32_t a=0;a<n;++a)if(a!=selected){HistoryInteger gap=history_integer(winner)-history_integer(v[base+2u*(uint32_t)permutation_lo[a]]);if(gap<=twice_radius)robust=false;}
        wide *so=(wide*)scores;for(uint32_t a=0;a<n;++a)so[section*n+a]=v[base+2u*(uint32_t)permutation_lo[a]];
        wide *ro=(wide*)report;ro[5u*section]=selected;ro[5u*section+1u]=winner;ro[5u*section+2u]=ties;ro[5u*section+3u]=robust?1:0;ro[5u*section+4u]=radius;
    }
    for(uint32_t j=0;j<2u*n*sections;++j)scores_hi[j]=scores[j];
    for(uint32_t j=0;j<10u*sections;++j)report_hi[j]=report[j];
}
