// Exact graph of the stored dyadic normal operator. No target observation, fit or
// centre of a source family is selected here. The input axis rows are construction data.
extern "C" __global__ void section_normal_applied_relation(
    const int64_t *state,const int64_t *state_hi,uint32_t sources,uint32_t graph_sources,uint32_t targets,uint32_t grain,
    int64_t *basis,int64_t *basis_hi,int64_t *workspace,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!sources||sources>graph_sources||!targets||grain<1||grain>120){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t m=2u*sources,f=2u*graph_sources,w=f+2u*targets;
    for(size_t i=0;i<(size_t)2u*m*targets;++i)
        if(state[i]!=state_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<(size_t)w*w;++i)basis[i]=basis_hi[i]=0;
    const wide *M=(const wide *)state;wide *row=(wide *)workspace,S=(wide)1<<grain;
    for(uint32_t axis=0;axis<f;++axis){
        for(uint32_t j=0;j<w;++j)row[j]=0;
        row[axis]=S;
        for(uint32_t t=0;t<targets;++t){
            wide re=axis<m?M[(size_t)t*m+2u*(axis/2u)]:0,im=axis<m?M[(size_t)t*m+2u*(axis/2u)+1u]:0;
            row[f+2u*t]=(axis&1u)?sub_checked(0,im,slot):re;
            row[f+2u*t+1u]=(axis&1u)?re:im;
        }
        if(*slot)return;
        condition_stage_row(basis,basis_hi,w,row,slot);
        if(*slot)return;
    }
}
