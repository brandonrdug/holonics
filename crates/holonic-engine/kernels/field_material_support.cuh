// Exact coordinate restriction of a contextual report. One target coordinate owns 82
// words; radii, source geometry, chronology and scalar defects are common standing.
__device__ size_t material_coordinate_word(uint32_t n,uint32_t t,uint32_t coordinate,uint32_t word){
    if(word<44u)return (size_t)(word/4u)*(4u*t+2u)+4u*coordinate+word%4u;
    word-=44u;
    if(word<8u)return contextual_beta(n,t)+(size_t)(word/4u)*4u*t+4u*coordinate+word%4u;
    word-=8u;
    return contextual_raw(n,t)+(size_t)(word/10u)*10u*t+10u*coordinate+word%10u;
}
__device__ size_t material_common_word(uint32_t n,uint32_t t,uint32_t word){
    if(word<22u)return (size_t)(word/2u)*(4u*t+2u)+4u*t+word%2u;
    word-=22u;uint32_t geometry=68u*n+46u;
    return word<geometry?contextual_output_visible(n,t)+word:contextual_meta(n,t)+word-geometry;
}
extern "C" __global__ void section_field_material_support(
    const int64_t *input,uint32_t n,uint32_t t,int64_t *lo,int64_t *hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t count=0;
    for(uint32_t i=0;i<t;++i){bool present=false;
        for(uint32_t w=0;w<82u;++w)if(input[material_coordinate_word(n,t,i,w)]!=0){present=true;break;}
        if(present)lo[1u+count]=hi[1u+count]=i,++count;
    }
    lo[0]=hi[0]=count;for(uint32_t i=count;i<t;++i)lo[1u+i]=hi[1u+i]=-1;
}
extern "C" __global__ void section_field_material_pack(
    const int64_t *input,const int64_t *support,uint32_t n,uint32_t t,uint32_t count,
    int64_t *lo,int64_t *hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t j=blockIdx.x*blockDim.x+threadIdx.x,common=68u*n+96u;
    if(j>=common+82u*count)return;
    if(support[0]!=(int64_t)count || count>t){atomicOr(slot,REFUSED_MALFORMED);return;}
    size_t from;
    if(j<common)from=material_common_word(n,t,j);
    else{uint32_t row=(j-common)/82u;int64_t axis=support[1u+row];
        if(axis<0 || axis>=(int64_t)t || (row && support[row]>=axis)){atomicOr(slot,REFUSED_MALFORMED);return;}
        from=material_coordinate_word(n,t,(uint32_t)axis,(j-common)%82u);
    }
    lo[j]=hi[j]=input[from];
}
extern "C" __global__ void section_field_material_unfold(
    const int64_t *packed,const int64_t *support,uint32_t n,uint32_t t,uint32_t count,uint32_t current_only,
    int64_t *lo,int64_t *hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t row=blockIdx.x;if(threadIdx.x)return;
    uint32_t common=68u*n+96u;
    if(support[0]!=(int64_t)count || count>t){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(row==t){
        if(current_only){lo[4u*t]=hi[4u*t]=packed[0];lo[4u*t+1u]=hi[4u*t+1u]=packed[1];}
        else for(uint32_t j=0;j<common;++j){size_t at=material_common_word(n,t,j);lo[at]=hi[at]=packed[j];}
        return;
    }
    if(row>t)return;
    uint32_t left=0,right=count;
    while(left<right){uint32_t mid=left+(right-left)/2u;if(support[1u+mid]<(int64_t)row)left=mid+1u;else right=mid;}
    bool present=left<count && support[1u+left]==(int64_t)row;
    for(uint32_t j=0;j<(current_only?4u:82u);++j){
        size_t at=current_only?4u*(size_t)row+j:material_coordinate_word(n,t,row,j);
        lo[at]=hi[at]=present?packed[common+82u*(size_t)left+j]:0;
    }
}
