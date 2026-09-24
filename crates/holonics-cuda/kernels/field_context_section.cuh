// Two actual passages with one common nonzero source face. Their context contrast is kept
// as the oriented pair of complete-source expressions, not replaced by its numerical centre.
// The established scalar chart is the REAL ray alpha*(c1-c0); no unobserved i-multiple is added.
extern "C" __global__ void section_field_context_section(
    const int64_t *table,uint32_t n,uint32_t grain,
    int64_t *derived,int64_t *derived_hi,int64_t *joint,int64_t *joint_hi,
    int64_t *fixed,int64_t *fixed_hi,int64_t *base,int64_t *base_hi,int64_t *endpoint,int64_t *endpoint_hi,int64_t *proof,int64_t *proof_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!n || n>(UINT32_MAX-4u)/6u || grain<1u || grain>120u){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint32_t D=6u*n,S=4u*n,Y=2u*n,J=2u+Y;
    extern __shared__ wide scratch[];wide *u=scratch,*left=u+D,*right=left+D,*row=right+D;
    wide ignored_den,ld,rd;
    const int64_t *q[12];for(uint32_t i=0;i<12;++i){q[i]=(const int64_t *)(uintptr_t)(uint64_t)table[i];if(!q[i]){atomicOr(slot,REFUSED_MALFORMED);return;}}
    if(!field_paired_build_faces(q[0],q[1],q[2],q[3],q[4],n,1,u,left,&ignored_den,&ld,slot))return;
    if(!field_paired_build_faces(q[6],q[7],q[8],q[9],q[10],n,1,u,right,&ignored_den,&rd,slot))return;
    bool source_nonzero=false;
    for(uint32_t j=0;j<S;++j){
        HistoryInteger diff=history_integer(left[j])*history_integer(rd)-history_integer(right[j])*history_integer(ld);
        if(diff.overflow || !diff.is_zero()){atomicOr(slot,REFUSED_MALFORMED);return;}
        source_nonzero=source_nonzero || left[j]!=0;
    }
    if(!source_nonzero){atomicOr(slot,REFUSED_MALFORMED);return;}
    const int64_t *a=q[5],*b=q[11];
    if(a[6u*D+15u]!=(int64_t)grain || b[6u*D+15u]!=(int64_t)grain){atomicOr(slot,REFUSED_MALFORMED);return;}
    HistoryInteger re,im;history_pairing_value(a,b,D,re,im,slot);
    HistoryInteger square=history_read_integer(a+6u*D+10u,slot)+history_read_integer(b+6u*D+10u,slot)-HistoryInteger(2)*re;
    wide ea=((const wide *)(a+6u*D+16u))[0],eb=((const wide *)(b+6u*D+16u))[0];
    if(ea<0 || eb<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide error=add_checked(ea,eb,slot);HistoryInteger error_square=history_integer(error)*history_integer(error);
    if(*slot || square.overflow || square.negative || error_square.overflow || !(error_square<square)){
        atomicOr(slot,REFUSED_CARRIER);return;
    }
    // Preserve the common source and first actual return in their separate normalized charts.
    for(uint32_t j=0;j<S;++j)u[j]=left[j];wide den=ld;fibre_normalize(u,S,&den,slot);
    for(uint32_t j=0;j<S;++j)to_word(u[j],slot);to_word(den,slot);if(*slot)return;
    for(uint32_t j=0;j<S;++j)fixed[j]=fixed_hi[j]=(int64_t)u[j];fixed[S]=fixed_hi[S]=(int64_t)den;
    for(uint32_t j=0;j<Y;++j)u[j]=sub_checked(0,left[S+j],slot);den=ld;fibre_normalize(u,Y,&den,slot);
    for(uint32_t j=0;j<Y;++j)to_word(u[j],slot);to_word(den,slot);if(*slot)return;
    for(uint32_t j=0;j<Y;++j)base[j]=base_hi[j]=(int64_t)u[j];base[Y]=base_hi[Y]=(int64_t)den;
    for(uint32_t j=0;j<Y;++j)u[j]=sub_checked(0,right[S+j],slot);den=rd;fibre_normalize(u,Y,&den,slot);
    for(uint32_t j=0;j<Y;++j)to_word(u[j],slot);to_word(den,slot);if(*slot)return;
    for(uint32_t j=0;j<Y;++j)endpoint[j]=endpoint_hi[j]=(int64_t)u[j];endpoint[Y]=endpoint_hi[Y]=(int64_t)den;
    den=product_checked(ld,rd,slot);
    for(uint32_t j=0;j<Y;++j)row[2u+j]=sub_checked(product_checked(left[S+j],rd,slot),product_checked(right[S+j],ld,slot),slot);
    if(*slot)return;fibre_normalize(row+2u,Y,&den,slot);
    if(!condition_nonzero(row+2u,Y)){atomicOr(slot,REFUSED_MALFORMED);return;}
    row[0]=den;row[1]=0;
    for(size_t j=0;j<(size_t)J*J;++j)derived[j]=derived_hi[j]=0;
    condition_stage_row(derived,derived_hi,J,row,slot);if(*slot)return;
    context_section_joint(derived,2u,Y,joint,joint_hi);
    history_write_integer(square,proof,proof_hi,slot);
    ((wide *)(proof+6u))[0]=((wide *)(proof_hi+6u))[0]=error;proof[5]=proof_hi[5]=grain;
    history_write_integer(re,proof+8u,proof_hi+8u,slot);
    history_write_integer(im,proof+13u,proof_hi+13u,slot);
}
