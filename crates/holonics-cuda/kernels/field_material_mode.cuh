// Read the already formed complete material operator on m=(e_left-e_right)/2.
// Mhat m = (1/2) sum beta_i conjugate(q(source_i)). These are immutable factors,
// not a second learner or a replay of their developmental operations.
__device__ void material_mode_source(
    uint64_t source,uint64_t left,uint64_t right,uint64_t current_cut,
    const wide *contact,const wide *left_before,const wide *right_before,const wide *prefix,
    const wide *mode,uint32_t D,wide *real,wide *imaginary,uint32_t *slot
) {
    *real=0;*imaginary=0;
    bool l=source>=left,r=source>=right;
    if(l && r) {
        *real=mode[0];*imaginary=mode[1];
        if((source^current_cut)&1u){*real=sub_checked(0,*real,slot);*imaginary=sub_checked(0,*imaginary,slot);}return;
    }
    if(!l && !r)return;
    if(!prefix){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *born=l?left_before:right_before;
    uint32_t start=3u*(D+1u);
    for(uint32_t j=0;j<D;j+=2){
        wide a=sub_checked(prefix[start+j],born[start+j],slot),b=sub_checked(prefix[start+j+1],born[start+j+1],slot);
        *real=add_checked(*real,add_checked(product_checked(contact[j],a,slot),product_checked(contact[j+1],b,slot),slot),slot);
        *imaginary=add_checked(*imaginary,sub_checked(product_checked(contact[j],b,slot),product_checked(contact[j+1],a,slot),slot),slot);
    }
    if((source&1u)^(!l)){*real=sub_checked(0,*real,slot);*imaginary=sub_checked(0,*imaginary,slot);}
}

extern "C" __global__ void section_complete_material_mode(
    const int64_t *state,const int64_t *source_report,const int64_t *refreshed,const int64_t *receiving_report,
    const wide *contact,const wide *mode_report,const wide *left_before,const wide *right_before,
    const int64_t *factors,uint32_t count,uint32_t nodes,uint32_t grain,
    uint64_t left,uint64_t right,uint64_t source_at,uint64_t current_cut,uint64_t mode_cut,
    int64_t *out_lo,int64_t *out_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t R=2u*nodes,D=6u*nodes,stride=R+1u;
    if(!nodes || grain<1 || grain>120 || left==right || source_at<left || source_at<right || current_cut<source_at
        || mode_cut>current_cut || mode_cut<left || mode_cut<right
        || contact[D]!=1 || mode_report[2]<0 || mode_report[3]<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide S=(wide)((uwide)1u<<grain);
    if(S%mode_report[3]){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide q[3];for(uint32_t j=0;j<3;++j)q[j]=product_checked(mode_report[j],S/mode_report[3],slot);
    if(*slot)return;
    wide q_source[3]={q[0],q[1],q[2]};
    if((source_at^mode_cut)&1u){q_source[0]=sub_checked(0,q_source[0],slot);q_source[1]=sub_checked(0,q_source[1],slot);}
    wide *out=(wide *)out_lo,*upper=(wide *)out_hi;
    size_t ball_words=2u*(3u+13u*(size_t)stride),raw_at=ball_words;
    for(uint32_t j=0;j<3u+13u*stride;++j)out[j]=upper[j]=0;
    for(uint32_t j=0;j<3;++j)out[j]=q_source[j];
    wide *balls=out+3;
    wide kr[3]={0,0,0},yr[3]={0,0,0},full_rounds=0;
    bool changed=false,old_present=false;
    for(uint32_t f=0;f<count;++f) {
        if((uint64_t)factors[4u*f+3u]>source_at)changed=true;else old_present=true;
    }
    const int64_t *original_exact=source_report+complete_forward_at(nodes);
    const int64_t *current_exact=refreshed?refreshed:original_exact;
    for(uint32_t row=0;row<nodes;++row){
        HistoryInteger old_r,old_i,now_r,now_i;
        for(uint32_t f=0;f<count;++f){
            const int64_t *increment=(const int64_t *)(uintptr_t)(uint64_t)factors[4u*f];
            const wide *prefix=(const wide *)(uintptr_t)(uint64_t)factors[4u*f+1u];
            uint64_t source=(uint64_t)factors[4u*f+2u],cut=(uint64_t)factors[4u*f+3u];
            if(!increment || cut>current_cut || source>=cut){atomicOr(slot,REFUSED_MALFORMED);return;}
            wide qr,qi;material_mode_source(source,left,right,mode_cut,contact,left_before,right_before,prefix,q,D,&qr,&qi,slot);
            const wide *beta=(const wide *)(increment+complete_ball_words(nodes));
            HistoryInteger dr,di;
            complete_complex_product(history_integer(beta[2u*row]),history_integer(beta[2u*row+1u]),history_integer(qr),-history_integer(qi),dr,di);
            now_r=now_r+dr;now_i=now_i+di;
            if(cut<=source_at){old_r=old_r+dr;old_i=old_i+di;}
        }
        if(*slot)return;
        HistoryInteger k_r[3]={old_r,now_r,now_r-old_r},k_i[3]={old_i,now_i,now_i-old_i};
        for(uint32_t b=0;b<3;++b){
            balls[b*stride+2u*row]=complete_to_grid(k_r[b],grain+1,&kr[b],slot);
            balls[b*stride+2u*row+1u]=complete_to_grid(k_i[b],grain+1,&kr[b],slot);
            HistoryInteger a,z;
            complete_complex_product(k_r[b],k_i[b],history_integer(q_source[0]),history_integer(q_source[1]),a,z);
            balls[(3u+b)*stride+2u*row]=complete_to_grid(a,2u*grain+1,&yr[b],slot);
            balls[(3u+b)*stride+2u*row+1u]=complete_to_grid(z,2u*grain+1,&yr[b],slot);
            if(b<2){
                size_t at=raw_at+5u*(b*R+2u*row);
                history_write_integer(k_r[b],out_lo+at,out_hi+at,slot);
                history_write_integer(k_i[b],out_lo+at+5u,out_hi+at+5u,slot);
            }
        }
        for(uint32_t j=0;j<2;++j){
            uint32_t coord=2u*row+j;
            HistoryInteger a=history_read_integer(original_exact+5u*coord,slot),b=history_read_integer(current_exact+5u*coord,slot);
            wide ignored=0;
            balls[8u*stride+coord]=complete_to_grid(a,2u*grain,&ignored,slot);
            balls[9u*stride+coord]=complete_to_grid(b,2u*grain,&full_rounds,slot);
            history_write_integer(a,out_lo+raw_at+5u*(2u*R+coord),out_hi+raw_at+5u*(2u*R+coord),slot);
            history_write_integer(b,out_lo+raw_at+5u*(3u*R+coord),out_hi+raw_at+5u*(3u*R+coord),slot);
            balls[6u*stride+coord]=sub_checked(balls[8u*stride+coord],balls[3u*stride+coord],slot);
            balls[7u*stride+coord]=sub_checked(balls[9u*stride+coord],balls[4u*stride+coord],slot);
            balls[10u*stride+coord]=sub_checked(balls[9u*stride+coord],balls[8u*stride+coord],slot);
            if(receiving_report){
                balls[11u*stride+coord]=((const wide *)receiving_report)[2u*stride+coord];
                balls[12u*stride+coord]=sub_checked(balls[11u*stride+coord],balls[8u*stride+coord],slot);
            }
        }
    }
    if(*slot)return;
    const wide *old_bounds=(const wide *)(source_report+complete_extra_at(nodes));
    const wide *new_bounds=(const wide *)(state+complete_state_words(nodes)-4u);
    if(old_bounds[0]<0 || new_bounds[0]<0 || new_bounds[1]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    // The initial operator is zero. Updates whose source predates both births have exactly
    // zero columns here, regardless of the uncertainty in their other coefficient columns.
    wide old_error=old_present?old_bounds[0]:0;
    wide errors[3]={old_error,changed?new_bounds[0]:old_error,changed?add_checked(old_error,new_bounds[0],slot):0};
    wide qnorm=complete_norm(q_source,2,slot);
    for(uint32_t b=0;b<3;++b){
        wide knorm=add_checked(complete_norm(balls+b*stride,R,slot),kr[b],slot);
        balls[b*stride+R]=add_checked(errors[b],kr[b],slot);
        balls[(3u+b)*stride+R]=add_checked(yr[b],add_checked(
            ft_ceil_product(errors[b],add_checked(qnorm,q_source[2],slot),grain,slot),
            ft_ceil_product(knorm,q_source[2],grain,slot),slot),slot);
    }
    balls[8u*stride+R]=((const wide *)source_report)[R];
    balls[9u*stride+R]=complete_forward_error(new_bounds[0],new_bounds[1],source_report+complete_source_at(nodes),D,grain,full_rounds,slot);
    balls[6u*stride+R]=add_checked(balls[8u*stride+R],balls[3u*stride+R],slot);
    balls[7u*stride+R]=add_checked(balls[9u*stride+R],balls[4u*stride+R],slot);
    balls[10u*stride+R]=!refreshed?0:add_checked(balls[8u*stride+R],balls[9u*stride+R],slot);
    if(receiving_report){
        balls[11u*stride+R]=((const wide *)receiving_report)[3u*stride-1u];
        balls[12u*stride+R]=add_checked(balls[11u*stride+R],balls[8u*stride+R],slot);
    }
    if(*slot)return;
    for(size_t i=0;i<ball_words;++i)out_hi[i]=out_lo[i];
}

// Frozen current material map, applied to the mode's descended future word. The complete
// original report remains the shared origin of this return, including its coefficient defects.
extern "C" __global__ void section_material_mode_unfold(
    const wide *origin,uint32_t nodes,uint64_t steps,wide *lo,wide *hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    uint32_t R=2u*nodes;const wide *mode=origin+3u+4u*(R+1u);
    if(!nodes || mode[R]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<R;++i)lo[i]=hi[i]=(steps&1u)?sub_checked(0,mode[i],slot):mode[i];
    lo[R]=hi[R]=mode[R];
}
