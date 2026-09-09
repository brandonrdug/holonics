// Ordinary material return over Q(S) tensor Q(C), with the direct-sum experiment retained.
// S is the actual addressed visible source
// and C is the complete field context available before reception. Equal-source returns also
// conduct their source-null contrast against the first actual reference of that source face.
// Both contacts are staged; the enclosing field publishes their one complete successor.
__device__ size_t contextual_balls(uint32_t n,uint32_t t=0){return 22u*(2u*(size_t)(t?t:n)+1u);}
__device__ size_t contextual_beta(uint32_t n,uint32_t t=0){return contextual_balls(n,t);}
__device__ size_t contextual_profile_words(uint32_t n){return 16u*(size_t)n+12u;}
__device__ size_t contextual_output_visible(uint32_t n,uint32_t t=0){return contextual_beta(n,t)+8u*(t?t:n);}
__device__ size_t contextual_input_visible(uint32_t n,uint32_t t=0){return contextual_output_visible(n,t)+contextual_profile_words(n);}
__device__ size_t contextual_context(uint32_t n,uint32_t t=0){return contextual_input_visible(n,t)+contextual_profile_words(n);}
__device__ size_t contextual_raw(uint32_t n,uint32_t t=0){return contextual_context(n,t)+36u*n+22u;}
__device__ size_t contextual_meta(uint32_t n,uint32_t t=0){return contextual_raw(n,t)+30u*(t?t:n);}
__device__ size_t contextual_extra(uint32_t n,uint32_t t=0){return contextual_meta(n,t)+4u;}

__device__ void contextual_visible(wide *source,wide denominator,uint32_t n,uint32_t grain,int64_t *out,uint32_t *slot){
    uint32_t d=4u*n;wide S=(wide)((uwide)1u<<grain);wide *raw=(wide *)out,*hat=(wide *)(out+8u*n+2u);
    fibre_normalize(source,d,&denominator,slot);if(*slot)return;
    for(uint32_t i=0;i<d;++i)raw[i]=source[i];raw[d]=denominator;
    HistoryInteger norm=complete_power(2u*grain,slot);wide rounds=0;
    for(uint32_t i=0;i<d;++i){
        hat[i]=history_narrow(complete_divide(history_integer(source[i])*history_integer(S),history_integer(denominator),&rounds,slot),slot);
        norm=norm+history_integer(hat[i])*history_integer(hat[i]);
    }
    history_write_integer(norm,out+16u*n+2u,out+16u*n+2u,slot);
    out[16u*n+7u]=0;((wide *)(out+16u*n+8u))[0]=rounds;
    ((wide *)(out+16u*n+10u))[0]=history_norm_ceiling(norm,slot);
}

__device__ wide contextual_normalized_error(wide error,wide norm_upper,uint32_t grain,uint32_t *slot){
    wide S=(wide)((uwide)1u<<grain),lower=norm_upper>error?sub_checked(sub_checked(norm_upper,error,slot),1,slot):0;
    if(lower<S)lower=S;if(error>=lower)return 2*S;
    wide rounds=0;HistoryInteger num=HistoryInteger(2)*history_integer(error)*history_integer(S);
    wide value=history_narrow(complete_divide(num,history_integer(lower),&rounds,slot),slot);
    return add_checked(value,rounds,slot);
}
__device__ wide contextual_source_error(const int64_t *visible,const int64_t *context,uint32_t n,uint32_t grain,uint32_t version,uint32_t *slot){
    uint32_t D=6u*n;wide S=(wide)((uwide)1u<<grain);
    wide es=((const wide *)(visible+16u*n+8u))[0],ec=((const wide *)(context+6u*D+16u))[0];
    wide ns=((const wide *)(visible+16u*n+10u))[0],nc=((const wide *)(context+6u*D+20u))[0];
    if(es<0 || ec<0 || ns<0 || nc<0){atomicOr(slot,REFUSED_MALFORMED);return 0;}
    if(version>=2u){
        wide error=add_checked(contextual_normalized_error(es,ns,grain,slot),contextual_normalized_error(ec,nc,grain,slot),slot);
        return error>2*S?2*S:error;
    }
    wide e=add_checked(es,ec,slot),upper=ns>nc?ns:nc;
    wide lower=upper>e?sub_checked(sub_checked(upper,e,slot),1,slot):0;if(lower<S)lower=S;
    if(e>=lower)return 2*S;
    wide rounds=0;HistoryInteger num=HistoryInteger(2)*history_integer(e)*history_integer(S);
    wide value=history_narrow(complete_divide(num,history_integer(lower),&rounds,slot),slot);
    return add_checked(value,rounds,slot);
}

__device__ void contextual_pair(const int64_t *sa,const int64_t *ca,const int64_t *sb,const int64_t *cb,
    uint32_t n,uint32_t grain,MomentInteger &num,MomentInteger &den,uint32_t *slot){
    uint32_t D=6u*n;HistoryInteger cr,ci,sr,si;
    history_pairing_value(ca,cb,D,cr,ci,slot);
    const wide *a=(const wide *)(sa+8u*n+2u),*b=(const wide *)(sb+8u*n+2u);
    for(uint32_t j=0;j<4u*n;j+=2u)history_complex_add_product(sr,si,a[j],a[j+1],b[j],b[j+1],true);
    MomentInteger re=moment_lift(cr)+moment_lift(sr)+moment_lift(complete_power(2u*grain,slot));
    MomentInteger im=moment_lift(ci)+moment_lift(si);
    MomentInteger na=moment_lift(history_read_integer(ca+6u*D+10u,slot))+moment_lift(history_read_integer(sa+16u*n+2u,slot));
    MomentInteger nb=moment_lift(history_read_integer(cb+6u*D+10u,slot))+moment_lift(history_read_integer(sb+16u*n+2u,slot));
    num=re*re+im*im;den=na*nb;
    if(*slot || num.overflow || den.overflow || num.negative || den.negative || den.is_zero() || den<num)atomicOr(slot,REFUSED_CARRIER);
}
__device__ wide contextual_fraction(MomentInteger num,const MomentInteger &den,uint32_t grain,bool *remainder,uint32_t *slot){
    if(num.overflow || den.overflow || num.negative || den.negative || den.is_zero() || den<num){atomicOr(slot,REFUSED_CARRIER);return 0;}
    if(num==den){*remainder=false;return (wide)((uwide)1u<<grain);}
    wide result=0;
    for(int bit=(int)grain-1;bit>=0;--bit){num=moment_twice(num);if(num.overflow){atomicOr(slot,REFUSED_CARRIER);return 0;}
        if(num>=den){num=num-den;result|=(wide)((uwide)1u<<bit);}}
    *remainder=!num.is_zero();return result;
}
// An operative context is the complete ordered outgoing/internal current carrier.
// Birth order is the field's actual order; shorter histories have exact zero future slots.
__device__ void contextual_operative_source(const wide *current,const wide *b,uint32_t count,uint32_t n,uint32_t grain,uint32_t at,
    wide radius,const int64_t *state,int64_t *next,int64_t *next_hi,int64_t *out,int64_t *hi,uint32_t *slot){
    uint32_t D=6u*n;size_t stride=D+1u;
    if(radius<0 || (count && !b) || state[2u*D+5u]!=(int64_t)at || state[2u*D+6u]!=(int64_t)grain){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<6u*D+22u;++i)out[i]=hi[i]=0;
    for(uint32_t i=0;i<2u*D+8u;++i)next[i]=next_hi[i]=0;
    next[2u*D+5u]=next_hi[2u*D+5u]=(int64_t)at+1;next[2u*D+6u]=next_hi[2u*D+6u]=grain;
    wide *v=(wide *)out;HistoryInteger square;
    for(uint32_t i=0;i<D;++i){v[i]=current[stride+i];square=square+history_integer(v[i])*history_integer(v[i]);}
    for(uint64_t i=0;i<2u*(uint64_t)count;++i)square=square+history_integer(b[i])*history_integer(b[i]);
    history_write_integer(square,out+6u*D+10u,hi+6u*D+10u,slot);
    out[6u*D+15u]=grain;((wide *)(out+6u*D+16u))[0]=radius;out[6u*D+18u]=count;out[6u*D+19u]=at;
    ((wide *)(out+6u*D+20u))[0]=history_norm_ceiling(square,slot);
    for(uint32_t i=0;i<6u*D+22u;++i)hi[i]=out[i];
}
__device__ void contextual_context_pair(const int64_t *a,const wide *ba,const int64_t *b,const wide *bb,uint32_t D,uint32_t grain,uint32_t version,
    MomentInteger &num,MomentInteger &den,uint32_t *slot){
    if(version<3u){moment_pair(a,b,D,grain,num,den,slot);return;}
    int64_t ka=a[6u*D+18u],kb=b[6u*D+18u];
    if(ka<0 || kb<0 || (ka && !ba) || (kb && !bb) || a[6u*D+15u]!=(int64_t)grain || b[6u*D+15u]!=(int64_t)grain){atomicOr(slot,REFUSED_MALFORMED);return;}
    HistoryInteger re,im;const wide *oa=(const wide *)a,*ob=(const wide *)b;
    for(uint32_t i=0;i<D;i+=2u)history_complex_add_product(re,im,oa[i],oa[i+1u],ob[i],ob[i+1u],true);
    for(int64_t i=0;i<(ka<kb?ka:kb);++i)history_complex_add_product(re,im,ba[2u*i],ba[2u*i+1u],bb[2u*i],bb[2u*i+1u],true);
    MomentInteger unit=moment_lift(complete_power(2u*grain,slot));MomentInteger real=unit+moment_lift(re),imaginary=moment_lift(im);
    num=real*real+imaginary*imaginary;
    den=(unit+moment_lift(history_read_integer(a+6u*D+10u,slot)))*(unit+moment_lift(history_read_integer(b+6u*D+10u,slot)));
    if(num.overflow || den.overflow || den.is_zero() || num.negative || den.negative || den<num)atomicOr(slot,REFUSED_CARRIER);
}
__device__ wide contextual_kernel(const int64_t *sa,const int64_t *ca,const int64_t *sb,const int64_t *cb,
    uint32_t n,uint32_t grain,uint32_t version,uint32_t *remainder,uint32_t *slot,const wide *ba=nullptr,const wide *bb=nullptr){
    if(version>=2u){
        HistoryInteger sr,si;const wide *a=(const wide *)(sa+8u*n+2u),*b=(const wide *)(sb+8u*n+2u);
        for(uint32_t j=0;j<4u*n;j+=2u)history_complex_add_product(sr,si,a[j],a[j+1],b[j],b[j+1],true);
        MomentInteger real=moment_lift(sr)+moment_lift(complete_power(2u*grain,slot)),imaginary=moment_lift(si);
        MomentInteger num=real*real+imaginary*imaginary;
        MomentInteger den=moment_lift(history_read_integer(sa+16u*n+2u,slot))*moment_lift(history_read_integer(sb+16u*n+2u,slot));
        bool rs=false,rc=false;wide ks=contextual_fraction(num,den,grain,&rs,slot);
        MomentInteger cn,cd;contextual_context_pair(ca,ba,cb,bb,6u*n,grain,version,cn,cd,slot);
        wide kc=contextual_fraction(cn,cd,grain,&rc,slot),rounds=0;
        wide product=ft_product(ks,kc,grain,&rounds,slot);*remainder=rs+rc+(rounds?1u:0u);return product;
    }
    MomentInteger num,den;contextual_pair(sa,ca,sb,cb,n,grain,num,den,slot);
    bool rem=false;wide value=*slot?0:contextual_fraction(num,den,grain,&rem,slot);*remainder=rem;return value;
}
__device__ const int64_t *contextual_at(const int64_t *table,uint32_t at){return (const int64_t *)(uintptr_t)(uint64_t)table[3u*(size_t)at];}
__device__ const wide *contextual_b_at(const int64_t *table,uint32_t at){return (const wide *)(uintptr_t)(uint64_t)table[3u*(size_t)at+1u];}
__device__ uint32_t contextual_query_context(const int64_t *now,uint32_t n,uint32_t at,uint32_t q,uint32_t targets=0){
    const int64_t *meta=now+contextual_meta(n,targets);return q==0?at:q==1?at-1u:q==2?(uint32_t)meta[1]:(uint32_t)meta[2]-1u;
}
__device__ void contextual_query_parts(const int64_t *table,const int64_t *now,uint32_t n,uint32_t at,uint32_t query,
    const int64_t **visible,const int64_t **context,uint32_t *slot,uint32_t targets=0){
    const int64_t *meta=now+contextual_meta(n,targets);int64_t source=meta[1],reference=meta[2];
    if(query==0){*visible=now+contextual_output_visible(n,targets);*context=now+contextual_context(n,targets);return;}
    if(source<0 || !at){atomicOr(slot,REFUSED_MALFORMED);return;}
    if(query==1){*visible=now+contextual_input_visible(n,targets);*context=contextual_at(table,at-1u)+contextual_context(n,targets);return;}
    if(query==2){const int64_t *old=contextual_at(table,(uint32_t)source);*visible=old+contextual_output_visible(n,targets);*context=old+contextual_context(n,targets);return;}
    if(reference<0 || reference>=(int64_t)at){atomicOr(slot,REFUSED_MALFORMED);return;}
    *visible=contextual_at(table,(uint32_t)reference)+contextual_input_visible(n,targets);
    *context=contextual_at(table,(uint32_t)reference-1u)+contextual_context(n,targets);
}
__device__ void contextual_bound_add(HistoryInteger value,HistoryInteger &positive,HistoryInteger &negative){
    if(value.negative)negative=negative-value;else positive=positive+value;
}
__device__ void contextual_factor_add(HistoryInteger beta,const int64_t *weight,HistoryInteger &sum,HistoryInteger &positive,HistoryInteger &negative){
    sum=sum+beta*history_integer(((const wide *)weight)[0]);
    if(weight[2])contextual_bound_add(beta*HistoryInteger(weight[2]),positive,negative);
}
__device__ HistoryInteger contextual_shift(const MomentInteger &value,uint32_t shift,bool *remainder,uint32_t *slot){
    HistoryInteger result;
    if(value.overflow || value.negative){atomicOr(slot,REFUSED_CARRIER);return result;}
    for(uint32_t bit=0;bit<544u;++bit)if((value.limb[bit/32u]>>(bit%32u))&1u){
        if(bit<shift)*remainder=true;
        else if(bit-shift>=256u)atomicOr(slot,REFUSED_CARRIER);
        else result.limb[(bit-shift)/32u]|=(uint32_t)1u<<((bit-shift)%32u);
    }
    return result;
}
// Update the existing operator current through one coercive return. dnorm_upper is the
// numerical source norm bound, dsquare_grid its squared-norm upper bound on the S grid.
__device__ void contextual_update_bounds(wide *et,wide *nt,const wide *target,const wide *prediction,const wide *beta,
    uint32_t R,uint32_t grain,wide target_error,wide eval_error,wide source_error,wide dnorm_upper,wide dsquare_grid,
    bool gain_remainder,wide beta_rounds,wide *beta_error,uint32_t *slot){
    wide S=(wide)((uwide)1u<<grain),rnorm=0;HistoryInteger residual_square,beta_square,energy=history_integer(*nt)*history_integer(*nt);
    for(uint32_t j=0;j<R;++j){wide r=sub_checked(target[j],prediction[j],slot);residual_square=residual_square+history_integer(r)*history_integer(r);
        HistoryInteger b=history_integer(beta[j]);beta_square=beta_square+b*b;
        energy=energy+HistoryInteger(2)*history_integer(prediction[j])*b;}
    rnorm=history_norm_ceiling(residual_square,slot);wide bnorm=history_norm_ceiling(beta_square,slot);
    *beta_error=add_checked(beta_rounds,gain_remainder?div_ceil(rnorm,S,slot):0,slot);
    wide numeric=add_checked(div_ceil(eval_error,2,slot),ft_ceil_product(dnorm_upper,*beta_error,grain,slot),slot);
    wide y_norm=complete_norm(target,R,slot);
    *et=add_checked(*et,add_checked(numeric,add_checked(div_ceil(target_error,2,slot),
        ft_ceil_product(add_checked(*nt,y_norm,slot),source_error,grain,slot),slot),slot),slot);
    bool remainder=false;HistoryInteger norm_term=contextual_shift(moment_lift(beta_square)*moment_lift(history_integer(dsquare_grid)),grain,&remainder,slot);
    if(remainder)norm_term=norm_term+1;
    energy=energy+norm_term+HistoryInteger(2)*history_integer(eval_error)*history_integer(bnorm);
    wide by_energy=history_norm_ceiling(energy,slot);
    wide by_triangle=add_checked(*nt,ft_ceil_product(bnorm,dnorm_upper,grain,slot),slot);
    *nt=by_energy<by_triangle?by_energy:by_triangle;
}

// Generate the complete tensor packet in least-significant-factor order. Phase is multiplied
// before receiver projection. An exact zero factor makes this coordinate, and its remainder,
// zero; other tensor coordinates remain present.
__device__ void contextual_tensor_target(const int64_t *incoming,uint32_t n,uint32_t width,
    uint32_t targets,uint32_t grain,wide *target,wide *radius,uint32_t *slot){
    wide S=(wide)1<<grain;*radius=0;
    if(width<2u || n%width){atomicOr(slot,REFUSED_MALFORMED);return;}
    uint64_t extent=1;for(uint32_t f=0;f<n/width;++f){extent*=width;if(extent>UINT32_MAX){atomicOr(slot,REFUSED_CARRIER);return;}}
    if(extent!=targets){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t word=0;word<targets;++word){
        uint32_t address=word;wide re=S,im=0,error=0;
        for(uint32_t f=0;f<n/width;++f){
            const int64_t *v=incoming+3u*(f*width+address%width);address/=width;
            if(v[2]<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
            if(v[0]==0 && v[1]==0){re=im=error=0;break;}
            wide ar[2],ea=0;
            for(uint32_t j=0;j<2;++j){
                wide lo=signed_product_divide_2(v[j],S/2,v[2],0,slot),hi=signed_product_divide_2(v[j],S/2,v[2],1,slot);
                ar[j]=v[j]<0?hi:lo;ea=add_checked(ea,lo==hi?0:1,slot);
            }
            wide nz=history_norm_ceiling(history_integer(re)*history_integer(re)+history_integer(im)*history_integer(im),slot);
            wide na=history_norm_ceiling(history_integer(ar[0])*history_integer(ar[0])+history_integer(ar[1])*history_integer(ar[1]),slot);
            wide next_re,next_im,rounds=0;ft_complex_product(re,im,ar[0],ar[1],grain,&next_re,&next_im,&rounds,slot);
            error=add_checked(rounds,add_checked(ft_ceil_product(nz,ea,grain,slot),
                ft_ceil_product(add_checked(na,ea,slot),error,grain,slot),slot),slot);
            re=next_re;im=next_im;
        }
        target[2u*word]=re;target[2u*word+1u]=im;*radius=add_checked(*radius,error,slot);
    }
}

__device__ void contextual_material_prepare(
    const int64_t *state,const int64_t *original,const int64_t *table,uint32_t at,uint64_t source_ordinal,
    int64_t *weights,int64_t *evaluations,const int64_t *query,const int64_t *origin,const int64_t *incoming,
    const int64_t *frame,const int64_t *origin_frame,const int64_t *covariance,const wide *before,const wide *current,
    uint32_t n,uint32_t linked,uint32_t grain,uint32_t version,int64_t *next,int64_t *next_hi,int64_t *out,int64_t *out_hi,
    wide *scratch,uint32_t *slot,wide joint_radius=-1,const wide *operative_b=nullptr,uint32_t operative_count=0,uint32_t targets=0,uint32_t target_factor_width=0
) {
    if(!targets)targets=n;
    uint32_t R=2u*targets,D=6u*n,stride=R+1u;size_t ga=2u*D+8u,raw_stride=30u*targets;
    wide *ball=(wide *)out,*abs_beta=(wide *)(out+contextual_beta(n,targets)),*ctx_beta=abs_beta+R;
    wide S=(wide)((uwide)1u<<grain);int64_t *meta=out+contextual_meta(n,targets);wide *extra=(wide *)(out+contextual_extra(n,targets));
    if(threadIdx.x==0){
        for(size_t i=0;i<contextual_extra(n,targets)+24u;++i)out[i]=out_hi[i]=0;
        if((linked && (!at || source_ordinal>=at || !original)) || at>=(uint32_t)INT64_MAX){atomicOr(slot,REFUSED_MALFORMED);}
        if(!*slot && version>=3u)contextual_operative_source(current,version==4u?nullptr:operative_b,version==4u?0u:operative_count,n,grain,at,joint_radius,state,next,next_hi,out+contextual_context(n,targets),out_hi+contextual_context(n,targets),slot);
        else if(!*slot)field_current_history_source_prepare(query,origin,incoming,frame,origin_frame,covariance,before,current,state,
            n,linked,grain,at,next,next_hi,out+contextual_context(n,targets),out_hi+contextual_context(n,targets),scratch,slot,joint_radius);
        wide ud=1,dd=1;
        if(!*slot && field_paired_build_faces(query,origin,incoming,frame,origin_frame,n,linked,scratch,scratch+D,&ud,&dd,slot))
            contextual_visible(scratch,ud,n,grain,out+contextual_output_visible(n,targets),slot);
        meta[0]=at;meta[1]=linked?(int64_t)source_ordinal:-1;meta[2]=linked?(int64_t)at:-1;meta[3]=version;
        if(linked && !*slot){
            for(size_t j=0;j<contextual_profile_words(n);++j)out[contextual_input_visible(n,targets)+j]=original[contextual_output_visible(n,targets)+j];
            // First actual receiving occurrence fixes the affine reference of this exact source
            // face. Every subsequent observation contributes; this is not an answer selection.
            for(uint32_t i=1;i<at;++i){
                const int64_t *old=contextual_at(table,i),*m=old+contextual_meta(n,targets);
                if(m[1]<0 || m[2]!=(int64_t)i)continue;
                bool same=true;const wide *a=(const wide *)(out+contextual_input_visible(n,targets)),*b=(const wide *)(old+contextual_input_visible(n,targets));
                for(uint32_t j=0;j<=4u*n;++j)if(a[j]!=b[j]){same=false;break;}
                if(same){meta[2]=i;break;}
            }
        }
        wide target_error=0;
        if(target_factor_width && !*slot)contextual_tensor_target(incoming,n,target_factor_width,targets,grain,ball+2u*stride,&target_error,slot);
        else for(uint32_t j=0;j<R && !*slot;++j){
            const int64_t *v=incoming+3u*(j/2u);
            wide lo=signed_product_divide_2(v[j%2u],S/2,v[2],0,slot),hi=signed_product_divide_2(v[j%2u],S/2,v[2],1,slot);
            ball[2u*stride+j]=v[j%2u]<0?hi:lo;if(lo!=hi)target_error=add_checked(target_error,1,slot);
        }
        ball[3u*stride-1u]=target_error;
    }
    __syncthreads();if(*slot)return;
    bool contrasted=linked && meta[2]<(int64_t)at;
    // One kernel row per immutable input source and query. Reflected factors reuse the
    // reference row's weights rather than recomputing the same source pairing.
    for(uint32_t i=threadIdx.x;i<=at;i+=blockDim.x){
        const int64_t *entry=i==at?out:contextual_at(table,i);bool valid=entry[contextual_meta(n,targets)+1u]>=0;
        for(uint32_t q=0;q<4u;++q){
            int64_t *weight=weights+((size_t)i*4u+q)*4u;for(uint32_t j=0;j<4u;++j)weight[j]=0;
            if(!valid || (q>0 && !linked) || (q==3 && !contrasted))continue;
            if(q==2 && source_ordinal==(uint64_t)at-1u){for(uint32_t j=0;j<4u;++j)weight[j]=weights[((size_t)i*4u+1u)*4u+j];continue;}
            const int64_t *sv,*cv;contextual_query_parts(table,out,n,at,q,&sv,&cv,slot,targets);if(*slot)continue;
            const int64_t *si=entry+contextual_input_visible(n,targets),*ci=contextual_at(table,i-1u)+contextual_context(n,targets);
            uint32_t context_at=contextual_query_context(out,n,at,q,targets);
            const wide *bq=context_at==at?operative_b:contextual_b_at(table,context_at);
            uint32_t rem=0;wide k=contextual_kernel(si,ci,sv,cv,n,grain,version,&rem,slot,contextual_b_at(table,i-1u),bq);
            ((wide *)weight)[0]=k;weight[2]=rem;weight[3]=0;
        }
    }
    __syncthreads();if(*slot)return;
    for(uint32_t coordinate=threadIdx.x;coordinate<4u*R;coordinate+=blockDim.x){
        uint32_t q=coordinate/R,j=coordinate%R;HistoryInteger sum,pos,neg;
        if(q==0 || (linked && (q<3 || contrasted))){
            for(uint32_t i=0;i<at;++i){
                const int64_t *old=contextual_at(table,i),*m=old+contextual_meta(n,targets);if(m[1]<0)continue;
                const wide *b=(const wide *)(old+contextual_beta(n,targets));
                contextual_factor_add(history_integer(b[j])+history_integer(b[R+j]),weights+((size_t)i*4u+q)*4u,sum,pos,neg);
                if(m[2]<(int64_t)i)contextual_factor_add(-history_integer(b[R+j]),weights+((size_t)m[2]*4u+q)*4u,sum,pos,neg);
            }
        }
        int64_t *raw=evaluations+q*raw_stride;
        history_write_integer(sum,raw+5u*j,raw+5u*j,slot);
        history_write_integer(pos,raw+5u*(R+j),raw+5u*(R+j),slot);
        history_write_integer(neg,raw+5u*(2u*R+j),raw+5u*(2u*R+j),slot);
    }
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        const wide *old_bounds=(const wide *)(state+ga);wide et=old_bounds[0],nt=old_bounds[1];
        if(et<0 || nt<0)atomicOr(slot,REFUSED_MALFORMED);
        wide input_error=0,reference_error=0;
        if(linked && !*slot){
            const int64_t *si=out+contextual_input_visible(n,targets),*ci=contextual_at(table,at-1u)+contextual_context(n,targets);
            input_error=contextual_source_error(si,ci,n,grain,version,slot);extra[11]=input_error;
            wide rounds=0,eval=moment_read_evaluation(evaluations+raw_stride,R,grain,ball+stride,&rounds,slot);extra[5]=eval;
            ball[2u*stride-1u]=add_checked(et,add_checked(ft_ceil_product(nt,input_error,grain,slot),eval,slot),slot);
            rounds=0;wide ev2=moment_read_evaluation(evaluations+2u*raw_stride,R,grain,ball+7u*stride,&rounds,slot);
            wide old_error=contextual_source_error(original+contextual_output_visible(n,targets),original+contextual_context(n,targets),n,grain,version,slot);
            ball[8u*stride-1u]=add_checked(et,add_checked(ft_ceil_product(nt,old_error,grain,slot),ev2,slot),slot);
            const wide *produced=(const wide *)original;
            wide beta_rounds=0;
            for(uint32_t j=0;j<R;++j){
                ball[3u*stride+j]=sub_checked(ball[2u*stride+j],produced[j],slot);
                ball[4u*stride+j]=sub_checked(ball[7u*stride+j],produced[j],slot);
                ball[5u*stride+j]=sub_checked(ball[stride+j],ball[7u*stride+j],slot);
                wide residual=sub_checked(ball[2u*stride+j],ball[stride+j],slot);ball[6u*stride+j]=residual;
                abs_beta[j]=residual/2;if(residual%2)++beta_rounds;
            }
            ball[4u*stride-1u]=add_checked(ball[3u*stride-1u],produced[R],slot);
            ball[5u*stride-1u]=add_checked(ball[8u*stride-1u],produced[R],slot);
            ball[6u*stride-1u]=add_checked(ball[2u*stride-1u],ball[8u*stride-1u],slot);
            // The immediately preceding source has exactly the same operator and context
            // here. These are shared unknown values, not independent numerical balls.
            if(source_ordinal==(uint64_t)at-1u){ball[5u*stride-1u]=0;ball[6u*stride-1u]=0;}
            ball[7u*stride-1u]=add_checked(ball[3u*stride-1u],ball[2u*stride-1u],slot);
            extra[2]=S/2;extra[3]=0;
            // Half-grid beta truncation is bounded by ceil(number of half-grid residues/2).
            contextual_update_bounds(&et,&nt,ball+2u*stride,ball+stride,abs_beta,R,grain,ball[3u*stride-1u],eval,input_error,S,S,
                false,div_ceil(beta_rounds,2,slot),extra+4,slot);
            if(contrasted && !*slot){
                const int64_t *ref=contextual_at(table,(uint32_t)meta[2]);const wide *ref_ball=(const wide *)ref;
                reference_error=contextual_source_error(ref+contextual_input_visible(n,targets),contextual_at(table,(uint32_t)meta[2]-1u)+contextual_context(n,targets),n,grain,version,slot);
                int64_t *a=evaluations+raw_stride,*b=evaluations+3u*raw_stride;
                for(uint32_t j=0;j<R;++j){
                    HistoryInteger sum=history_read_integer(a+5u*j,slot)-history_read_integer(b+5u*j,slot);
                    HistoryInteger pos=history_read_integer(a+5u*(R+j),slot)+history_read_integer(b+5u*(2u*R+j),slot);
                    HistoryInteger neg=history_read_integer(a+5u*(2u*R+j),slot)+history_read_integer(b+5u*(R+j),slot);
                    contextual_factor_add(history_integer(abs_beta[j]),weights+((size_t)at*4u+1u)*4u,sum,pos,neg);
                    contextual_factor_add(-history_integer(abs_beta[j]),weights+((size_t)at*4u+3u)*4u,sum,pos,neg);
                    history_write_integer(sum,b+5u*j,b+5u*j,slot);history_write_integer(pos,b+5u*(R+j),b+5u*(R+j),slot);history_write_integer(neg,b+5u*(2u*R+j),b+5u*(2u*R+j),slot);
                    ball[8u*stride+j]=sub_checked(ball[2u*stride+j],ref_ball[2u*stride+j],slot);
                }
                ball[9u*stride-1u]=add_checked(ball[3u*stride-1u],ref_ball[3u*stride-1u],slot);
                rounds=0;wide deval=moment_read_evaluation(b,R,grain,ball+9u*stride,&rounds,slot);extra[9]=deval;
                wide de=add_checked(input_error,reference_error,slot);
                ball[10u*stride-1u]=add_checked(product_checked(2,et,slot),add_checked(ft_ceil_product(nt,de,grain,slot),deval,slot),slot);
                ball[11u*stride-1u]=add_checked(ball[9u*stride-1u],ball[10u*stride-1u],slot);
                MomentInteger num,den;
                if(version>=2u)contextual_context_pair(ci,contextual_b_at(table,at-1u),contextual_at(table,(uint32_t)meta[2]-1u)+contextual_context(n,targets),contextual_b_at(table,(uint32_t)meta[2]-1u),D,grain,version,num,den,slot);
                else contextual_pair(si,ci,ref+contextual_input_visible(n,targets),contextual_at(table,(uint32_t)meta[2]-1u)+contextual_context(n,targets),n,grain,num,den,slot);
                bool rem=false;wide gain=contextual_fraction(den,MomentInteger(3)*den-MomentInteger(2)*num,grain,&rem,slot);extra[6]=gain;extra[7]=rem;
                beta_rounds=0;
                for(uint32_t j=0;j<R;++j){wide residual=sub_checked(ball[8u*stride+j],ball[9u*stride+j],slot);ball[10u*stride+j]=residual;
                    ctx_beta[j]=ft_product(residual,gain,grain,&beta_rounds,slot);}
                wide k=((const wide *)(weights+((size_t)at*4u+3u)*4u))[0];
                contextual_update_bounds(&et,&nt,ball+8u*stride,ball+9u*stride,ctx_beta,R,grain,ball[9u*stride-1u],deval,de,2*S,2*(S-k),rem,beta_rounds,extra+8,slot);
            }
        }
        extra[0]=et;extra[1]=nt;
        ((wide *)(next+ga))[0]=((wide *)(next_hi+ga))[0]=et;((wide *)(next+ga))[1]=((wide *)(next_hi+ga))[1]=nt;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t j=threadIdx.x;j<R;j+=blockDim.x){
        int64_t *raw=evaluations;HistoryInteger sum=history_read_integer(raw+5u*j,slot),pos=history_read_integer(raw+5u*(R+j),slot),neg=history_read_integer(raw+5u*(2u*R+j),slot);
        if(linked){
            contextual_factor_add(history_integer(abs_beta[j])+history_integer(ctx_beta[j]),weights+(size_t)at*16u,sum,pos,neg);
            if(contrasted)contextual_factor_add(-history_integer(ctx_beta[j]),weights+(size_t)meta[2]*16u,sum,pos,neg);
        }
        raw=out+contextual_raw(n,targets);history_write_integer(sum,raw+5u*j,out_hi+contextual_raw(n,targets)+5u*j,slot);
        history_write_integer(pos,raw+5u*(R+j),out_hi+contextual_raw(n,targets)+5u*(R+j),slot);
        history_write_integer(neg,raw+5u*(2u*R+j),out_hi+contextual_raw(n,targets)+5u*(2u*R+j),slot);
    }
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        wide rounds=0,error=moment_read_evaluation(out+contextual_raw(n,targets),R,grain,ball,&rounds,slot);extra[10]=error;
        wide ex=contextual_source_error(out+contextual_output_visible(n,targets),out+contextual_context(n,targets),n,grain,version,slot);
        ball[R]=add_checked(extra[0],add_checked(ft_ceil_product(extra[1],ex,grain,slot),error,slot),slot);
        if(*slot)return;
        for(size_t i=0;i<contextual_extra(n,targets)+24u;++i)out_hi[i]=out[i];
    }
}
