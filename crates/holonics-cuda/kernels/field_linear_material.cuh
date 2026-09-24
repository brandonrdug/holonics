// Finite complex-current operator; shared by the legacy and operative source charts.
__device__ __forceinline__ void field_material_transport_prepare(
    const wide *state, const wide *origin_current, const wide *origin_forward,
    const wide *current, const int64_t *incoming, uint32_t nodes, uint32_t linked, uint32_t grain,
    wide *delta_lo, wide *delta_hi, wide *report_lo, wide *report_hi, uint32_t *slot,
    uint32_t targets=0,uint32_t target_factor_width=0
) {
    if(!targets)targets=nodes;
    if (!state || !current || !incoming || !delta_lo || !delta_hi || !report_lo || !report_hi
        || !nodes || grain < 1u || grain > 120u || linked > 1u
        || (linked && (!origin_current || !origin_forward))) {
        atomicOr(slot, REFUSED_MALFORMED); return;
    }
    const uint32_t sources = 3u * nodes, source_real = 6u * nodes, target_real = 2u * targets;
    const size_t coefficients = (size_t)target_real * sources;
    const size_t target_stride = (size_t)target_real + 1u;
    const size_t gain_at = 6u * target_stride;
    const size_t extra_at = gain_at + source_real + 1u;
    const size_t report_values = extra_at + 5u;
    const size_t junction_stride = (size_t)source_real + 1u;
    const wide scale = (wide)1 << grain;
    for (size_t i = 0; i < report_values; ++i) report_lo[i] = report_hi[i] = 0;
    for (size_t i = 0; i <= coefficients; ++i) delta_lo[i] = delta_hi[i] = 0;
    wide old_l1 = 0;
    for (size_t i = 0; i < coefficients; ++i) old_l1 = add_checked(old_l1, ft_abs(state[i], slot), slot);
    wide error = state[coefficients];
    if (error < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
    wide *observed = report_lo + 2u * target_stride;
    wide observed_error = 0, observed_l1 = 0;
    if(target_factor_width) {
        contextual_tensor_target(incoming,nodes,target_factor_width,targets,grain,observed,&observed_error,slot);
        for(uint32_t i=0;i<target_real;++i)observed_l1=add_checked(observed_l1,ft_abs(observed[i],slot),slot);
    } else {
    for (uint32_t i = 0; i < target_real; ++i) {
        const int64_t *value = incoming + 3u * (i / 2u);
        if (value[2] <= 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
        wide floor = signed_product_divide_2((wide)value[i % 2u], scale / 2, (wide)value[2], 0, slot);
        wide ceil = signed_product_divide_2((wide)value[i % 2u], scale / 2, (wide)value[2], 1, slot);
        observed[i] = value[i % 2u] < 0 ? ceil : floor;
        if (floor != ceil) observed_error = add_checked(observed_error, 1, slot);
        observed_l1 = add_checked(observed_l1, ft_abs(observed[i], slot), slot);
    }
    }
    observed[target_real] = observed_error;
    if (*slot) return;
    if (linked) {
        const wide *source = origin_current + junction_stride;
        const wide source_error = source[source_real];
        if (source_error < 0 || origin_forward[target_real] < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
        wide *present = report_lo + target_stride;
        wide source_rounds = ft_prediction(state, nullptr, source, targets, sources, grain, present, slot);
        wide present_error = ft_prediction_error(error, old_l1, source, source_real,
            source_error, source_rounds, grain, slot);
        present[target_real] = present_error;
        report_lo[extra_at + 3u] = source_rounds;
        wide *returned = report_lo + 3u * target_stride;
        wide *chronology = report_lo + 4u * target_stride;
        wide *difference = report_lo + 5u * target_stride;
        wide difference_l1 = 0;
        for (uint32_t i = 0; i < target_real; ++i) {
            returned[i] = sub_checked(observed[i], origin_forward[i], slot);
            chronology[i] = sub_checked(present[i], origin_forward[i], slot);
            difference[i] = sub_checked(observed[i], present[i], slot);
            difference_l1 = add_checked(difference_l1, ft_abs(difference[i], slot), slot);
        }
        returned[target_real] = add_checked(observed_error, origin_forward[target_real], slot);
        chronology[target_real] = add_checked(present_error, origin_forward[target_real], slot);
        difference[target_real] = add_checked(observed_error, present_error, slot);
        wide denominator = scale, denominator_rounds = 0;
        for (uint32_t i = 0; i < source_real; ++i) {
            wide floor = product_shift(source[i], source[i], (int)grain, 0, slot);
            wide ceil = product_shift(source[i], source[i], (int)grain, 1, slot);
            denominator = add_checked(denominator, ceil, slot);
            if (floor != ceil) denominator_rounds = add_checked(denominator_rounds, 1, slot);
        }
        if (*slot) return;
        wide *gain = report_lo + gain_at;
        wide gain_error = div_ceil(denominator_rounds, 2, slot);
        for (uint32_t i = 0; i < source_real; ++i) {
            wide value = i & 1u ? -source[i] : source[i];
            wide floor = signed_product_divide_2(value, scale / 2, denominator, 0, slot);
            wide ceil = signed_product_divide_2(value, scale / 2, denominator, 1, slot);
            gain[i] = value < 0 ? ceil : floor;
            if (floor != ceil) gain_error = add_checked(gain_error, 1, slot);
        }
        gain[source_real] = gain_error;
        wide delta_rounds = 0;
        for (uint32_t row = 0; row < targets; ++row) for (uint32_t column = 0; column < sources; ++column) {
            size_t at = 2u * ((size_t)row * sources + column);
            ft_complex_product(difference[2u * row], difference[2u * row + 1u],
                gain[2u * column], gain[2u * column + 1u], grain,
                delta_lo + at, delta_lo + at + 1u, &delta_rounds, slot);
            add_checked(state[at], delta_lo[at], slot);
            add_checked(state[at + 1u], delta_lo[at + 1u], slot);
        }
        wide rounding = add_checked(div_ceil(source_rounds, 2, slot),
            add_checked(ft_ceil_product(difference_l1, gain_error, grain, slot), delta_rounds, slot), slot);
        // F(T,x,y) is nonexpansive in T. The complete graph-projector source variation is
        // bounded by ||x-xhat||; the L1 norms below are conservative Frobenius/Euclidean bounds.
        error = add_checked(error, add_checked(
            ft_ceil_product(add_checked(old_l1, observed_l1, slot), source_error, grain, slot),
            add_checked(div_ceil(observed_error, 2, slot), rounding, slot), slot), slot);
        report_lo[extra_at + 1u] = denominator;
        report_lo[extra_at + 2u] = rounding;
    }
    if (*slot) return;
    wide new_l1 = 0;
    for (size_t i = 0; i < coefficients; ++i)
        new_l1 = add_checked(new_l1, ft_abs(add_checked(state[i], delta_lo[i], slot), slot), slot);
    const wide *new_source = current + junction_stride;
    if (new_source[source_real] < 0) { atomicOr(slot, REFUSED_MALFORMED); return; }
    wide new_rounds = ft_prediction(state, delta_lo, new_source, targets, sources, grain, report_lo, slot);
    report_lo[target_real] = ft_prediction_error(error, new_l1, new_source, source_real,
        new_source[source_real], new_rounds, grain, slot);
    report_lo[extra_at] = delta_lo[coefficients] = error;
    report_lo[extra_at + 4u] = new_rounds;
    if (*slot) return;
    for (size_t i = 0; i < report_values; ++i) report_hi[i] = report_lo[i];
    for (size_t i = 0; i <= coefficients; ++i) delta_hi[i] = delta_lo[i];
}

__device__ wide linear_material_row(const wide *state,const wide *delta,const wide *source,
    uint32_t row,uint32_t sources,uint32_t grain,wide *out,uint32_t *slot){
    wide real=0,imaginary=0,rounds=0;
    for(uint32_t column=0;column<sources;++column){
        size_t at=2u*((size_t)row*sources+column);wide ar=state[at],ai=state[at+1u];
        if(delta){ar=add_checked(ar,delta[at],slot);ai=add_checked(ai,delta[at+1u],slot);}
        wide pr,pi;ft_complex_product(ar,ai,source[2u*column],source[2u*column+1u],grain,&pr,&pi,&rounds,slot);
        real=add_checked(real,pr,slot);imaginary=add_checked(imaginary,pi,slot);
    }
    out[2u*row]=real;out[2u*row+1u]=imaginary;return rounds;
}
// Independent matrix rows keep their original column order. Shared error totals are
// reduced between barriers; no continuing state is written by this preparation.
__device__ void field_linear_material_parallel(
    const wide *state,const wide *origin_current,const wide *origin_forward,const wide *current,
    const int64_t *incoming,uint32_t nodes,uint32_t linked,uint32_t grain,
    wide *delta_lo,wide *delta_hi,wide *report_lo,wide *report_hi,uint32_t *slot,
    uint32_t targets,uint32_t factor_width
){
    uint32_t sources=3u*nodes,R=2u*targets;size_t coefficients=(size_t)R*sources,stride=R+1u;
    size_t gain_at=6u*stride,extra=gain_at+2u*sources+1u,words=extra+5u,js=2u*sources+1u;
    wide S=(wide)1<<grain;
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)report_lo[j]=report_hi[j]=0;
    for(size_t j=threadIdx.x;j<=coefficients;j+=blockDim.x)delta_lo[j]=delta_hi[j]=0;
    __syncthreads();
    if(threadIdx.x==0){
        if(!nodes || !targets || grain<1 || grain>120 || linked>1 || state[coefficients]<0 || (linked&&(!origin_current||!origin_forward)))atomicOr(slot,REFUSED_MALFORMED);
        wide *observed=report_lo+2u*stride,err=0,l1=0;
        if(!*slot && factor_width)contextual_tensor_target(incoming,nodes,factor_width,targets,grain,observed,&err,slot);
        else if(!*slot)for(uint32_t j=0;j<R;++j){
            const int64_t *v=incoming+3u*(j/2u);if(v[2]<=0){atomicOr(slot,REFUSED_MALFORMED);break;}
            wide lo=signed_product_divide_2(v[j%2u],S/2,v[2],0,slot),hi=signed_product_divide_2(v[j%2u],S/2,v[2],1,slot);
            observed[j]=v[j%2u]<0?hi:lo;if(lo!=hi)err=add_checked(err,1,slot);
        }
        for(uint32_t j=0;j<R;++j)l1=add_checked(l1,ft_abs(observed[j],slot),slot);
        observed[R]=err;report_lo[extra+2u]=l1;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        wide l1=0;for(uint32_t j=0;j<2u*sources;++j)l1=add_checked(l1,ft_abs(state[(size_t)row*2u*sources+j],slot),slot);
        report_lo[2u*row]=l1;report_lo[2u*row+1u]=linked?linear_material_row(state,nullptr,origin_current+js,row,sources,grain,report_lo+stride,slot):0;
    }
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        wide old_l1=0,rounds=0;for(uint32_t row=0;row<targets;++row){old_l1=add_checked(old_l1,report_lo[2u*row],slot);rounds=add_checked(rounds,report_lo[2u*row+1u],slot);}
        report_lo[extra]=old_l1;report_lo[extra+3u]=rounds;
        if(linked){
            const wide *source=origin_current+js;wide source_error=source[2u*sources],old_error=origin_forward[R];
            if(source_error<0 || old_error<0){atomicOr(slot,REFUSED_MALFORMED);}
            wide present_error=ft_prediction_error(state[coefficients],old_l1,source,2u*sources,source_error,rounds,grain,slot);
            report_lo[2u*stride-1u]=present_error;
            for(uint32_t j=0;j<R;++j){
                report_lo[3u*stride+j]=sub_checked(report_lo[2u*stride+j],origin_forward[j],slot);
                report_lo[4u*stride+j]=sub_checked(report_lo[stride+j],origin_forward[j],slot);
                report_lo[5u*stride+j]=sub_checked(report_lo[2u*stride+j],report_lo[stride+j],slot);
            }
            wide observed_error=report_lo[3u*stride-1u];
            report_lo[4u*stride-1u]=add_checked(observed_error,old_error,slot);
            report_lo[5u*stride-1u]=add_checked(present_error,old_error,slot);
            report_lo[6u*stride-1u]=add_checked(observed_error,present_error,slot);
            wide den=S,den_rounds=0;
            for(uint32_t j=0;j<2u*sources;++j){wide a=product_shift(source[j],source[j],grain,0,slot),b=product_shift(source[j],source[j],grain,1,slot);den=add_checked(den,b,slot);if(a!=b)den_rounds=add_checked(den_rounds,1,slot);}
            wide ge=div_ceil(den_rounds,2,slot);
            for(uint32_t j=0;j<2u*sources;++j){wide v=j&1u?-source[j]:source[j];wide a=signed_product_divide_2(v,S/2,den,0,slot),b=signed_product_divide_2(v,S/2,den,1,slot);report_lo[gain_at+j]=v<0?b:a;if(a!=b)ge=add_checked(ge,1,slot);}
            report_lo[gain_at+2u*sources]=ge;report_lo[extra+1u]=den;
        }
    }
    __syncthreads();if(*slot)return;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x){
        wide rounds=0,l1=0;
        for(uint32_t column=0;column<sources;++column){
            size_t at=2u*((size_t)row*sources+column);
            if(linked)ft_complex_product(report_lo[5u*stride+2u*row],report_lo[5u*stride+2u*row+1u],report_lo[gain_at+2u*column],report_lo[gain_at+2u*column+1u],grain,delta_lo+at,delta_lo+at+1u,&rounds,slot);
            l1=add_checked(l1,ft_abs(add_checked(state[at],delta_lo[at],slot),slot),slot);
            l1=add_checked(l1,ft_abs(add_checked(state[at+1u],delta_lo[at+1u],slot),slot),slot);
        }
        report_lo[2u*row]=rounds;report_lo[2u*row+1u]=l1;
    }
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        wide rounds=0,new_l1=0;for(uint32_t row=0;row<targets;++row){rounds=add_checked(rounds,report_lo[2u*row],slot);new_l1=add_checked(new_l1,report_lo[2u*row+1u],slot);}
        wide error=state[coefficients];
        if(linked){
            wide residual_l1=0;for(uint32_t j=0;j<R;++j)residual_l1=add_checked(residual_l1,ft_abs(report_lo[5u*stride+j],slot),slot);
            wide rounding=add_checked(div_ceil(report_lo[extra+3u],2,slot),add_checked(ft_ceil_product(residual_l1,report_lo[gain_at+2u*sources],grain,slot),rounds,slot),slot);
            error=add_checked(error,add_checked(ft_ceil_product(add_checked(report_lo[extra],report_lo[extra+2u],slot),origin_current[js+2u*sources],grain,slot),add_checked(div_ceil(report_lo[3u*stride-1u],2,slot),rounding,slot),slot),slot);
            report_lo[extra+2u]=rounding;
        }else report_lo[extra+2u]=0;
        report_lo[extra]=error;report_lo[extra+4u]=new_l1;
    }
    __syncthreads();if(*slot)return;
    for(uint32_t row=threadIdx.x;row<targets;row+=blockDim.x)
        delta_hi[row]=linear_material_row(state,delta_lo,current+js,row,sources,grain,report_lo,slot);
    __syncthreads();if(*slot)return;
    if(threadIdx.x==0){
        wide rounds=0;for(uint32_t row=0;row<targets;++row)rounds=add_checked(rounds,delta_hi[row],slot);
        if(current[js+2u*sources]<0){atomicOr(slot,REFUSED_MALFORMED);}
        report_lo[R]=ft_prediction_error(report_lo[extra],report_lo[extra+4u],current+js,2u*sources,current[js+2u*sources],rounds,grain,slot);
        report_lo[extra+4u]=rounds;delta_lo[coefficients]=report_lo[extra];
    }
    __syncthreads();if(*slot)return;
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)report_hi[j]=report_lo[j];
    for(size_t j=threadIdx.x;j<=coefficients;j+=blockDim.x)delta_hi[j]=delta_lo[j];
}
