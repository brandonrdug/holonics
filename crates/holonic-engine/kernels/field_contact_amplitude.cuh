// Positive point amplitudes and reconstruction from one fixed pair template.
// The current parameter is a sufficient state; this operation appends no update history.
__device__ bool amplitude_bound_ok(uwide total, uint32_t grain, uint32_t k) {
    const uint32_t bit = grain + k - 1u;
    return bit >= 128u || total <= (((uwide)1) << bit);
}
__device__ wide amplitude_trunc_shift(wide x, uint32_t k, uint32_t *status) {
    return k >= 128u ? 0 : of_magnitude(magnitude(x) >> k, x < 0, status);
}
__device__ wide amplitude_ceil_shift(wide x, uint32_t k, uint32_t *status) {
    if (x < 0) { atomicOr(status,REFUSED_MALFORMED); return 0; }
    if (k >= 128u) return x != 0;
    const uwide a=(uwide)x, q=a>>k;
    const bool remainder=k && (a & ((((uwide)1)<<k)-1u));
    return of_magnitude(q + remainder, false, status);
}
extern "C" __global__ void section_field_contact_amplitude_proposal(
    const int64_t *gradient,const int64_t *gradient_hi,
    const int64_t *rho,const int64_t *rho_hi,
    uint32_t groups,uint32_t requested_step_bits,uint32_t grain,
    int64_t *amplitude,int64_t *amplitude_hi,
    int64_t *steps,int64_t *steps_hi,
    int64_t *reference,int64_t *reference_hi,int64_t *flags,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
    uint32_t row=blockIdx.x;
    if(threadIdx.x || row>=groups)return;
    uint32_t *status=ec_status(flags,row);
    if(upstream_refused(census,lineage,lineage_count,status))return;
    if(grain<1u || grain>120u || requested_step_bits>128u){atomicOr(status,REFUSED_MALFORMED);return;}
    size_t o=6u*(size_t)row;
    for(uint32_t i=0;i<6u;++i)
        if(gradient[o+i]!=gradient_hi[o+i] || rho[o+i]!=rho_hi[o+i]){atomicOr(status,REFUSED_MALFORMED);return;}
    const wide *g=(const wide*)(gradient+o), *old=(const wide*)(rho+o);
    if(g[1] || g[2]<0 || old[0]<=0 || old[1] || old[2]){atomicOr(status,REFUSED_MALFORMED);return;}
    // Each magnitude fits 2^127; their sum fits UNSIGNED 128 bits, even when g is MIN.
    uwide total=magnitude(g[0])+(uwide)g[2];
    uint32_t k=requested_step_bits;
    while(k<128u && !amplitude_bound_ok(total,grain,k))++k;
    const wide unit=((wide)1)<<grain;
    wide delta=amplitude_trunc_shift(g[0],k,status);
    wide alpha=add_checked(unit,delta,status);
    if(alpha<(unit>>1)){atomicOr(status,REFUSED_MALFORMED);return;}
    // The selected parameter is the upward dyadic projection of the positive proposal.
    // Thus even a one-word positive amplitude cannot round down to zero.
    wide next=ft_ceil_product(alpha,old[0],grain,status);
    if(next<=0){atomicOr(status,REFUSED_MALFORMED);return;}
    wide *a=(wide*)(amplitude+o);a[0]=next;a[1]=0;a[2]=0;
    ec_seal(amplitude+o,amplitude_hi+o,2u,status);
    ((wide*)steps)[row]=(wide)k;
    ec_seal(steps+2u*(size_t)row,steps_hi+2u*(size_t)row,0u,status);
    if(reference){
        // Unrounded alpha uses the true gradient in its source ball. Separate this
        // reference error from the exact chosen active rho point.
        const bool truncation=k>=128u ? g[0]!=0 : k && (magnitude(g[0]) & ((((uwide)1)<<k)-1u));
        wide alpha_error=add_checked(amplitude_ceil_shift(g[2],k,status),truncation,status);
        wide r=add_checked(ft_ceil_product(old[0],alpha_error,grain,status),1,status);
        wide *p=(wide*)(reference+o);p[0]=next;p[1]=0;p[2]=r;
        ec_seal(reference+o,reference_hi+o,2u,status);
    }
}
// One block owns one row of the selected CSR chart. Both charts use the contact-row
// amplitude; a transpose row is a boundary coordinate and is NOT a contact group.
extern "C" __global__ void section_field_contact_amplitude_rebuild(
    const int64_t *offsets,const int64_t *offsets_hi,
    const int64_t *indices,const int64_t *indices_hi,
    const int64_t *values,const int64_t *values_hi,
    const int64_t *t_offsets,const int64_t *t_offsets_hi,
    const int64_t *t_rows,const int64_t *t_rows_hi,
    const int64_t *t_values,const int64_t *t_values_hi,
    const int64_t *amplitude,const int64_t *amplitude_hi,
    uint32_t rows,uint32_t boundary_channels,uint32_t nnz,uint32_t group_width,uint32_t grain,
    uint32_t transpose,int64_t *out,int64_t *out_hi,
    int64_t *rounding,int64_t *rounding_hi,int64_t *flags,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count) {
    uint32_t row=blockIdx.x, population=transpose?boundary_channels:rows;
    if(threadIdx.x || row>=population)return;
    uint32_t *status=ec_status(flags,row);
    if(upstream_refused(census,lineage,lineage_count,status))return;
    if(!rows || !boundary_channels || !group_width || rows%group_width || grain<1u || grain>120u){atomicOr(status,REFUSED_MALFORMED);return;}
    const int64_t *off=transpose?t_offsets:offsets,*oh=transpose?t_offsets_hi:offsets_hi;
    const int64_t *idx=transpose?t_rows:indices,*ih=transpose?t_rows_hi:indices_hi;
    const int64_t *v=transpose?t_values:values,*vh=transpose?t_values_hi:values_hi;
    size_t start=2u*(size_t)row;
    for(uint32_t i=0;i<4u;++i)if(off[start+i]!=oh[start+i]){atomicOr(status,REFUSED_MALFORMED);return;}
    if(off[start]<0 || off[start+1u] || off[start+3u] || off[start+2u]<off[start] || (uint64_t)off[start+2u]>nnz){atomicOr(status,REFUSED_MALFORMED);return;}
    if(row==0 && off[start]!=0){atomicOr(status,REFUSED_MALFORMED);return;}
    if(row+1u==population && (uint64_t)off[start+2u]!=nnz){atomicOr(status,REFUSED_MALFORMED);return;}
    wide error=0;
    for(uint32_t at=(uint32_t)off[start];at<(uint32_t)off[start+2u];++at){
        size_t ip=2u*(size_t)at;
        if(idx[ip]!=ih[ip] || idx[ip+1u]!=ih[ip+1u] || idx[ip]<0 || idx[ip+1u]){atomicOr(status,REFUSED_MALFORMED);return;}
        if(transpose ? (uint64_t)idx[ip]>=rows : ((idx[ip]&1) || (uint64_t)idx[ip]/2u>=boundary_channels)){atomicOr(status,REFUSED_MALFORMED);return;}
        uint32_t contact=transpose?(uint32_t)idx[ip]:row;
        size_t ap=6u*(size_t)(contact/group_width);
        for(uint32_t i=0;i<6u;++i)if(amplitude[ap+i]!=amplitude_hi[ap+i]){atomicOr(status,REFUSED_MALFORMED);return;}
        const wide *a=(const wide*)(amplitude+ap);
        if(a[0]<=0 || a[1] || a[2]){atomicOr(status,REFUSED_MALFORMED);return;}
        size_t vp=4u*(size_t)at;
        for(uint32_t i=0;i<4u;++i)if(v[vp+i]!=vh[vp+i]){atomicOr(status,REFUSED_MALFORMED);return;}
        const wide *basis=(const wide*)(v+vp);wide *dest=(wide*)(out+vp);
        for(uint32_t component=0;component<2u;++component){
            MaterialInterval x=mp_mul(mp_point(a[0]),mp_point(basis[component]),grain,status);
            dest[component]=x.lo;
            error=add_checked(error,x.lo!=x.hi,status);
        }
        for(uint32_t i=0;i<4u;++i)out_hi[vp+i]=out[vp+i];
    }
    if(!nnz && row==0)for(uint32_t i=0;i<4u;++i){out[i]=0;out_hi[i]=0;}
    ((wide*)rounding)[row]=error;
    ec_seal(rounding+2u*(size_t)row,rounding_hi+2u*(size_t)row,0u,status);
}
extern "C" __global__ void section_field_contact_amplitude_bounds(
    const int64_t *rho,const int64_t *rho_hi,
    const int64_t *rounding,const int64_t *rounding_hi,
    const int64_t *basis_bounds,const int64_t *basis_bounds_hi,
    const int64_t *current_bounds,const int64_t *current_bounds_hi,
    uint32_t groups,uint32_t rows,uint32_t grain,
    int64_t *out,int64_t *out_hi,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x || threadIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    if(!groups || !rows || grain<1u || grain>120u){atomicOr(slot,REFUSED_MALFORMED);return;}
    wide largest=0,error=0;
    for(uint32_t row=0;row<groups;++row){
        size_t p=6u*(size_t)row;
        for(uint32_t i=0;i<6u;++i)if(rho[p+i]!=rho_hi[p+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
        const wide *a=(const wide*)(rho+p);
        if(a[0]<=0 || a[1] || a[2]){atomicOr(slot,REFUSED_MALFORMED);return;}
        if(a[0]>largest)largest=a[0];
    }
    for(uint32_t row=0;row<rows;++row){
        size_t p=2u*(size_t)row;
        if(rounding[p]!=rounding_hi[p] || rounding[p+1u]!=rounding_hi[p+1u] || ((const wide*)rounding)[row]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
        error=add_checked(error,((const wide*)rounding)[row],slot);
    }
    for(uint32_t i=0;i<4u;++i)if(basis_bounds[i]!=basis_bounds_hi[i] || current_bounds[i]!=current_bounds_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *base=(const wide*)basis_bounds,*current=(const wide*)current_bounds;
    if(base[0]<0 || base[1]<0 || current[0]<0 || current[1]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    ((wide*)out)[0]=add_checked(ft_ceil_product(largest,base[0],grain,slot),error,slot);
    ((wide*)out)[1]=current[1];
    for(uint32_t i=0;i<4u;++i)out_hi[i]=out[i];
}
