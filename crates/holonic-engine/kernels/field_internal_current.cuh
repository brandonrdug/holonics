__device__ void internal_current_store(const wide *v,int64_t *lo,int64_t *hi) {
    wide *ol=(wide *)lo,*oh=(wide *)hi;
    for(uint32_t j=0;j<4;++j) ol[j]=oh[j]=v[j];
    lo[8]=hi[8]=lo[9]=hi[9]=0;lo[10]=hi[10]=1;lo[11]=hi[11]=v[2] ? 1 : 2;
    if(!v[2] && v[0]>=(wide)INT64_MIN && v[0]<=(wide)INT64_MAX && v[1]>=(wide)INT64_MIN
        && v[1]<=(wide)INT64_MAX && v[3]<=(wide)INT64_MAX) {
        lo[8]=hi[8]=(int64_t)v[0];lo[9]=hi[9]=(int64_t)v[1];
        lo[10]=hi[10]=(int64_t)v[3];lo[11]=hi[11]=0;
    }
}

// One actual contact's internal phase current. This is the existing prefix decoder:
// b_j(at)=(-1)^at d_j^* (P_at-P_before_j), from b'=d^*v-b and the alternating prefix.
// Contact coordinates are exact. Enclosed prefixes return a ball, never a selected centre.
extern "C" __global__ void section_field_internal_current(
    const int64_t *birth,const int64_t *source,const int64_t *incoming,
    const int64_t *birth_frame,const int64_t *source_frame,
    const int64_t *before,const int64_t *before_hi,const int64_t *now,const int64_t *now_hi,
    uint32_t nodes,uint32_t mode,uint32_t grain,uint64_t at,
    int64_t *contact_lo,int64_t *contact_hi,int64_t *out_lo,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x) return;
    if(upstream_refused(census,lineage,lineage_count,slot)) return;
    if(!nodes || nodes>UINT32_MAX/6u || (mode!=1 && mode!=2)
        || (mode==2 && (grain<1u || grain>120u))) { atomicOr(slot,REFUSED_MALFORMED);return; }
    uint32_t D=6u*nodes,stride=D+1u,words=(mode==1 ? 4u : 12u)*stride;
    for(uint32_t j=0;j<words;++j) if(before[j]!=before_hi[j] || now[j]!=now_hi[j]) {
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    extern __shared__ wide scratch[];
    wide *u=scratch,*d=u+D;wide ud,dd;
    if(!field_paired_build_faces(birth,source,incoming,birth_frame,source_frame,
        nodes,1,u,d,&ud,&dd,slot)) return;
    wide pd,real=0,imaginary=0,radius=0;
    if(mode==1) {
        wide a=now[3u*stride+D],b=before[3u*stride+D];
        if(a<=0 || b<=0) { atomicOr(slot,REFUSED_MALFORMED);return; }
        pd=fibre_lcm(a,b,slot);if(*slot) return;
        for(uint32_t j=0;j<D;++j) u[j]=sub_checked(
            product_checked(now[3u*stride+j],pd/a,slot),
            product_checked(before[3u*stride+j],pd/b,slot),slot);
    } else {
        const wide *a=(const wide *)now,*b=(const wide *)before;
        if(a[3u*stride+D]<0 || b[3u*stride+D]<0) { atomicOr(slot,REFUSED_MALFORMED);return; }
        pd=(wide)((uwide)1u<<grain);
        // The same immutable prefix denotes the same unknown exact value, not two independent
        // balls. Preserve that correlation when the shared-drive constructor asks P-P.
        wide error=before==now ? 0 : add_checked(a[3u*stride+D],b[3u*stride+D],slot),l1=0;
        for(uint32_t j=0;j<D;++j) {
            u[j]=sub_checked(a[3u*stride+j],b[3u*stride+j],slot);
            l1=add_checked(l1,of_magnitude(magnitude(d[j]),0,slot),slot);
        }
        radius=product_checked(l1,error,slot);
    }
    if(*slot) return;
    for(uint32_t j=0;j<D;j+=2) {
        real=add_checked(real,add_checked(product_checked(d[j],u[j],slot),
            product_checked(d[j+1],u[j+1],slot),slot),slot);
        imaginary=add_checked(imaginary,sub_checked(product_checked(d[j],u[j+1],slot),
            product_checked(d[j+1],u[j],slot),slot),slot);
    }
    if(at&1u) { real=sub_checked(0,real,slot);imaginary=sub_checked(0,imaginary,slot); }
    wide v[4]={real,imaginary,radius,product_checked(dd,pd,slot)};
    if(*slot) return;
    fibre_normalize(v,3,v+3,slot);if(*slot) return;
    wide *cl=(wide *)contact_lo,*ch=(wide *)contact_hi;
    for(uint32_t j=0;j<D;++j) cl[j]=ch[j]=d[j];cl[D]=ch[D]=dd;
    // The optional point port is guarded in its original return. Status 1 is a non-point
    // numerical enclosure, 2 an exact scalar outside the i64 current wire, 0 available.
    internal_current_store(v,out_lo,out_hi);
}

// Equality of the complete normalized rational root contacts. This proves equal forcing,
// not identity of the two occurrences. Their distinct lineage is retained by the mode owner.
extern "C" __global__ void section_internal_shared_drive(
    const int64_t *left,const int64_t *left_hi,const int64_t *right,const int64_t *right_hi,uint32_t words,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x) return;
    if(upstream_refused(census,lineage,lineage_count,slot)) return;
    for(uint32_t j=0;j<words;++j) if(left[j]!=left_hi[j] || right[j]!=right_hi[j] || left[j]!=right[j]) {
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
}

// Execute the descended generator word on ONE shared amplitude, with fixed numerical fibre.
// No original body, input waveform, prefix history, or per-step replay is needed.
extern "C" __global__ void section_internal_mode_unfold(
    const int64_t *origin,const int64_t *origin_hi,uint64_t steps,int64_t *lo,int64_t *hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x) return;
    if(upstream_refused(census,lineage,lineage_count,slot)) return;
    for(uint32_t j=0;j<12;++j) if(origin[j]!=origin_hi[j]) {atomicOr(slot,REFUSED_MALFORMED);return;}
    const wide *a=(const wide *)origin;
    if(a[2]<0 || a[3]<=0) {atomicOr(slot,REFUSED_MALFORMED);return;}
    wide v[4]={a[0],a[1],a[2],a[3]};
    if(steps&1u) {v[0]=sub_checked(0,v[0],slot);v[1]=sub_checked(0,v[1],slot);}
    if(*slot) return;
    internal_current_store(v,lo,hi);
}
