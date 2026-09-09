// Operative contact/current carriers inside the paired-field owner. These kernels write only
// fresh staging. They do not publish a field successor or choose a point from an enclosure.
// Maps are contact-major complex columns, b is the corresponding internal current. Packed wide
// centres share one dyadic grain; bounds are complete complex Frobenius/Euclidean radii.
__device__ wide operative_grid(HistoryInteger value,uint32_t grain,wide *rounds,uint32_t *slot){
    return history_narrow(complete_divide(value,complete_power(grain,slot),rounds,slot),slot);
}
__device__ void operative_copy_point(int64_t *lo,int64_t *hi,size_t words){
    for(size_t i=threadIdx.x;i<words;i+=blockDim.x)hi[i]=lo[i];
}
extern "C" __global__ void __launch_bounds__(512) section_field_operative_mount(
    const int64_t *table,const wide *current,uint32_t n,uint32_t count,uint32_t grain,uint64_t at,
    int64_t *map_lo,int64_t *map_hi,int64_t *b_lo,int64_t *b_hi,
    int64_t *bound_lo,int64_t *bound_hi,wide *scratch,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x)return;
    if(upstream_refused(census,lineage,lineage_count,slot))return;
    const uint32_t D=6u*n;const size_t stride=D+1u;
    if(!n || n>UINT32_MAX/6u || grain<1u || grain>120u || current[4u*stride-1u]<0){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
    wide S=(wide)((uwide)1u<<grain);
    wide *map=(wide *)map_lo,*b=(wide *)b_lo;
    for(uint32_t i=threadIdx.x;i<count;i+=blockDim.x){
        const int64_t *entry=table+7u*(size_t)i;wide *u=scratch+(size_t)i*(2u*D+4u),*d=u+D;
        const int64_t *query=(const int64_t *)(uintptr_t)entry[0],*origin=(const int64_t *)(uintptr_t)entry[1];
        const int64_t *incoming=(const int64_t *)(uintptr_t)entry[2],*frame=(const int64_t *)(uintptr_t)entry[3];
        const int64_t *old_frame=(const int64_t *)(uintptr_t)entry[4];
        const wide *before=(const wide *)(uintptr_t)entry[5];
        wide ud=1,dd=1,ed=0,round_b=0;
        if(entry[6]<1 || (uint64_t)entry[6]>at || before[4u*stride-1u]<0 || before[4u*stride-1u]>current[4u*stride-1u]){
            atomicOr(slot,REFUSED_MALFORMED);continue;
        }
        if(!field_paired_build_faces(query,origin,incoming,frame,old_frame,n,1,u,d,&ud,&dd,slot))continue;
        HistoryInteger dnorm,pnorm,re,im;
        for(uint32_t j=0;j<D;++j){
            wide value=history_narrow(complete_divide(history_integer(d[j])*history_integer(S),history_integer(dd),&ed,slot),slot);
            map[(size_t)i*D+j]=value;dnorm=dnorm+history_integer(value)*history_integer(value);
            u[j]=sub_checked(current[3u*stride+j],before[3u*stride+j],slot);
            pnorm=pnorm+history_integer(u[j])*history_integer(u[j]);
        }
        for(uint32_t j=0;j<D;j+=2u)history_complex_add_product(re,im,map[(size_t)i*D+j],map[(size_t)i*D+j+1u],u[j],u[j+1u],true);
        wide br=operative_grid(re,grain,&round_b,slot),bi=operative_grid(im,grain,&round_b,slot);
        b[2u*i]=(at&1u)?sub_checked(0,br,slot):br;b[2u*i+1u]=(at&1u)?sub_checked(0,bi,slot):bi;
        wide nd=history_norm_ceiling(dnorm,slot),np=history_norm_ceiling(pnorm,slot);
        wide ep=add_checked(current[4u*stride-1u],before[4u*stride-1u],slot);
        wide eb=add_checked(ft_ceil_product(add_checked(nd,ed,slot),ep,grain,slot),
            add_checked(ft_ceil_product(ed,np,grain,slot),round_b,slot),slot);
        u[2u*D]=ed;u[2u*D+1u]=eb;
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        HistoryInteger ed2,eb2;
        for(uint32_t i=0;i<count;++i){const wide *s=scratch+(size_t)i*(2u*D+4u);ed2=ed2+history_integer(s[2u*D])*history_integer(s[2u*D]);eb2=eb2+history_integer(s[2u*D+1u])*history_integer(s[2u*D+1u]);}
        ((wide *)bound_lo)[0]=history_norm_ceiling(ed2,slot);((wide *)bound_lo)[1]=history_norm_ceiling(eb2,slot);
        if(!count){for(uint32_t j=0;j<D;++j)map[j]=0;b[0]=b[1]=0;}
    }
    __syncthreads();if(*slot)return;
    operative_copy_point(map_lo,map_hi,2u*(size_t)(count?count:1u)*D);
    operative_copy_point(b_lo,b_hi,4u*(size_t)(count?count:1u));
    operative_copy_point(bound_lo,bound_hi,4);
}

// The supplied delta radius encloses the complete unrounded rank-two map, not just each
// separate factor. The native constitutive-return producer owes that bound and its carriers.
extern "C" __global__ void __launch_bounds__(512) section_field_operative_update(
    const int64_t *old_map,const int64_t *old_b,const int64_t *old_bounds,
    const int64_t *ports,const int64_t *currents,const int64_t *delta_b,const int64_t *delta_bounds,
    uint32_t D,uint32_t count,uint32_t factor_count,uint32_t grain,uint32_t exact_deposit,
    int64_t *map_lo,int64_t *map_hi,int64_t *b_lo,int64_t *b_hi,int64_t *bound_lo,int64_t *bound_hi,
    wide *rounds,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    const wide *a=(const wide *)old_map,*b=(const wide *)old_b,*p=(const wide *)ports,*r=(const wide *)currents;
    const wide *db=(const wide *)delta_b,*e=(const wide *)old_bounds,*de=(const wide *)delta_bounds;
    wide *out=(wide *)map_lo,*bout=(wide *)b_lo;
    if(!D || (D&1u) || factor_count>count || grain<1u || grain>120u || exact_deposit>1u || e[0]<0 || e[1]<0 || de[0]<0 || de[1]<0){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=threadIdx.x;i<count;i+=blockDim.x){
        wide omitted=0;
        for(uint32_t j=0;j<D;j+=2u){
            HistoryInteger re,im;
            if(i<factor_count)for(uint32_t f=0;f<2u;++f)
                history_complex_add_product(re,im,r[2u*((size_t)f*factor_count+i)],r[2u*((size_t)f*factor_count+i)+1u],p[(size_t)f*D+j],p[(size_t)f*D+j+1u],true);
            wide dr=operative_grid(re,grain,&omitted,slot),di=operative_grid(im,grain,&omitted,slot);
            out[(size_t)i*D+j]=add_checked(a[(size_t)i*D+j],dr,slot);
            out[(size_t)i*D+j+1u]=add_checked(a[(size_t)i*D+j+1u],di,slot);
        }
        bout[2u*i]=db?add_checked(b[2u*i],db[2u*i],slot):b[2u*i];bout[2u*i+1u]=db?add_checked(b[2u*i+1u],db[2u*i+1u],slot):b[2u*i+1u];rounds[i]=omitted;
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        wide omitted=0;for(uint32_t i=0;i<count;++i)omitted=add_checked(omitted,rounds[i],slot);
        // The exact-deposit chart defines the NEW coefficient by the finite projected product
        // above. Its unrounded-response defect is retained with the journal's factors/bounds;
        // it is not silently reinterpreted as uncertainty in the chosen numerical coefficient.
        // This changes no pre-existing map uncertainty and asserts no exact unrounded flow.
        ((wide *)bound_lo)[0]=exact_deposit?e[0]:add_checked(e[0],add_checked(de[0],omitted,slot),slot);
        ((wide *)bound_lo)[1]=add_checked(e[1],de[1],slot);
        if(!count){for(uint32_t j=0;j<D;++j)out[j]=0;bout[0]=bout[1]=0;}
    }
    __syncthreads();if(*slot)return;
    operative_copy_point(map_lo,map_hi,2u*(size_t)(count?count:1u)*D);
    operative_copy_point(b_lo,b_hi,4u*(size_t)(count?count:1u));operative_copy_point(bound_lo,bound_hi,4);
}

// Recomputed moments include every mixed term of simultaneous D,b changes. C is a complex
// port matrix; h=D b. The radii refer to these complete objects, not componentwise point seals.
__device__ void operative_moments_prepare(
    const int64_t *map_wire,const int64_t *b_wire,const int64_t *bounds,uint32_t D,uint32_t count,uint32_t grain,
    int64_t *c_lo,int64_t *c_hi,int64_t *h_lo,int64_t *h_hi,int64_t *out_bounds_lo,int64_t *out_bounds_hi,
    wide *rounds,uint32_t *slot
){
    const uint32_t m=D/2u;const wide *map=(const wide *)map_wire,*b=(const wide *)b_wire,*e=(const wide *)bounds;
    wide *C=(wide *)c_lo,*h=(wide *)h_lo;
    if(!D || (D&1u) || grain<1u || grain>120u || e[0]<0 || e[1]<0){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t ij=threadIdx.x;ij<(size_t)m*m+m;ij+=blockDim.x){
        HistoryInteger re,im;wide omitted=0;
        if(ij<(size_t)m*m){
            uint32_t i=ij/m,j=ij%m;
            for(uint32_t k=0;k<count;++k)history_complex_add_product(re,im,map[(size_t)k*D+2u*j],map[(size_t)k*D+2u*j+1u],map[(size_t)k*D+2u*i],map[(size_t)k*D+2u*i+1u],true);
            C[2u*ij]=operative_grid(re,grain,&omitted,slot);C[2u*ij+1u]=operative_grid(im,grain,&omitted,slot);
        }else{
            uint32_t i=ij-(size_t)m*m;
            for(uint32_t k=0;k<count;++k)history_complex_add_product(re,im,map[(size_t)k*D+2u*i],map[(size_t)k*D+2u*i+1u],b[2u*k],b[2u*k+1u],false);
            h[2u*i]=operative_grid(re,grain,&omitted,slot);h[2u*i+1u]=operative_grid(im,grain,&omitted,slot);
        }
        rounds[ij]=omitted;
    }
    __syncthreads();if(*slot)return;
    if(!threadIdx.x){
        HistoryInteger dn,bn;wide rc=0,rh=0;
        for(size_t i=0;i<(size_t)count*D;++i)dn=dn+history_integer(map[i])*history_integer(map[i]);
        for(size_t i=0;i<2u*(size_t)count;++i)bn=bn+history_integer(b[i])*history_integer(b[i]);
        wide nd=history_norm_ceiling(dn,slot),nb=history_norm_ceiling(bn,slot);
        for(size_t i=0;i<(size_t)m*m;++i)rc=add_checked(rc,rounds[i],slot);
        for(size_t i=(size_t)m*m;i<(size_t)m*m+m;++i)rh=add_checked(rh,rounds[i],slot);
        wide ec=add_checked(ft_ceil_product(add_checked(product_checked(2,nd,slot),e[0],slot),e[0],grain,slot),rc,slot);
        wide eh=add_checked(ft_ceil_product(nd,e[1],grain,slot),add_checked(ft_ceil_product(nb,e[0],grain,slot),ft_ceil_product(e[0],e[1],grain,slot),slot),slot);
        ((wide *)out_bounds_lo)[0]=ec;((wide *)out_bounds_lo)[1]=add_checked(eh,rh,slot);
        ((wide *)out_bounds_lo)[2]=nd;((wide *)out_bounds_lo)[3]=nb;
    }
    __syncthreads();if(*slot)return;
    operative_copy_point(c_lo,c_hi,4u*(size_t)m*m);operative_copy_point(h_lo,h_hi,2u*D);operative_copy_point(out_bounds_lo,out_bounds_hi,8);
}
extern "C" __global__ void __launch_bounds__(512) section_field_operative_moments(
    const int64_t *map_wire,const int64_t *b_wire,const int64_t *bounds,uint32_t D,uint32_t count,uint32_t grain,
    int64_t *c_lo,int64_t *c_hi,int64_t *h_lo,int64_t *h_hi,int64_t *out_bounds_lo,int64_t *out_bounds_hi,
    wide *rounds,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
    if(blockIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
    operative_moments_prepare(map_wire,b_wire,bounds,D,count,grain,c_lo,c_hi,h_lo,h_hi,out_bounds_lo,out_bounds_hi,rounds,slot);
}
