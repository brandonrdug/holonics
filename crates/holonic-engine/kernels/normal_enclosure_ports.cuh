// GPU receivers for contiguous complex-coordinate blocks and same-shape addition.
// Operands remain wide paired-int64 carriers throughout; no host numerical readout is used.
extern "C" __global__ void section_normal_enclosure_sum(
    const int64_t *left,const int64_t *left_hi,uint32_t la,
    const int64_t *right,const int64_t *right_hi,uint32_t ra,uint32_t width,
    int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
    const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!width||(width&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(size_t i=0;i<2u*((size_t)width+1u);++i){
        if(left[la+i]!=left_hi[la+i]||right[ra+i]!=right_hi[ra+i]){
            atomicOr(slot,REFUSED_MALFORMED);return;
        }
    }
    const wide *a=(const wide *)(left+la),*b=(const wide *)(right+ra); wide *y=(wide *)out;
    if(a[width]<0||b[width]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
    for(uint32_t i=0;i<width;++i)y[i]=add_checked(a[i],b[i],slot);
    y[width]=add_checked(a[width],b[width],slot);
    if(*slot)return;
    for(size_t i=0;i<2u*((size_t)width+1u);++i)out_hi[i]=out[i];
}

// Convert every point row in one resident section into a complete enclosure in one passage.
// Rational denominators stay in the source row; direct_normal_source_ball performs the same
// outward arithmetic and malformed-point checks as the single-row receiver.
extern "C" __global__ void section_normal_enclosure_section(
    const int64_t *source,const int64_t *source_hi,uint32_t xstride,uint32_t xrational,
    uint32_t rows,uint32_t width,uint32_t grain,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!rows||!width||(width&1u)||grain<1||grain>120){atomicOr(slot,REFUSED_MALFORMED);return;}
    const size_t stride=2u*((size_t)width+1u),words=stride*rows;
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)out[j]=0;
    __syncthreads();
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            const uint32_t at=row*xstride;
            direct_normal_source_ball(source,source_hi,at,
                xrational?at+width:UINT32_MAX,UINT32_MAX,0,width,grain,
                (wide *)(out+row*stride),slot);
        }
        __syncthreads();if(*slot)return;
    }
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)out_hi[j]=out[j];
}

extern "C" __global__ void section_normal_enclosure_sum_section(
    const int64_t *left,const int64_t *left_hi,uint32_t la,
    const int64_t *right,const int64_t *right_hi,uint32_t ra,
    uint32_t left_stride,uint32_t right_stride,uint32_t rows,uint32_t width,
    int64_t *out,int64_t *out_hi,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!rows||!width||(width&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
    const size_t stride=2u*((size_t)width+1u),words=stride*rows;
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)out[j]=0;
    __syncthreads();
    for(uint32_t row=0;row<rows;++row){
        if(!threadIdx.x){
            const size_t left_at=(size_t)la+(size_t)row*left_stride;
            const size_t right_at=(size_t)ra+(size_t)row*right_stride;
            const size_t out_at=(size_t)row*stride;
            for(size_t j=0;j<stride;++j)
                if(left[left_at+j]!=left_hi[left_at+j]||right[right_at+j]!=right_hi[right_at+j]){atomicOr(slot,REFUSED_MALFORMED);break;}
            if(!*slot){
                const wide *a=(const wide *)(left+left_at),*b=(const wide *)(right+right_at);wide *y=(wide *)(out+out_at);
                if(a[width]<0||b[width]<0)atomicOr(slot,REFUSED_MALFORMED);
                if(!*slot){
                    for(uint32_t j=0;j<width;++j)y[j]=add_checked(a[j],b[j],slot);
                    y[width]=add_checked(a[width],b[width],slot);
                }
            }
        }
        __syncthreads();if(*slot)return;
    }
    for(size_t j=threadIdx.x;j<words;j+=blockDim.x)out_hi[j]=out[j];
}

// Demand-driven variant of flattening. Each input row is scattered to one declared destination
// row; unassigned destination rows remain zero. The final radius is the sum of participating
// source radii, so the compact face remains conservative for the whole selected family.
extern "C" __global__ void section_normal_enclosure_scatter_section(
    const int64_t *source,const int64_t *source_hi,uint32_t source_offset,uint32_t source_width,uint32_t source_rows,
    uint32_t start,uint32_t count,const int64_t *dest,const int64_t *dest_hi,uint32_t dest_count,
    uint32_t output_rows,int64_t *out,int64_t *out_hi,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!source_rows||!source_width||!count||dest_count!=source_rows||!output_rows||
       (source_width&1u)||(start&1u)||(count&1u)||(uint64_t)start+count>source_width){
        atomicOr(slot,REFUSED_MALFORMED);return;
    }
    const size_t source_stride=2u*((size_t)source_width+1u),out_width=(size_t)output_rows*count;
    const size_t out_stride=2u*(out_width+1u);
    if(!threadIdx.x){
        wide *y=(wide *)out;wide radius=0;
        for(size_t j=0;j<out_stride;++j){out[j]=0;out_hi[j]=0;}
        for(uint32_t row=0;row<source_rows;++row){
            const size_t source_at=(size_t)source_offset+(size_t)row*source_stride;
            const wide *x=(const wide *)(source+source_at);
            const int64_t *xl=source+source_at,*xh=source_hi+source_at;
            for(size_t j=0;j<source_stride;++j)
                if(xl[j]!=xh[j]){atomicOr(slot,REFUSED_MALFORMED);return;}
            const int64_t *d=dest,*dl=dest,*dh=dest_hi;
            if(dl[row]!=dh[row]||d[row]<0||d[row]>=(int64_t)output_rows||x[source_width]<0){
                atomicOr(slot,REFUSED_MALFORMED);return;
            }
            const size_t destination=(size_t)d[row]*count;
            // The unpublished upper packet serves as a linear-time occupancy workspace.
            if(out_hi[2u*destination]!=0){atomicOr(slot,REFUSED_MALFORMED);return;}
            out_hi[2u*destination]=1;
            for(uint32_t j=0;j<count;++j)y[destination+j]=x[start+j];
            radius=add_checked(radius,x[source_width],slot);
        }
        y[out_width]=radius;
        if(*slot)return;
        for(size_t j=0;j<out_stride;++j)out_hi[j]=out[j];
    }
}

// Restrict every row of one enclosure section to a declared complex-coordinate range. The
// per-row radius is copied unchanged; the omitted coordinates remain part of the finer source
// section owned by the caller.
extern "C" __global__ void section_normal_enclosure_restrict_section(
    const int64_t *source,const int64_t *source_hi,uint32_t source_width,uint32_t rows,
    uint32_t start,uint32_t count,int64_t *out,int64_t *out_hi,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
    if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
    if(!rows||!source_width||!count||(source_width&1u)||(start&1u)||(count&1u)||
       (uint64_t)start+count>source_width){atomicOr(slot,REFUSED_MALFORMED);return;}
    const size_t source_stride=2u*((size_t)source_width+1u),out_stride=2u*((size_t)count+1u);
    if(!threadIdx.x){
        for(uint32_t row=0;row<rows;++row){
            const size_t sa=(size_t)row*source_stride,oa=(size_t)row*out_stride;
            for(size_t j=0;j<source_stride;++j)
                if(source[sa+j]!=source_hi[sa+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
            const wide *x=(const wide *)(source+sa);wide *y=(wide *)(out+oa);
            if(x[source_width]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
            for(uint32_t j=0;j<count;++j)y[j]=x[start+j];
            y[count]=x[source_width];
        }
        if(*slot)return;
        for(size_t j=0;j<out_stride*rows;++j)out_hi[j]=out[j];
    }
}
