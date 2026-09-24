// Restrictions and regroupings of joint enclosure packets. The original joint ball remains
// the canonical state; row projections are borrowed operands of an incident operation.
extern "C" __global__ void section_enclosure_regroup(
 const int64_t *input,const int64_t *input_hi,uint64_t offset,
 uint32_t input_rows,uint32_t input_d,uint32_t output_rows,uint32_t output_d,
 int64_t *out,int64_t *out_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=output_rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 if(!input_d||!output_d||(input_d&1u)||(output_d&1u)||
    (uint64_t)input_rows*input_d!=(uint64_t)output_rows*output_d){atomicOr(status,REFUSED_MALFORMED);return;}
 const size_t os=2u*((size_t)output_d+1u),is=2u*((size_t)input_d+1u);
 int64_t *ow=out+os*row;wide *y=(wide*)ow;HistoryInteger radius_square;
 uint64_t start=(uint64_t)row*output_d,end=start+output_d;
 uint32_t first=(uint32_t)(start/input_d),last=(uint32_t)((end-1u)/input_d);
 for(uint32_t r=first;r<=last;++r){
  const int64_t *x=input+offset+is*r,*xh=input_hi+offset+is*r;
  if(!ec_ball(x,xh,input_d,status))return;
  // The Euclidean product bound is valid even when the source rows are correlated.
  wide radius=((const wide*)x)[input_d];
  if(radius<0){atomicOr(status,REFUSED_MALFORMED);return;}
  radius_square=radius_square+history_integer(radius)*history_integer(radius);
 }
 for(uint32_t j=0;j<output_d;++j){uint64_t at=start+j;
  y[j]=((const wide*)(input+offset+is*(at/input_d)))[at%input_d];}
 y[output_d]=history_norm_ceiling(radius_square,status);ec_seal(ow,out_hi+os*row,output_d,status);
}

extern "C" __global__ void section_normal_enclosure_zero(
    uint32_t rows,uint32_t width,int64_t *out,int64_t *out_hi,uint32_t *slot,
    const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 if(!rows||!width||(width&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
 const size_t stride=2u*((size_t)width+1u),words=stride*rows;
 for(size_t i=threadIdx.x;i<words;i+=blockDim.x)out[i]=0;
 __syncthreads();
 for(size_t i=threadIdx.x;i<words;i+=blockDim.x)out_hi[i]=out[i];
}
