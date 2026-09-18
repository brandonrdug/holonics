// Adapt an actual reflection and target to the existing paired-material adjoint.
// The query stores [lower,upper] pairs of wide values; lo/hi buffers encode the same exact words.
extern "C" __global__ void section_field_reflection_target(
 const int64_t *input,const int64_t *input_hi,uint32_t ia,
 const int64_t *output,const int64_t *output_hi,uint32_t oa,
 const int64_t *target,const int64_t *target_hi,uint32_t ta,uint32_t target_width,
 const int64_t *source_bounds,const int64_t *source_bounds_hi,
 const int64_t *held,const int64_t *held_hi,uint32_t has_held,
 uint32_t n,uint32_t count,uint32_t grain,uint32_t step_bits,
 int64_t *forward,int64_t *forward_hi,int64_t *after_b,int64_t *after_b_hi,
 int64_t *bounds,int64_t *bounds_hi,int64_t *query,int64_t *query_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const uint32_t d=6u*n;const size_t width=(size_t)d+2u*count,stride=(size_t)d+1u;
 if(!n||grain<1||grain>120||step_bits>120||(ia&1u)||(oa&1u)||(ta&1u)
    ||(target_width!=d&&target_width!=width&&(!has_held||!target_width||target_width>d||(target_width&1u)))){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<2u*(width+1u);++i)if(input[ia+i]!=input_hi[ia+i]||output[oa+i]!=output_hi[oa+i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<2u*((size_t)target_width+1u);++i)if(target[ta+i]!=target_hi[ta+i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<4;++i)if(source_bounds[i]!=source_bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 if(has_held)for(uint32_t i=0;i<d/2u;++i)
   if(held[i]!=held_hi[i]||(held[i]!=0&&held[i]!=1)){atomicOr(slot,REFUSED_MALFORMED);return;}
 const wide *x=(const wide*)(input+ia),*y=(const wide*)(output+oa),*t=(const wide*)(target+ta),*se=(const wide*)source_bounds;
 if(*slot||x[width]<0||y[width]<0||t[target_width]<0||se[0]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide *v=(wide*)forward,*b=(wide*)after_b,*e=(wide*)bounds,*q=(wide*)query;
 for(size_t i=0;i<6u*stride;++i)v[i]=0;
 for(size_t i=0;i<2u*(size_t)(count?count:1u);++i)b[i]=0;
 for(size_t i=0;i<2u*((size_t)10u*n+2u*count);++i)q[i]=0;
 for(uint32_t j=0;j<d;++j)v[j]=add_checked(x[j],y[j],slot);
 v[d]=add_checked(x[width],y[width],slot);
 for(uint32_t j=0;j<2u*count;++j)b[j]=y[d+j];
 e[0]=se[0];e[1]=y[width];
 wide divisor=(wide)((uwide)1u<<step_bits);
 bool active=target_width>d;
 for(uint32_t j=0;j<target_width&&j<d;++j)if(!has_held||!held[j/2u])active=true;
 wide radius=active?div_ceil(add_checked(t[target_width],y[width],slot),divisor,slot):0;
 for(uint32_t j=0;j<target_width;++j){
  if(has_held&&j<d&&held[j/2u]){q[2u*((size_t)4u*n+j)]=0;q[2u*((size_t)4u*n+j)+1u]=0;continue;}
  wide round=0;
  wide g=history_narrow(complete_divide(history_integer(sub_checked(t[j],y[j],slot)),history_integer(divisor),&round,slot),slot);
  wide error=add_checked(radius,round,slot);
  size_t at=j<d?2u*((size_t)4u*n+j):2u*((size_t)10u*n+j-d);
  q[at]=sub_checked(g,error,slot);q[at+1u]=add_checked(g,error,slot);
 }
 if(*slot)return;
 for(size_t i=0;i<12u*stride;++i)forward_hi[i]=forward[i];
 for(size_t i=0;i<4u*(size_t)(count?count:1u);++i)after_b_hi[i]=after_b[i];
 for(size_t i=0;i<4;++i)bounds_hi[i]=bounds[i];
 for(size_t i=0;i<4u*((size_t)10u*n+2u*count);++i)query_hi[i]=query[i];
}

extern "C" __global__ void section_field_reflection_input_cotangent(
 const int64_t *diagnostics,const int64_t *diagnostics_hi,uint32_t d,uint32_t count,
 int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
 const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const size_t width=(size_t)d+2u*count,offset=2u*(size_t)d+4u*count;
 if(!d||(d&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<2u*(offset+8u);++i)if(diagnostics[i]!=diagnostics_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 const wide *p=(const wide*)diagnostics;wide *y=(wide*)out;
 if(*slot||p[offset+1u]<0||p[offset+2u]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<width;++i)y[i]=p[i];
 y[width]=add_checked(p[offset+1u],p[offset+2u],slot);
 if(*slot)return;for(size_t i=0;i<2u*(width+1u);++i)out_hi[i]=out[i];
}

// Form Q*(target-output) for all rows before the same self-adjoint fixed-D reflection.
// Both source enclosures and dyadic division remainders remain in the returned bound.
extern "C" __global__ void section_field_target_residual_section(
 const int64_t *output,const int64_t *output_hi,uint32_t output_stride,
 const int64_t *target,const int64_t *target_hi,uint32_t target_stride,
 const int64_t *mask,const int64_t *mask_hi,uint32_t has_mask,
 uint32_t d,uint32_t count,uint32_t rows,uint32_t step_bits,
 int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,
 const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const uint32_t width=d+2u*count;
 if(!d||(d&1u)||!rows||output_stride!=2u*(width+1u)||target_stride!=2u*(d+1u)||step_bits>120u){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
 const wide divisor=(wide)((uwide)1u<<step_bits);
 if(!threadIdx.x&&has_mask){
  if(!mask||!mask_hi)atomicOr(slot,REFUSED_MALFORMED);
  else for(uint32_t j=0;j<d/2u;++j)if(mask[j]!=mask_hi[j]||(mask[j]!=0&&mask[j]!=1))atomicOr(slot,REFUSED_MALFORMED);
 }
 __syncthreads();if(*slot)return;
 for(uint32_t row=0;row<rows;++row){
  const int64_t *yw=output+(size_t)row*output_stride,*yh=output_hi+(size_t)row*output_stride;
  const int64_t *tw=target+(size_t)row*target_stride,*th=target_hi+(size_t)row*target_stride;
  wide *g=(wide*)out+(size_t)row*(width+1u);
  if(!threadIdx.x){
   const wide *y=(const wide*)yw,*t=(const wide*)tw;
   for(size_t j=0;j<output_stride;++j)if(yw[j]!=yh[j])atomicOr(slot,REFUSED_MALFORMED);
   for(size_t j=0;j<target_stride;++j)if(tw[j]!=th[j])atomicOr(slot,REFUSED_MALFORMED);
   if(y[width]<0||t[d]<0)atomicOr(slot,REFUSED_MALFORMED);
   for(uint32_t j=0;j<width;++j)g[j]=0;
   wide rounding=0;bool active=false;
   if(!*slot)for(uint32_t j=0;j<d;++j)if(!has_mask||!mask[j/2u]){
    active=true;wide error=0;
    g[j]=history_narrow(complete_divide(history_integer(sub_checked(t[j],y[j],slot)),history_integer(divisor),&error,slot),slot);
    rounding=add_checked(rounding,error,slot);
   }
   g[width]=active?add_checked(div_ceil(add_checked(y[width],t[d],slot),divisor,slot),rounding,slot):0;
  }
  __syncthreads();if(*slot)return;
  for(size_t j=threadIdx.x;j<2u*(size_t)(width+1u);j+=blockDim.x)out_hi[(size_t)row*2u*(width+1u)+j]=out[(size_t)row*2u*(width+1u)+j];
  __syncthreads();
 }
}
