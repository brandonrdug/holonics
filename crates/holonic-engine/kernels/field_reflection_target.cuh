// Adapt an actual reflection and target to the existing paired-material adjoint.
// The query stores [lower,upper] pairs of wide values; lo/hi buffers encode the same exact words.
extern "C" __global__ void section_field_reflection_target(
 const int64_t *input,const int64_t *input_hi,uint32_t ia,
 const int64_t *output,const int64_t *output_hi,uint32_t oa,
 const int64_t *target,const int64_t *target_hi,uint32_t ta,uint32_t target_width,
 const int64_t *source_bounds,const int64_t *source_bounds_hi,
 uint32_t n,uint32_t count,uint32_t grain,uint32_t step_bits,
 int64_t *forward,int64_t *forward_hi,int64_t *after_b,int64_t *after_b_hi,
 int64_t *bounds,int64_t *bounds_hi,int64_t *query,int64_t *query_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const uint32_t d=6u*n;const size_t width=(size_t)d+2u*count,stride=(size_t)d+1u;
 if(!n||grain<1||grain>120||step_bits>120||(ia&1u)||(oa&1u)||(ta&1u)
    ||(target_width!=d&&target_width!=width)){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<2u*(width+1u);++i)if(input[ia+i]!=input_hi[ia+i]||output[oa+i]!=output_hi[oa+i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<2u*((size_t)target_width+1u);++i)if(target[ta+i]!=target_hi[ta+i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<4;++i)if(source_bounds[i]!=source_bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
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
 wide radius=div_ceil(add_checked(t[target_width],y[width],slot),divisor,slot);
 for(uint32_t j=0;j<target_width;++j){
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
