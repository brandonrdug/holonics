// A current-only operative journal term. All arithmetic is in the retained wide grid.
extern "C" __global__ void section_field_reflection_current_delta(
 const int64_t *old_b,const int64_t *old_b_hi,const int64_t *bounds,const int64_t *bounds_hi,
 const int64_t *output,const int64_t *output_hi,uint32_t at,uint32_t d,uint32_t count,
 int64_t *ports,int64_t *ports_hi,int64_t *factors,int64_t *factors_hi,
 int64_t *delta_b,int64_t *delta_b_hi,int64_t *delta_bounds,int64_t *delta_bounds_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const size_t width=(size_t)d+2u*count;
 if(!d||(d&1u)||(at&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<4u*(size_t)(count?count:1u);++i)if(old_b[i]!=old_b_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<4;++i)if(bounds[i]!=bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<2u*(width+1u);++i)if(output[at+i]!=output_hi[at+i])atomicOr(slot,REFUSED_MALFORMED);
 const wide *b=(const wide*)old_b,*e=(const wide*)bounds,*y=(const wide*)(output+at);
 if(*slot||e[1]<0||y[width]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<4u*d;++i)ports[i]=ports_hi[i]=0;
 for(size_t i=0;i<8;++i)factors[i]=factors_hi[i]=0;
 for(size_t i=0;i<4u*(size_t)(count?count:1u);++i)delta_b[i]=delta_b_hi[i]=0;
 for(uint32_t i=0;i<2u*count;++i)((wide*)delta_b)[i]=sub_checked(y[d+i],b[i],slot);
 ((wide*)delta_bounds)[0]=0;
 ((wide*)delta_bounds)[1]=count?add_checked(y[width],e[1],slot):0;
 if(*slot)return;
 for(size_t i=0;i<4u*(size_t)(count?count:1u);++i)delta_b_hi[i]=delta_b[i];
 for(size_t i=0;i<4;++i)delta_bounds_hi[i]=delta_bounds[i];
}

// The six report blocks retain their actual meanings: potential, outgoing, D*b,
// historical occurrence prefix, entering current, and exact-solve residual receiver.
extern "C" __global__ void section_field_reflection_report(
 const int64_t *input,const int64_t *input_hi,uint32_t ia,
 const int64_t *output,const int64_t *output_hi,uint32_t oa,
 const int64_t *before,const int64_t *before_hi,const int64_t *aggregate,const int64_t *aggregate_hi,
 const int64_t *moment_bounds,const int64_t *moment_bounds_hi,const int64_t *trace,const int64_t *trace_hi,
 uint32_t d,uint32_t count,uint32_t grain,int64_t *report,int64_t *report_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const size_t width=(size_t)d+2u*count,stride=(size_t)d+1u;
 if(!d||(d&1u)||(ia&1u)||(oa&1u)||grain<1||grain>120){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<2u*(width+1u);++i)if(input[ia+i]!=input_hi[ia+i]||output[oa+i]!=output_hi[oa+i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<12u*stride;++i)if(before[i]!=before_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<2u*d;++i)if(aggregate[i]!=aggregate_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<8;++i)if(moment_bounds[i]!=moment_bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<18u*d;++i)if(trace[i]!=trace_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 const wide *x=(const wide*)(input+ia),*y=(const wide*)(output+oa),*old=(const wide*)before;
 const wide *h=(const wide*)aggregate,*mb=(const wide*)moment_bounds;wide *r=(wide*)report;
 if(*slot||x[width]<0||y[width]<0||mb[1]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t j=0;j<d;++j){
  r[j]=add_checked(x[j],y[j],slot);r[stride+j]=y[j];r[2u*stride+j]=h[j];
  r[3u*stride+j]=old[3u*stride+j];r[4u*stride+j]=x[j];
  MomentInteger residual;const int64_t *raw=trace+18u*j;
  for(uint32_t i=0;i<MomentInteger::LIMBS;++i){if(raw[i]<0||(uint64_t)raw[i]>UINT32_MAX)atomicOr(slot,REFUSED_MALFORMED);residual.limb[i]=(uint32_t)raw[i];}
  if(raw[MomentInteger::LIMBS]!=0&&raw[MomentInteger::LIMBS]!=1)atomicOr(slot,REFUSED_MALFORMED);
  residual.negative=raw[MomentInteger::LIMBS]!=0;wide rounding=0;
  r[5u*stride+j]=operative_moment_grid(residual,2u*grain,&rounding,slot);
 }
 r[d]=add_checked(x[width],y[width],slot);r[2u*stride-1u]=y[width];r[3u*stride-1u]=mb[1];
 r[4u*stride-1u]=old[4u*stride-1u];r[5u*stride-1u]=x[width];r[6u*stride-1u]=1;
 if(*slot)return;for(size_t i=0;i<12u*stride;++i)report_hi[i]=report[i];
}

// The staged current is exactly the reflected image. Its old-current terms cancel in
// b+(b_next-b); adding their independent radii again would erase this source equality.
extern "C" __global__ void section_field_reflection_current_bound(
 const int64_t *output,const int64_t *output_hi,uint32_t at,uint32_t width,
 int64_t *bounds,int64_t *bounds_hi,uint32_t count,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 for(size_t j=0;j<2u*((size_t)width+1u);++j)if(output[at+j]!=output_hi[at+j])atomicOr(slot,REFUSED_MALFORMED);
 const wide *y=(const wide*)(output+at);
 if(*slot||y[width]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 ((wide*)bounds)[1]=count?y[width]:0;
 for(uint32_t j=2;j<4;++j)bounds_hi[j]=bounds[j];
}
