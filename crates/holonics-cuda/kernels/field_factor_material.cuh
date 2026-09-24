// A material return appends its two producing factors to the same executable D program.
// Pure-current continuation shares D and writes only the internal-current section.
extern "C" __global__ void section_field_factor_append(
 const int64_t *old_left,const int64_t *old_left_hi,const int64_t *old_right,const int64_t *old_right_hi,
 const int64_t *old_defects,const int64_t *old_defects_hi,const int64_t *ports,const int64_t *ports_hi,
 const int64_t *currents,const int64_t *currents_hi,const int64_t *delta_bounds,const int64_t *delta_bounds_hi,
 uint32_t rank,uint32_t d,uint32_t count,uint32_t grain,uint32_t exact,
 int64_t *left,int64_t *left_hi,int64_t *right,int64_t *right_hi,int64_t *defects,int64_t *defects_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 const size_t at=(size_t)blockIdx.x*blockDim.x+threadIdx.x,stride=(size_t)gridDim.x*blockDim.x;
 for(size_t i=at;i<2u*((size_t)rank+2u)*d;i+=stride){
  const size_t base=2u*(size_t)rank*d;int64_t value;
  if(i<base){value=old_left[i];if(value!=old_left_hi[i])atomicOr(slot,REFUSED_MALFORMED);}
  else{value=ports[i-base];if(value!=ports_hi[i-base])atomicOr(slot,REFUSED_MALFORMED);}
  left[i]=left_hi[i]=value;
 }
 for(size_t i=at;i<4u*((size_t)rank+2u)*count;i+=stride){
  const size_t base=4u*(size_t)rank*count;int64_t value;
  if(i<base){value=old_right[i];if(value!=old_right_hi[i])atomicOr(slot,REFUSED_MALFORMED);}
  else{value=currents[i-base];if(value!=currents_hi[i-base])atomicOr(slot,REFUSED_MALFORMED);}
  right[i]=right_hi[i]=value;
 }
 for(size_t i=at;i<2u*(size_t)rank;i+=stride){
  if(old_defects[i]!=old_defects_hi[i])atomicOr(slot,REFUSED_MALFORMED);
  defects[i]=defects_hi[i]=old_defects[i];
 }
 if(at==0){
  for(uint32_t i=0;i<4;++i)if(delta_bounds[i]!=delta_bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
  const wide error=((const wide*)delta_bounds)[0];
  if(error<0||((const wide*)delta_bounds)[1]!=0){atomicOr(slot,REFUSED_MALFORMED);return;}
  // The journal carries the complete matrix-increment radius, as every operative
  // return does. It also bounds each of the two constituent factor products.
  // Exact deposits choose the finite dyadic factors, retaining the original radius
  // in the journal; their products stay exact at the factor representation's 2g scale.
  for(uint32_t p=0;p<2;++p){
   ((wide*)defects)[rank+p]=exact?0:error;((wide*)defects_hi)[rank+p]=exact?0:error;
  }
 }
}
extern "C" __global__ void section_field_factor_current(
 const int64_t *before,const int64_t *before_hi,const int64_t *before_bounds,const int64_t *before_bounds_hi,
 const int64_t *delta,const int64_t *delta_hi,const int64_t *delta_bounds,const int64_t *delta_bounds_hi,
 const int64_t *image,const int64_t *image_hi,uint32_t image_at,uint32_t d,uint32_t count,
 int64_t *out,int64_t *out_hi,int64_t *out_bounds,int64_t *out_bounds_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 const size_t at=(size_t)blockIdx.x*blockDim.x+threadIdx.x,stride=(size_t)gridDim.x*blockDim.x;
 for(size_t i=at;i<2u*(size_t)count;i+=stride){
  if(before[2*i]!=before_hi[2*i]||before[2*i+1]!=before_hi[2*i+1]){atomicOr(slot,REFUSED_MALFORMED);continue;}
  wide value=((const wide*)before)[i];
  if(delta){
   if(delta[2*i]!=delta_hi[2*i]||delta[2*i+1]!=delta_hi[2*i+1]){atomicOr(slot,REFUSED_MALFORMED);continue;}
   value=add_checked(value,((const wide*)delta)[i],slot);
  }
  if(delta)((wide*)out)[i]=((wide*)out_hi)[i]=value;
 }
 if(at==0){
  for(uint32_t i=0;i<4;++i)if(before_bounds[i]!=before_bounds_hi[i]||delta_bounds[i]!=delta_bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
  const wide *prior=(const wide*)before_bounds,*change=(const wide*)delta_bounds;
  if(prior[0]<0||prior[1]<0||change[0]<0||change[1]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
  wide radius=delta?add_checked(prior[1],change[1],slot):prior[1];
  if(image){
   size_t pos=image_at+2u*((size_t)d+2u*count);
   if(image[pos]!=image_hi[pos]||image[pos+1]!=image_hi[pos+1])atomicOr(slot,REFUSED_MALFORMED);
   radius=*((const wide*)(image+pos));if(radius<0)atomicOr(slot,REFUSED_MALFORMED);
  }
  // The incidence anchor bound remains separate from appended factor defects.
  ((wide*)out_bounds)[0]=((wide*)out_bounds_hi)[0]=prior[0];
  ((wide*)out_bounds)[1]=((wide*)out_bounds_hi)[1]=radius;
 }
}
// Convert factor-ball radii into the complete rank-two matrix increment radius. The second
// entry is zero: a material-only return has no internal-current increment.
extern "C" __global__ void section_field_factor_delta_bound(
 const int64_t *ports,const int64_t *ports_hi,const int64_t *currents,const int64_t *currents_hi,
 const int64_t *bounds,const int64_t *bounds_hi,uint32_t d,uint32_t count,uint32_t grain,
 int64_t *out,int64_t *out_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 for(size_t i=0;i<4u*(size_t)d;++i)if(ports[i]!=ports_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t i=0;i<8u*(size_t)count;++i)if(currents[i]!=currents_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t i=0;i<4;++i)if(bounds[i]!=bounds_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 wide rp=((const wide*)bounds)[0],rc=((const wide*)bounds)[1];
 if(rp<0||rc<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide pn=complete_norm((const wide*)ports,2u*d,slot),cn=complete_norm((const wide*)currents,4u*count,slot);
 wide error=add_checked(ft_ceil_product(rp,cn,grain,slot),add_checked(ft_ceil_product(rc,pn,grain,slot),ft_ceil_product(rp,rc,grain,slot),slot),slot);
 ((wide*)out)[0]=((wide*)out_hi)[0]=error;((wide*)out)[1]=((wide*)out_hi)[1]=0;
}
