// D = D0 + sum p c*. CSR and its transpose are two access charts of the SAME map.
// Each contraction returns an outward error for its numerical centre, including the
// amplification of a rounded low-rank scalar by its remaining factor.
__device__ wide factor_grid(HistoryInteger value,uint32_t grain,wide *rounds,uint32_t *slot){
 return history_narrow(complete_divide(value,complete_power(grain,slot),rounds,slot),slot);
}
__device__ void factor_sealed(const int64_t *lo,const int64_t *hi,size_t words,uint32_t *slot){
 for(size_t i=0;i<words;++i)if(lo[i]!=hi[i])atomicOr(slot,REFUSED_MALFORMED);
}
__device__ wide factor_total_error(const wide *bounds,const wide *defects,uint32_t rank,uint32_t *slot){
 wide error=bounds[0];if(error<0||bounds[1]<0)atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t p=0;p<rank;++p){if(defects[p]<0)atomicOr(slot,REFUSED_MALFORMED);error=add_checked(error,defects[p],slot);}
 return error;
}
__device__ void factor_validate_packet(
 const int64_t *off,const int64_t *off_hi,const int64_t *col,const int64_t *col_hi,const int64_t *val,const int64_t *val_hi,
 const int64_t *toff,const int64_t *toff_hi,const int64_t *trow,const int64_t *trow_hi,const int64_t *tval,const int64_t *tval_hi,
 const int64_t *left,const int64_t *left_hi,const int64_t *right,const int64_t *right_hi,const int64_t *defects,const int64_t *defects_hi,
 uint32_t d,uint32_t count,uint32_t nnz,uint32_t rank,uint32_t *slot){
 factor_sealed(off,off_hi,2u*((size_t)count+1u),slot);
 factor_sealed(col,col_hi,2u*(size_t)nnz,slot);factor_sealed(val,val_hi,4u*(size_t)nnz,slot);
 factor_sealed(toff,toff_hi,2u*((size_t)d/2u+1u),slot);
 factor_sealed(trow,trow_hi,2u*(size_t)nnz,slot);factor_sealed(tval,tval_hi,4u*(size_t)nnz,slot);
 factor_sealed(left,left_hi,2u*(size_t)rank*d,slot);factor_sealed(right,right_hi,4u*(size_t)rank*count,slot);factor_sealed(defects,defects_hi,2u*(size_t)rank,slot);
 for(uint32_t i=0;i<=count;++i)if(off[2u*i+1u]!=0||off[2u*i]<0||(uint64_t)off[2u*i]>nnz||(i&&off[2u*i]<off[2u*(i-1u)]))atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t i=0;i<=d/2u;++i)if(toff[2u*i+1u]!=0||toff[2u*i]<0||(uint64_t)toff[2u*i]>nnz||(i&&toff[2u*i]<toff[2u*(i-1u)]))atomicOr(slot,REFUSED_MALFORMED);
 if(off[0]!=0||toff[0]!=0||(uint64_t)off[2u*count]!=nnz||(uint64_t)toff[d]!=nnz)atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t i=0;i<nnz;++i){
  if(col[2u*i+1u]!=0||col[2u*i]<0||(col[2u*i]&1)|| (uint64_t)col[2u*i]+1u>=d)atomicOr(slot,REFUSED_MALFORMED);
  if(trow[2u*i+1u]!=0||trow[2u*i]<0||(uint64_t)trow[2u*i]>=count)atomicOr(slot,REFUSED_MALFORMED);
 }
 for(uint32_t i=0;i<rank;++i)if(((const wide*)defects)[i]<0)atomicOr(slot,REFUSED_MALFORMED);
 if(*slot)return;
 // Unique contact/port entries and equal population make this a bijection. A different
 // transpose would invalidate positive definiteness, so it is rejected before any action.
 for(uint32_t port=0;port<d/2u;++port){
  const uint32_t first=(uint32_t)toff[2u*port],last=(uint32_t)toff[2u*(port+1u)];
  for(uint32_t i=first;i<last;++i)if(i>first&&trow[2u*i]<=trow[2u*(i-1u)])atomicOr(slot,REFUSED_MALFORMED);
 }
 for(uint32_t row=0;row<count;++row){
  const uint32_t first=(uint32_t)off[2u*row],last=(uint32_t)off[2u*(row+1u)];
  for(uint32_t i=first;i<last;++i){
   for(uint32_t j=first;j<i;++j)if(col[2u*j]==col[2u*i])atomicOr(slot,REFUSED_MALFORMED);
   const uint32_t port=(uint32_t)col[2u*i]/2u;bool found=false;
   for(uint32_t j=(uint32_t)toff[2u*port];j<(uint32_t)toff[2u*(port+1u)];++j)if((uint32_t)trow[2u*j]==row){
    found=true;for(uint32_t q=0;q<4;++q)if(val[4u*i+q]!=tval[4u*j+q])atomicOr(slot,REFUSED_MALFORMED);
   }
   if(!found)atomicOr(slot,REFUSED_MALFORMED);
  }
 }
}
// Exact block sum for a factor contraction. Every lane owns disjoint input coordinates;
// the reduction joins signed integer partials BEFORE their one final grain division.
// Storage is 2*512*(8 limbs + sign + overflow)*4 = 40,960 shared bytes. The mounted
// function attributes and the launch law admit this resource with the chosen block extent.
__device__ void factor_store_partial(uint32_t *dst,const HistoryInteger &value){
 for(uint32_t j=0;j<HistoryInteger::LIMBS;++j)dst[j]=value.limb[j];
 dst[HistoryInteger::LIMBS]=value.negative;dst[HistoryInteger::LIMBS+1u]=value.overflow;
}
__device__ HistoryInteger factor_load_partial(const uint32_t *src){
 HistoryInteger value;for(uint32_t j=0;j<HistoryInteger::LIMBS;++j)value.limb[j]=src[j];
 value.negative=src[HistoryInteger::LIMBS]!=0;value.overflow=src[HistoryInteger::LIMBS+1u]!=0;return value;
}
// One block cooperates on each solve: independent output coordinates own their sums.
// rounds has rank+max(d/2,count)+1 words; the last word joins all contraction defects.
__device__ wide factor_apply(
 bool adjoint,const int64_t *offsets,const int64_t *columns,const wide *values,
 const int64_t *transpose_offsets,const int64_t *transpose_rows,const wide *transpose_values,
 const wide *left,const wide *right,const wide *x,uint32_t d,uint32_t count,uint32_t rank,uint32_t grain,
 wide *out,wide *rounds,wide *scalars,bool certify,uint32_t *slot){
 const uint32_t outputs=adjoint?count:d/2u,inputs=adjoint?d:2u*count;
 const uint32_t output_width=adjoint?2u*count:d,max_outputs=d/2u>count?d/2u:count;
 const wide *contracted=adjoint?left:right,*remaining=adjoint?right:left;
 constexpr uint32_t partial_words=HistoryInteger::LIMBS+2u;
 __shared__ uint32_t partial[2u*512u*partial_words];
 if(blockDim.x>512u){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return 0;}
 for(uint32_t p=0;p<rank;++p){
  HistoryInteger re,im;
  for(uint32_t j=2u*threadIdx.x;j<inputs;j+=2u*blockDim.x)
   history_complex_add_product(re,im,contracted[(size_t)p*inputs+j],contracted[(size_t)p*inputs+j+1u],x[j],x[j+1u],true);
  uint32_t *real_part=partial+threadIdx.x*partial_words;
  uint32_t *imaginary_part=partial+(512u+threadIdx.x)*partial_words;
  factor_store_partial(real_part,re);factor_store_partial(imaginary_part,im);
  __syncthreads();
  for(uint32_t active=blockDim.x;active>1u;active=(active+1u)/2u){
   const uint32_t stride=(active+1u)/2u;
   if(threadIdx.x<active/2u){
    factor_store_partial(real_part,factor_load_partial(real_part)+factor_load_partial(real_part+stride*partial_words));
    factor_store_partial(imaginary_part,factor_load_partial(imaginary_part)+factor_load_partial(imaginary_part+stride*partial_words));
   }
   __syncthreads();
  }
  if(!threadIdx.x){
   wide omitted=0;
   scalars[2u*p]=factor_grid(factor_load_partial(partial),grain,&omitted,slot);
   scalars[2u*p+1u]=factor_grid(factor_load_partial(partial+512u*partial_words),grain,&omitted,slot);
   if(certify)rounds[p]=ft_ceil_product(omitted,complete_norm(remaining+(size_t)p*output_width,output_width,slot),grain,slot);
  }
  __syncthreads();
 }
 for(uint32_t row=threadIdx.x;row<outputs;row+=blockDim.x){
  HistoryInteger re,im;wide omitted=0;
  const int64_t *off=adjoint?offsets:transpose_offsets,*indices=adjoint?columns:transpose_rows;
  const wide *val=adjoint?values:transpose_values;
  for(uint32_t at=(uint32_t)off[2u*row];at<(uint32_t)off[2u*(row+1u)];++at){
   const uint32_t index=adjoint?(uint32_t)indices[2u*at]:2u*(uint32_t)indices[2u*at];
   history_complex_add_product(re,im,val[2u*at],val[2u*at+1u],x[index],x[index+1u],adjoint);
  }
  for(uint32_t p=0;p<rank;++p)history_complex_add_product(re,im,remaining[(size_t)p*output_width+2u*row],remaining[(size_t)p*output_width+2u*row+1u],scalars[2u*p],scalars[2u*p+1u],false);
  out[2u*row]=factor_grid(re,grain,&omitted,slot);out[2u*row+1u]=factor_grid(im,grain,&omitted,slot);if(certify)rounds[rank+row]=omitted;
 }
 __syncthreads();
 // Only the right-hand side and final residual need contraction certificates.
 // Intermediate Richardson proposals are certified afresh at their final residual.
 if(!certify)return 0;
 if(!threadIdx.x){wide error=0;for(uint32_t i=0;i<rank+outputs;++i)error=add_checked(error,rounds[i],slot);rounds[rank+max_outputs]=error;}
 __syncthreads();return rounds[rank+max_outputs];
}
extern "C" __global__ void __launch_bounds__(512) section_field_factor_aggregate(
 const int64_t *offsets,const int64_t *offsets_hi,const int64_t *columns,const int64_t *columns_hi,
 const int64_t *values,const int64_t *values_hi,const int64_t *transpose_offsets,const int64_t *transpose_offsets_hi,
 const int64_t *transpose_rows,const int64_t *transpose_rows_hi,const int64_t *transpose_values,const int64_t *transpose_values_hi,
 const int64_t *left_wire,const int64_t *left_hi,const int64_t *right_wire,const int64_t *right_hi,
 const int64_t *defects,const int64_t *defects_hi,const int64_t *b_wire,const int64_t *b_hi,
 const int64_t *input_bounds,const int64_t *input_bounds_hi,uint32_t d,uint32_t count,uint32_t nnz,uint32_t rank,uint32_t grain,
 int64_t *aggregate,int64_t *aggregate_hi,int64_t *moment_bounds,int64_t *moment_bounds_hi,int64_t *work_wire,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
 if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 if(!d||(d&1u)||!count||grain<1u||grain>120u){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
 if(!threadIdx.x){
  factor_validate_packet(offsets,offsets_hi,columns,columns_hi,values,values_hi,transpose_offsets,transpose_offsets_hi,transpose_rows,transpose_rows_hi,transpose_values,transpose_values_hi,left_wire,left_hi,right_wire,right_hi,defects,defects_hi,d,count,nnz,rank,slot);
  factor_sealed(b_wire,b_hi,4u*(size_t)count,slot);factor_sealed(input_bounds,input_bounds_hi,4,slot);
 }
 __syncthreads();if(*slot)return;
 const wide *val=(const wide*)values,*tv=(const wide*)transpose_values,*left=(const wide*)left_wire,*right=(const wide*)right_wire,*b=(const wide*)b_wire,*eb=(const wide*)input_bounds;
 wide *work=(wide*)work_wire,*rounds=work,*scalars=rounds+d+2u*count+rank+1u;
 const wide rounding=factor_apply(false,offsets,columns,val,transpose_offsets,transpose_rows,tv,left,right,b,d,count,rank,grain,(wide*)aggregate,rounds,scalars,true,slot);
 if(!threadIdx.x){
  wide max_column=0,max_row=0;
  // The complex absolute value is bounded by |real|+|imaginary|, so no irrational
  // coefficient has to be rounded inward when constructing the 1/infinity norm bound.
  for(uint32_t row=0;row<count;++row){wide sum=0;for(uint32_t at=(uint32_t)offsets[2u*row];at<(uint32_t)offsets[2u*(row+1u)];++at)sum=add_checked(sum,add_checked(ft_abs(val[2u*at],slot),ft_abs(val[2u*at+1u],slot),slot),slot);if(sum>max_column)max_column=sum;}
  for(uint32_t row=0;row<d/2u;++row){wide sum=0;for(uint32_t at=(uint32_t)transpose_offsets[2u*row];at<(uint32_t)transpose_offsets[2u*(row+1u)];++at)sum=add_checked(sum,add_checked(ft_abs(tv[2u*at],slot),ft_abs(tv[2u*at+1u],slot),slot),slot);if(sum>max_row)max_row=sum;}
  wide norm=history_norm_ceiling(history_integer(max_column)*history_integer(max_row),slot);
  for(uint32_t p=0;p<rank;++p)norm=add_checked(norm,ft_ceil_product(complete_norm(left+(size_t)p*d,d,slot),complete_norm(right+2u*(size_t)p*count,2u*count,slot),grain,slot),slot);
  wide map_error=factor_total_error(eb,(const wide*)defects,rank,slot),bnorm=complete_norm(b,2u*count,slot);
  wide aggregate_error=add_checked(rounding,add_checked(ft_ceil_product(norm,eb[1],grain,slot),ft_ceil_product(map_error,add_checked(bnorm,eb[1],slot),grain,slot),slot),slot);
  ((wide*)moment_bounds)[0]=ft_ceil_product(map_error,add_checked(product_checked(2,norm,slot),map_error,slot),grain,slot);
  ((wide*)moment_bounds)[1]=aggregate_error;((wide*)moment_bounds)[2]=norm;((wide*)moment_bounds)[3]=bnorm;
 }
 __syncthreads();if(*slot)return;
 for(size_t i=threadIdx.x;i<2u*(size_t)d;i+=blockDim.x)aggregate_hi[i]=aggregate[i];
 for(size_t i=threadIdx.x;i<8u;i+=blockDim.x)moment_bounds_hi[i]=moment_bounds[i];
}
extern "C" __global__ void section_field_factor_action(
 const int64_t *offsets,const int64_t *offsets_hi,const int64_t *columns,const int64_t *columns_hi,
 const int64_t *values,const int64_t *values_hi,const int64_t *transpose_offsets,const int64_t *transpose_offsets_hi,const int64_t *transpose_rows,const int64_t *transpose_rows_hi,const int64_t *transpose_values,const int64_t *transpose_values_hi,const int64_t *left_wire,const int64_t *left_hi,
 const int64_t *right_wire,const int64_t *right_hi,const int64_t *defects,const int64_t *defects_hi,const int64_t *operator_bounds,const int64_t *operator_bounds_hi,const int64_t *map_bounds,const int64_t *map_bounds_hi,
 const int64_t *input,const int64_t *input_hi,uint32_t input_at,uint32_t d,uint32_t count,uint32_t nnz,uint32_t rank,
 uint32_t grain,uint32_t steps,uint32_t omega_bits,int64_t *work_wire,int64_t *out,int64_t *out_hi,int64_t *residual,int64_t *residual_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
 if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const uint32_t width=d+2u*count;
 if(!d||(d&1u)||!count||!steps||grain<1u||grain>120u||(omega_bits>120u&&omega_bits!=UINT32_MAX)||(input_at&1u)){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
 __shared__ uint32_t selected_omega;
 __shared__ wide map_error,norm,rhs_error,dual_error;
 const wide *x=(const wide*)(input+input_at);
 if(!threadIdx.x){
  factor_sealed(input+input_at,input_hi+input_at,2u*((size_t)width+1u),slot);
  factor_sealed(operator_bounds,operator_bounds_hi,8,slot);factor_sealed(map_bounds,map_bounds_hi,4,slot);
  if(x[width]<0)atomicOr(slot,REFUSED_MALFORMED);
  norm=((const wide*)operator_bounds)[2];if(norm<0)atomicOr(slot,REFUSED_MALFORMED);
  map_error=factor_total_error((const wide*)map_bounds,(const wide*)defects,rank,slot);
  const HistoryInteger scale2=complete_power(2u*grain,slot);
  const HistoryInteger target=scale2+history_integer(norm)*history_integer(norm);
  selected_omega=omega_bits==UINT32_MAX?0:omega_bits;
  if(omega_bits==UINT32_MAX)while(selected_omega<120u&&complete_power(selected_omega,slot)*scale2<target)++selected_omega;
  if(complete_power(selected_omega,slot)*scale2<target)atomicOr(slot,REFUSED_MALFORMED);
 }
 __syncthreads();if(*slot)return;
 const wide *val=(const wide*)values,*tv=(const wide*)transpose_values,*left=(const wide*)left_wire,*right=(const wide*)right_wire;
 wide *work=(wide*)work_wire,*rhs=work,*v=rhs+d,*av=v+d,*dual=av+d,*res=dual+2u*count,*rounds=res+d,*scalars=rounds+d+2u*count+rank+1u;
 for(uint32_t i=threadIdx.x;i<d;i+=blockDim.x)v[i]=0;
 __syncthreads();
 wide e=factor_apply(false,offsets,columns,val,transpose_offsets,transpose_rows,tv,left,right,x+d,d,count,rank,grain,rhs,rounds,scalars,true,slot);
 if(!threadIdx.x)rhs_error=product_checked(2,e,slot);
 for(uint32_t i=threadIdx.x;i<d;i+=blockDim.x)rhs[i]=product_checked(2,add_checked(x[i],rhs[i],slot),slot);
 __syncthreads();if(*slot)return;
 for(uint32_t step=0;step<steps;++step){
  factor_apply(true,offsets,columns,val,transpose_offsets,transpose_rows,tv,left,right,v,d,count,rank,grain,dual,rounds,scalars,false,slot);
  factor_apply(false,offsets,columns,val,transpose_offsets,transpose_rows,tv,left,right,dual,d,count,rank,grain,av,rounds,scalars,false,slot);
  for(uint32_t i=threadIdx.x;i<d;i+=blockDim.x){wide omitted=0;HistoryInteger residual=history_integer(rhs[i])-history_integer(v[i])-history_integer(av[i]);v[i]=add_checked(v[i],factor_grid(residual,selected_omega,&omitted,slot),slot);}
  __syncthreads();if(*slot)return;
 }
 e=factor_apply(true,offsets,columns,val,transpose_offsets,transpose_rows,tv,left,right,v,d,count,rank,grain,dual,rounds,scalars,true,slot);
 if(!threadIdx.x)dual_error=e;
 __syncthreads();
 e=factor_apply(false,offsets,columns,val,transpose_offsets,transpose_rows,tv,left,right,dual,d,count,rank,grain,av,rounds,scalars,true,slot);
 for(uint32_t i=threadIdx.x;i<d;i+=blockDim.x){res[i]=sub_checked(rhs[i],add_checked(v[i],av[i],slot),slot);((wide*)out)[i]=sub_checked(v[i],x[i],slot);((wide*)residual)[i]=res[i];}
 for(uint32_t i=threadIdx.x;i<2u*count;i+=blockDim.x)((wide*)out)[d+i]=sub_checked(dual[i],x[d+i],slot);
 __syncthreads();if(*slot)return;
 if(!threadIdx.x){
  wide scale=(wide)((uwide)1u<<grain);
  // All iteration arithmetic is certified afresh at the final candidate: A>=I makes
  // this residual independent of whether the iteration reached its requested accuracy.
  wide R=add_checked(complete_norm(res,d,slot),add_checked(rhs_error,add_checked(ft_ceil_product(norm,dual_error,grain,slot),e,slot),slot),slot);
  wide solved_error=add_checked(ft_ceil_product(add_checked(scale,norm,slot),R,grain,slot),dual_error,slot);
  // S_D is unitary; changing D by epsilon changes its graph reflection by at most
  // 2 epsilon. Input uncertainty therefore contributes its original joint radius once.
  wide parameter_error=ft_ceil_product(product_checked(2,map_error,slot),complete_norm(x,width,slot),grain,slot);
  ((wide*)out)[width]=add_checked(x[width],add_checked(solved_error,parameter_error,slot),slot);
  // Retain an outward bound on the residual for the actual D and input as well.
  wide A_error=ft_ceil_product(map_error,add_checked(product_checked(2,norm,slot),map_error,slot),grain,slot);
  wide source_error=ft_ceil_product(product_checked(2,add_checked(scale,add_checked(norm,map_error,slot),slot),slot),x[width],grain,slot);
  ((wide*)residual)[d]=add_checked(R,add_checked(source_error,add_checked(ft_ceil_product(product_checked(2,map_error,slot),complete_norm(x+d,2u*count,slot),grain,slot),ft_ceil_product(A_error,complete_norm(v,d,slot),grain,slot),slot),slot),slot);
 }
 __syncthreads();if(*slot)return;
 for(size_t i=threadIdx.x;i<2u*((size_t)width+1u);i+=blockDim.x)out_hi[i]=out[i];
 for(size_t i=threadIdx.x;i<2u*((size_t)d+1u);i+=blockDim.x)residual_hi[i]=residual[i];
}
extern "C" __global__ void section_field_factor_pullback(
 const int64_t *offsets,const int64_t *offsets_hi,const int64_t *columns,const int64_t *columns_hi,
 const int64_t *values,const int64_t *values_hi,const int64_t *transpose_offsets,const int64_t *transpose_offsets_hi,const int64_t *transpose_rows,const int64_t *transpose_rows_hi,const int64_t *transpose_values,const int64_t *transpose_values_hi,const int64_t *left_wire,const int64_t *left_hi,
 const int64_t *right_wire,const int64_t *right_hi,const int64_t *input,const int64_t *input_hi,uint32_t input_at,
 const int64_t *forward,const int64_t *forward_hi,uint32_t forward_at,const int64_t *covector,const int64_t *covector_hi,uint32_t covector_at,
 const int64_t *incoming,const int64_t *incoming_hi,uint32_t incoming_at,uint32_t d,uint32_t count,uint32_t nnz,uint32_t rank,uint32_t grain,
 int64_t *work_wire,int64_t *ports,int64_t *ports_hi,int64_t *currents,int64_t *currents_hi,int64_t *bounds,int64_t *bounds_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
){
 if(blockIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 const uint32_t width=d+2u*count;
 if(!d||(d&1u)||!count||grain<1u||grain>120u||(input_at&1u)||(forward_at&1u)||(covector_at&1u)||(incoming_at&1u)){if(!threadIdx.x)atomicOr(slot,REFUSED_MALFORMED);return;}
 const wide *x=(const wide*)(input+input_at),*y=(const wide*)(forward+forward_at),*g=(const wide*)(covector+covector_at),*h=(const wide*)(incoming+incoming_at);
 if(!threadIdx.x){
  factor_sealed(input+input_at,input_hi+input_at,2u*((size_t)width+1u),slot);factor_sealed(forward+forward_at,forward_hi+forward_at,2u*((size_t)width+1u),slot);
  factor_sealed(covector+covector_at,covector_hi+covector_at,2u*((size_t)width+1u),slot);factor_sealed(incoming+incoming_at,incoming_hi+incoming_at,2u*((size_t)width+1u),slot);
  if(x[width]<0||y[width]<0||g[width]<0||h[width]<0)atomicOr(slot,REFUSED_MALFORMED);
 }
 __syncthreads();if(*slot)return;
 wide *rounds=(wide*)work_wire;
 for(uint32_t i=threadIdx.x;i<d;i+=blockDim.x){
  wide sum=add_checked(h[i],g[i],slot);((wide*)ports)[i]=sum/2;rounds[i]=(wide)(sum%2!=0);
  ((wide*)ports)[d+i]=add_checked(x[i],y[i],slot);
 }
 for(uint32_t i=threadIdx.x;i<2u*count;i+=blockDim.x){
  ((wide*)currents)[i]=sub_checked(x[d+i],y[d+i],slot);
  wide diff=sub_checked(g[d+i],h[d+i],slot);((wide*)currents)[2u*count+i]=diff/2;rounds[d+i]=(wide)(diff%2!=0);
 }
 __syncthreads();if(*slot)return;
 if(!threadIdx.x){
  wide rxy=add_checked(x[width],y[width],slot),rhg=add_checked(h[width],g[width],slot),rp=0,rc=0;
  for(uint32_t i=0;i<d;++i)rp=add_checked(rp,rounds[i],slot);
  for(uint32_t i=0;i<2u*count;++i)rc=add_checked(rc,rounds[d+i],slot);
  wide half=rhg/2+(wide)(rhg%2!=0);
  ((wide*)bounds)[0]=add_checked(rxy,add_checked(half,rp,slot),slot);
  ((wide*)bounds)[1]=add_checked(rxy,add_checked(half,rc,slot),slot);
 }
 __syncthreads();if(*slot)return;
 for(size_t i=threadIdx.x;i<4u*(size_t)d;i+=blockDim.x)ports_hi[i]=ports[i];
 for(size_t i=threadIdx.x;i<8u*(size_t)count;i+=blockDim.x)currents_hi[i]=currents[i];
 for(size_t i=threadIdx.x;i<4u;i+=blockDim.x)bounds_hi[i]=bounds[i];
}
