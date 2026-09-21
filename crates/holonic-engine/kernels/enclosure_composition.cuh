// Composition of existing dyadic enclosure rows. A row owns its output and refusal word;
// the following reduction joins every refusal after all rows, independent of scheduling.
__device__ uint32_t *ec_status(int64_t *flags,uint32_t row){
 uint32_t *status=(uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);for(uint32_t i=0;i<SLOT_WORDS;++i)status[i]=0;return status;
}
__device__ bool ec_ball(const int64_t *lo,const int64_t *hi,uint32_t d,uint32_t *status){
 for(size_t j=0;j<2u*((size_t)d+1u);++j)if(lo[j]!=hi[j])atomicOr(status,REFUSED_MALFORMED);
 if(((const wide *)lo)[d]<0)atomicOr(status,REFUSED_MALFORMED);
 return !*status;
}
__device__ wide ec_ceil(MomentInteger n,MomentInteger den,uint32_t *status){
 bool rem=false;wide q=normal_grid(exact_divide_positive(n,den,&rem),0,false,status);
 return add_checked(q,(wide)rem,status);
}
__device__ wide ec_l1(const wide *x,uint32_t d,uint32_t *status){
 MomentInteger sum;for(uint32_t i=0;i<d;++i)sum=sum+normal_abs(normal_wide(x[i]));
 return normal_grid(sum,0,false,status);
}
__device__ void ec_seal(int64_t *lo,int64_t *hi,uint32_t d,uint32_t *status){
 if(!*status)for(size_t j=0;j<2u*((size_t)d+1u);++j)hi[j]=lo[j];
}
extern "C" __global__ void section_enclosure_collect_row_status(
 const int64_t *flags,uint32_t rows,uint32_t *slot){
 // Every row was admitted under the same lane lineage; fold its complete receipt after all
 // row kernels finish, preserving the shared upstream metadata while ORing local refusals.
 uint32_t row=blockIdx.x*blockDim.x+threadIdx.x;
 if(row>=rows)return;
 const uint32_t *source=(const uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);
 atomicOr(slot+SLOT_REFUSED,source[SLOT_REFUSED]);
 atomicOr(slot+SLOT_UPSTREAM_FLAGS,source[SLOT_UPSTREAM_FLAGS]);
 atomicMax(slot+SLOT_UPSTREAM_COUNT,source[SLOT_UPSTREAM_COUNT]);
 atomicMax(slot+SLOT_LINEAGE,source[SLOT_LINEAGE]);
 if(source[SLOT_UPSTREAM_FIRST]){
  const uint32_t previous=atomicCAS(slot+SLOT_UPSTREAM_FIRST,0u,source[SLOT_UPSTREAM_FIRST]);
  if(previous)atomicMin(slot+SLOT_UPSTREAM_FIRST,source[SLOT_UPSTREAM_FIRST]);
 }
}
extern "C" __global__ void section_enclosure_gather_phase(
 const int64_t *x,const int64_t *xh,const int64_t *map,const int64_t *mh,
 uint32_t input_rows,uint32_t rows,uint32_t d,uint32_t out_d,
 int64_t *out,int64_t *oh,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const int64_t *m=map+4u*(size_t)row;
 for(uint32_t j=0;j<4;++j)if(m[j]!=mh[4u*(size_t)row+j])atomicOr(status,REFUSED_MALFORMED);
 if(m[0]<0||(uint64_t)m[0]>=input_rows||m[3]<=0||!d||(d&1u)||!out_d||(out_d&1u))atomicOr(status,REFUSED_MALFORMED);
 if(*status)return;
 const int64_t *a=x+2u*((size_t)d+1u)*m[0],*ah=xh+2u*((size_t)d+1u)*m[0];
 if(!ec_ball(a,ah,d,status))return;
 const wide *v=(const wide*)a;int64_t *ow=out+2u*((size_t)out_d+1u)*row;wide *y=(wide*)ow;wide round=0;
 for(uint32_t j=0;j<out_d;j+=2u){
  if(j>=d){y[j]=y[j+1u]=0;continue;}
  MomentInteger re,im;normal_product(re,im,normal_wide(v[j]),normal_wide(v[j+1u]),normal_wide(m[1]),normal_wide(m[2]),false);
  bool r=false,i=false;y[j]=normal_grid(exact_divide_positive(re,normal_wide(m[3]),&r),0,false,status);
  y[j+1u]=normal_grid(exact_divide_positive(im,normal_wide(m[3]),&i),0,false,status);
  round=add_checked(round,(wide)r+(wide)i,status);
 }
 y[out_d]=add_checked(v[d],round,status);ec_seal(ow,oh+2u*((size_t)out_d+1u)*row,out_d,status);
}
extern "C" __global__ void section_enclosure_scatter_phase_adjoint(
 const int64_t *x,const int64_t *xh,const int64_t *offsets,const int64_t *offsets_hi,
 const int64_t *entries,const int64_t *entries_hi,
 uint32_t rows,uint32_t output_rows,uint32_t d,
 int64_t *out,int64_t *oh,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=output_rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 int64_t *ow=out+2u*((size_t)d+1u)*row;wide *y=(wide*)ow;for(uint32_t j=0;j<=d;++j)y[j]=0;
 const int64_t *lo=offsets+(size_t)row,*hi=offsets_hi+(size_t)row;
 const int64_t *next=offsets+(size_t)(row+1),*next_hi=offsets_hi+(size_t)(row+1);
 if(lo[0]!=hi[0]||next[0]!=next_hi[0]
    ||lo[0]<0||next[0]<lo[0]||next[0]>(int64_t)rows){atomicOr(status,REFUSED_MALFORMED);return;}
 uint32_t start=(uint32_t)lo[0],end=(uint32_t)next[0];
 for(uint32_t at=start;at<end;++at){
  const int64_t *m=entries+4u*(size_t)at,*mh=entries_hi+4u*(size_t)at;
  for(uint32_t j=0;j<4;++j)if(m[j]!=mh[j])atomicOr(status,REFUSED_MALFORMED);
  if(m[0]<0||(uint64_t)m[0]>=rows||m[3]<=0){atomicOr(status,REFUSED_MALFORMED);return;}
  const int64_t *a=x+2u*((size_t)d+1u)*(uint32_t)m[0],*ah=xh+2u*((size_t)d+1u)*(uint32_t)m[0];
  if(!ec_ball(a,ah,d,status))return;const wide *v=(const wide*)a;
  y[d]=add_checked(y[d],v[d],status);
  for(uint32_t j=0;j<d;j+=2u){
   MomentInteger re,im;normal_product(re,im,normal_wide(v[j]),normal_wide(v[j+1u]),normal_wide(m[1]),normal_wide(m[2]),true);
   bool r=false,i=false;wide re_value=normal_grid(exact_divide_positive(re,normal_wide(m[3]),&r),0,false,status);
   wide im_value=normal_grid(exact_divide_positive(im,normal_wide(m[3]),&i),0,false,status);
   y[j]=add_checked(y[j],re_value,status);y[j+1u]=add_checked(y[j+1u],im_value,status);
   y[d]=add_checked(y[d],(wide)r+(wide)i,status);
  }
 }
 ec_seal(ow,oh+2u*((size_t)d+1u)*row,d,status);
}
// Copy complete enclosure packets from a resident row table. The table stores
// [lower pointer, upper pointer, row count, output offset] for each source; the
// output radius word therefore travels with the same row as every coordinate.
extern "C" __global__ void section_enclosure_concatenate_rows(
 const int64_t *table,const int64_t *table_hi,uint32_t source_count,uint32_t source_width,
 uint32_t output_rows,int64_t *out,int64_t *out_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=output_rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const int64_t *source_lo=nullptr,*source_hi=nullptr;uint32_t local=0;bool found=false;
 for(uint32_t at=0;at<source_count;++at){
  const int64_t *m=table+4u*(size_t)at,*mh=table_hi+4u*(size_t)at;
  for(uint32_t j=0;j<4;++j)if(m[j]!=mh[j])atomicOr(status,REFUSED_MALFORMED);
  if(m[2]<0||m[3]<0){atomicOr(status,REFUSED_MALFORMED);continue;}
  uint64_t count=(uint64_t)m[2],offset=(uint64_t)m[3];
  if(count>UINT32_MAX||offset>UINT32_MAX||offset+count<offset){atomicOr(status,REFUSED_MALFORMED);continue;}
  if(!found&&row>=offset&&row<offset+count){
   source_lo=(const int64_t *)(uintptr_t)(uint64_t)m[0];
   source_hi=(const int64_t *)(uintptr_t)(uint64_t)m[1];
   local=row-(uint32_t)offset;found=true;
  }
 }
 if(*status||!found||!source_width){atomicOr(status,REFUSED_MALFORMED);return;}
 int64_t *destination=out+(size_t)row*source_width,*destination_hi=out_hi+(size_t)row*source_width;
 const int64_t *source=source_lo+(size_t)local*source_width,*source_upper=source_hi+(size_t)local*source_width;
 for(uint32_t j=0;j<source_width;++j){destination[j]=source[j];destination_hi[j]=source_upper[j];}
}
// H seed +(I-H)((1-mu)seed+mu generated), mu=2^-step_bits.
extern "C" __global__ void section_enclosure_refine_rows(
 const int64_t *generated,const int64_t *gh,const int64_t *seed,const int64_t *sh,
 const int64_t *held,const int64_t *hh,uint32_t rows,uint32_t d,uint32_t step_bits,
 int64_t *out,int64_t *oh,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 if(step_bits>120u){atomicOr(status,REFUSED_MALFORMED);return;}
 const size_t stride=2u*((size_t)d+1u);const int64_t *a=generated+stride*row,*b=seed+stride*row;
 if(!ec_ball(a,gh+stride*row,d,status)||!ec_ball(b,sh+stride*row,d,status))return;
 const wide *g=(const wide*)a,*s=(const wide*)b;wide *y=(wide*)(out+stride*row);
 wide divisor=(wide)((uwide)1<<step_bits),round=0;bool any_held=false,any_free=false;
 for(uint32_t j=0;j<d;++j){
  size_t mi=(size_t)row*(d/2u)+j/2u;int64_t fixed=held[mi];
  if(fixed!=hh[mi]||(fixed!=0&&fixed!=1)){atomicOr(status,REFUSED_MALFORMED);return;}
  if(fixed){y[j]=s[j];any_held=true;}else{
   any_free=true;bool r=false;MomentInteger num=normal_wide(s[j])*normal_wide(divisor-1)+normal_wide(g[j]);
   y[j]=normal_grid(exact_divide_positive(num,normal_wide(divisor),&r),0,false,status);round=add_checked(round,(wide)r,status);
  }
 }
 MomentInteger radius=normal_wide(s[d])*normal_wide(any_held?divisor:(any_free?divisor-1:0));
 if(any_free)radius=radius+normal_wide(g[d]);
 y[d]=add_checked(ec_ceil(radius,normal_wide(divisor),status),round,status);
 ec_seal(out+stride*row,oh+stride*row,d,status);
}
extern "C" __global__ void section_enclosure_bilinear_features(
 const int64_t *source,const int64_t *source_hi,const int64_t *condition,const int64_t *condition_hi,
 uint32_t rows,uint32_t d,uint32_t k,uint32_t grain,
 int64_t *out,int64_t *oh,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 if(grain<1||grain>120||!d||!k||(d&1u)||(k&1u)){atomicOr(status,REFUSED_MALFORMED);return;}
 const int64_t *sw=source+2u*((size_t)d+1u)*row,*cw=condition+2u*((size_t)k+1u)*row;
 if(!ec_ball(sw,source_hi+2u*((size_t)d+1u)*row,d,status)||!ec_ball(cw,condition_hi+2u*((size_t)k+1u)*row,k,status))return;
 const wide *s=(const wide*)sw,*c=(const wide*)cw;wide S=(wide)((uwide)1<<grain),round=0;
 const size_t f=(size_t)d+k+(size_t)d*(k/2u);int64_t *ow=out+2u*(f+1u)*row;wide *y=(wide*)ow;
 for(uint32_t i=0;i<d;++i)y[i]=s[i];for(uint32_t j=0;j<k;++j)y[d+j]=c[j];
 for(uint32_t j=0;j<k;j+=2u)for(uint32_t i=0;i<d;i+=2u){
  size_t at=d+k+(size_t)(j/2u)*d+i;MomentInteger re,im;
  normal_product(re,im,normal_wide(s[i]),normal_wide(s[i+1u]),normal_wide(c[j]),normal_wide(c[j+1u]),false);
  bool rr=false,ri=false;y[at]=normal_grid(exact_divide_positive(re,normal_wide(S),&rr),0,false,status);
  y[at+1u]=normal_grid(exact_divide_positive(im,normal_wide(S),&ri),0,false,status);round=add_checked(round,(wide)rr+(wide)ri,status);
 }
 MomentInteger radius=normal_wide(ec_l1(s,d,status))*normal_wide(c[k])+normal_wide(ec_l1(c,k,status))*normal_wide(s[d])+normal_wide(s[d])*normal_wide(c[k]);
 y[f]=add_checked(add_checked(add_checked(s[d],c[k],status),ec_ceil(radius,normal_wide(S),status),status),round,status);
 ec_seal(ow,oh+2u*(f+1u)*row,(uint32_t)f,status);
}
extern "C" __global__ void section_enclosure_bilinear_adjoint(
 const int64_t *source,const int64_t *source_hi,const int64_t *condition,const int64_t *condition_hi,
 const int64_t *covector,const int64_t *covector_hi,uint32_t rows,uint32_t d,uint32_t k,uint32_t grain,
 int64_t *source_out,int64_t *source_oh,int64_t *condition_out,int64_t *condition_oh,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const size_t f=(size_t)d+k+(size_t)d*(k/2u);
 const int64_t *sw=source+2u*((size_t)d+1u)*row,*cw=condition+2u*((size_t)k+1u)*row,*gw=covector+2u*(f+1u)*row;
 if(!ec_ball(sw,source_hi+2u*((size_t)d+1u)*row,d,status)||!ec_ball(cw,condition_hi+2u*((size_t)k+1u)*row,k,status)||!ec_ball(gw,covector_hi+2u*(f+1u)*row,(uint32_t)f,status))return;
 const wide *s=(const wide*)sw,*c=(const wide*)cw,*g=(const wide*)gw;wide S=(wide)((uwide)1<<grain);
 wide *ys=(wide*)(source_out+2u*((size_t)d+1u)*row),*yc=(wide*)(condition_out+2u*((size_t)k+1u)*row);
 wide sr=0,cr=0;
 for(uint32_t i=0;i<d;i+=2u){
  MomentInteger re=normal_wide(g[i])*normal_wide(S),im=normal_wide(g[i+1u])*normal_wide(S);
  for(uint32_t j=0;j<k;j+=2u){size_t at=d+k+(size_t)(j/2u)*d+i;
   normal_product(re,im,normal_wide(g[at]),normal_wide(g[at+1u]),normal_wide(c[j]),normal_wide(c[j+1u]),true);}
  bool rr=false,ri=false;ys[i]=normal_grid(exact_divide_positive(re,normal_wide(S),&rr),0,false,status);
  ys[i+1u]=normal_grid(exact_divide_positive(im,normal_wide(S),&ri),0,false,status);sr=add_checked(sr,(wide)rr+(wide)ri,status);
 }
 for(uint32_t j=0;j<k;j+=2u){
  MomentInteger re=normal_wide(g[d+j])*normal_wide(S),im=normal_wide(g[d+j+1u])*normal_wide(S);
  for(uint32_t i=0;i<d;i+=2u){size_t at=d+k+(size_t)(j/2u)*d+i;
   normal_product(re,im,normal_wide(g[at]),normal_wide(g[at+1u]),normal_wide(s[i]),normal_wide(s[i+1u]),true);}
  bool rr=false,ri=false;yc[j]=normal_grid(exact_divide_positive(re,normal_wide(S),&rr),0,false,status);
  yc[j+1u]=normal_grid(exact_divide_positive(im,normal_wide(S),&ri),0,false,status);cr=add_checked(cr,(wide)rr+(wide)ri,status);
 }
 wide gn=ec_l1(g,(uint32_t)f,status),sn=ec_l1(s,d,status),cn=ec_l1(c,k,status);
 MomentInteger rs=(normal_wide(S)+normal_wide(cn))*normal_wide(g[f])+normal_wide(c[k])*normal_wide(gn)+normal_wide(c[k])*normal_wide(g[f]);
 MomentInteger rc=(normal_wide(S)+normal_wide(sn))*normal_wide(g[f])+normal_wide(s[d])*normal_wide(gn)+normal_wide(s[d])*normal_wide(g[f]);
 ys[d]=add_checked(ec_ceil(rs,normal_wide(S),status),sr,status);yc[k]=add_checked(ec_ceil(rc,normal_wide(S),status),cr,status);
 ec_seal(source_out+2u*((size_t)d+1u)*row,source_oh+2u*((size_t)d+1u)*row,d,status);
 ec_seal(condition_out+2u*((size_t)k+1u)*row,condition_oh+2u*((size_t)k+1u)*row,k,status);
}
extern "C" __global__ void section_normal_enclosed_adjoint(
 const int64_t *state,const int64_t *state_hi,const int64_t *covector,const int64_t *covector_hi,
 uint32_t rows,uint32_t sources,uint32_t targets,uint32_t grain,
 int64_t *out,int64_t *oh,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const uint32_t d=2u*sources,t=2u*targets;const size_t matrix=(size_t)d*targets;
 for(size_t j=0;j<2u*matrix;++j)if(state[j]!=state_hi[j])atomicOr(status,REFUSED_MALFORMED);
 const int64_t *gw=covector+2u*((size_t)t+1u)*row;
 if(*status||!ec_ball(gw,covector_hi+2u*((size_t)t+1u)*row,t,status))return;
 const wide *M=(const wide*)state,*g=(const wide*)gw;wide *y=(wide*)(out+2u*((size_t)d+1u)*row);
 wide S=(wide)((uwide)1<<grain),round=0;MomentInteger norm;
 for(size_t j=0;j<matrix;++j)norm=norm+normal_abs(normal_wide(M[j]));
 for(uint32_t i=0;i<d;i+=2u){MomentInteger re,im;
  for(uint32_t j=0;j<targets;++j)normal_product(re,im,normal_wide(g[2u*j]),normal_wide(g[2u*j+1u]),normal_wide(M[(size_t)j*d+i]),normal_wide(M[(size_t)j*d+i+1u]),true);
  bool rr=false,ri=false;y[i]=normal_grid(exact_divide_positive(re,normal_wide(S),&rr),0,false,status);
  y[i+1u]=normal_grid(exact_divide_positive(im,normal_wide(S),&ri),0,false,status);round=add_checked(round,(wide)rr+(wide)ri,status);
 }
 y[d]=add_checked(ec_ceil(norm*normal_wide(g[t]),normal_wide(S),status),round,status);
 ec_seal(out+2u*((size_t)d+1u)*row,oh+2u*((size_t)d+1u)*row,d,status);
}
