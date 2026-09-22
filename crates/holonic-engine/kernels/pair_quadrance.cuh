// The geometric score and its complete local return. Geometry and transported values have
// separate charts: q/u below are spatial receiver coordinates; value covectors live in v.
// Score = -beta |q-u|^2/2; h is returned by the existing normalized receiver.
__device__ MaterialInterval pair_square(MaterialInterval x,uint32_t grain,uint32_t *status){
 MaterialInterval a=mp_mul(mp_point(x.lo),mp_point(x.lo),grain,status);
 MaterialInterval b=mp_mul(mp_point(x.hi),mp_point(x.hi),grain,status);
 return {(x.lo<=0&&x.hi>=0)?0:(a.lo<b.lo?a.lo:b.lo),a.hi>b.hi?a.hi:b.hi};
}
extern "C" __global__ void section_pair_quadrance_logits(
 const int64_t *query,const int64_t *query_hi,const int64_t *neighbors,const int64_t *neighbors_hi,
 uint32_t rows,uint32_t n,uint32_t dimensions,uint32_t grain,int64_t beta_m,int32_t beta_e,
 int64_t *logits,int64_t *logits_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const size_t w=(size_t)dimensions+1,pw=2u*(size_t)n+1;
 if(!ec_ball(query+2*w*row,query_hi+2*w*row,dimensions,status))return;
 const wide *q=(const wide*)query+w*row;wide *out=(wide*)logits+pw*row,*hi=(wide*)logits_hi+pw*row;
 wide radius=0;
 for(uint32_t j=0;j<n;++j){
  size_t at=((size_t)row*n+j)*2*w;
  if(!ec_ball(neighbors+at,neighbors_hi+at,dimensions,status))return;
  const wide *u=(const wide*)(neighbors+at);MaterialInterval quadrance=mp_point(0);
  for(uint32_t d=0;d<dimensions;++d){
   MaterialInterval delta=mp_add(phase_coordinate(q,dimensions,d,status),mp_neg(phase_coordinate(u,dimensions,d,status),status),status);
   quadrance=mp_add(quadrance,pair_square(delta,grain,status),status);
  }
  MaterialInterval score=mp_neg(phase_scale(quadrance,beta_m,beta_e-1,status),status);
  wide r=add_checked(sub_checked(score.hi,score.lo,status),1,status)>>1;
  out[2*j]=add_checked(score.lo,r,status);out[2*j+1]=0;radius=add_checked(radius,r,status);
 }
 out[pw-1]=radius;ec_seal((int64_t*)out,(int64_t*)hi,(uint32_t)pw-1,status);
}
extern "C" __global__ void section_pair_quadrance_adjoint(
 const int64_t *query,const int64_t *query_hi,const int64_t *neighbors,const int64_t *neighbors_hi,
 const int64_t *participation,const int64_t *participation_hi,const int64_t *h,const int64_t *h_hi,
 const int64_t *gy,const int64_t *gy_hi,
 uint32_t rows,uint32_t n,uint32_t dimensions,uint32_t components,uint32_t grain,int64_t beta_m,int32_t beta_e,
 int64_t *dq,int64_t *dq_hi,int64_t *du,int64_t *du_hi,int64_t *dv,int64_t *dv_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const size_t w=(size_t)dimensions+1,vw=(size_t)components+1,pw=2u*(size_t)n+1;
 if(!ec_ball(query+2*w*row,query_hi+2*w*row,dimensions,status)
 ||!ec_ball(participation+2*pw*row,participation_hi+2*pw*row,(uint32_t)pw-1,status)
 ||!ec_ball(h+2*pw*row,h_hi+2*pw*row,(uint32_t)pw-1,status)
 ||!ec_ball(gy+2*vw*row,gy_hi+2*vw*row,components,status))return;
 const wide *q=(const wide*)query+w*row,*p=(const wide*)participation+pw*row,*hv=(const wide*)h+pw*row,*g=(const wide*)gy+vw*row;
 wide *qr=(wide*)dq+w*row,*qh=(wide*)dq_hi+w*row;
 for(uint32_t d=0;d<dimensions;++d){qr[d]=0;qh[d]=0;}
 for(uint32_t j=0;j<n;++j){
  const size_t index=(size_t)row*n+j,at=2*w*index;
  if(!ec_ball(neighbors+at,neighbors_hi+at,dimensions,status))return;
  const wide *u=(const wide*)(neighbors+at);
  MaterialInterval b=phase_scale(phase_coordinate(hv,(uint32_t)pw-1,2*j,status),beta_m,beta_e,status);
  MaterialInterval a=phase_coordinate(p,(uint32_t)pw-1,2*j,status);
  wide *ur=(wide*)du+w*index,*uh=(wide*)du_hi+w*index,*vr=(wide*)dv+vw*index,*vh=(wide*)dv_hi+vw*index;
  for(uint32_t d=0;d<dimensions;++d){
   MaterialInterval delta=mp_add(phase_coordinate(q,dimensions,d,status),mp_neg(phase_coordinate(u,dimensions,d,status),status),status);
   MaterialInterval back=mp_mul(b,delta,grain,status),negative=mp_neg(back,status);
   qr[d]=add_checked(qr[d],negative.lo,status);qh[d]=add_checked(qh[d],negative.hi,status);
   ur[d]=back.lo;uh[d]=back.hi;
  }
  for(uint32_t d=0;d<components;++d){MaterialInterval back=mp_mul(a,phase_coordinate(g,components,d,status),grain,status);vr[d]=back.lo;vh[d]=back.hi;}
  phase_pack(ur,uh,ur,dimensions,status);ec_seal((int64_t*)ur,(int64_t*)uh,dimensions,status);
  phase_pack(vr,vh,vr,components,status);ec_seal((int64_t*)vr,(int64_t*)vh,components,status);
 }
 phase_pack(qr,qh,qr,dimensions,status);ec_seal((int64_t*)qr,(int64_t*)qh,dimensions,status);
}
