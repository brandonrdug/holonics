// Phase transport: bounded bilinear logits -> existing normalized receiver -> weighted current.
// The same receiver supplies h=J_p r in reverse. All other operations compose the existing
// outward MaterialInterval arithmetic, on row-owned flags, with separate status union.
__device__ MaterialInterval phase_coordinate(const wide *v,uint32_t d,uint32_t j,uint32_t *status){
 return {sub_checked(v[j],v[d],status),add_checked(v[j],v[d],status)};
}
__device__ MaterialInterval phase_scale(MaterialInterval a,int64_t m,int32_t e,uint32_t *status){
 wide lo,hi,discard;
 if(m>=0){dyadic_scale(a.lo,m,e,&lo,&discard,status);dyadic_scale(a.hi,m,e,&discard,&hi,status);}
 else{dyadic_scale(a.hi,m,e,&lo,&discard,status);dyadic_scale(a.lo,m,e,&discard,&hi,status);}
 return {lo,hi};
}
__device__ void phase_pack(const wide *lo,const wide *hi,wide *out,uint32_t d,uint32_t *status){
 wide radius=0;
 for(uint32_t j=0;j<d;++j){
  if(hi[j]<lo[j]){atomicOr(status,REFUSED_INVERTED);return;}
  wide r=add_checked(sub_checked(hi[j],lo[j],status),1,status)>>1;
  out[j]=add_checked(lo[j],r,status);radius=add_checked(radius,r,status);
 }
 out[d]=radius;
}
extern "C" __global__ void section_phase_participation(
 const int64_t *query,const int64_t *query_hi,const int64_t *neighbors,const int64_t *neighbors_hi,
 uint32_t rows,uint32_t neighbors_per_row,uint32_t components,uint32_t grain,int64_t beta_m,int32_t beta_e,
 int64_t *logits,int64_t *logits_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const size_t w=(size_t)components+1u,pw=2u*(size_t)neighbors_per_row+1u;
 const int64_t *qw=query+2u*w*row,*qh=query_hi+2u*w*row;
 if(!ec_ball(qw,qh,components,status))return;const wide *q=(const wide*)qw;
 wide *out=(wide*)logits+pw*row,*oh=(wide*)logits_hi+pw*row;wide radius=0;
 for(uint32_t j=0;j<neighbors_per_row;++j){
  const size_t at=((size_t)row*neighbors_per_row+j)*2u*w;
  if(!ec_ball(neighbors+at,neighbors_hi+at,components,status))return;
  const wide *u=(const wide*)(neighbors+at);MaterialInterval score={0,0};
  for(uint32_t d=0;d<components;++d)score=mp_add(score,mp_mul(phase_coordinate(q,components,d,status),phase_coordinate(u,components,d,status),grain,status),status);
  score=phase_scale(score,beta_m,beta_e,status);
  wide r=add_checked(sub_checked(score.hi,score.lo,status),1,status)>>1;
  out[2u*j]=add_checked(score.lo,r,status);out[2u*j+1u]=0;radius=add_checked(radius,r,status);
 }
 out[pw-1u]=radius;ec_seal((int64_t*)out,(int64_t*)oh,(uint32_t)pw-1u,status);
}
// The existing normalized receiver supplies a REAL simplex.  Anchor its centre
// calculation to one value so a common translation is transported exactly. The
// value-ball contribution is max r_i, independent of the number of coordinates.
__device__ void phase_joint_weighted(
 const int64_t *neighbors,const int64_t *neighbors_hi,const wide *p,
 uint32_t n,uint32_t d,uint32_t grain,wide *y,wide *yh,uint32_t *status){
 const size_t stride=2u*((size_t)d+1u);const wide *base=(const wide*)neighbors;
 if(!ec_ball(neighbors,neighbors_hi,d,status))return;
 wide largest=0;HistoryInteger contrast_square;
 const wide unit=((wide)1)<<grain;
 for(uint32_t k=0;k<d;++k)y[k]=yh[k]=base[k];
 for(uint32_t j=0;j<n;++j){
  size_t at=stride*j;if(!ec_ball(neighbors+at,neighbors_hi+at,d,status))return;
  const wide *v=(const wide*)(neighbors+at);
  if(p[2u*j]<0 || p[2u*j]>unit || p[2u*j+1u]){atomicOr(status,REFUSED_MALFORMED);return;}
  if(v[d]>largest)largest=v[d];
  if(!j)continue;
  for(uint32_t k=0;k<d;++k){
   wide delta=sub_checked(v[k],base[k],status);
   HistoryInteger value=history_integer(delta);contrast_square=contrast_square+value*value;
   MaterialInterval term=mp_mul(mp_point(p[2u*j]),mp_point(delta),grain,status);
   y[k]=add_checked(y[k],term.lo,status);yh[k]=add_checked(yh[k],term.hi,status);
  }
 }
 phase_pack(y,yh,y,d,status);
 wide weight_error=ft_ceil_product(p[2u*n],history_norm_ceiling(contrast_square,status),grain,status);
 y[d]=add_checked(y[d],add_checked(weight_error,largest,status),status);
}
// J_p annihilates the common term <g,v_0>.  Removing it BEFORE enclosing
// the score covector avoids inventing uncertainty in that constant direction.
__device__ void phase_joint_terms(
 const int64_t *neighbors,const int64_t *neighbors_hi,const wide *g,const wide *gp,
 uint32_t n,uint32_t d,uint32_t grain,wide *out,uint32_t *status){
 const size_t stride=2u*((size_t)d+1u);const wide *base=(const wide*)neighbors;
 if(!ec_ball(neighbors,neighbors_hi,d,status))return;
 if(n==1u){out[0]=out[1]=out[2]=0;return;}
 wide gnorm=complete_norm(g,d,status);HistoryInteger error_square;
 for(uint32_t j=0;j<n;++j){
  const size_t at=stride*j;if(!ec_ball(neighbors+at,neighbors_hi+at,d,status))return;
  const wide *v=(const wide*)(neighbors+at);
  MaterialInterval dot=mp_point(gp?sub_checked(gp[2u*j],gp[0],status):0);
  HistoryInteger delta_square;
  if(j)for(uint32_t k=0;k<d;++k){
   wide delta=sub_checked(v[k],base[k],status);HistoryInteger value=history_integer(delta);
   delta_square=delta_square+value*value;
   dot=mp_add(dot,mp_mul(mp_point(g[k]),mp_point(delta),grain,status),status);
  }
  wide delta_radius=j?add_checked(v[d],base[d],status):0;
  wide source_error=add_checked(ft_ceil_product(gnorm,delta_radius,grain,status),
   ft_ceil_product(g[d],add_checked(history_norm_ceiling(delta_square,status),delta_radius,status),grain,status),status);
  wide round=add_checked(sub_checked(dot.hi,dot.lo,status),1,status)>>1;
  out[2u*j]=add_checked(dot.lo,round,status);out[2u*j+1u]=0;
  HistoryInteger e=history_integer(add_checked(source_error,round,status));error_square=error_square+e*e;
 }
 out[2u*n]=add_checked(history_norm_ceiling(error_square,status),gp?gp[2u*n]:0,status);
}
extern "C" __global__ void section_phase_participation_weighted(
 const int64_t *neighbors,const int64_t *neighbors_hi,const int64_t *participation,const int64_t *participation_hi,
 uint32_t rows,uint32_t neighbors_per_row,uint32_t components,uint32_t grain,uint32_t joint,
 int64_t *output,int64_t *output_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const size_t w=(size_t)components+1u,pw=2u*(size_t)neighbors_per_row+1u;
 const int64_t *pp=participation+2u*pw*row,*ph=participation_hi+2u*pw*row;
 if(!ec_ball(pp,ph,(uint32_t)pw-1u,status))return;const wide *p=(const wide*)pp;
 wide *y=(wide*)output+w*row,*yh=(wide*)output_hi+w*row;
 if(joint){
  if(joint!=1u){atomicOr(status,REFUSED_MALFORMED);return;}
  size_t first=2u*w*(size_t)row*neighbors_per_row;
  phase_joint_weighted(neighbors+first,neighbors_hi+first,p,neighbors_per_row,components,grain,y,yh,status);
  ec_seal((int64_t*)y,(int64_t*)yh,components,status);return;
 }
 for(uint32_t d=0;d<components;++d){y[d]=0;yh[d]=0;}
 for(uint32_t j=0;j<neighbors_per_row;++j){
  size_t at=((size_t)row*neighbors_per_row+j)*2u*w;
  if(!ec_ball(neighbors+at,neighbors_hi+at,components,status))return;const wide *u=(const wide*)(neighbors+at);
  MaterialInterval a=phase_coordinate(p,(uint32_t)pw-1u,2u*j,status);
  for(uint32_t d=0;d<components;++d){MaterialInterval v=mp_mul(a,phase_coordinate(u,components,d,status),grain,status);y[d]=add_checked(y[d],v.lo,status);yh[d]=add_checked(yh[d],v.hi,status);}
 }
 phase_pack(y,yh,y,components,status);ec_seal((int64_t*)y,(int64_t*)yh,components,status);
}
extern "C" __global__ void section_phase_participation_terms(
 const int64_t *neighbors,const int64_t *neighbors_hi,const int64_t *gy,const int64_t *gy_hi,const int64_t *gp,const int64_t *gp_hi,
 uint32_t rows,uint32_t neighbors_per_row,uint32_t components,uint32_t grain,uint32_t joint,
 int64_t *terms,int64_t *terms_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const size_t w=(size_t)components+1u,pw=2u*(size_t)neighbors_per_row+1u;
 if(!ec_ball(gy+2u*w*row,gy_hi+2u*w*row,components,status))return;
 if(gp&&!ec_ball(gp+2u*pw*row,gp_hi+2u*pw*row,(uint32_t)pw-1u,status))return;
 const wide *g=(const wide*)gy+w*row,*gc=gp?(const wide*)gp+pw*row:nullptr;
 wide *r=(wide*)terms+pw*row,*rh=(wide*)terms_hi+pw*row;wide radius=0;
 if(joint){
  if(joint!=1u){atomicOr(status,REFUSED_MALFORMED);return;}
  size_t first=2u*w*(size_t)row*neighbors_per_row;
  phase_joint_terms(neighbors+first,neighbors_hi+first,g,gc,neighbors_per_row,components,grain,r,status);
  ec_seal((int64_t*)r,(int64_t*)rh,(uint32_t)pw-1u,status);return;
 }
 for(uint32_t j=0;j<neighbors_per_row;++j){
  const size_t at=((size_t)row*neighbors_per_row+j)*2u*w;
  if(!ec_ball(neighbors+at,neighbors_hi+at,components,status))return;const wide *u=(const wide*)(neighbors+at);
  MaterialInterval value=gc?phase_coordinate(gc,(uint32_t)pw-1u,2u*j,status):mp_point(0);
  for(uint32_t d=0;d<components;++d)value=mp_add(value,mp_mul(phase_coordinate(g,components,d,status),phase_coordinate(u,components,d,status),grain,status),status);
  wide rr=add_checked(sub_checked(value.hi,value.lo,status),1,status)>>1;
  r[2u*j]=add_checked(value.lo,rr,status);r[2u*j+1u]=0;radius=add_checked(radius,rr,status);
 }
 r[pw-1u]=radius;ec_seal((int64_t*)r,(int64_t*)rh,(uint32_t)pw-1u,status);
}
extern "C" __global__ void section_phase_participation_adjoint(
 const int64_t *query,const int64_t *query_hi,const int64_t *neighbors,const int64_t *neighbors_hi,
 const int64_t *participation,const int64_t *participation_hi,const int64_t *h,const int64_t *h_hi,const int64_t *gy,const int64_t *gy_hi,
 uint32_t rows,uint32_t neighbors_per_row,uint32_t components,uint32_t grain,int64_t beta_m,int32_t beta_e,
 int64_t *source,int64_t *source_hi,int64_t *returned,int64_t *returned_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 const size_t w=(size_t)components+1u,pw=2u*(size_t)neighbors_per_row+1u;
 if(!ec_ball(query+2u*w*row,query_hi+2u*w*row,components,status)||!ec_ball(gy+2u*w*row,gy_hi+2u*w*row,components,status)
  ||!ec_ball(participation+2u*pw*row,participation_hi+2u*pw*row,(uint32_t)pw-1u,status)||!ec_ball(h+2u*pw*row,h_hi+2u*pw*row,(uint32_t)pw-1u,status))return;
 const wide *q=(const wide*)query+w*row,*g=(const wide*)gy+w*row,*p=(const wide*)participation+pw*row,*hv=(const wide*)h+pw*row;
 wide *dq=(wide*)source+w*row,*dqh=(wide*)source_hi+w*row;
 for(uint32_t d=0;d<components;++d){dq[d]=0;dqh[d]=0;}
 for(uint32_t j=0;j<neighbors_per_row;++j){
  const size_t at=((size_t)row*neighbors_per_row+j)*2u*w;
  if(!ec_ball(neighbors+at,neighbors_hi+at,components,status))return;const wide *u=(const wide*)(neighbors+at);
  const MaterialInterval a=phase_coordinate(p,(uint32_t)pw-1u,2u*j,status),b=phase_scale(phase_coordinate(hv,(uint32_t)pw-1u,2u*j,status),beta_m,beta_e,status);
  wide *du=(wide*)(returned+at),*duh=(wide*)(returned_hi+at);
  for(uint32_t d=0;d<components;++d){
   const MaterialInterval qpart=mp_mul(b,phase_coordinate(u,components,d,status),grain,status);
   dq[d]=add_checked(dq[d],qpart.lo,status);dqh[d]=add_checked(dqh[d],qpart.hi,status);
   const MaterialInterval upart=mp_add(mp_mul(a,phase_coordinate(g,components,d,status),grain,status),mp_mul(b,phase_coordinate(q,components,d,status),grain,status),status);
   du[d]=upart.lo;duh[d]=upart.hi;
  }
  phase_pack(du,duh,du,components,status);ec_seal((int64_t*)du,(int64_t*)duh,components,status);
 }
 phase_pack(dq,dqh,dq,components,status);ec_seal((int64_t*)dq,(int64_t*)dqh,components,status);
}
// The complex pair potential s_j = beta <q|u_j> has Re s_j = the bilinear score above and
// Im s_j = beta sum_d (q_re u_im - q_im u_re) over the (re,im) pairs of the real-coded chart.
// Its phase face is phi_j = Im s_j / 2; the magnitude face p = softmax(Re s) is unchanged, so the
// participation and its weighted output do not read phi. Returned as a ball of the logits chart:
// phi in the real slot, exactly zero in the imaginary one.
__device__ MaterialInterval phase_imaginary_score(const wide *q,const wide *u,uint32_t components,uint32_t grain,uint32_t *status){
 MaterialInterval im={0,0};
 for(uint32_t d=0;d+1u<components;d+=2u){
  im=mp_add(im,mp_mul(phase_coordinate(q,components,d,status),phase_coordinate(u,components,d+1u,status),grain,status),status);
  im=mp_add(im,mp_neg(mp_mul(phase_coordinate(q,components,d+1u,status),phase_coordinate(u,components,d,status),grain,status),status),status);
 }
 return im;
}
extern "C" __global__ void section_phase_participation_phase(
 const int64_t *query,const int64_t *query_hi,const int64_t *neighbors,const int64_t *neighbors_hi,
 uint32_t rows,uint32_t neighbors_per_row,uint32_t components,uint32_t grain,int64_t beta_m,int32_t beta_e,
 int64_t *phase,int64_t *phase_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 if(components%2u){atomicOr(status,REFUSED_MALFORMED);return;}
 const size_t w=(size_t)components+1u,pw=2u*(size_t)neighbors_per_row+1u;
 const int64_t *qw=query+2u*w*row,*qh=query_hi+2u*w*row;
 if(!ec_ball(qw,qh,components,status))return;const wide *q=(const wide*)qw;
 wide *out=(wide*)phase+pw*row,*oh=(wide*)phase_hi+pw*row;wide radius=0;
 for(uint32_t j=0;j<neighbors_per_row;++j){
  const size_t at=((size_t)row*neighbors_per_row+j)*2u*w;
  if(!ec_ball(neighbors+at,neighbors_hi+at,components,status))return;
  const wide *u=(const wide*)(neighbors+at);
  // beta/2: the phase is half the imaginary potential.
  MaterialInterval value=phase_scale(phase_imaginary_score(q,u,components,grain,status),beta_m,beta_e-1,status);
  wide r=add_checked(sub_checked(value.hi,value.lo,status),1,status)>>1;
  out[2u*j]=add_checked(value.lo,r,status);out[2u*j+1u]=0;radius=add_checked(radius,r,status);
 }
 out[pw-1u]=radius;ec_seal((int64_t*)out,(int64_t*)oh,(uint32_t)pw-1u,status);
}
// The adjoint of phi_j = (beta/2) Im <q|u_j> for a covector g on the phase face (real slot g_j):
//   dq_re += (beta/2) sum_j g_j u_j,im    dq_im -= (beta/2) sum_j g_j u_j,re
//   du_j,re -= (beta/2) g_j q_im          du_j,im += (beta/2) g_j q_re
// These terms add to the magnitude face's own adjoint; the two faces read disjoint slots of s.
extern "C" __global__ void section_phase_participation_phase_adjoint(
 const int64_t *query,const int64_t *query_hi,const int64_t *neighbors,const int64_t *neighbors_hi,
 const int64_t *gphi,const int64_t *gphi_hi,
 uint32_t rows,uint32_t neighbors_per_row,uint32_t components,uint32_t grain,int64_t beta_m,int32_t beta_e,
 int64_t *source,int64_t *source_hi,int64_t *returned,int64_t *returned_hi,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 if(components%2u){atomicOr(status,REFUSED_MALFORMED);return;}
 const size_t w=(size_t)components+1u,pw=2u*(size_t)neighbors_per_row+1u;
 if(!ec_ball(query+2u*w*row,query_hi+2u*w*row,components,status)||!ec_ball(gphi+2u*pw*row,gphi_hi+2u*pw*row,(uint32_t)pw-1u,status))return;
 const wide *q=(const wide*)query+w*row,*g=(const wide*)gphi+pw*row;
 wide *dq=(wide*)source+w*row,*dqh=(wide*)source_hi+w*row;
 for(uint32_t d=0;d<components;++d){dq[d]=0;dqh[d]=0;}
 for(uint32_t j=0;j<neighbors_per_row;++j){
  const size_t at=((size_t)row*neighbors_per_row+j)*2u*w;
  if(!ec_ball(neighbors+at,neighbors_hi+at,components,status))return;const wide *u=(const wide*)(neighbors+at);
  const MaterialInterval b=phase_scale(phase_coordinate(g,(uint32_t)pw-1u,2u*j,status),beta_m,beta_e-1,status);
  wide *du=(wide*)(returned+at),*duh=(wide*)(returned_hi+at);
  for(uint32_t d=0;d+1u<components;d+=2u){
   const MaterialInterval qre=mp_mul(b,phase_coordinate(u,components,d+1u,status),grain,status);
   const MaterialInterval qim=mp_neg(mp_mul(b,phase_coordinate(u,components,d,status),grain,status),status);
   dq[d]=add_checked(dq[d],qre.lo,status);dqh[d]=add_checked(dqh[d],qre.hi,status);
   dq[d+1u]=add_checked(dq[d+1u],qim.lo,status);dqh[d+1u]=add_checked(dqh[d+1u],qim.hi,status);
   const MaterialInterval ure=mp_neg(mp_mul(b,phase_coordinate(q,components,d+1u,status),grain,status),status);
   const MaterialInterval uim=mp_mul(b,phase_coordinate(q,components,d,status),grain,status);
   du[d]=ure.lo;duh[d]=ure.hi;du[d+1u]=uim.lo;duh[d+1u]=uim.hi;
  }
  phase_pack(du,duh,du,components,status);ec_seal((int64_t*)du,(int64_t*)duh,components,status);
 }
 phase_pack(dq,dqh,dq,components,status);ec_seal((int64_t*)dq,(int64_t*)dqh,components,status);
}
