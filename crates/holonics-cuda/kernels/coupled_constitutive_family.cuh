// Evaluate a dependent pair (x(theta), eta(theta)) at ONE parameter assignment. This is
// substitution in a family, not an assertion that theta is its actual latent cause. The
// retained original anchor must admit this assignment before any constitutive reaction.
extern "C" __global__ void section_coupled_family_operands(
 const int64_t *coeff,const int64_t *coeff_hi,uint32_t n,uint32_t kc,
 const int64_t *theta,const int64_t *theta_hi,const int64_t *anchor,const int64_t *anchor_hi,
 int64_t *source,int64_t *source_hi,int64_t *eta,int64_t *eta_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t t=8u*n+2u,s=6u*n,y=2u*n,f=s+2u*kc+s*kc,w=f+y;
 if(!n||!kc){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<2u*(4u*n+2u);++i)if(anchor[i]!=anchor_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 if(((const wide*)anchor)[0]!=0){atomicOr(slot,REFUSED_CARRIER);return;}
 for(size_t i=0;i<2u*(size_t)(t+1u)*(w+1u);++i)if(coeff[i]!=coeff_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide td=fibre_current_denominator(theta,theta_hi,t,UINT32_MAX,slot);
 for(uint32_t i=0;i<t;++i)if(theta[i]!=theta_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 const wide *c=(const wide*)coeff;wide cd=1;
 for(uint32_t row=0;row<=t;++row){wide d=c[(size_t)row*(w+1u)+w];
  if(d<=0){atomicOr(slot,REFUSED_MALFORMED);return;}cd=fibre_lcm(cd,d,slot);}
 wide den=product_checked(cd,td,slot);if(*slot)return;
 extern __shared__ wide values[];
 for(uint32_t j=0;j<s+y;++j){uint32_t at=j<s?j:f+j-s;wide v=0;
  for(uint32_t row=0;row<=t;++row){wide weight=row?theta[row-1u]:td;
   wide term=product_checked(c[(size_t)row*(w+1u)+at],cd/c[(size_t)row*(w+1u)+w],slot);
   v=add_checked(v,product_checked(term,weight,slot),slot);}
  values[j]=v;
 }
 if(*slot)return;fibre_normalize(values,s+y,&den,slot);
 for(uint32_t j=0;j<s+y;++j)to_word(values[j],slot);to_word(den,slot);if(*slot)return;
 for(uint32_t j=0;j<s;++j)source[j]=source_hi[j]=(int64_t)values[j];
 for(uint32_t j=0;j<y;++j)eta[j]=eta_hi[j]=(int64_t)values[s+j];
 source[s]=source_hi[s]=eta[y]=eta_hi[y]=(int64_t)den;
}

// A conditional section of the ORIGINAL affine source, at the same admitted theta. This
// singleton is an operand in evaluating a dependent generator; it never replaces its domain.
extern "C" __global__ void section_coupled_family_section(
 const int64_t *family,const int64_t *family_hi,uint32_t ps,uint32_t t,
 const int64_t *theta,const int64_t *theta_hi,const int64_t *anchor,const int64_t *anchor_hi,
 int64_t *out,int64_t *out_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 if(t<10u||(t-2u)%8u){atomicOr(slot,REFUSED_MALFORMED);return;}
 uint32_t a=(t-2u)/2u;size_t pk=(size_t)ps+t;
 for(size_t i=0;i<pk+4u+(size_t)t*t;++i)if(family[i]!=family_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<2u*(a+2u);++i)if(anchor[i]!=anchor_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 if(((const wide*)anchor)[0]!=0){atomicOr(slot,REFUSED_CARRIER);return;}
 wide td=fibre_current_denominator(theta,theta_hi,t,UINT32_MAX,slot),fd=family[pk];
 if(fd<=0||family[pk+1u]==1){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<t;++i)if(theta[i]!=theta_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide den=product_checked(fd,td,slot);if(*slot)return;
 const int64_t *dirs=family+pk+4u;extern __shared__ wide value[];
 for(uint32_t j=0;j<t;++j){wide v=product_checked(family[ps+j],td,slot);
  for(uint32_t k=0;k<t;++k)v=add_checked(v,product_checked(product_checked(dirs[(size_t)k*t+j],theta[k],slot),fd,slot),slot);
  value[j]=v;
 }
 if(*slot)return;fibre_normalize(value,t,&den,slot);
 if(value[0]!=den||value[1]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t j=0;j<t;++j)to_word(value[j],slot);to_word(den,slot);if(*slot)return;
 size_t ow=1u+t,count=ow+4u+(size_t)t*t;
 for(size_t i=0;i<count;++i)out[i]=out_hi[i]=0;
 for(uint32_t j=0;j<t;++j)out[1u+j]=out_hi[1u+j]=(int64_t)value[j];
 out[ow]=out_hi[ow]=(int64_t)den;out[ow+2u]=out_hi[ow+2u]=-1;
}

// Invert the affine coordinate map at the existing declared source receiver. The graph
// (D^T theta,theta) retains the coordinate kernel. Its particular is an encoding of the
// measured source face, never an assertion that the complete source family is a point.
extern "C" __global__ void section_coupled_receiver_coordinates(
 const int64_t *family,const int64_t *family_hi,uint32_t ps,uint32_t t,
 const int64_t *receiver,const int64_t *receiver_hi,
 int64_t *graph,int64_t *graph_hi,int64_t *coordinates,int64_t *coordinates_hi,
 int64_t *report,int64_t *report_hi,int64_t *workspace,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 if(t<10u||(t-2u)%8u){atomicOr(slot,REFUSED_MALFORMED);return;}
 uint32_t a=(t-2u)/2u,w=2u*t;size_t pk=(size_t)ps+t;
 for(size_t i=0;i<pk+4u+(size_t)t*t;++i)if(family[i]!=family_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<8u+8u*a;++i)if(receiver[i]!=receiver_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 const wide *r=(const wide*)receiver;wide fd=family[pk],ad=r[1],jd=r[2u+a];
 if(fd<=0||ad<=0||jd<=0||r[0]!=0||family[pk+1u]==1){atomicOr(slot,REFUSED_CARRIER);return;}
 const int64_t *dirs=family+pk+4u;wide *row=(wide*)workspace,*query=row+w;
 for(size_t i=0;i<(size_t)w*w;++i)graph[i]=graph_hi[i]=0;
 for(uint32_t p=0;p<t;++p){
  for(uint32_t j=0;j<t;++j){row[j]=dirs[(size_t)p*t+j];row[t+j]=p==j?1:0;}
  condition_stage_row(graph,graph_hi,w,row,slot);if(*slot)return;
 }
 wide den=fibre_lcm(fibre_lcm(fd,ad,slot),jd,slot);if(*slot)return;
 for(uint32_t j=0;j<t;++j){
  wide value=j<2u?(j?0:den):(j<2u+a?product_checked(r[2u+j-2u],den/ad,slot):product_checked(r[3u+a+j-2u-a],den/jd,slot));
  query[j]=sub_checked(value,product_checked(family[ps+j],den/fd,slot),slot);query[t+j]=0;
 }
 if(*slot)return;uint32_t disposition=0,rank=0;
 fibre_query(graph,t,w,query,&den,nullptr,-1,&disposition,&rank,slot);if(*slot)return;
 if(disposition==1u){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t j=t;j<w;++j)query[j]=sub_checked(0,query[j],slot);
 for(uint32_t j=0;j<w;++j)to_word(query[j],slot);to_word(den,slot);if(*slot)return;
 for(uint32_t j=0;j<w;++j)report[j]=report_hi[j]=(int64_t)query[j];
 report[w]=report_hi[w]=(int64_t)den;report[w+1u]=report_hi[w+1u]=disposition;
 report[w+2u]=report_hi[w+2u]=-1;report[w+3u]=report_hi[w+3u]=rank;
 for(uint32_t i=0;i<t;++i)for(uint32_t j=0;j<t;++j){
  int64_t v=graph[(size_t)(t+i)*w+t+i]?graph[(size_t)(t+i)*w+t+j]:0;
  report[(size_t)w+4u+(size_t)i*t+j]=report_hi[(size_t)w+4u+(size_t)i*t+j]=v;
 }
 for(uint32_t j=0;j<t;++j)coordinates[j]=coordinates_hi[j]=(int64_t)query[t+j];
 coordinates[t]=coordinates_hi[t]=(int64_t)den;
}

// Pack the supported declared receiver face as (lambda, anchor, p, c; denominator).
// All arithmetic stays resident and exact; a non-supported receiver is refused.
extern "C" __global__ void section_coupled_receiver_face_packet(
 const int64_t *receiver,const int64_t *receiver_hi,uint32_t n,
 int64_t *packet,int64_t *packet_hi,uint32_t *slot,const uint32_t *census,
 const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 if(!n||32ull*n+8ull>UINT32_MAX){atomicOr(slot,REFUSED_MALFORMED);return;}uint32_t a=4u*n,t=2u*a+2u;
 for(uint32_t i=0;i<8u+8u*a;++i)if(receiver[i]!=receiver_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 const wide *r=(const wide*)receiver; if(r[0]!=0||r[1]<=0||r[2u+a]<=0){atomicOr(slot,REFUSED_CARRIER);return;}
 wide den=fibre_lcm(r[1],r[2u+a],slot);if(*slot)return;
 packet[0]=packet_hi[0]=to_word(den,slot); packet[1]=packet_hi[1]=0;
 for(uint32_t j=0;j<a;++j){packet[2u+j]=packet_hi[2u+j]=to_word(product_checked(r[2u+j],den/r[1],slot),slot);}
 for(uint32_t j=0;j<a;++j){packet[2u+a+j]=packet_hi[2u+a+j]=to_word(product_checked(r[3u+a+j],den/r[2u+a],slot),slot);}
 packet[t]=packet_hi[t]=to_word(den,slot);
}

// Expand a resident face packet back to the receiver wire consumed by the coordinate solver.
extern "C" __global__ void section_coupled_face_packet_receiver(
 const int64_t *packet,const int64_t *packet_hi,uint32_t n,
 int64_t *receiver,int64_t *receiver_hi,uint32_t *slot,const uint32_t *census,
 const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 if(!n||32ull*n+8ull>UINT32_MAX){atomicOr(slot,REFUSED_MALFORMED);return;}uint32_t a=4u*n,t=2u*a+2u;
 for(uint32_t i=0;i<=t;++i)if(packet[i]!=packet_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 const int64_t *p=packet;wide den=p[t];if(den<=0||p[0]!=den||p[1]!=0){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<8u+8u*a;++i)receiver[i]=receiver_hi[i]=0;
 wide *r=(wide*)receiver,*rh=(wide*)receiver_hi;
 r[1]=rh[1]=den;
 for(uint32_t j=0;j<a;++j)r[2u+j]=rh[2u+j]=(wide)p[2u+j];
 r[2u+a]=rh[2u+a]=den;
 for(uint32_t j=0;j<a;++j)r[3u+a+j]=rh[3u+a+j]=(wide)p[2u+a+j];
}

// Exact joint F(x) AND R(x,y) AND G(y). Solve in the product's direction coordinates,
// retaining the pair (x,y), rather than mapping its supported source through R again.
extern "C" __global__ void section_wave_family_pullback(
 const int64_t *basis,const int64_t *basis_hi,
 const int64_t *left,const int64_t *left_hi,uint32_t ls,
 const int64_t *right,const int64_t *right_hi,uint32_t rs,uint32_t t,
 int64_t *graph,int64_t *graph_hi,int64_t *joint,int64_t *joint_hi,
 int64_t *lb,int64_t *lb_hi,int64_t *rb,int64_t *rb_hi,
 int64_t *lo,int64_t *lo_hi,int64_t *ro,int64_t *ro_hi,int64_t *workspace,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint64_t w64=2ull*t,k64=2ull*w64,lk64=(uint64_t)ls+t,rk64=(uint64_t)rs+t;
 if(!t||k64>UINT32_MAX-4u||lk64>UINT32_MAX-4u||rk64>UINT32_MAX-4u){atomicOr(slot,REFUSED_MALFORMED);return;}
 uint32_t w=(uint32_t)w64,k=(uint32_t)k64,lk=(uint32_t)lk64,rk=(uint32_t)rk64;
 for(size_t i=0;i<(size_t)w*w;++i)if(basis[i]!=basis_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<(size_t)lk+4u+(size_t)t*t;++i)if(left[i]!=left_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<(size_t)rk+4u+(size_t)t*t;++i)if(right[i]!=right_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 if(left[lk]<=0||right[rk]<=0||left[lk+1]<0||left[lk+1]>2||right[rk+1]<0||right[rk+1]>2){atomicOr(slot,REFUSED_MALFORMED);return;}
 condition_empty_report(joint,joint_hi,w,w);condition_empty_report(lo,lo_hi,w,t);condition_empty_report(ro,ro_hi,w,t);
 for(size_t i=0;i<(size_t)k*k;++i)graph[i]=graph_hi[i]=0;
 if(left[lk+1]==1||right[rk+1]==1)return;
 wide *r=(wide*)workspace,*row=r+w,*q=row+k;
 uint32_t ignored=0,rank=0;
 for(uint32_t column=0;column<w;++column){
  for(uint32_t j=0;j<w;++j)r[j]=column<t?(j<t?left[(size_t)lk+4u+(size_t)column*t+j]:0):(j>=t?right[(size_t)rk+4u+(size_t)(column-t)*t+j-t]:0);
  // Retain the original direction before reduction by the actual relation R.
  for(uint32_t j=0;j<w;++j)row[w+j]=r[j];
  wide den=1;fibre_query(basis,w,w,r,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
  for(uint32_t j=0;j<w;++j){row[j]=r[j];row[w+j]=product_checked(row[w+j],den,slot);}
  if(*slot)return;condition_stage_row(graph,graph_hi,k,row,slot);if(*slot)return;
 }
 wide ld=left[lk],rd=right[rk],cd=fibre_lcm(ld,rd,slot),den=cd;
 for(uint32_t j=0;j<w;++j)r[j]=j<t?product_checked(left[ls+j],cd/ld,slot):product_checked(right[rs+j-t],cd/rd,slot);
 if(*slot)return;fibre_query(basis,w,w,r,&den,nullptr,-1,&ignored,&rank,slot);if(*slot)return;
 for(uint32_t j=0;j<k;++j)q[j]=j<w?sub_checked(0,r[j],slot):0;
 uint32_t status=0;fibre_query(graph,w,k,q,&den,nullptr,-1,&status,&rank,slot);if(*slot)return;
 for(uint32_t j=w;j<k;++j)q[j]=sub_checked(0,q[j],slot);
 if(status!=1u){
  wide common=fibre_lcm(den,cd,slot);
  for(uint32_t j=0;j<k;++j)q[j]=product_checked(q[j],common/den,slot);
  for(uint32_t j=0;j<w;++j){wide origin=j<t?product_checked(left[ls+j],common/ld,slot):product_checked(right[rs+j-t],common/rd,slot);q[w+j]=add_checked(q[w+j],origin,slot);}
  den=common;fibre_normalize(q,k,&den,slot);
 }
 if(*slot)return;condition_store_report(graph,w,k,q,den,status,rank,joint,joint_hi,slot);if(*slot)return;
 condition_project(joint,w,w,0,t,lb,lb_hi,lo,lo_hi,row,slot);
 if(*slot)return;condition_project(joint,w,w,t,t,rb,rb_hi,ro,ro_hi,row,slot);
}
