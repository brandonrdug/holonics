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
