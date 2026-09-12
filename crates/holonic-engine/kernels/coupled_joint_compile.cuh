// Compile the actual paired family and current member relation to an exact A/B/D predicate.
// Parameters are original source-generator coefficients, condition coordinates, and relation
// row witnesses. The latter are NOT learned material coefficients. The recorded condition is
// imposed separately; anchor-ball membership is retained by the companion receiver below.
extern "C" __global__ void section_coupled_joint_compile(
 const int64_t *coeff,const int64_t *coeff_hi,const int64_t *basis,const int64_t *basis_hi,
 const int64_t *fixed,const int64_t *fixed_hi,uint32_t n,uint32_t kc,
 int64_t *al,int64_t *ah,int64_t *bl,int64_t *bh,int64_t *dl,int64_t *dh,
 int64_t *workspace,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;
 if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t t=8u*n+2u,s=6u*n,h=2u*kc,r=2u*n,f=s+h+s*kc,w=f+r;
 uint32_t p=t+h+w,cols=p+1u,rank=s+h+s*h+r+w+1u,outputs=w+h;
 size_t ac=(size_t)rank*cols,dc=(size_t)outputs*rank,cc=(size_t)(t+1u)*(w+1u);
 if(!n||!kc){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<2u*cc;++i)if(coeff[i]!=coeff_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<(size_t)w*w;++i)if(basis[i]!=basis_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide hd=fibre_current_denominator(fixed,fixed_hi,h,UINT32_MAX,slot);if(*slot)return;
 for(uint32_t i=0;i<h;++i)if(fixed[i]!=fixed_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 const wide *c=(const wide*)coeff;wide ad=1;
 for(uint32_t row=0;row<=t;++row){wide den=c[(size_t)row*(w+1u)+w];
  if(den<=0){atomicOr(slot,REFUSED_MALFORMED);return;}ad=fibre_lcm(ad,den,slot);if(*slot)return;}
 wide *a=(wide*)workspace,*d=a+ac;
 for(size_t i=0;i<ac;++i){a[i]=0;bl[i]=bh[i]=0;}
 for(size_t i=0;i<dc;++i)d[i]=0;
 uint32_t mix=s+h,eta=mix+s*h,witness=eta+r,one=rank-1u;
 for(uint32_t j=0;j<s;++j){
  bl[(size_t)j*cols+p]=bh[(size_t)j*cols+p]=1;
  for(uint32_t row=0;row<=t;++row){uint32_t at=row?row-1u:p;
   wide v=product_checked(c[(size_t)row*(w+1u)+j],ad/c[(size_t)row*(w+1u)+w],slot);
   a[(size_t)j*cols+at]=v;
   for(uint32_t z=0;z<h;++z)a[(size_t)(mix+j*h+z)*cols+at]=v;
  }
 }
 for(uint32_t j=0;j<h;++j){a[(size_t)(s+j)*cols+t+j]=ad;
  bl[(size_t)(s+j)*cols+p]=bh[(size_t)(s+j)*cols+p]=1;
  for(uint32_t i=0;i<s;++i)bl[(size_t)(mix+i*h+j)*cols+t+j]=bh[(size_t)(mix+i*h+j)*cols+t+j]=1;
 }
 for(uint32_t j=0;j<r;++j){bl[(size_t)(eta+j)*cols+p]=bh[(size_t)(eta+j)*cols+p]=1;
  for(uint32_t row=0;row<=t;++row){uint32_t at=row?row-1u:p;
   a[(size_t)(eta+j)*cols+at]=product_checked(c[(size_t)row*(w+1u)+f+j],ad/c[(size_t)row*(w+1u)+w],slot);
  }
 }
 for(uint32_t j=0;j<w;++j){a[(size_t)(witness+j)*cols+t+h+j]=ad;
  bl[(size_t)(witness+j)*cols+p]=bh[(size_t)(witness+j)*cols+p]=1;}
 a[(size_t)one*cols+p]=ad;bl[(size_t)one*cols+p]=bh[(size_t)one*cols+p]=1;
 for(uint32_t j=0;j<s+h;++j)d[(size_t)j*rank+j]=hd;
 for(uint32_t hc=0;hc<kc;++hc)for(uint32_t sc=0;sc<3u*n;++sc){
  uint32_t eq=s+h+2u*(hc*3u*n+sc),x=2u*sc,y=2u*hc;
  d[(size_t)eq*rank+mix+x*h+y]=hd;d[(size_t)eq*rank+mix+(x+1u)*h+y+1u]=-hd;
  d[(size_t)(eq+1u)*rank+mix+x*h+y+1u]=hd;d[(size_t)(eq+1u)*rank+mix+(x+1u)*h+y]=hd;
 }
 for(uint32_t j=0;j<r;++j)d[(size_t)(f+j)*rank+eta+j]=hd;
 for(uint32_t eq=0;eq<w;++eq)for(uint32_t row=0;row<w;++row)
  d[(size_t)eq*rank+witness+row]=sub_checked(0,product_checked(basis[(size_t)row*w+eq],hd,slot),slot);
 for(uint32_t j=0;j<h;++j){d[(size_t)(w+j)*rank+s+j]=hd;d[(size_t)(w+j)*rank+one]=-(wide)fixed[j];}
 if(*slot)return;fibre_normalize(a,(uint32_t)ac,&ad,slot);fibre_normalize(d,(uint32_t)dc,&hd,slot);
 for(size_t i=0;i<ac;++i)to_word(a[i],slot);for(size_t i=0;i<dc;++i)to_word(d[i],slot);to_word(ad,slot);to_word(hd,slot);if(*slot)return;
 for(size_t i=0;i<ac;++i)al[i]=ah[i]=(int64_t)a[i];for(size_t i=0;i<dc;++i)dl[i]=dh[i]=(int64_t)d[i];
 al[ac]=ah[ac]=(int64_t)ad;bl[ac]=bh[ac]=1;dl[dc]=dh[dc]=(int64_t)hd;
}

// Evaluate the ORIGINAL anchor at the SAME source parameter occurrence. Equation agreement
// does not replace this inequality. Return status + rational delta, never a selected centre.
extern "C" __global__ void section_coupled_joint_anchor(
 const int64_t *family,const int64_t *family_hi,uint32_t ps,
 const int64_t *ball,const int64_t *ball_hi,uint32_t ball_at,uint32_t n,uint32_t grain,
 const int64_t *theta,const int64_t *theta_hi,uint32_t parameters,
 int64_t *report,int64_t *report_hi,uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x)return;if(upstream_refused(census,lineage,lineage_count,slot))return;
 uint32_t a=4u*n,t=2u+2u*a;size_t pk=(size_t)ps+t;
 if(!n||grain<1||grain>120||parameters<t||(ball_at&1u)){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(size_t i=0;i<pk+4u+(size_t)t*t;++i)if(family[i]!=family_hi[i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 for(uint32_t i=0;i<2u*(a+1u);++i)if(ball[ball_at+i]!=ball_hi[ball_at+i]){atomicOr(slot,REFUSED_MALFORMED);return;}
 wide td=fibre_current_denominator(theta,theta_hi,parameters,UINT32_MAX,slot),fd=family[pk];
 if(fd<=0||family[pk+1u]==1||family[ps]!=fd||family[ps+1u])atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t i=0;i<parameters;++i)if(theta[i]!=theta_hi[i])atomicOr(slot,REFUSED_MALFORMED);
 const wide *b=(const wide*)(ball+ball_at);wide S=(wide)1<<grain;if(b[a]<0)atomicOr(slot,REFUSED_MALFORMED);if(*slot)return;
 const int64_t *dirs=family+pk+4u;extern __shared__ wide delta[];
 wide den=fibre_lcm(product_checked(fd,td,slot),S,slot);if(*slot)return;
 for(uint32_t j=0;j<a;++j){wide v=product_checked(family[ps+2u+j],td,slot);
  for(uint32_t k=0;k<t;++k)v=add_checked(v,product_checked(product_checked(dirs[(size_t)k*t+2u+j],theta[k],slot),fd,slot),slot);
  delta[j]=sub_checked(product_checked(v,den/product_checked(fd,td,slot),slot),product_checked(b[j],den/S,slot),slot);
 }
 if(*slot)return;fibre_normalize(delta,a,&den,slot);if(*slot)return;
 FamilyReceiverInteger square;for(uint32_t j=0;j<a;++j){auto v=family_receiver_integer(delta[j]);square=square+v*v;}
 auto ss=family_receiver_integer(S),rr=family_receiver_integer(b[a]),dd=family_receiver_integer(den);
 auto left=square*ss*ss,right=rr*rr*dd*dd;
 if(left.overflow||right.overflow){atomicOr(slot,REFUSED_CARRIER);return;}
 wide *out=(wide*)report;out[0]=left<=right?0:1;out[1]=den;for(uint32_t j=0;j<a;++j)out[2u+j]=delta[j];
 for(uint32_t j=0;j<2u*(a+2u);++j)report_hi[j]=report[j];
}
