// The implicit-midpoint (Cayley) reaction step of the power-neutral law, per row, and its adjoint.
//
// Material chart (targets n complex, sources F = n + k/2 + n k complex, words at S = 2^grain):
//   W_s = columns [0,n)            linear self-relation (certified passive on the host: herm W_s <= 0)
//   W_c = columns [n, n+k/2)       contrast port coupling
//   A_r = columns [n+k/2+r n, +n)  one slice per REAL contrast coordinate c_r, exactly skew-Hermitian
// K(c) = W_s + sum_r c_r A_r, A(c) = I - K(c)/2. Forward (h = 1):
//   A(c) y = (I + K(c)/2) p + W_c c,   mid = (p + y)/2,
// i.e. y - p = K(c) mid + W_c c (Holon/Cayley.lean::midpoint_reaction_balance). With herm K <= 0
// (skew slices for every real c, passive W_s), herm A >= I, so ||A^-1|| <= 1 and the Cayley map
// C = A^-1 (I + K/2) = 2A^-1 - I has ||C|| <= 1 (Holon/Cayley.lean::cayley_isometry when W_s is skew).
// The centre is a floating-point proposal rounded to the grain and refined against the EXACT residual
// rho = (I + K/2) p0 + W_c c0 - A y_c; the radius is certified, never assumed:
//   r_y = r_p                                   (||C(c)|| <= 1 at fixed c)
//       + r_c (F_A X + F_c)                     (mean value in c at p0; |mid| <= X; ||A^-1|| <= 1)
//       + |rho|                                 (||A^-1|| <= 1 at the centre)
// with F_A = sqrt(sum_r ||A_r||_F^2) and F_c = ||W_c||_F, both ceiled, X = |p0|_1 + F_c(|c0|_1 + r_c)/2.
// This is Holon/Cayley.lean::device_containment with K_k = 1: ||L c - c'|| <= r' - r.
// Adjoint: A^H u = g, g_p = (I + K/2)^H u = 2u - g, r_u = r_g + r_c F_A |g0|/2 + |rho_u|.
// The material return is (Phi(mid, c), u) and the contrast return the realified feature pullback of
// W^H u at (mid, c); both use existing kernels.
constexpr uint32_t ECY_MAX = 8u;
__device__ double ecy_double_wide(wide x){
 const int64_t hi=(int64_t)(x>>64);const uint64_t lo=(uint64_t)x;
 return ldexp((double)hi,64)+(double)lo;
}
__device__ double ecy_double_moment(const MomentInteger &x){
 double v=0.0;for(int j=MomentInteger::LIMBS-1;j>=0;--j)v=ldexp(v,32)+(double)x.limb[j];
 return x.negative?-v:v;
}
__device__ wide ecy_wide_double(double v,uint32_t *status){
 if(!isfinite(v)||fabs(v)>=0x1p125){atomicOr(status,REFUSED_CARRIER);return 0;}
 const double r=rint(v),a=fabs(r),hi=floor(ldexp(a,-64)),lo=a-ldexp(hi,64);
 const uwide m=((uwide)(uint64_t)hi<<64)|(uwide)(uint64_t)lo;
 return r<0?-(wide)m:(wide)m;
}
// Complex LU with partial pivoting, in place, on an n x n system (n <= ECY_MAX). Returns false when a
// pivot vanishes: the proposal is then refused, never replaced.
__device__ bool ecy_lu(double (*re)[ECY_MAX],double (*im)[ECY_MAX],uint32_t n,uint32_t *perm){
 for(uint32_t i=0;i<n;++i)perm[i]=i;
 for(uint32_t c=0;c<n;++c){
  uint32_t best=c;double size=hypot(re[c][c],im[c][c]);
  for(uint32_t r=c+1;r<n;++r){double s=hypot(re[r][c],im[r][c]);if(s>size){size=s;best=r;}}
  if(!(size>0.0))return false;
  if(best!=c){for(uint32_t j=0;j<n;++j){double t=re[c][j];re[c][j]=re[best][j];re[best][j]=t;t=im[c][j];im[c][j]=im[best][j];im[best][j]=t;}
   uint32_t t=perm[c];perm[c]=perm[best];perm[best]=t;}
  const double pr=re[c][c],pi=im[c][c],den=pr*pr+pi*pi;
  for(uint32_t r=c+1;r<n;++r){
   const double fr=(re[r][c]*pr+im[r][c]*pi)/den,fi=(im[r][c]*pr-re[r][c]*pi)/den;
   re[r][c]=fr;im[r][c]=fi;
   for(uint32_t j=c+1;j<n;++j){re[r][j]-=fr*re[c][j]-fi*im[c][j];im[r][j]-=fr*im[c][j]+fi*re[c][j];}
  }
 }
 return true;
}
__device__ void ecy_solve(double (*re)[ECY_MAX],double (*im)[ECY_MAX],uint32_t n,const uint32_t *perm,
 const double *br,const double *bi,double *xr,double *xi){
 double yr[ECY_MAX],yi[ECY_MAX];
 for(uint32_t r=0;r<n;++r){double sr=br[perm[r]],si=bi[perm[r]];
  for(uint32_t j=0;j<r;++j){sr-=re[r][j]*yr[j]-im[r][j]*yi[j];si-=re[r][j]*yi[j]+im[r][j]*yr[j];}
  yr[r]=sr;yi[r]=si;}
 for(int r=(int)n-1;r>=0;--r){double sr=yr[r],si=yi[r];
  for(uint32_t j=r+1;j<n;++j){sr-=re[r][j]*xr[j]-im[r][j]*xi[j];si-=re[r][j]*xi[j]+im[r][j]*xr[j];}
  const double pr=re[r][r],pi=im[r][r],den=pr*pr+pi*pi;
  xr[r]=(sr*pr+si*pi)/den;xi[r]=(si*pr-sr*pi)/den;}
}
// Material coefficient (target a, complex source j), interleaved (re, im) at S.
__device__ wide ecy_m(const wide *M,uint32_t F,uint32_t a,uint32_t j,uint32_t part){return M[(size_t)a*2u*F+2u*(size_t)j+part];}
// K S^2 entry (a,b) exactly: W_s S + sum_r c_r A_r.
__device__ void ecy_k(const wide *M,const wide *C,uint32_t n,uint32_t k,uint32_t F,wide S,uint32_t a,uint32_t b,
 MomentInteger &kr,MomentInteger &ki){
 kr=normal_wide(ecy_m(M,F,a,b,0))*normal_wide(S);ki=normal_wide(ecy_m(M,F,a,b,1))*normal_wide(S);
 for(uint32_t r=0;r<k;++r){const uint32_t j=n+k/2u+r*n+b;const MomentInteger cr=normal_wide(C[r]);
  kr=kr+normal_wide(ecy_m(M,F,a,j,0))*cr;ki=ki+normal_wide(ecy_m(M,F,a,j,1))*cr;}
}
__device__ double ecy_kd(const wide *M,const wide *C,uint32_t n,uint32_t k,uint32_t F,uint32_t grain,uint32_t a,uint32_t b,uint32_t part){
 double v=ldexp(ecy_double_wide(ecy_m(M,F,a,b,part)),-(int)grain);
 for(uint32_t r=0;r<k;++r)v+=ldexp(ecy_double_wide(C[r]),-(int)grain)*ldexp(ecy_double_wide(ecy_m(M,F,a,n+k/2u+r*n+b,part)),-(int)grain);
 return v;
}
// Common row validation: material point words, slice skewness, ball shapes.
__device__ bool ecy_admit(const int64_t *state,const int64_t *state_hi,uint32_t n,uint32_t k,uint32_t grain,
 uint32_t certified,uint32_t *status){
 if(grain<1u||grain>120u||!n||n>ECY_MAX||(k&1u)){atomicOr(status,REFUSED_MALFORMED);return false;}
 // The host certificate (herm W_s <= 0 by exact inertia) is the premise of ||A^-1|| <= 1.
 if(!certified){atomicOr(status,REFUSED_BOUND);return false;}
 const uint32_t F=n+k/2u+n*k;const size_t words=2u*(2u*(size_t)F*n);
 for(size_t j=0;j<words;++j)if(state[j]!=state_hi[j]){atomicOr(status,REFUSED_MALFORMED);return false;}
 const wide *M=(const wide*)state;
 for(uint32_t r=0;r<k;++r)for(uint32_t a=0;a<n;++a)for(uint32_t b=0;b<=a;++b){
  const uint32_t ja=n+k/2u+r*n+b,jb=n+k/2u+r*n+a;
  if(ecy_m(M,F,a,ja,0)!=-ecy_m(M,F,b,jb,0)||ecy_m(M,F,a,ja,1)!=ecy_m(M,F,b,jb,1)){atomicOr(status,REFUSED_BOUND);return false;}
 }
 return true;
}
// ceil sqrt of the sum of squares of the slice (and coupling) words, at S.
__device__ void ecy_norms(const wide *M,uint32_t n,uint32_t k,uint32_t F,wide *FA,wide *FC,uint32_t *status){
 HistoryInteger a,c;
 for(uint32_t t=0;t<n;++t){
  for(uint32_t j=n;j<n+k/2u;++j)for(uint32_t part=0;part<2u;++part){HistoryInteger v=history_integer(ecy_m(M,F,t,j,part));c=c+v*v;}
  for(uint32_t j=n+k/2u;j<F;++j)for(uint32_t part=0;part<2u;++part){HistoryInteger v=history_integer(ecy_m(M,F,t,j,part));a=a+v*v;}
 }
 *FA=history_norm_ceiling(a,status);*FC=history_norm_ceiling(c,status);
}
extern "C" __global__ void section_enclosure_cayley_reaction(
 const int64_t *state,const int64_t *state_hi,const int64_t *drive,const int64_t *drive_hi,
 const int64_t *condition,const int64_t *condition_hi,
 uint32_t rows,uint32_t n,uint32_t k,uint32_t grain,uint32_t certified,
 int64_t *out,int64_t *oh,int64_t *mid,int64_t *mh,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 if(!ecy_admit(state,state_hi,n,k,grain,certified,status))return;
 const uint32_t d=2u*n,F=n+k/2u+n*k;
 const int64_t *pw=drive+2u*((size_t)d+1u)*row;
 if(!ec_ball(pw,drive_hi+2u*((size_t)d+1u)*row,d,status))return;
 const wide *C=nullptr;wide rc=0,cn=0;
 if(k){const int64_t *cw=condition+2u*((size_t)k+1u)*row;
  if(!ec_ball(cw,condition_hi+2u*((size_t)k+1u)*row,k,status))return;
  C=(const wide*)cw;rc=C[k];cn=ec_l1(C,k,status);}
 const wide *M=(const wide*)state,*P=(const wide*)pw;const wide S=(wide)((uwide)1<<grain);
 // Proposal: LU of A = I - K/2 in double.
 double are[ECY_MAX][ECY_MAX],aim[ECY_MAX][ECY_MAX];uint32_t perm[ECY_MAX];
 for(uint32_t a=0;a<n;++a)for(uint32_t b=0;b<n;++b){
  are[a][b]=(a==b?1.0:0.0)-0.5*ecy_kd(M,C,n,k,F,grain,a,b,0);aim[a][b]=-0.5*ecy_kd(M,C,n,k,F,grain,a,b,1);}
 if(!ecy_lu(are,aim,n,perm)){atomicOr(status,REFUSED_BOUND);return;}
 // W_c c0 at S^2, exactly.
 MomentInteger wr[ECY_MAX],wi[ECY_MAX];
 for(uint32_t a=0;a<n;++a){wr[a]=MomentInteger();wi[a]=MomentInteger();
  for(uint32_t j=0;j<k/2u;++j)normal_product(wr[a],wi[a],normal_wide(ecy_m(M,F,a,n+j,0)),normal_wide(ecy_m(M,F,a,n+j,1)),
   normal_wide(C[2u*j]),normal_wide(C[2u*j+1u]),false);}
 // rhs (grain units) = (I + K/2) p0 + W_c c0 = 2 p0 - A p0 + W_c c0, in double.
 double br[ECY_MAX],bi[ECY_MAX],xr[ECY_MAX],xi[ECY_MAX];
 for(uint32_t a=0;a<n;++a){
  double sr=ecy_double_wide(P[2u*a]),si=ecy_double_wide(P[2u*a+1u]);
  for(uint32_t b=0;b<n;++b){const double kr=ecy_kd(M,C,n,k,F,grain,a,b,0),ki=ecy_kd(M,C,n,k,F,grain,a,b,1);
   const double pr=ecy_double_wide(P[2u*b]),pi=ecy_double_wide(P[2u*b+1u]);sr+=0.5*(kr*pr-ki*pi);si+=0.5*(kr*pi+ki*pr);}
  br[a]=sr+ldexp(ecy_double_moment(wr[a]),-(int)grain);bi[a]=si+ldexp(ecy_double_moment(wi[a]),-(int)grain);}
 ecy_solve(are,aim,n,perm,br,bi,xr,xi);
 wide Y[2u*ECY_MAX];
 for(uint32_t a=0;a<n;++a){Y[2u*a]=ecy_wide_double(xr[a],status);Y[2u*a+1u]=ecy_wide_double(xi[a],status);}
 if(*status)return;
 // Exact residual R = 2S^3 rho = 2S^2 (P - Y) + K S^2 (P + Y) + 2S (W_c c0 S^2); two refinements.
 MomentInteger Rr[ECY_MAX],Ri[ECY_MAX];const MomentInteger S2=normal_wide(S)*normal_wide(S);
 for(uint32_t pass=0;pass<3u;++pass){
  for(uint32_t a=0;a<n;++a){
   Rr[a]=S2*normal_wide(2)*(normal_wide(P[2u*a])-normal_wide(Y[2u*a]))+normal_wide(2)*normal_wide(S)*wr[a];
   Ri[a]=S2*normal_wide(2)*(normal_wide(P[2u*a+1u])-normal_wide(Y[2u*a+1u]))+normal_wide(2)*normal_wide(S)*wi[a];
   for(uint32_t b=0;b<n;++b){MomentInteger kr,ki;ecy_k(M,C,n,k,F,S,a,b,kr,ki);
    normal_product(Rr[a],Ri[a],kr,ki,normal_wide(P[2u*b])+normal_wide(Y[2u*b]),normal_wide(P[2u*b+1u])+normal_wide(Y[2u*b+1u]),false);}
  }
  if(pass==2u)break;
  for(uint32_t a=0;a<n;++a){br[a]=ldexp(ecy_double_moment(Rr[a]),-(int)(2u*grain+1u));bi[a]=ldexp(ecy_double_moment(Ri[a]),-(int)(2u*grain+1u));}
  ecy_solve(are,aim,n,perm,br,bi,xr,xi);
  for(uint32_t a=0;a<n;++a){Y[2u*a]=add_checked(Y[2u*a],ecy_wide_double(xr[a],status),status);
   Y[2u*a+1u]=add_checked(Y[2u*a+1u],ecy_wide_double(xi[a],status),status);}
  if(*status)return;
 }
 MomentInteger rl1;for(uint32_t a=0;a<n;++a)rl1=rl1+normal_abs(Rr[a])+normal_abs(Ri[a]);
 const wide centre=ec_ceil(rl1,S2*normal_wide(2),status);
 wide FA=0,FC=0;ecy_norms(M,n,k,F,&FA,&FC,status);
 const wide pn=ec_l1(P,d,status),rp=P[d];
 const wide X=add_checked(pn,ec_ceil(normal_wide(FC)*(normal_wide(cn)+normal_wide(rc)),normal_wide(2)*normal_wide(S),status),status);
 const wide spread=ec_ceil(normal_wide(rc)*(normal_wide(FA)*normal_wide(X)+normal_wide(FC)*normal_wide(S)),S2,status);
 const wide ry=add_checked(add_checked(rp,spread,status),centre,status);
 if(*status)return;
 int64_t *ow=out+2u*((size_t)d+1u)*row;wide *y=(wide*)ow;
 for(uint32_t j=0;j<d;++j)y[j]=Y[j];y[d]=ry;
 int64_t *mw=mid+2u*((size_t)d+1u)*row;wide *x=(wide*)mw;wide odd=0;
 for(uint32_t j=0;j<d;++j){const wide s=add_checked(P[j],Y[j],status);x[j]=s>>1;odd=add_checked(odd,(wide)(s&1),status);}
 const wide half=add_checked(rp,ry,status);
 x[d]=add_checked(add_checked(half>>1,half&1,status),odd,status);
 ec_seal(ow,oh+2u*((size_t)d+1u)*row,d,status);ec_seal(mw,mh+2u*((size_t)d+1u)*row,d,status);
}
extern "C" __global__ void section_enclosure_cayley_adjoint(
 const int64_t *state,const int64_t *state_hi,const int64_t *condition,const int64_t *condition_hi,
 const int64_t *covector,const int64_t *covector_hi,
 uint32_t rows,uint32_t n,uint32_t k,uint32_t grain,uint32_t certified,
 int64_t *uo,int64_t *uh,int64_t *po,int64_t *ph,int64_t *flags,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;
 uint32_t *status=ec_status(flags,row);if(upstream_refused(census,lineage,lineage_count,status))return;
 if(!ecy_admit(state,state_hi,n,k,grain,certified,status))return;
 const uint32_t d=2u*n,F=n+k/2u+n*k;
 const int64_t *gw=covector+2u*((size_t)d+1u)*row;
 if(!ec_ball(gw,covector_hi+2u*((size_t)d+1u)*row,d,status))return;
 const wide *C=nullptr;wide rc=0;
 if(k){const int64_t *cw=condition+2u*((size_t)k+1u)*row;
  if(!ec_ball(cw,condition_hi+2u*((size_t)k+1u)*row,k,status))return;
  C=(const wide*)cw;rc=C[k];}
 const wide *M=(const wide*)state,*G=(const wide*)gw;const wide S=(wide)((uwide)1<<grain);
 // A^H = I - K^H/2.
 double are[ECY_MAX][ECY_MAX],aim[ECY_MAX][ECY_MAX];uint32_t perm[ECY_MAX];
 for(uint32_t a=0;a<n;++a)for(uint32_t b=0;b<n;++b){
  are[a][b]=(a==b?1.0:0.0)-0.5*ecy_kd(M,C,n,k,F,grain,b,a,0);aim[a][b]=0.5*ecy_kd(M,C,n,k,F,grain,b,a,1);}
 if(!ecy_lu(are,aim,n,perm)){atomicOr(status,REFUSED_BOUND);return;}
 double br[ECY_MAX],bi[ECY_MAX],xr[ECY_MAX],xi[ECY_MAX];
 for(uint32_t a=0;a<n;++a){br[a]=ecy_double_wide(G[2u*a]);bi[a]=ecy_double_wide(G[2u*a+1u]);}
 ecy_solve(are,aim,n,perm,br,bi,xr,xi);
 wide U[2u*ECY_MAX];
 for(uint32_t a=0;a<n;++a){U[2u*a]=ecy_wide_double(xr[a],status);U[2u*a+1u]=ecy_wide_double(xi[a],status);}
 if(*status)return;
 // R = 2S^3 rho_u = 2S^2 (G - U) + K^H S^2 U.
 MomentInteger Rr[ECY_MAX],Ri[ECY_MAX];const MomentInteger S2=normal_wide(S)*normal_wide(S);
 for(uint32_t pass=0;pass<3u;++pass){
  for(uint32_t a=0;a<n;++a){
   Rr[a]=S2*normal_wide(2)*(normal_wide(G[2u*a])-normal_wide(U[2u*a]));
   Ri[a]=S2*normal_wide(2)*(normal_wide(G[2u*a+1u])-normal_wide(U[2u*a+1u]));
   // (K^H U)_a = sum_b conj(K_ba) U_b = U_b conj(K_ba).
   for(uint32_t b=0;b<n;++b){MomentInteger kr,ki;ecy_k(M,C,n,k,F,S,b,a,kr,ki);
    normal_product(Rr[a],Ri[a],normal_wide(U[2u*b]),normal_wide(U[2u*b+1u]),kr,ki,true);}
  }
  if(pass==2u)break;
  for(uint32_t a=0;a<n;++a){br[a]=ldexp(ecy_double_moment(Rr[a]),-(int)(2u*grain+1u));bi[a]=ldexp(ecy_double_moment(Ri[a]),-(int)(2u*grain+1u));}
  ecy_solve(are,aim,n,perm,br,bi,xr,xi);
  for(uint32_t a=0;a<n;++a){U[2u*a]=add_checked(U[2u*a],ecy_wide_double(xr[a],status),status);
   U[2u*a+1u]=add_checked(U[2u*a+1u],ecy_wide_double(xi[a],status),status);}
  if(*status)return;
 }
 MomentInteger rl1;for(uint32_t a=0;a<n;++a)rl1=rl1+normal_abs(Rr[a])+normal_abs(Ri[a]);
 const wide centre=ec_ceil(rl1,S2*normal_wide(2),status);
 wide FA=0,FC=0;ecy_norms(M,n,k,F,&FA,&FC,status);
 const wide gn=ec_l1(G,d,status),rg=G[d];
 const wide spread=ec_ceil(normal_wide(rc)*normal_wide(FA)*normal_wide(gn),S2*normal_wide(2),status);
 const wide ru=add_checked(add_checked(rg,spread,status),centre,status);
 if(*status)return;
 int64_t *uw=uo+2u*((size_t)d+1u)*row,*pw=po+2u*((size_t)d+1u)*row;wide *u=(wide*)uw,*gp=(wide*)pw;
 for(uint32_t j=0;j<d;++j){u[j]=U[j];gp[j]=add_checked(add_checked(U[j],U[j],status),-G[j],status);}
 u[d]=ru;gp[d]=add_checked(add_checked(ru,ru,status),rg,status);
 ec_seal(uw,uh+2u*((size_t)d+1u)*row,d,status);ec_seal(pw,ph+2u*((size_t)d+1u)*row,d,status);
}
