// At fixed exact h, retain r=A(h)s+c(h). The condition and mixed-feature coordinates
// are not independent uncertain directions. Contract the same stored M, once, exactly
// before the final grid projection; only A(h) transports the source radius.
extern "C" __global__ void section_normal_applied_condition(
 const int64_t *state,const int64_t *state_hi,
 const int64_t *source,const int64_t *source_hi,uint32_t sa,uint32_t d,
 const int64_t *h,const int64_t *h_hi,uint32_t ha,uint32_t hd,uint32_t hs,uint32_t k,
 uint32_t targets,uint32_t grain,int64_t *out,int64_t *out_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 if(!d||!k||(d&1u)||(k&1u)||(sa&1u)||!targets||grain<1||grain>120){atomicOr(slot,REFUSED_MALFORMED);return;}
 const size_t f=(size_t)d+k+(size_t)d*(k/2u);
 for(size_t j=0;j<2u*f*targets;++j)if(state[j]!=state_hi[j])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t j=0;j<2u*((size_t)d+1u);++j)if(source[sa+j]!=source_hi[sa+j])atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t j=0;j<k;++j)if(h[ha+j]!=h_hi[ha+j])atomicOr(slot,REFUSED_MALFORMED);
 wide den=fibre_current_denominator(h,h_hi,hd,hs,slot),S=(wide)1<<grain;
 const wide *M=(const wide*)state,*x=(const wide*)(source+sa);wide *y=(wide*)out;
 if(*slot||den<=0||x[d]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 MomentInteger denominator=normal_wide(S)*normal_wide(den),gain;
 wide rounding=0;
 for(uint32_t row=0;row<targets;++row){
  const wide *a=M+row*f;MomentInteger yr,yi;
  for(uint32_t j=0;j<k;j+=2u){
   normal_product(yr,yi,normal_wide(a[d+j]),normal_wide(a[d+j+1u]),
       normal_wide(h[ha+j])*normal_wide(S),normal_wide(h[ha+j+1u])*normal_wide(S),false);
  }
  for(uint32_t i=0;i<d;i+=2u){
   MomentInteger ar=normal_wide(a[i])*normal_wide(den),ai=normal_wide(a[i+1u])*normal_wide(den);
   for(uint32_t j=0;j<k/2u;++j){
    size_t at=d+k+(size_t)j*d+i;
    normal_product(ar,ai,normal_wide(a[at]),normal_wide(a[at+1u]),normal_wide(h[ha+2u*j]),normal_wide(h[ha+2u*j+1u]),false);
   }
   gain=gain+normal_abs(ar)+normal_abs(ai);
   normal_product(yr,yi,ar,ai,normal_wide(x[i]),normal_wide(x[i+1u]),false);
  }
  bool rr=false,ri=false;
  y[2u*row]=normal_grid(exact_divide_positive(yr,denominator,&rr),0,false,slot);
  y[2u*row+1u]=normal_grid(exact_divide_positive(yi,denominator,&ri),0,false,slot);
  rounding=add_checked(rounding,(wide)rr+(wide)ri,slot);
 }
 bool rem=false;MomentInteger bound=exact_divide_positive(gain*normal_wide(x[d]),denominator,&rem);
 y[2u*targets]=add_checked(add_checked(normal_grid(bound,0,false,slot),(wide)rem,slot),rounding,slot);
 if(*slot)return;for(size_t j=0;j<2u*(2u*(size_t)targets+1u);++j)out_hi[j]=out[j];
}
