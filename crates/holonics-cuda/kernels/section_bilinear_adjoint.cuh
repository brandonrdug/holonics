// The covector port of section_constitutive_bilinear_source.
//
// The forward packet is phi = [s, c, c(x)s] with the mixed block the ordinary complex product
// s_i c_j, so phi is holomorphic in each operand separately. The real transpose of a complex
// multiplication by w is multiplication by conj(w); by the product rule the same feature
// covector therefore returns to BOTH operands,
//
//   g_s[i] = g[s_i]  + sum_j conj(c_j) g[c_j (x) s_i],
//   g_c[j] = g[c_j]  + sum_i conj(s_i) g[c_j (x) s_i],
//
// and <D phi[ds,dc], g> = <ds, g_s> + <dc, g_c> holds coordinate-wise in the interleaved real
// chart. Each return is a fresh linear map of the same covector, so each enclosure carries its
// own complex Frobenius bound times the supplied radius; no operand is read back to the host.
extern "C" __global__ void section_bilinear_source_adjoint(
 const int64_t *source,const int64_t *source_hi,uint32_t source_stride,uint32_t source_rational,
 const int64_t *condition,const int64_t *condition_hi,uint32_t condition_stride,uint32_t condition_rational,
 const int64_t *covector,const int64_t *covector_hi,
 uint32_t rows,uint32_t source_complex,uint32_t condition_complex,
 int64_t *source_out,int64_t *source_out_hi,int64_t *condition_out,int64_t *condition_out_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 uint64_t width64=2u*((uint64_t)source_complex+condition_complex+(uint64_t)source_complex*condition_complex);
 if(!rows||!source_complex||!condition_complex||width64>=UINT32_MAX){atomicOr(slot,REFUSED_MALFORMED);return;}
 const uint32_t width=(uint32_t)width64,ds=2u*source_complex,dc=2u*condition_complex,mixed=ds+dc;
 const size_t covector_row=2u*((size_t)width+1u);
 const size_t source_out_row=2u*((size_t)ds+1u),condition_out_row=2u*((size_t)dc+1u);
 for(uint32_t row=0;row<rows;++row){
  const int64_t *x=source+(size_t)row*source_stride,*xh=source_hi+(size_t)row*source_stride;
  const int64_t *h=condition+(size_t)row*condition_stride,*hh=condition_hi+(size_t)row*condition_stride;
  const int64_t *gl=covector+(size_t)row*covector_row,*gh=covector_hi+(size_t)row*covector_row;
  wide sden=fibre_current_denominator(x,xh,source_rational?ds:UINT32_MAX,UINT32_MAX,slot);
  wide cden=fibre_current_denominator(h,hh,condition_rational?dc:UINT32_MAX,UINT32_MAX,slot);
  for(uint32_t j=0;j<ds;++j)if(x[j]!=xh[j])atomicOr(slot,REFUSED_MALFORMED);
  for(uint32_t j=0;j<dc;++j)if(h[j]!=hh[j])atomicOr(slot,REFUSED_MALFORMED);
  for(size_t j=0;j<covector_row;++j)if(gl[j]!=gh[j])atomicOr(slot,REFUSED_MALFORMED);
  if(*slot)return;
  const wide *g=(const wide *)gl;
  if(g[width]<0||sden<=0||cden<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
  wide *ys=(wide *)(source_out+(size_t)row*source_out_row);
  wide *yc=(wide *)(condition_out+(size_t)row*condition_out_row);
  // Both returns are blocks of one identity and one conjugated operand coordinate, so each
  // column of the transported map repeats and its complex Frobenius bound is counted once.
  MomentInteger source_column=normal_wide(cden)*normal_wide(cden),source_cap=normal_abs(normal_wide(cden));
  for(uint32_t j=0;j<dc;j+=2u){
   source_column=source_column+normal_wide(h[j])*normal_wide(h[j])+normal_wide(h[j+1u])*normal_wide(h[j+1u]);
   source_cap=source_cap+normal_abs(normal_wide(h[j]))+normal_abs(normal_wide(h[j+1u]));
  }
  MomentInteger condition_column=normal_wide(sden)*normal_wide(sden),condition_cap=normal_abs(normal_wide(sden));
  for(uint32_t i=0;i<ds;i+=2u){
   condition_column=condition_column+normal_wide(x[i])*normal_wide(x[i])+normal_wide(x[i+1u])*normal_wide(x[i+1u]);
   condition_cap=condition_cap+normal_abs(normal_wide(x[i]))+normal_abs(normal_wide(x[i+1u]));
  }
  wide source_rounding=0,condition_rounding=0;
  for(uint32_t i=0;i<source_complex;++i){
   MomentInteger re=normal_wide(g[2u*i])*normal_wide(cden),im=normal_wide(g[2u*i+1u])*normal_wide(cden);
   for(uint32_t j=0;j<condition_complex;++j){
    size_t at=(size_t)mixed+2u*((size_t)j*source_complex+i);
    // normal_product(...,true) forms a·conj(b); with a=g and b=c that is conj(c)·g exactly.
    normal_product(re,im,normal_wide(g[at]),normal_wide(g[at+1u]),
        normal_wide(h[2u*j]),normal_wide(h[2u*j+1u]),true);
   }
   bool rr=false,ri=false;
   ys[2u*i]=normal_grid(exact_divide_positive(re,normal_wide(cden),&rr),0,false,slot);
   ys[2u*i+1u]=normal_grid(exact_divide_positive(im,normal_wide(cden),&ri),0,false,slot);
   source_rounding=add_checked(source_rounding,(wide)rr+(wide)ri,slot);
  }
  for(uint32_t j=0;j<condition_complex;++j){
   MomentInteger re=normal_wide(g[ds+2u*j])*normal_wide(sden),im=normal_wide(g[ds+2u*j+1u])*normal_wide(sden);
   for(uint32_t i=0;i<source_complex;++i){
    size_t at=(size_t)mixed+2u*((size_t)j*source_complex+i);
    normal_product(re,im,normal_wide(g[at]),normal_wide(g[at+1u]),
        normal_wide(x[2u*i]),normal_wide(x[2u*i+1u]),true);
   }
   bool rr=false,ri=false;
   yc[2u*j]=normal_grid(exact_divide_positive(re,normal_wide(sden),&rr),0,false,slot);
   yc[2u*j+1u]=normal_grid(exact_divide_positive(im,normal_wide(sden),&ri),0,false,slot);
   condition_rounding=add_checked(condition_rounding,(wide)rr+(wide)ri,slot);
  }
  // The transported radius is the map's norm times the supplied radius, in the numerator
  // scale of the conjugated operand; the truncated coordinates are paid for on top of it.
  MomentInteger source_square=normal_wide((wide)source_complex)*source_column;
  wide source_norm=normal_wave_root_capped(source_square,
      normal_grid(normal_wide((wide)source_complex)*source_cap,0,false,slot),slot);
  MomentInteger condition_square=normal_wide((wide)condition_complex)*condition_column;
  wide condition_norm=normal_wave_root_capped(condition_square,
      normal_grid(normal_wide((wide)condition_complex)*condition_cap,0,false,slot),slot);
  bool sr=false,cr=false;
  MomentInteger source_bound=exact_divide_positive(
      normal_wide(source_norm)*normal_wide(g[width]),normal_wide(cden),&sr);
  MomentInteger condition_bound=exact_divide_positive(
      normal_wide(condition_norm)*normal_wide(g[width]),normal_wide(sden),&cr);
  ys[ds]=add_checked(add_checked(normal_grid(source_bound,0,false,slot),(wide)sr,slot),source_rounding,slot);
  yc[dc]=add_checked(add_checked(normal_grid(condition_bound,0,false,slot),(wide)cr,slot),condition_rounding,slot);
  if(*slot)return;
 }
 for(size_t j=0;j<source_out_row*rows;++j)source_out_hi[j]=source_out[j];
 for(size_t j=0;j<condition_out_row*rows;++j)condition_out_hi[j]=condition_out[j];
}
