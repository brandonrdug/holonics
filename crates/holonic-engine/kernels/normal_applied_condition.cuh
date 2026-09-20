// At fixed exact h, retain r=A(h)s+c(h). The condition and mixed-feature coordinates
// are not independent uncertain directions. Contract the same stored M, once, exactly
// before the final grid projection; only A(h) transports the source radius.
extern "C" __global__ void section_normal_applied_condition(
 const int64_t *state,const int64_t *state_hi,
 const int64_t *source,const int64_t *source_hi,uint32_t sa,uint32_t d,uint32_t whole,
 const int64_t *external,const int64_t *external_hi,uint32_t ea,uint32_t joint,
 const int64_t *h,const int64_t *h_hi,uint32_t ha,uint32_t hd,uint32_t hs,uint32_t k,
 uint32_t targets,uint32_t grain,int64_t *out,int64_t *out_hi,
 uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(blockIdx.x||threadIdx.x||upstream_refused(census,lineage,lineage_count,slot))return;
 if(!d||!k||whole<d||(whole&1u)||(d&1u)||(k&1u)||(sa&1u)||!targets||grain<1||grain>120){atomicOr(slot,REFUSED_MALFORMED);return;}
 const size_t f=(size_t)d+k+(size_t)d*(k/2u);
 for(size_t j=0;j<2u*f*targets;++j)if(state[j]!=state_hi[j])atomicOr(slot,REFUSED_MALFORMED);
 for(size_t j=0;j<2u*((size_t)whole+1u);++j)if(source[sa+j]!=source_hi[sa+j])atomicOr(slot,REFUSED_MALFORMED);
 for(uint32_t j=0;j<k;++j)if(h[ha+j]!=h_hi[ha+j])atomicOr(slot,REFUSED_MALFORMED);
 wide den=fibre_current_denominator(h,h_hi,hd,hs,slot),S=(wide)1<<grain;
 const wide *M=(const wide*)state,*x=(const wide*)(source+sa);wide *y=(wide*)out;
 if(*slot||den<=0||x[whole]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 if(joint==1u)for(size_t j=0;j<2u*(2u*(size_t)targets+1u);++j)
  if(external[ea+j]!=external_hi[ea+j])atomicOr(slot,REFUSED_MALFORMED);
 const wide *e=(const wide*)(external+ea);
 if(joint==1u&&e[2u*targets]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
 MomentInteger denominator=normal_wide(S)*normal_wide(den),gain,square;
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
   // A declared incoming-boundary reaction receives the same x as the identity path.
   // Contract (I+A), rather than independently summing two enclosures of x.
   if(joint==2u && i==2u*row)ar=ar+denominator;
   gain=gain+normal_abs(ar)+normal_abs(ai);
   square=square+ar*ar+ai*ai;
   normal_product(yr,yi,ar,ai,normal_wide(x[i]),normal_wide(x[i+1u]),false);
  }
  bool rr=false,ri=false;
  y[2u*row]=normal_grid(exact_divide_positive(yr,denominator,&rr),0,false,slot);
  y[2u*row+1u]=normal_grid(exact_divide_positive(yi,denominator,&ri),0,false,slot);
  if(joint==1u){y[2u*row]=add_checked(y[2u*row],e[2u*row],slot);y[2u*row+1u]=add_checked(y[2u*row+1u],e[2u*row+1u],slot);}
  rounding=add_checked(rounding,(wide)rr+(wide)ri,slot);
 }
 // Frobenius bound of the exactly contracted A(h). Work at dyadic gain scale S;
 // ceil before the integer root is outward and keeps every fractional scale factor.
 bool cap_rem=false,square_rem=false;
 MomentInteger cap_value=exact_divide_positive(gain,normal_wide(den),&cap_rem);
 wide cap=add_checked(normal_grid(cap_value,0,false,slot),(wide)cap_rem,slot);
 MomentInteger square_value=exact_divide_positive(square,normal_wide(den)*normal_wide(den),&square_rem);
 if(square_rem)square_value=square_value+MomentInteger(1);
 wide norm=normal_wave_root_capped(square_value,cap,slot);
 // diag(A,I) acts on the ONE joint Euclidean family. Tail coordinates retain their
 // original dependence on s; restriction and independent rejoining would add rho twice.
 uint32_t tail=joint==1u?whole-d:0u, width=2u*targets+tail;
 if(tail&&norm<S)norm=S;
 bool rem=false;MomentInteger bound=exact_divide_positive(normal_wide(norm)*normal_wide(x[whole]),normal_wide(S),&rem);
 y[width]=add_checked(add_checked(normal_grid(bound,0,false,slot),(wide)rem,slot),rounding,slot);
 if(joint==1u)y[width]=add_checked(y[width],e[2u*targets],slot);
 for(uint32_t j=0;j<tail;++j)y[2u*targets+j]=x[d+j];
 if(*slot)return;for(size_t j=0;j<2u*((size_t)width+1u);++j)out_hi[j]=out[j];
}

// The same law over a section of rows, where the condition of a row may itself be an
// enclosure. Write s = x + eps and c = h + delta with |eps| <= rho_s, |delta| <= rho_c. Then
//
//   M phi(s,c) = M phi(x,h) + A(h) eps + L_x delta + Q(delta, eps),
//   L_x delta  = c-block delta + mixed block contracted with (delta (x) x),
//
// so the transported radius is ||A(h)|| rho_s + ||L_x|| rho_c + ||Q|| rho_s rho_c. Each norm
// is the complex Frobenius bound of its own block, taken outward; at rho_c = 0 every added
// term vanishes and the row equals the single-row owner above, bit for bit. A point condition
// row enters through its rational denominator, an enclosed one at the dyadic scale S.
extern "C" __global__ void section_normal_applied_condition_rows(
 const int64_t *state,const int64_t *state_hi,
 const int64_t *source,const int64_t *source_hi,uint32_t source_stride,
 const int64_t *condition,const int64_t *condition_hi,uint32_t condition_stride,
 uint32_t condition_enclosed,uint32_t condition_rational,
 uint32_t rows,uint32_t d,uint32_t k,uint32_t targets,uint32_t identity,uint32_t grain,
 int64_t *out,int64_t *out_hi,int64_t *flags,
 uint32_t *global_slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count){
 if(threadIdx.x)return;uint32_t row=blockIdx.x;if(row>=rows)return;uint32_t *status=(uint32_t *)(flags+(SLOT_WORDS/2u)*(size_t)row);uint32_t *slot=status;for(uint32_t i=0;i<SLOT_WORDS;++i)status[i]=0;if(upstream_refused(census,lineage,lineage_count,status))return; (void)global_slot;
 if(!rows||!d||!k||(d&1u)||(k&1u)||!targets||grain<1||grain>120||identity>1||condition_enclosed>1
    ||(identity&&d!=2u*targets)){atomicOr(slot,REFUSED_MALFORMED);return;}
 const uint32_t width=identity?d:2u*targets;
 const size_t f=(size_t)d+k+(size_t)d*(k/2u);
 for(size_t j=0;j<2u*f*targets;++j)if(state[j]!=state_hi[j])atomicOr(slot,REFUSED_MALFORMED);
 if(*slot)return;
 const wide *M=(const wide *)state;
 const wide S=(wide)1<<grain;
 const size_t source_row=2u*((size_t)d+1u),out_row=2u*((size_t)width+1u);const size_t source_at=(size_t)row*source_stride,condition_at=(size_t)row*condition_stride,out_at=(size_t)row*out_row;
 extern __shared__ wide applied_condition_scratch[];
 {
  const size_t sa=source_at,ca=condition_at;
  for(size_t j=0;j<source_row;++j)if(source[sa+j]!=source_hi[sa+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
  const wide *x=(const wide *)(source+sa);
  if(x[d]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
  wide den,rc=0;
  if(condition_enclosed){
   for(size_t j=0;j<2u*((size_t)k+1u);++j)
    if(condition[ca+j]!=condition_hi[ca+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
   const wide *h=(const wide *)(condition+ca);
   if(h[k]<0){atomicOr(slot,REFUSED_MALFORMED);return;}
   for(uint32_t j=0;j<k;++j)applied_condition_scratch[j]=h[j];
   den=S;rc=h[k];
  }else{
   den=fibre_current_denominator(condition+ca,condition_hi+ca,
       condition_rational?k:UINT32_MAX,UINT32_MAX,slot);
   if(*slot)return;
   for(uint32_t j=0;j<k;++j){
    if(condition[ca+j]!=condition_hi[ca+j]){atomicOr(slot,REFUSED_MALFORMED);return;}
    applied_condition_scratch[j]=condition[ca+j];
   }
  }
  if(den<=0){atomicOr(slot,REFUSED_MALFORMED);return;}
  const wide *h=applied_condition_scratch;
  wide *y=(wide *)(out+out_at);
  MomentInteger denominator=normal_wide(S)*normal_wide(den);
  MomentInteger gain,square,condition_gain,condition_square,mixed_gain,mixed_square;
  wide rounding=0;
  for(uint32_t t=0;t<targets;++t){
   const wide *a=M+(size_t)t*f;MomentInteger yr,yi;
   for(uint32_t j=0;j<k;j+=2u)
    normal_product(yr,yi,normal_wide(a[d+j]),normal_wide(a[d+j+1u]),
        normal_wide(h[j])*normal_wide(S),normal_wide(h[j+1u])*normal_wide(S),false);
   for(uint32_t i=0;i<d;i+=2u){
    MomentInteger ar=normal_wide(a[i])*normal_wide(den),ai=normal_wide(a[i+1u])*normal_wide(den);
    for(uint32_t j=0;j<k/2u;++j){
     size_t at=(size_t)d+k+(size_t)j*d+i;
     normal_product(ar,ai,normal_wide(a[at]),normal_wide(a[at+1u]),
         normal_wide(h[2u*j]),normal_wide(h[2u*j+1u]),false);
    }
    // The identity path shares x with the reaction; contract (I+A) rather than summing
    // two enclosures of the same x, exactly as the single-row owner does.
    if(identity&&i==2u*t)ar=ar+denominator;
    gain=gain+normal_abs(ar)+normal_abs(ai);
    square=square+ar*ar+ai*ai;
    normal_product(yr,yi,ar,ai,normal_wide(x[i]),normal_wide(x[i+1u]),false);
   }
   bool rr=false,ri=false;
   y[2u*t]=normal_grid(exact_divide_positive(yr,denominator,&rr),0,false,slot);
   y[2u*t+1u]=normal_grid(exact_divide_positive(yi,denominator,&ri),0,false,slot);
   rounding=add_checked(rounding,(wide)rr+(wide)ri,slot);
   if(rc)for(uint32_t j=0;j<k/2u;++j){
    // L_x at denominator S^2: the condition block scaled by S, plus the mixed block
    // contracted with the source centre. The identity path does not depend on c.
    MomentInteger lr=normal_wide(a[d+2u*j])*normal_wide(S),li=normal_wide(a[d+2u*j+1u])*normal_wide(S);
    for(uint32_t i=0;i<d;i+=2u){
     size_t at=(size_t)d+k+(size_t)j*d+i;
     normal_product(lr,li,normal_wide(a[at]),normal_wide(a[at+1u]),
         normal_wide(x[i]),normal_wide(x[i+1u]),false);
    }
    condition_gain=condition_gain+normal_abs(lr)+normal_abs(li);
    condition_square=condition_square+lr*lr+li*li;
   }
   if(rc&&x[d])for(uint32_t j=0;j<k/2u;++j)for(uint32_t i=0;i<d;i+=2u){
    size_t at=(size_t)d+k+(size_t)j*d+i;
    mixed_gain=mixed_gain+normal_abs(normal_wide(a[at]))+normal_abs(normal_wide(a[at+1u]));
    mixed_square=mixed_square+normal_wide(a[at])*normal_wide(a[at])
        +normal_wide(a[at+1u])*normal_wide(a[at+1u]);
   }
  }
  bool cap_rem=false,square_rem=false;
  MomentInteger cap_value=exact_divide_positive(gain,normal_wide(den),&cap_rem);
  wide cap=add_checked(normal_grid(cap_value,0,false,slot),(wide)cap_rem,slot);
  MomentInteger square_value=exact_divide_positive(square,normal_wide(den)*normal_wide(den),&square_rem);
  if(square_rem)square_value=square_value+MomentInteger(1);
  wide norm=normal_wave_root_capped(square_value,cap,slot);
  bool rem=false;
  MomentInteger bound=exact_divide_positive(normal_wide(norm)*normal_wide(x[d]),normal_wide(S),&rem);
  wide radius=add_checked(add_checked(normal_grid(bound,0,false,slot),(wide)rem,slot),rounding,slot);
  if(rc){
   // L_x is carried at denominator S^2. Divide the gain and the square by that scale BEFORE
   // the root, exactly as A(h) does above, so the rooted magnitude stays in its carrier.
   bool condition_cap_rem=false,condition_square_rem=false;
   MomentInteger condition_cap_value=exact_divide_positive(condition_gain,normal_wide(S),&condition_cap_rem);
   wide condition_cap=add_checked(normal_grid(condition_cap_value,0,false,slot),(wide)condition_cap_rem,slot);
   MomentInteger condition_square_value=exact_divide_positive(
       condition_square,normal_wide(S)*normal_wide(S),&condition_square_rem);
   if(condition_square_rem)condition_square_value=condition_square_value+MomentInteger(1);
   wide condition_norm=normal_wave_root_capped(condition_square_value,condition_cap,slot);
   bool condition_rem=false;
   MomentInteger condition_bound=exact_divide_positive(
       normal_wide(condition_norm)*normal_wide(rc),normal_wide(S),&condition_rem);
   radius=add_checked(radius,
       add_checked(normal_grid(condition_bound,0,false,slot),(wide)condition_rem,slot),slot);
   if(x[d]){
    wide mixed_norm=normal_wave_root_capped(mixed_square,normal_grid(mixed_gain,0,false,slot),slot);
    bool first_rem=false,second_rem=false;
    MomentInteger first=exact_divide_positive(
        normal_wide(mixed_norm)*normal_wide(x[d]),normal_wide(S),&first_rem);
    wide step=add_checked(normal_grid(first,0,false,slot),(wide)first_rem,slot);
    MomentInteger second=exact_divide_positive(
        normal_wide(step)*normal_wide(rc),normal_wide(S),&second_rem);
    radius=add_checked(radius,
        add_checked(normal_grid(second,0,false,slot),(wide)second_rem,slot),slot);
   }
  }
  y[width]=radius;
  if(*status)return;
 }
 for(size_t j=0;j<out_row;++j)out_hi[out_at+j]=out[out_at+j];
}
