// REQ-063 exact matrix absorption component.
//
// Boundary of this component: G and delta-H are already grouped exact deposits; gamma is an
// externally certified dyadic scalar supplied by the caller. This file does not implement the
// listener forward/adjoint, the joint gamma certificate, or paired-port projection. A paired
// caller must supply the declared projected G and symmetrized delta-H. Production absorption is
// eta=1. The only matrix storage is the runtime-width signed-magnitude API in exact_integer.cuh.
//
// One cooperative launch computes one locus crossing. All output arrays are staging destinations;
// caller publishes/swaps Wnext/Hnext/Rnext only when the returned status is OK. The current state
// is never mutated by this kernel, including when a result or workspace reports NEED_CAPACITY.
#include "exact_integer.cuh"
#include <cooperative_groups.h>
#include <stddef.h>
#include <stdint.h>

namespace hnn_epoch_matrix {
namespace cg = cooperative_groups;

enum : uint32_t {
  OK = 0,
  NEED_CAPACITY = 1,
  BAD_VIEW = 2,
  NON_DESCENDING = 3,
  ASYMMETRIC_METRIC = 4,
  EXPONENT_OVERFLOW = 5,
  IDENTITY_DEFECT = 6,
  NEGATIVE_GAIN = 7
};

// An array's exact values and their l1 bounds share the same element indexing but have independent
// runtime limb capacities. For input arrays use value/bound; for staged arrays use out_value and
// out_bound. Every array has one dyadic exponent: x[e] = integer[e] * 2^(-exponent).
struct ExactArray {
  const HnnExactConst *value;
  const HnnExactConst *bound;
  HnnExactMut *out_value;
  HnnExactMut *out_bound;
  size_t entries;
  int64_t exponent;
};

struct Dyadic {
  HnnExactConst value;
  HnnExactConst bound;
  int64_t exponent;
};

struct MatrixCrossing {
  size_t rows; // W, R, G are rows x cols; H and delta-H are cols x cols
  size_t cols;
  ExactArray W, H, R, deltaH, G;
  Dyadic gamma; // caller-certified fresh gain; distinct from eta, which is fixed to one

  // Wnext/Hnext/Rnext carry raw staging exponents in their ExactArray.exponent fields; success
  // canonicalizes their limbs/bounds and returns the resulting exponents through Result.
  ExactArray Hprime, Rprime, direction, step, stepRemainder;
  ExactArray stepH, Wnext, Hnext, Rnext;
  ExactArray fallA, fallQuadratic, fall, fallLower;
  int64_t *majorizer_exponent; // cols entries: actual-scale M_jj = 2^majorizer_exponent[j]

  // Exponents are supplied for grouped inputs and staged outputs. They are scalar metadata,
  // not a fixed limb-width or admission limit.
  int64_t hprime_exponent;
  int64_t rprime_exponent;
  int64_t map_lattice_exponent; // declared W lattice, independent of W's canonical exponent
};

// temporary_words contains 4 value and 4 l1 slots per GPU lane. work_words is the exact_integer
// operation workspace per lane. Their sizes are derived from the caller's live operand capacities.
struct Workspace {
  uint64_t *temporary;
  size_t temporary_words;
  uint64_t *work;
  size_t work_words;
};

struct Result {
  uint32_t status;
  uint64_t required_words;
  uint64_t failing_entry;
  int64_t direction_exponent;
  int64_t step_exponent;
  int64_t fall_exponent;
  int64_t lower_exponent;
  int64_t Hprime_exponent;
  int64_t Rprime_exponent;
  int64_t Hnext_exponent; // canonical output exponent on success
  int64_t Wnext_exponent; // canonical output exponent on success
  int64_t Rnext_exp; // canonical output exponent on success
  int64_t eta;
};

struct Bank {
  HnnExactMut value[4];
  HnnExactMut bound[4];
  uint64_t *work;
  size_t work_capacity;
};

__device__ __forceinline__ void set_error(Result *r, uint32_t code, size_t need, size_t entry) {
  atomicCAS((unsigned int *)&r->status, OK, code);
  atomicMax((unsigned long long *)&r->required_words, (unsigned long long)need);
  if (code != OK) atomicCAS((unsigned long long *)&r->failing_entry, ~0ull, (unsigned long long)entry);
}

__device__ __forceinline__ void check(Result *r, HnnExactResult x, size_t entry) {
  if (x.status == HNN_XINT_NEED_CAPACITY) set_error(r, NEED_CAPACITY, x.required, entry);
  else if (x.status != HNN_XINT_OK) set_error(r, BAD_VIEW, x.required, entry);
}

__device__ __forceinline__ Bank make_bank(Workspace w, size_t tid) {
  Bank b;
  if(!w.temporary||!w.work||w.temporary_words<8||!w.work_words){
    for(int i=0;i<4;++i){b.value[i]={nullptr,0,0,false};b.bound[i]={nullptr,0,0,false};}
    b.work=nullptr;b.work_capacity=0;return b;
  }
  const size_t each = w.temporary_words / 8;
  uint64_t *p = w.temporary + tid * w.temporary_words;
  for (int i = 0; i < 4; ++i) b.value[i] = {p + (size_t)i * each, each, 0, false};
  for (int i = 0; i < 4; ++i) b.bound[i] = {p + (size_t)(4 + i) * each, each, 0, false};
  b.work = w.work + tid * w.work_words;
  b.work_capacity = w.work_words;
  return b;
}

__device__ __forceinline__ HnnExactConst in_value(const ExactArray &a, size_t i) {
  return a.value ? a.value[i] : HnnExactConst{a.out_value[i].limb, a.out_value[i].size, a.out_value[i].negative};
}
__device__ __forceinline__ HnnExactConst in_bound(const ExactArray &a, size_t i) {
  return a.bound ? a.bound[i] : HnnExactConst{a.out_bound[i].limb, a.out_bound[i].size, false};
}
__device__ __forceinline__ HnnExactMut *outv(ExactArray &a, size_t i) { return a.out_value + i; }
__device__ __forceinline__ HnnExactMut *outb(ExactArray &a, size_t i) { return a.out_bound + i; }

__device__ __forceinline__ bool array_view(const ExactArray &a, size_t n, bool output) {
  if (a.entries != n) return false;
  if (output) return a.out_value && a.out_bound;
  return a.value && a.bound;
}

__device__ __forceinline__ HnnExactConst zero_value() { return {nullptr, 0, false}; }

__device__ __forceinline__ HnnExactResult add(HnnExactConst a, HnnExactConst b,
                                               HnnExactMut *o, Bank &k, bool sub=false) {
  return sub ? hnn_exact_sub(a,b,o,k.work,k.work_capacity)
             : hnn_exact_add(a,b,o,k.work,k.work_capacity);
}
__device__ __forceinline__ HnnExactResult mul(HnnExactConst a, HnnExactConst b,
                                               HnnExactMut *o, Bank &k) {
  return hnn_exact_mul(a,b,o,k.work,k.work_capacity);
}
__device__ __forceinline__ HnnExactResult shl(HnnExactConst a, int64_t n,
                                               HnnExactMut *o, Bank &k) {
  return hnn_exact_shift(a,n,o,k.work,k.work_capacity);
}

__device__ __forceinline__ bool checked_add_exp(int64_t a, int64_t b, int64_t *out) {
  if ((b > 0 && a > INT64_MAX-b) || (b < 0 && a < INT64_MIN-b)) return false;
  *out=a+b; return true;
}
__device__ __forceinline__ bool checked_sub_exp(int64_t a, int64_t b, int64_t *out) {
  if ((b>0 && a<INT64_MIN+b) || (b<0 && a>INT64_MAX+b)) return false;
  *out=a-b; return true;
}

__device__ __forceinline__ void certified_add_scaled(const ExactArray &a, size_t ai, int64_t ae,
    const ExactArray &b, size_t bi, int64_t be, int64_t out_exp, ExactArray &out, size_t oi,
    Bank &k, Result *result, size_t id, bool subtract=false) {
  int64_t as,bs;
  if (!checked_sub_exp(out_exp,ae,&as)||!checked_sub_exp(out_exp,be,&bs)||as<0||bs<0) {
    set_error(result,EXPONENT_OVERFLOW,0,id); return;
  }
  HnnExactResult x=shl(in_value(a,ai),as,&k.value[0],k);
  HnnExactResult xb=shl(in_bound(a,ai),as,&k.bound[0],k);
  HnnExactResult y=shl(in_value(b,bi),bs,&k.value[1],k);
  HnnExactResult yb=shl(in_bound(b,bi),bs,&k.bound[1],k);
  check(result,x,id);check(result,xb,id);check(result,y,id);check(result,yb,id);
  if(result->status!=OK)return;
  check(result,add({k.value[0].limb,k.value[0].size,k.value[0].negative},
                   {k.value[1].limb,k.value[1].size,k.value[1].negative},outv(out,oi),k,subtract),id);
  check(result,add({k.bound[0].limb,k.bound[0].size,false},
                   {k.bound[1].limb,k.bound[1].size,false},outb(out,oi),k),id);
  if(result->status==OK && !hnn_exact_certified_valid({in_value(out,oi),in_bound(out,oi)}))
    set_error(result,BAD_VIEW,0,id);
}

__device__ __forceinline__ uint64_t bit_length(HnnExactConst a) {
  if(!a.size)return 0;
  return (uint64_t)(a.size-1)*64 + (64u-(uint64_t)__clzll(a.limb[a.size-1]));
}

// One exact multiply-accumulate for a dot product. The bound accumulates products of l1 bounds,
// so cancellation in the signed value can never make the capacity certificate optimistic.
__device__ __forceinline__ void dot_product(const ExactArray &a,size_t abase,const ExactArray &b,
    size_t bbase,size_t n,HnnExactMut *outvptr,HnnExactMut *outbptr,Bank &k,Result *res,size_t id) {
  HnnExactConst acc=zero_value(), accb=zero_value();
  int slot=0;
  for(size_t j=0;j<n;++j){
    check(res,mul(in_value(a,abase+j),in_value(b,bbase+j),&k.value[3],k),id);
    check(res,mul(in_bound(a,abase+j),in_bound(b,bbase+j),&k.bound[3],k),id);
    if(res->status!=OK)return;
    int next=slot^1;
    check(res,add(acc,{k.value[3].limb,k.value[3].size,k.value[3].negative},&k.value[next],k),id);
    check(res,add(accb,{k.bound[3].limb,k.bound[3].size,false},&k.bound[next],k),id);
    if(res->status!=OK)return;
    acc={k.value[next].limb,k.value[next].size,k.value[next].negative};
    accb={k.bound[next].limb,k.bound[next].size,false}; slot=next;
  }
  check(res,add(acc,zero_value(),outvptr,k),id);
  check(res,add(accb,zero_value(),outbptr,k),id);
}

// Exact quotient/remainder by 2^shift, both toward zero and with the numerator's sign. This is a
// partition, unlike hnn_exact_shift's exact-rebase operation. The caller carries the discarded
// remainder in the receiving news equation.
__device__ __forceinline__ HnnExactResult div_pow2(HnnExactConst a,int64_t shift,
    HnnExactMut *q,HnnExactMut *r) {
  if(!hnn_xvalid(a)||shift<0||!hnn_xmut_valid(q)||!hnn_xmut_valid(r))return {HNN_XINT_BAD_VIEW,0};
  const uint64_t s=(uint64_t)shift, word=s/64, bit=s%64;
  size_t qn=word>=a.size?0:a.size-(size_t)word;
  while(qn){size_t k=(size_t)word+qn-1;uint64_t top=a.limb[k]>>bit;
    if(bit&&k+1<a.size)top|=a.limb[k+1]<<(64-bit);if(top)break;--qn;}
  size_t rn=word<a.size?(size_t)word:a.size;
  uint64_t partial=0;
  if(bit&&word<a.size){partial=a.limb[word]&((uint64_t(1)<<bit)-1);if(partial)rn=(size_t)word+1;}
  while(rn){size_t k=rn-1;uint64_t top=(bit&&word<a.size&&k==(size_t)word)?partial:a.limb[k];if(top)break;--rn;}
  if(q->capacity<qn)return {HNN_XINT_NEED_CAPACITY,qn};
  if(r->capacity<rn)return {HNN_XINT_NEED_CAPACITY,rn};
  for(size_t i=0;i<qn;++i){size_t k=(size_t)word+i;uint64_t v=a.limb[k]>>bit;
    if(bit&&k+1<a.size)v|=a.limb[k+1]<<(64-bit);q->limb[i]=v;}
  for(size_t i=0;i<rn;++i){uint64_t v=0;if(i<(size_t)word)v=a.limb[i];
    else if(bit&&i==(size_t)word)v=partial;r->limb[i]=v;}
  q->size=qn;q->negative=a.negative&&qn!=0;r->size=rn;r->negative=a.negative&&rn!=0;
  return {HNN_XINT_OK,qn};
}

// Conservative nonnegative rebase: out = ceil(a / 2^shift). Capacity is computed exactly before
// the first write. This keeps a certified l1 bound valid when its value numerator is exactly
// divisible but the bound itself is not.
__device__ __forceinline__ uint64_t right_shifted_word(HnnExactConst a,uint64_t word,uint64_t bit,size_t i) {
  size_t k=(size_t)word+i;uint64_t v=a.limb[k]>>bit;
  if(bit&&k+1<a.size)v|=a.limb[k+1]<<(64-bit);return v;
}
__device__ __forceinline__ HnnExactResult ceil_shift_right(HnnExactConst a,uint64_t shift,HnnExactMut *out) {
  if(!hnn_xvalid(a)||a.negative||!hnn_xmut_valid(out))return {HNN_XINT_BAD_VIEW,0};
  const uint64_t word=shift/64,bit=shift%64;
  size_t qn=word>=a.size?0:a.size-(size_t)word;
  while(qn&&right_shifted_word(a,word,bit,qn-1)==0)--qn;
  bool rem=false;const size_t full=(size_t)(word<a.size?word:a.size);
  for(size_t i=0;i<full;++i)if(a.limb[i]){rem=true;break;}
  if(!rem&&bit&&word<a.size&&(a.limb[word]&((uint64_t(1)<<bit)-1)))rem=true;
  bool all_ones=qn!=0;
  for(size_t i=0;i<qn&&all_ones;++i)if(right_shifted_word(a,word,bit,i)!=UINT64_MAX)all_ones=false;
  size_t need=qn;
  if(rem&&(qn==0||all_ones)){if(need==SIZE_MAX)return {HNN_XINT_BAD_VIEW,0};++need;}
  if(out->capacity<need)return {HNN_XINT_NEED_CAPACITY,need};
  for(size_t i=0;i<qn;++i)out->limb[i]=right_shifted_word(a,word,bit,i);
  if(rem){if(qn==0)out->limb[0]=1;else{
      size_t i=0;while(i<qn){uint64_t v=out->limb[i]+1;out->limb[i]=v;if(v)break;++i;}
      if(i==qn)out->limb[qn]=1;
    }}
  out->size=need;out->negative=false;return {HNN_XINT_OK,need};
}

__device__ __forceinline__ uint64_t trailing_zero_bits(HnnExactConst a) {
  if(!a.size)return UINT64_MAX;
  uint64_t whole=0;size_t i=0;while(i<a.size&&a.limb[i]==0){++i;whole+=64;}
  if(i==a.size)return UINT64_MAX;
  return whole+(uint64_t)__ffsll((long long)a.limb[i])-1;
}

__device__ __forceinline__ HnnExactConst bank_value(Bank &k,int i) {
  return {k.value[i].limb,k.value[i].size,k.value[i].negative};
}
__device__ __forceinline__ HnnExactConst bank_bound(Bank &k,int i) {
  return {k.bound[i].limb,k.bound[i].size,false};
}

// Match EpochArray's u32 exponent canonicalization. At nonnegative exponents, cancel common
// powers only down to exponent zero. If a raw exponent is negative, rebase exactly upward to zero.
// Bounds are ceiled only for a right rebase; left rebases are exact. All-zero arrays use exponent 0.
__device__ __forceinline__ void canonicalize_array(ExactArray &a,size_t n,int64_t raw_exp,
    int64_t *canonical_exp,Bank &k,Result *res,size_t id_base) {
  bool any=false;uint64_t common=UINT64_MAX;
  for(size_t i=0;i<n;++i){
    HnnExactCertified c{in_value(a,i),in_bound(a,i)};
    if(!hnn_exact_certified_valid(c)){set_error(res,BAD_VIEW,0,id_base+i);return;}
    if(c.value.size){any=true;uint64_t z=trailing_zero_bits(c.value);if(z<common)common=z;}
  }
  int64_t target=0;uint64_t shift=0;bool left=false;
  if(any){
    if(raw_exp<0){
      if(raw_exp==INT64_MIN){set_error(res,EXPONENT_OVERFLOW,0,id_base);return;}
      left=true;shift=(uint64_t)(-raw_exp);target=0;
    }else{
      shift=common<(uint64_t)raw_exp?common:(uint64_t)raw_exp;
      if(!checked_sub_exp(raw_exp,(int64_t)shift,&target)){
        set_error(res,EXPONENT_OVERFLOW,0,id_base);return;}
    }
  }else target=0;

  for(size_t i=0;i<n;++i){
    HnnExactConst v=in_value(a,i),b=in_bound(a,i);
    if(any){
      if(left){
        check(res,shl(v,(int64_t)shift,&k.value[0],k),id_base+i);
        check(res,shl(b,(int64_t)shift,&k.bound[0],k),id_base+i);
      }else{
        int64_t right=-(int64_t)shift;
        check(res,shl(v,right,&k.value[0],k),id_base+i);
        HnnExactResult br=ceil_shift_right(b,shift,&k.bound[0]);
        if(br.status==HNN_XINT_NEED_CAPACITY)set_error(res,NEED_CAPACITY,br.required,id_base+i);
        else if(br.status!=HNN_XINT_OK)set_error(res,BAD_VIEW,br.required,id_base+i);
      }
      if(res->status!=OK)return;
      check(res,add(bank_value(k,0),zero_value(),outv(a,i),k),id_base+i);
      check(res,add(bank_bound(k,0),zero_value(),outb(a,i),k),id_base+i);
    }else{
      // Exact zero value; only the conservative l1 bound needs a scale conversion.
      if(raw_exp>0){
        HnnExactResult br=ceil_shift_right(b,(uint64_t)raw_exp,&k.bound[0]);
        if(br.status==HNN_XINT_NEED_CAPACITY)set_error(res,NEED_CAPACITY,br.required,id_base+i);
        else if(br.status!=HNN_XINT_OK)set_error(res,BAD_VIEW,br.required,id_base+i);
        if(res->status!=OK)return;
        check(res,add(bank_bound(k,0),zero_value(),outb(a,i),k),id_base+i);
      }else if(raw_exp<0){
        if(raw_exp==INT64_MIN){set_error(res,EXPONENT_OVERFLOW,0,id_base+i);return;}
        check(res,shl(b,-raw_exp,&k.bound[0],k),id_base+i);
        if(res->status!=OK)return;
        check(res,add(bank_bound(k,0),zero_value(),outb(a,i),k),id_base+i);
      }
      outv(a,i)->size=0;outv(a,i)->negative=false;
    }
    if(res->status!=OK)return;
    if(!hnn_exact_certified_valid({in_value(a,i),in_bound(a,i)})){
      set_error(res,BAD_VIEW,0,id_base+i);return;
    }
  }
  a.exponent=target;*canonical_exp=target;
}

__device__ __forceinline__ bool ceil_log2_exact(HnnExactConst x,int64_t *out) {
  uint64_t bits=bit_length(x); if(!bits){*out=0;return true;}
  if(bits>(uint64_t)INT64_MAX)return false;
  bool power=true;for(size_t i=0;i+1<x.size;++i)if(x.limb[i])power=false;
  uint64_t top=x.limb[x.size-1];if(top&(top-1))power=false;
  *out=(int64_t)(bits-(power?1:0));return true;
}

// Accumulate a signed product after any exact power-of-two scaling. The l1 accumulator adds the
// magnitudes of the terms, not the magnitude of the cancelled result.
__device__ __forceinline__ void accumulate_product(HnnExactConst x,HnnExactConst xb,
    HnnExactConst y,HnnExactConst yb,int64_t shift,bool negate,int *slot,Bank &k,Result *res,size_t id) {
  check(res,mul(x,y,&k.value[3],k),id);check(res,mul(xb,yb,&k.bound[3],k),id);
  if(res->status!=OK)return;
  check(res,shl(bank_value(k,3),shift,&k.value[2],k),id);
  check(res,shl(bank_bound(k,3),shift,&k.bound[2],k),id);
  if(res->status!=OK)return;
  HnnExactConst term=bank_value(k,2),termBound=bank_bound(k,2);
  if(negate)term.negative=!term.negative;
  int next=*slot^1;
  check(res,add(bank_value(k,*slot),term,&k.value[next],k),id);
  check(res,add(bank_bound(k,*slot),termBound,&k.bound[next],k),id);
  if(res->status==OK)*slot=next;
}

__device__ __forceinline__ void accumulate_triple(HnnExactConst x,HnnExactConst xb,
    HnnExactConst y,HnnExactConst yb,HnnExactConst z,HnnExactConst zb,int *slot,Bank &k,
    Result *res,size_t id) {
  check(res,mul(x,y,&k.value[3],k),id);check(res,mul(xb,yb,&k.bound[3],k),id);
  if(res->status!=OK)return;
  check(res,mul(bank_value(k,3),z,&k.value[2],k),id);
  check(res,mul(bank_bound(k,3),zb,&k.bound[2],k),id);
  if(res->status!=OK)return;
  int next=*slot^1;
  check(res,add(bank_value(k,*slot),bank_value(k,2),&k.value[next],k),id);
  check(res,add(bank_bound(k,*slot),bank_bound(k,2),&k.bound[next],k),id);
  if(res->status==OK)*slot=next;
}

__device__ __forceinline__ void copy_accumulator(int slot,HnnExactMut *v,HnnExactMut *b,
    Bank &k,Result *res,size_t id) {
  check(res,add(bank_value(k,slot),zero_value(),v,k),id);
  check(res,add(bank_bound(k,slot),zero_value(),b,k),id);
}

__device__ __forceinline__ void exact_fall(MatrixCrossing &m,Result *res,Bank &k) {
  const int64_t ew=m.map_lattice_exponent, eh=m.hprime_exponent, er=m.rprime_exponent;
  int64_t ea,eq,elower;
  int64_t minM=m.majorizer_exponent[0];
  for(size_t j=1;j<m.cols;++j)if(m.majorizer_exponent[j]<minM)minM=m.majorizer_exponent[j];
  if(!checked_add_exp(ew,er,&ea)||!checked_add_exp(ew,ew,&eq)||!checked_add_exp(eq,eh,&eq)||
     !checked_add_exp(eq,1,&eq)||!checked_add_exp(ew,ew,&elower)||
     !checked_add_exp(elower,1,&elower)||!checked_sub_exp(elower,minM,&elower)){
    set_error(res,EXPONENT_OVERFLOW,0,0);return;}

  // A = tr(delta-W R'^T), at exponent ew + er.
  int sa=0;k.value[0].size=0;k.value[0].negative=false;k.bound[0].size=0;k.bound[0].negative=false;
  for(size_t i=0;i<m.rows*m.cols;++i)
    accumulate_product(in_value(m.step,i),in_bound(m.step,i),in_value(m.Rprime,i),in_bound(m.Rprime,i),
      0,false,&sa,k,res,i);
  if(res->status!=OK)return;
  copy_accumulator(sa,outv(m.fallA,0),outb(m.fallA,0),k,res,0);
  if(res->status!=OK)return;

  // Q = tr(delta-W H' delta-W^T), raw exponent 2*ew + eh. H' may have signed off-diagonals.
  int sq=0;k.value[0].size=0;k.value[0].negative=false;k.bound[0].size=0;k.bound[0].negative=false;
  for(size_t i=0;i<m.rows;++i)for(size_t j=0;j<m.cols;++j)for(size_t t=0;t<m.cols;++t){
    size_t ik=i*m.cols+t, tj=t*m.cols+j, ij=i*m.cols+j;
    accumulate_triple(in_value(m.step,ik),in_bound(m.step,ik),in_value(m.Hprime,tj),in_bound(m.Hprime,tj),
      in_value(m.step,ij),in_bound(m.step,ij),&sq,k,res,ik);
    if(res->status!=OK)return;
  }
  copy_accumulator(sq,outv(m.fallQuadratic,0),outb(m.fallQuadratic,0),k,res,0);
  if(res->status!=OK)return;

  // fall = A - Q/2, with both grouped at one exact dyadic exponent.
  int64_t ef=ea>eq?ea:eq;int64_t ashift,qshift;
  if(!checked_sub_exp(ef,ea,&ashift)||!checked_sub_exp(ef,eq,&qshift)||qshift<0){set_error(res,EXPONENT_OVERFLOW,0,0);return;}
  check(res,shl(in_value(m.fallA,0),ashift,&k.value[2],k),0);
  check(res,shl(in_bound(m.fallA,0),ashift,&k.bound[2],k),0);
  check(res,shl(in_value(m.fallQuadratic,0),qshift,&k.value[3],k),0);
  check(res,shl(in_bound(m.fallQuadratic,0),qshift,&k.bound[3],k),0);
  if(res->status!=OK)return;
  check(res,add(bank_value(k,2),bank_value(k,3),outv(m.fall,0),k,true),0);
  check(res,add(bank_bound(k,2),bank_bound(k,3),outb(m.fall,0),k),0);
  if(res->status!=OK)return;
  res->fall_exponent=ef;

  // lower = 1/2 sum_j M_jj |delta-W e_j|^2. Since M_jj=2^m_j,
  // the common exponent is 2*ew + 1 - min_j(m_j).
  int sl=0;k.value[0].size=0;k.value[0].negative=false;k.bound[0].size=0;k.bound[0].negative=false;
  for(size_t j=0;j<m.cols;++j){int64_t sh;
    if(!checked_sub_exp(m.majorizer_exponent[j],minM,&sh)||sh<0){set_error(res,EXPONENT_OVERFLOW,0,j);return;}
    for(size_t i=0;i<m.rows;++i){size_t ix=i*m.cols+j;
      check(res,mul(in_value(m.step,ix),in_value(m.step,ix),&k.value[3],k),ix);
      check(res,mul(in_bound(m.step,ix),in_bound(m.step,ix),&k.bound[3],k),ix);
      if(res->status!=OK)return;
      check(res,shl(bank_value(k,3),sh,&k.value[2],k),ix);
      check(res,shl(bank_bound(k,3),sh,&k.bound[2],k),ix);
      if(res->status!=OK)return;
      int next=sl^1;
      check(res,add(bank_value(k,sl),bank_value(k,2),&k.value[next],k),ix);
      check(res,add(bank_bound(k,sl),bank_bound(k,2),&k.bound[next],k),ix);
      if(res->status!=OK)return;sl=next;
    }
  }
  copy_accumulator(sl,outv(m.fallLower,0),outb(m.fallLower,0),k,res,0);
  if(res->status!=OK)return;
  res->lower_exponent=elower;

  // Compare exact numerators after an exact common-power alignment. A zero representative is
  // lawful; every nonzero representative must meet the strict eta=1 descent bound.
  int64_t ec=res->fall_exponent>res->lower_exponent?res->fall_exponent:res->lower_exponent;
  int64_t fs,ls;if(!checked_sub_exp(ec,res->fall_exponent,&fs)||!checked_sub_exp(ec,res->lower_exponent,&ls)){
    set_error(res,EXPONENT_OVERFLOW,0,0);return;}
  check(res,shl(in_value(m.fall,0),fs,&k.value[0],k),0);
  check(res,shl(in_value(m.fallLower,0),ls,&k.value[1],k),0);
  if(res->status!=OK)return;
  bool nonzero=false;for(size_t i=0;i<m.rows*m.cols;++i)if(in_value(m.step,i).size){nonzero=true;break;}
  HnnExactOrder ord=hnn_exact_compare(bank_value(k,0),bank_value(k,1));
  HnnExactOrder zeroCmp=hnn_exact_compare(bank_value(k,0),zero_value());
  if(ord.status!=HNN_XINT_OK||zeroCmp.status!=HNN_XINT_OK||ord.ordering<0||
     (nonzero&&zeroCmp.ordering<=0)||(!nonzero&&zeroCmp.ordering!=0))
    atomicCAS((unsigned int*)&res->status,OK,NON_DESCENDING);
}

__device__ __forceinline__ void abs_column(const MatrixCrossing &m,size_t col,int64_t *exp,
    Bank &k,Result *res) {
  HnnExactMut acc=k.value[0];acc.size=0;acc.negative=false;
  for(size_t r=0;r<m.cols;++r){
    HnnExactConst x=in_value(m.Hprime,r*m.cols+col);x.negative=false;
    check(res,add({acc.limb,acc.size,false},x,&k.value[1],k),col);
    if(res->status!=OK)return;
    // ping-pong to avoid output/input overlap
    HnnExactMut t=k.value[0];k.value[0]=k.value[1];k.value[1]=t;acc=k.value[0];
  }
  if(!ceil_log2_exact({acc.limb,acc.size,false},exp))set_error(res,EXPONENT_OVERFLOW,0,col);
}

// One crossing of a generic rows x cols locus. This component verifies symmetry of H', computes
// each exact M_j, applies the toward-zero W quotient at eta=1, and checks the exact fall against
// the majorizer lower bound before returning staged next-state views.
__global__ void absorb_crossing(MatrixCrossing m,Workspace ws,Result *result) {
  cg::grid_group grid=cg::this_grid();
  const size_t tid=(size_t)blockIdx.x*blockDim.x+threadIdx.x;
  const size_t nt=(size_t)gridDim.x*blockDim.x;
  if(tid==0){result->status=OK;result->required_words=0;result->failing_entry=~0ull;
    result->direction_exponent=0;result->step_exponent=m.map_lattice_exponent;result->eta=1;
    result->Hprime_exponent=m.hprime_exponent;result->Rprime_exponent=m.rprime_exponent;
    result->Hnext_exponent=m.Hnext.exponent;result->Wnext_exponent=m.Wnext.exponent;
    result->Rnext_exp=m.Rnext.exponent;}
  grid.sync();
  const size_t mn=m.rows*m.cols, nn=m.cols*m.cols;
  if(tid==0 && (m.rows==0||m.cols==0||mn/m.rows!=m.cols||nn/m.cols!=m.cols||
      !array_view(m.W,mn,false)||!array_view(m.H,nn,false)||!array_view(m.R,mn,false)||
      !array_view(m.G,mn,false)||!array_view(m.deltaH,nn,false)||
      !array_view(m.Hprime,nn,true)||!array_view(m.Rprime,mn,true)||
      !array_view(m.direction,mn,true)||!array_view(m.step,mn,true)||
      !array_view(m.stepRemainder,mn,true)||!array_view(m.stepH,mn,true)||
      !array_view(m.Wnext,mn,true)||!array_view(m.Hnext,nn,true)||!array_view(m.Rnext,mn,true)||
      !array_view(m.fallA,1,true)||!array_view(m.fallQuadratic,1,true)||!array_view(m.fall,1,true)||
     !array_view(m.fallLower,1,true)||!m.majorizer_exponent||
      !ws.temporary||!ws.work||ws.temporary_words<8||!ws.work_words))
    set_error(result,BAD_VIEW,0,0);
  if(tid==0&&result->status==OK&&!hnn_exact_certified_valid({m.gamma.value,m.gamma.bound}))
    set_error(result,BAD_VIEW,0,0);
  if(tid==0&&result->status==OK&&m.gamma.value.negative)set_error(result,NEGATIVE_GAIN,0,0);
  if(tid==0&&result->status==OK&&(m.Wnext.exponent<m.W.exponent||
      m.Wnext.exponent<m.map_lattice_exponent||m.Hnext.exponent!=m.hprime_exponent||
      m.Rnext.exponent<m.rprime_exponent||m.Hprime.exponent!=m.hprime_exponent||
      m.Rprime.exponent!=m.rprime_exponent||m.step.exponent!=m.map_lattice_exponent))
    set_error(result,EXPONENT_OVERFLOW,0,0);
  int64_t required_stepH_exp;
  if(tid==0&&result->status==OK&&(!checked_add_exp(m.map_lattice_exponent,m.hprime_exponent,&required_stepH_exp)||
      m.stepH.exponent!=required_stepH_exp))set_error(result,EXPONENT_OVERFLOW,0,0);
  grid.sync();
  Bank k=make_bank(ws,tid);

  // Validate every supplied value/l1 pair before any arithmetic can rely on the certificate.
  // This also admits canonical zero views whose limb pointer is null.
  if(result->status==OK){
    for(size_t i=tid;i<mn;i+=nt){
      if(!hnn_exact_certified_valid({in_value(m.W,i),in_bound(m.W,i)})||
         !hnn_exact_certified_valid({in_value(m.R,i),in_bound(m.R,i)})||
         !hnn_exact_certified_valid({in_value(m.G,i),in_bound(m.G,i)}))
        set_error(result,BAD_VIEW,0,i);
    }
    for(size_t i=tid;i<nn;i+=nt){
      if(!hnn_exact_certified_valid({in_value(m.H,i),in_bound(m.H,i)})||
         !hnn_exact_certified_valid({in_value(m.deltaH,i),in_bound(m.deltaH,i)}))
        set_error(result,BAD_VIEW,0,i);
    }
  }
  grid.sync();

  // H' = H + delta-H and R' = R + gamma G. Inputs are exact groupings with their own exponents.
  if(result->status==OK){
    for(size_t i=tid;i<nn;i+=nt)certified_add_scaled(m.H,i,m.H.exponent,m.deltaH,i,m.deltaH.exponent,
      m.hprime_exponent,m.Hprime,i,k,result,i);
    for(size_t i=tid;i<mn;i+=nt){
      int64_t ge,rs,gs;
      if(!checked_add_exp(m.G.exponent,m.gamma.exponent,&ge)||
         !checked_sub_exp(m.rprime_exponent,m.R.exponent,&rs)||
         !checked_sub_exp(m.rprime_exponent,ge,&gs)||rs<0||gs<0){set_error(result,EXPONENT_OVERFLOW,0,i);continue;}
      check(result,shl(in_value(m.R,i),rs,&k.value[0],k),i);
      check(result,shl(in_bound(m.R,i),rs,&k.bound[0],k),i);
      check(result,mul(in_value(m.G,i),m.gamma.value,&k.value[1],k),i);
      check(result,mul(in_bound(m.G,i),m.gamma.bound,&k.bound[1],k),i);
      check(result,shl({k.value[1].limb,k.value[1].size,k.value[1].negative},gs,&k.value[2],k),i);
      check(result,shl({k.bound[1].limb,k.bound[1].size,false},gs,&k.bound[2],k),i);
      if(result->status==OK){
        check(result,add({k.value[0].limb,k.value[0].size,k.value[0].negative},
                         {k.value[2].limb,k.value[2].size,k.value[2].negative},outv(m.Rprime,i),k),i);
        check(result,add({k.bound[0].limb,k.bound[0].size,false},
                         {k.bound[2].limb,k.bound[2].size,false},outb(m.Rprime,i),k),i);
      }
    }
  }
  grid.sync();

  // Exact metric symmetry is a precondition of the column/row majorizer proof.
  if(result->status==OK)for(size_t i=tid;i<nn;i+=nt){
    size_t r=i/m.cols,c=i%m.cols;HnnExactOrder o=hnn_exact_compare(in_value(m.Hprime,i),in_value(m.Hprime,c*m.cols+r));
    if(o.status!=HNN_XINT_OK||o.ordering!=0)atomicCAS((unsigned int*)&result->status,OK,ASYMMETRIC_METRIC);
  }
  grid.sync();

  // M_jj = 2^ceil(log2(sum_i |H'ij|)); each column is independent.
  if(result->status==OK)for(size_t j=tid;j<m.cols;j+=nt){
    abs_column(m,j,m.majorizer_exponent+j,k,result);
    if(result->status==OK){
      // Convert the numerator's ceil(log2(sum)) to the actual dyadic majorizer exponent.
      // A zero column is assigned M_jj=1 by convention.
      if(!k.value[0].size)m.majorizer_exponent[j]=0;
      else if(!checked_sub_exp(m.majorizer_exponent[j],m.hprime_exponent,&m.majorizer_exponent[j]))
        set_error(result,EXPONENT_OVERFLOW,0,j);
    }
  }
  grid.sync();
  if(tid==0&&result->status==OK){
    int64_t mx=INT64_MIN;
    for(size_t j=0;j<m.cols;++j)if(m.majorizer_exponent[j]>mx)mx=m.majorizer_exponent[j];
    // majorizer_exponent stores the actual power m_j in M_jj = 2^m_j. The exact column
    // sum is represented at Hprime.exponent, so its power is ceil(log2(sum numerator))-e_H.
    // A zero column uses M_jj=1 (power zero).
    if(!checked_add_exp(m.rprime_exponent,mx,&result->direction_exponent))set_error(result,EXPONENT_OVERFLOW,0,0);}
  if(tid==0&&result->status==OK&&(m.direction.exponent!=result->direction_exponent||
      m.stepRemainder.exponent!=result->direction_exponent))set_error(result,EXPONENT_OVERFLOW,0,0);
  grid.sync();

  // D = R' M^-1, represented at one common dyadic exponent to preserve grouped-array storage.
  if(result->status==OK)for(size_t i=tid;i<mn;i+=nt){size_t col=i%m.cols;int64_t sh;
    if(!checked_sub_exp(result->direction_exponent,m.rprime_exponent,&sh)) {set_error(result,EXPONENT_OVERFLOW,0,i);continue;}
    if(!checked_sub_exp(sh,m.majorizer_exponent[col],&sh)||sh<0){set_error(result,EXPONENT_OVERFLOW,0,i);continue;}
    check(result,shl(in_value(m.Rprime,i),sh,outv(m.direction,i),k),i);
    check(result,shl(in_bound(m.Rprime,i),sh,outb(m.direction,i),k),i);
  }
  grid.sync();

  // Toward-zero quotient onto W's lattice; the exact discarded partition is retained explicitly.
  if(result->status==OK)for(size_t i=tid;i<mn;i+=nt){int64_t sh;
    if(!checked_sub_exp(m.map_lattice_exponent,result->direction_exponent,&sh)){set_error(result,EXPONENT_OVERFLOW,0,i);continue;}
    if(sh>=0){check(result,shl(in_value(m.direction,i),sh,outv(m.step,i),k),i);
      check(result,shl(in_bound(m.direction,i),sh,outb(m.step,i),k),i);
      HnnExactMut *rv=outv(m.stepRemainder,i),*rb=outb(m.stepRemainder,i);rv->size=rb->size=0;rv->negative=rb->negative=false;
    }else{
      if(sh==INT64_MIN){set_error(result,EXPONENT_OVERFLOW,0,i);continue;}
      check(result,div_pow2(in_value(m.direction,i),-sh,outv(m.step,i),outv(m.stepRemainder,i)),i);
      check(result,div_pow2(in_bound(m.direction,i),-sh,outb(m.step,i),outb(m.stepRemainder,i)),i);
      // The quotient's term bound is floor(bound/2^shift); the partition remainder's bound is
      // its exact magnitude. This is a named quotient/remainder partition, never a silent shift.
      HnnExactMut *rb=outb(m.stepRemainder,i);HnnExactMut *rv=outv(m.stepRemainder,i);
      if(!hnn_xmut_valid(rb)||!hnn_xmut_valid(rv))set_error(result,BAD_VIEW,0,i);
      else if(rb->capacity<rv->size)set_error(result,NEED_CAPACITY,rv->size,i);
      else{for(size_t z=0;z<rv->size;++z)rb->limb[z]=rv->limb[z];rb->size=rv->size;rb->negative=false;}
    }
  }
  if(result->status==OK)for(size_t i=tid;i<mn;i+=nt)
    certified_add_scaled(m.W,i,m.W.exponent,m.step,i,m.map_lattice_exponent,
      m.Wnext.exponent,m.Wnext,i,k,result,i);
  grid.sync();

  // step-H product and exact carried news. Dot products reduce with signed value and l1 magnitude.
  if(result->status==OK)for(size_t i=tid;i<mn;i+=nt){size_t r=i/m.cols,c=i%m.cols;
    dot_product(m.step,r*m.cols,m.Hprime,c,m.cols,outv(m.stepH,i),outb(m.stepH,i),k,result,i);}
  grid.sync();
  if(result->status==OK)for(size_t i=tid;i<mn;i+=nt){
    int64_t product_exp;
    if(!checked_add_exp(m.map_lattice_exponent,m.hprime_exponent,&product_exp))set_error(result,EXPONENT_OVERFLOW,0,i);
    else certified_add_scaled(m.Rprime,i,m.rprime_exponent,m.stepH,i,product_exp,
      m.Rnext.exponent,m.Rnext,i,k,result,i,true);
  }
  if(tid==0&&result->status==OK)result->Rnext_exp=m.Rnext.exponent;
  if(result->status==OK)for(size_t i=tid;i<nn;i+=nt){
    // Hnext is a staged exact copy at the grouped H' exponent.
    check(result,add(in_value(m.Hprime,i),zero_value(),outv(m.Hnext,i),k),i);
    check(result,add(in_bound(m.Hprime,i),zero_value(),outb(m.Hnext,i),k),i);
  }
  grid.sync();

  // Exact crossing identity: R'' + delta-W H' = R' entrywise. This guards the carried remainder
  // relation with the actual staged outputs rather than relying only on an algebraic comment.
  if(result->status==OK)for(size_t i=tid;i<mn;i+=nt){
    int64_t product_exp, sh_r, sh_p;
    if(!checked_add_exp(m.map_lattice_exponent,m.hprime_exponent,&product_exp)||
       !checked_sub_exp(m.Rnext.exponent,m.Rnext.exponent,&sh_r)||
       !checked_sub_exp(m.Rnext.exponent,product_exp,&sh_p)||sh_r<0||sh_p<0){
      set_error(result,EXPONENT_OVERFLOW,0,i);continue;}
    check(result,shl(in_value(m.Rnext,i),sh_r,&k.value[0],k),i);
    check(result,shl(in_value(m.stepH,i),sh_p,&k.value[1],k),i);
    check(result,add(bank_value(k,0),bank_value(k,1),&k.value[2],k),i);
    int64_t sh_rp;
    if(!checked_sub_exp(m.Rnext.exponent,m.rprime_exponent,&sh_rp)||sh_rp<0){set_error(result,EXPONENT_OVERFLOW,0,i);continue;}
    check(result,shl(in_value(m.Rprime,i),sh_rp,&k.value[3],k),i);
    if(result->status==OK){
      HnnExactOrder o=hnn_exact_compare(bank_value(k,2),bank_value(k,3));
      if(o.status!=HNN_XINT_OK||o.ordering!=0)atomicCAS((unsigned int*)&result->status,OK,IDENTITY_DEFECT);
    }
  }
  grid.sync();

  // Exact fall and its majorizer lower bound are calculated by one lane per locus. They are scalar
  // reductions in this bounded component; matrix dot products above are distributed across lanes.
  if(tid==0&&result->status==OK)exact_fall(m,result,k);
  grid.sync();
  if(tid==0&&result->status==OK)
    canonicalize_array(m.Wnext,mn,m.Wnext.exponent,&result->Wnext_exponent,k,result,0);
  grid.sync();
  if(tid==0&&result->status==OK)
    canonicalize_array(m.Hnext,nn,m.Hnext.exponent,&result->Hnext_exponent,k,result,mn);
  grid.sync();
  if(tid==0&&result->status==OK)
    canonicalize_array(m.Rnext,mn,m.Rnext.exponent,&result->Rnext_exp,k,result,mn+nn);
  grid.sync();
  // No state is committed here. On OK the host swaps the staged exact arrays; on any defect or
  // NEED_CAPACITY it keeps the current arrays and may widen/rebase then retry this same crossing.
}

} // namespace hnn_epoch_matrix
