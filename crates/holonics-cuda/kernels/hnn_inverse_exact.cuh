// Runtime-width realization of the existing chart law (Lean HNN/LatticeWord).
// A=a/2^L_A, X=xi/2^L_c, scale=2^(L_A+L_c).
// rho=scale*I-a*xi; next=xi+nearest(xi*rho/scale), ties upward.
// Every dot retains its actual l1 bound. Charts keep the native signed64 contract;
// all intermediates and certificates use caller-owned exact limb spans.
#pragma once
#include "exact_integer.cuh"
#include <cooperative_groups.h>

struct HnnInverseExactWord { uint64_t offset,size; uint32_t negative,reserved; };
struct HnnInverseExactValue { uint64_t size; uint32_t negative,reserved; };
struct HnnInverseExactResult {
    uint32_t status,committed;
    uint64_t required_words,failing_entry;
};
static_assert(sizeof(HnnInverseExactWord)==24,"inverse input ABI");
static_assert(sizeof(HnnInverseExactValue)==16,"inverse output ABI");
static_assert(sizeof(HnnInverseExactResult)==24,"inverse result ABI");

namespace hnn_inverse_exact_detail {
__device__ __forceinline__ HnnExactConst view(const HnnExactMut &x) {
    return {x.size?x.limb:nullptr,x.size,x.negative};
}
__device__ __forceinline__ void fail(HnnInverseExactResult *r,uint32_t status,uint64_t need,uint64_t entry) {
    // Existing refusal precedence: an upstream operand dominates a chart-word
    // refusal; capacity never turns a malformed input into an admitted value.
    atomicMax(&r->status,status);
    atomicMax((unsigned long long*)&r->required_words,(unsigned long long)need);
    atomicMin((unsigned long long*)&r->failing_entry,(unsigned long long)entry);
}
__device__ __forceinline__ bool check(HnnExactResult op,HnnInverseExactResult *r,uint64_t entry) {
    if(op.status==HNN_XINT_OK)return true;
    fail(r,op.status==HNN_XINT_NEED_CAPACITY?1u:2u,op.required,entry);return false;
}
__device__ __forceinline__ bool input(HnnInverseExactWord word,const uint64_t *arena,
    uint64_t words,HnnExactConst *out) {
    if(word.reserved || word.negative>1 || word.offset>words || word.size>words-word.offset)return false;
    *out={word.size?arena+word.offset:nullptr,(size_t)word.size,word.negative!=0};
    return hnn_xvalid(*out);
}
__device__ __forceinline__ HnnExactConst signed_word(int64_t n,uint64_t *magnitude) {
    *magnitude=n<0?uint64_t(-(n+1))+1:uint64_t(n);
    return {*magnitude?magnitude:nullptr,*magnitude?size_t(1):size_t(0),n<0};
}
__device__ __forceinline__ void save(uint64_t index,HnnExactConst value,uint64_t capacity,
    uint64_t *out,HnnInverseExactValue *meta) {
    for(size_t k=0;k<value.size;++k)out[index*capacity+k]=value.limb[k];
    meta[index]={(uint64_t)value.size,value.negative?1u:0u,0u};
}
__device__ __forceinline__ HnnExactConst load(uint64_t index,uint64_t capacity,
    const uint64_t *out,const HnnInverseExactValue *meta) {
    const HnnInverseExactValue m=meta[index];
    return {m.size?out+index*capacity:nullptr,(size_t)m.size,m.negative!=0};
}

// Bank: term, signed ping-pong, l1 ping-pong, quotient, remainder, temporary,
// then 2*capacity+1 scratch. No operation aliases any input with its output.
__device__ __forceinline__ void residual(uint64_t entry,uint64_t n,uint64_t capacity,
    const uint64_t *arena,uint64_t arena_words,const HnnInverseExactWord *a,HnnExactConst scale,
    const int64_t *x,const uint32_t *status,uint64_t *out,HnnInverseExactValue *meta,
    uint64_t *bank,HnnInverseExactResult *result) {
    const uint64_t row=entry/n,col=entry%n;
    HnnExactMut term{bank,(size_t)capacity,0,false};
    HnnExactMut sums[2]={{bank+capacity,(size_t)capacity,0,false},{bank+2*capacity,(size_t)capacity,0,false}};
    HnnExactMut bounds[2]={{bank+3*capacity,(size_t)capacity,0,false},{bank+4*capacity,(size_t)capacity,0,false}};
    uint64_t *work=bank+8*capacity;const size_t workcap=2*capacity+1;
    unsigned current=0;
    for(uint64_t k=0;k<n;++k) {
        if(status && status[k*n+col]){fail(result,8,0,entry);return;}
        HnnExactConst av;uint64_t magnitude;
        if(!input(a[row*n+k],arena,arena_words,&av)){fail(result,2,0,entry);return;}
        const HnnExactConst xv=signed_word(x[k*n+col],&magnitude);
        if(!check(hnn_exact_mul(av,xv,&term,work,workcap),result,entry))return;
        const unsigned next=1-current;
        if(!check(hnn_exact_add(view(sums[current]),view(term),&sums[next],work,workcap),result,entry))return;
        HnnExactConst absolute=view(term);absolute.negative=false;
        if(!check(hnn_exact_add(view(bounds[current]),absolute,&bounds[next],work,workcap),result,entry))return;
        current=next;
    }
    const unsigned next=1-current;
    const HnnExactConst diagonal=row==col?scale:HnnExactConst{nullptr,0,false};
    if(!check(hnn_exact_sub(diagonal,view(sums[current]),&sums[next],work,workcap),result,entry))return;
    if(!check(hnn_exact_add(diagonal,view(bounds[current]),&bounds[next],work,workcap),result,entry))return;
    if(!hnn_exact_certified_valid({view(sums[next]),view(bounds[next])})){fail(result,2,0,entry);return;}
    save(2*entry,view(sums[next]),capacity,out,meta);
    save(2*entry+1,view(bounds[next]),capacity,out,meta);
}

__device__ __forceinline__ void certificate(uint64_t n,uint64_t capacity,uint64_t *out,
    HnnInverseExactValue *meta,uint64_t *bank,HnnInverseExactResult *result) {
    HnnExactMut sums[2]={{bank+capacity,(size_t)capacity,0,false},{bank+2*capacity,(size_t)capacity,0,false}};
    HnnExactMut best{bank+5*capacity,(size_t)capacity,0,false};
    uint64_t *work=bank+8*capacity;const size_t workcap=2*capacity+1;
    for(uint64_t row=0;row<n;++row){
        unsigned current=0;sums[0].size=0;sums[0].negative=false;
        for(uint64_t col=0;col<n;++col){
            HnnExactConst value=load(2*(row*n+col),capacity,out,meta);value.negative=false;
            const unsigned next=1-current;
            if(!check(hnn_exact_add(view(sums[current]),value,&sums[next],work,workcap),result,row*n+col))return;
            current=next;
        }
        if(hnn_xcmp(sums[current].limb,sums[current].size,best.limb,best.size)>0)
            hnn_xcommit(&best,sums[current].limb,sums[current].size,false);
    }
    save(4*n*n,view(best),capacity,out,meta);
}

__device__ __forceinline__ void refine(uint64_t entry,uint64_t n,uint64_t capacity,HnnExactConst scale,
    const int64_t *x,const uint32_t *status,uint64_t *out,HnnInverseExactValue *meta,
    int64_t *staged,uint64_t *bank,HnnInverseExactResult *result) {
    const uint64_t row=entry/n,col=entry%n;
    HnnExactMut term{bank,(size_t)capacity,0,false};
    HnnExactMut sums[2]={{bank+capacity,(size_t)capacity,0,false},{bank+2*capacity,(size_t)capacity,0,false}};
    HnnExactMut bounds[2]={{bank+3*capacity,(size_t)capacity,0,false},{bank+4*capacity,(size_t)capacity,0,false}};
    HnnExactMut q{bank+5*capacity,(size_t)capacity,0,false},rem{bank+6*capacity,(size_t)capacity,0,false};
    HnnExactMut tmp{bank+7*capacity,(size_t)capacity,0,false};
    uint64_t *work=bank+8*capacity;const size_t workcap=2*capacity+1;unsigned current=0;
    for(uint64_t k=0;k<n;++k){
        if(status && status[row*n+k]){fail(result,8,0,entry);return;}
        uint64_t magnitude;HnnExactConst xv=signed_word(x[row*n+k],&magnitude);
        if(!check(hnn_exact_mul(xv,load(2*(k*n+col),capacity,out,meta),&term,work,workcap),result,entry))return;
        const unsigned next=1-current;
        if(!check(hnn_exact_add(view(sums[current]),view(term),&sums[next],work,workcap),result,entry))return;
        HnnExactConst absolute=view(term);absolute.negative=false;
        if(!check(hnn_exact_add(view(bounds[current]),absolute,&bounds[next],work,workcap),result,entry))return;
        current=next;
    }
    if(!hnn_exact_certified_valid({view(sums[current]),view(bounds[current])})){fail(result,2,0,entry);return;}
    HnnExactDivResult division=hnn_exact_divrem(view(sums[current]),scale,&q,&rem,work,workcap);
    if(division.status!=HNN_XINT_OK){
        uint64_t need=division.quotient_required>division.remainder_required?division.quotient_required:division.remainder_required;
        fail(result,division.status==HNN_XINT_NEED_CAPACITY?1u:2u,need,entry);return;
    }
    // Compare 2*|remainder| with scale. At a negative tie, truncation already
    // chose the upward point. At a positive tie it must advance by one.
    HnnExactConst absolute=view(rem);absolute.negative=false;
    if(!check(hnn_exact_shift(absolute,1,&tmp,work,workcap),result,entry))return;
    const int order=hnn_xcmp(tmp.limb,tmp.size,scale.limb,scale.size);
    const bool adjust=order>0 || (order==0&&!rem.negative&&rem.size);
    if(adjust){
        uint64_t one=1;HnnExactConst unit{&one,1,rem.negative};
        if(!check(hnn_exact_add(view(q),unit,&tmp,work,workcap),result,entry))return;
        hnn_xcommit(&q,tmp.limb,tmp.size,tmp.negative);
        HnnExactConst signed_scale=scale;signed_scale.negative=rem.negative;
        if(!check(hnn_exact_sub(view(rem),signed_scale,&tmp,work,workcap),result,entry))return;
        hnn_xcommit(&rem,tmp.limb,tmp.size,tmp.negative);
    }
    uint64_t magnitude;HnnExactConst old=signed_word(x[entry],&magnitude);
    if(!check(hnn_exact_add(old,view(q),&tmp,work,workcap),result,entry))return;
    if(tmp.size>1 || (tmp.size && (tmp.negative?tmp.limb[0]>(uint64_t(1)<<63):tmp.limb[0]>INT64_MAX))){fail(result,4,0,entry);return;}
    const uint64_t mag=tmp.size?tmp.limb[0]:0;
    staged[entry]=tmp.negative?(mag==(uint64_t(1)<<63)?INT64_MIN:-int64_t(mag)):int64_t(mag);
    save(2*n*n+2*entry,view(rem),capacity,out,meta);
    save(2*n*n+2*entry+1,view(bounds[current]),capacity,out,meta);
}
} // namespace hnn_inverse_exact_detail

extern "C" __global__ void hnn_inverse_exact(
    const uint64_t *arena,uint64_t arena_words,const HnnInverseExactWord *operators,
    HnnInverseExactWord scale_word,uint64_t n,uint64_t capacity,uint32_t step,
    const int64_t *charts,const uint32_t *chart_status,int64_t *next,uint32_t *next_status,
    uint64_t *output,HnnInverseExactValue *meta,int64_t *staged,
    uint64_t *scratch,uint64_t scratch_words,HnnInverseExactResult *result
) {
    namespace cg=cooperative_groups;auto grid=cg::this_grid();
    using namespace hnn_inverse_exact_detail;
    const uint64_t lane=uint64_t(blockIdx.x)*blockDim.x+threadIdx.x,lanes=uint64_t(gridDim.x)*blockDim.x;
    if(lane==0)*result={0,0,0,UINT64_MAX};grid.sync();
    HnnExactConst scale;
    // The host checks all extent products and provides exactly this complete surface.
    if(!n || n>UINT64_MAX/n || !capacity || capacity>(UINT64_MAX-1)/10 ||
       lanes>UINT64_MAX/(10*capacity+1) || scratch_words<lanes*(10*capacity+1) || step>1 ||
       !input(scale_word,arena,arena_words,&scale) || !scale.size || scale.negative){
        if(lane==0)fail(result,2,0,0);
    }
    grid.sync();if(result->status)return;
    uint64_t *bank=scratch+lane*(10*capacity+1);const uint64_t entries=n*n;
    for(uint64_t entry=lane;entry<entries;entry+=lanes)
        residual(entry,n,capacity,arena,arena_words,operators,scale,charts,chart_status,output,meta,bank,result);
    grid.sync();if(result->status)return;
    if(lane==0)certificate(n,capacity,output,meta,bank,result);
    grid.sync();if(result->status)return;
    if(step)for(uint64_t entry=lane;entry<entries;entry+=lanes)
        refine(entry,n,capacity,scale,charts,chart_status,output,meta,staged,bank,result);
    grid.sync();if(result->status)return;
    // Publication follows the whole-grid check: no short-capacity, upstream or
    // signed64 failure can leave a partially moved chart or status array.
    if(step)for(uint64_t entry=lane;entry<entries;entry+=lanes){next[entry]=staged[entry];if(next_status)next_status[entry]=0;}
    grid.sync();if(lane==0)result->committed=1;
}
