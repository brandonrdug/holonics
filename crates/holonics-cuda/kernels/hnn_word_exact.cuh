// Runtime-width applications and carried splits of the executed word's maps.
//
// This is a stage of the existing word law, not a replacement law or an authored
// answer operator. Matrix entries and vector coordinates are immutable actual
// producing operands. The same matrix is read by rows for the forward stage and
// by columns for its adjoint. Every product sum retains its actual l1 bound.
// A second resident stage carries nearest-point remainders through the ordered
// vectors, including an arbitrary positive (and possibly odd) denominator.
// All output is staging until the last cooperative barrier publishes committed.
#pragma once
#include "exact_integer.cuh"
#include <cooperative_groups.h>
#include <stddef.h>
#include <stdint.h>

struct HnnWordExactWord {
    uint64_t offset, size;
    uint32_t negative, reserved;
};
struct HnnWordExactOutput {
    uint64_t value_size, bound_size;
    uint32_t negative, reserved;
};
struct HnnWordExactResult {
    uint32_t status, committed;
    uint64_t required_words, failing_entry;
};
static_assert(sizeof(HnnWordExactWord)==24,"word exact input ABI");
static_assert(sizeof(HnnWordExactOutput)==24,"word exact output ABI");
static_assert(sizeof(HnnWordExactResult)==24,"word exact result ABI");
static_assert(offsetof(HnnWordExactWord,negative)==16,"word exact sign ABI");
static_assert(offsetof(HnnWordExactResult,required_words)==8,"word exact capacity ABI");
static_assert(sizeof(size_t)==sizeof(uint64_t),"word exact arena offsets are 64-bit");

namespace hnn_word_exact_detail {
enum : uint32_t { OK=0, CAPACITY=1, BAD_VIEW=2, EXTENT=3, NOT_RUN=4 };
__device__ __forceinline__ bool mul_size(uint64_t a,uint64_t b,uint64_t *out) {
    if(a&&b>UINT64_MAX/a)return false;*out=a*b;return true;
}
__device__ __forceinline__ bool add_size(uint64_t a,uint64_t b,uint64_t *out) {
    if(b>UINT64_MAX-a)return false;*out=a+b;return true;
}
__device__ __forceinline__ void fail(HnnWordExactResult *r,uint32_t status,
    uint64_t required,uint64_t entry) {
    atomicCAS((unsigned int*)&r->status,OK,status);
    atomicMax((unsigned long long*)&r->required_words,(unsigned long long)required);
    atomicMin((unsigned long long*)&r->failing_entry,(unsigned long long)entry);
}
__device__ __forceinline__ bool check(HnnExactResult op,HnnWordExactResult *r,uint64_t entry) {
    if(op.status==HNN_XINT_OK)return true;
    fail(r,op.status==HNN_XINT_NEED_CAPACITY?CAPACITY:BAD_VIEW,
         op.status==HNN_XINT_NEED_CAPACITY?op.required:0,entry);return false;
}
__device__ __forceinline__ HnnExactConst view(const HnnExactMut &x) {
    return {x.size?x.limb:nullptr,x.size,x.negative};
}
__device__ __forceinline__ bool input(HnnWordExactWord w,const uint64_t *arena,
    uint64_t words,HnnExactConst *x) {
    if(w.reserved||w.negative>1||w.offset>words||w.size>words-w.offset
       ||(w.size&&!arena))return false;
    *x={w.size?arena+w.offset:nullptr,(size_t)w.size,w.negative!=0};return hnn_xvalid(*x);
}
__device__ __forceinline__ bool staged(uint64_t entry,const uint64_t *arena,
    uint64_t capacity,const HnnWordExactOutput *meta,HnnExactConst *value,HnnExactConst *bound) {
    const auto m=meta[entry];
    if(m.reserved||m.negative>1||m.value_size>capacity||m.bound_size>capacity)return false;
    const uint64_t *at=arena+2*entry*capacity;
    *value={m.value_size?at:nullptr,(size_t)m.value_size,m.negative!=0};
    *bound={m.bound_size?at+capacity:nullptr,(size_t)m.bound_size,false};
    return hnn_exact_certified_valid({*value,*bound});
}
__device__ __forceinline__ void publish(uint64_t entry,HnnExactConst value,HnnExactConst bound,
    uint64_t capacity,uint64_t *arena,HnnWordExactOutput *meta) {
    uint64_t *at=arena+2*entry*capacity;
    for(size_t i=0;i<value.size;++i)at[i]=value.limb[i];
    for(size_t i=0;i<bound.size;++i)at[capacity+i]=bound.limb[i];
    meta[entry]={(uint64_t)value.size,(uint64_t)bound.size,value.negative?1u:0u,0u};
}

// One lane owns term + two sums + two l1 bounds; operation scratch follows.
__device__ __forceinline__ void apply(uint64_t entry,uint64_t rows,uint64_t columns,
    bool transpose,uint64_t capacity,const uint64_t *arena,uint64_t arena_words,
    const HnnWordExactWord *matrix,const HnnWordExactWord *vectors,
    uint64_t *output,HnnWordExactOutput *meta,uint64_t *bank,HnnWordExactResult *result) {
    const uint64_t outputs=transpose?columns:rows,inputs=transpose?rows:columns;
    const uint64_t vector=entry/outputs,row=entry%outputs;
    HnnExactMut term{bank,(size_t)capacity,0,false};
    HnnExactMut sums[2]={{bank+capacity,(size_t)capacity,0,false},
                        {bank+2*capacity,(size_t)capacity,0,false}};
    HnnExactMut bounds[2]={{bank+3*capacity,(size_t)capacity,0,false},
                          {bank+4*capacity,(size_t)capacity,0,false}};
    uint64_t *work=bank+5*capacity;const size_t workcap=(size_t)(2*capacity+1);
    unsigned current=0;
    for(uint64_t j=0;j<inputs;++j) {
        HnnExactConst a,b;
        const uint64_t matrix_at=transpose?j*columns+row:row*columns+j;
        if(!input(matrix[matrix_at],arena,arena_words,&a)
           ||!input(vectors[vector*inputs+j],arena,arena_words,&b)) {
            fail(result,BAD_VIEW,0,entry);return;
        }
        if(!check(hnn_exact_mul(a,b,&term,work,workcap),result,entry))return;
        const unsigned next=1-current;
        if(!check(hnn_exact_add(view(sums[current]),view(term),&sums[next],work,workcap),result,entry))return;
        HnnExactConst magnitude=view(term);magnitude.negative=false;
        if(!check(hnn_exact_add(view(bounds[current]),magnitude,&bounds[next],work,workcap),result,entry))return;
        current=next;
    }
    if(!hnn_exact_certified_valid({view(sums[current]),view(bounds[current])})) {
        fail(result,BAD_VIEW,0,entry);return;
    }
    publish(entry,view(sums[current]),view(bounds[current]),capacity,output,meta);
}

// One lane owns a coordinate's complete ordered carry. The split is
// q = floor(n/d + 1/2), r = n - q*d, so negative ties go upward too.
// Bank: shifted, sum, q, r, twice-r, adjusted-q, adjusted-r, remainder,
// shifted l1, split l1, then 2*capacity+1 operation scratch.
__device__ __forceinline__ void carry(uint64_t column,uint64_t vectors,uint64_t columns,
    bool reverse,int64_t shift,HnnExactConst divisor,uint64_t input_capacity,
    const uint64_t *input_arena,const HnnWordExactOutput *input_meta,uint64_t capacity,
    uint64_t *output,HnnWordExactOutput *meta,uint64_t *bank,HnnWordExactResult *result) {
    HnnExactMut x[10];
    for(unsigned i=0;i<10;++i)x[i]={bank+i*capacity,(size_t)capacity,0,false};
    uint64_t *work=bank+10*capacity;const size_t workcap=(size_t)(2*capacity+1);
    const uint64_t one_word=1;const HnnExactConst one{&one_word,1,false};
    for(uint64_t ordinal=0;ordinal<vectors;++ordinal) {
        const uint64_t vector=reverse?vectors-1-ordinal:ordinal,entry=vector*columns+column;
        HnnExactConst value,bound;
        if(!staged(entry,input_arena,input_capacity,input_meta,&value,&bound)) {
            fail(result,BAD_VIEW,0,entry);return;
        }
        if(!check(hnn_exact_shift(value,shift,&x[0],work,workcap),result,entry)
           ||!check(hnn_exact_add(view(x[0]),view(x[7]),&x[1],work,workcap),result,entry)
           ||!check(hnn_exact_shift(bound,shift,&x[8],work,workcap),result,entry))return;
        HnnExactConst rem_magnitude=view(x[7]);rem_magnitude.negative=false;
        if(!check(hnn_exact_add(view(x[8]),rem_magnitude,&x[9],work,workcap),result,entry))return;
        if(!hnn_exact_certified_valid({view(x[1]),view(x[9])})) {
            fail(result,BAD_VIEW,0,entry);return;
        }
        const auto divided=hnn_exact_divrem(view(x[1]),divisor,&x[2],&x[3],work,workcap);
        if(divided.status!=HNN_XINT_OK) {
            const uint64_t needed=divided.quotient_required>divided.remainder_required
                ?divided.quotient_required:divided.remainder_required;
            fail(result,divided.status==HNN_XINT_NEED_CAPACITY?CAPACITY:BAD_VIEW,needed,entry);return;
        }
        HnnExactConst remainder_magnitude=view(x[3]);remainder_magnitude.negative=false;
        if(!check(hnn_exact_shift(remainder_magnitude,1,&x[4],work,workcap),result,entry))return;
        const auto order=hnn_exact_compare(view(x[4]),divisor);
        if(order.status!=HNN_XINT_OK){fail(result,BAD_VIEW,0,entry);return;}
        const bool adjust=x[3].negative?order.ordering>0:order.ordering>=0;
        HnnExactConst quotient=view(x[2]),remainder=view(x[3]);
        if(adjust) {
            const bool negative=x[3].negative;
            const auto qop=negative?hnn_exact_sub(quotient,one,&x[5],work,workcap)
                                   :hnn_exact_add(quotient,one,&x[5],work,workcap);
            if(!check(qop,result,entry))return;
            const auto rop=negative?hnn_exact_add(remainder,divisor,&x[6],work,workcap)
                                   :hnn_exact_sub(remainder,divisor,&x[6],work,workcap);
            if(!check(rop,result,entry))return;
            quotient=view(x[5]);remainder=view(x[6]);
        }
        // Retain the actual pre-split numerator l1, including the incoming
        // remainder, rather than replacing it with the post-cancellation value.
        // Its units are numerator units, declared by the resident denominator.
        publish(entry,quotient,view(x[9]),capacity,output,meta);
        hnn_xcommit(&x[7],remainder.limb,remainder.size,remainder.negative);
    }
    HnnExactConst rem=view(x[7]),bound=rem;bound.negative=false;
    publish(vectors*columns+column,rem,bound,capacity,output,meta);
}
} // namespace hnn_word_exact_detail

// Matrix and vectors share one immutable arena; vectors are vector-major. Output
// slots alternate value/l1, capacity limbs each. Scratch is (7*capacity+1)*lanes.
extern "C" __global__ void hnn_word_exact_apply(
    const uint64_t *arena,uint64_t arena_words,const HnnWordExactWord *matrix,
    const HnnWordExactWord *vectors,uint64_t rows,uint64_t columns,uint64_t count,
    uint32_t transpose,uint64_t capacity,uint64_t *output,uint64_t output_words,
    HnnWordExactOutput *meta,uint64_t *scratch,uint64_t scratch_words,HnnWordExactResult *result) {
    using namespace hnn_word_exact_detail;
    if(!result)return;
    auto grid=cooperative_groups::this_grid();
    const uint64_t lane=(uint64_t)blockIdx.x*blockDim.x+threadIdx.x,lanes=(uint64_t)gridDim.x*blockDim.x;
    uint64_t matrix_entries=0,vector_entries=0,entries=0,slots=0,required_output=0,stride=0,required_scratch=0;
    const bool extents=rows&&columns&&count&&capacity&&transpose<=1
        &&mul_size(rows,columns,&matrix_entries)
        &&mul_size(count,transpose?rows:columns,&vector_entries)
        &&mul_size(count,transpose?columns:rows,&entries)
        &&mul_size(entries,2,&slots)&&mul_size(slots,capacity,&required_output)
        &&mul_size(capacity,7,&stride)&&add_size(stride,1,&stride)&&mul_size(stride,lanes,&required_scratch);
    if(lane==0) {
        *result={OK,0,0,UINT64_MAX};
        if(!extents)fail(result,EXTENT,0,0);
        else if(!arena||!matrix||!vectors||!output||!meta||!scratch)fail(result,BAD_VIEW,0,0);
        else if(output_words<required_output||scratch_words<required_scratch)fail(result,EXTENT,0,0);
    }
    grid.sync();
    if(result->status==OK) {
        // Validate the complete immutable operand surface before any sum starts.
        for(uint64_t i=lane;i<matrix_entries;i+=lanes) {
            HnnExactConst x;if(!input(matrix[i],arena,arena_words,&x))fail(result,BAD_VIEW,0,i);
            else if(x.size>capacity)fail(result,CAPACITY,x.size,i);
        }
        for(uint64_t i=lane;i<vector_entries;i+=lanes) {
            HnnExactConst x;if(!input(vectors[i],arena,arena_words,&x))fail(result,BAD_VIEW,0,i);
            else if(x.size>capacity)fail(result,CAPACITY,x.size,i);
        }
    }
    grid.sync();
    if(result->status==OK)for(uint64_t i=lane;i<entries;i+=lanes)
        apply(i,rows,columns,transpose!=0,capacity,arena,arena_words,matrix,vectors,
              output,meta,scratch+lane*stride,result);
    grid.sync();
    if(lane==0&&result->status==OK)atomicExch((unsigned int*)&result->committed,1u);
}

// Carry consumes the resident apply output without an intervening re-upload.
// shift=L_w+return_precision_levels. The denominator retains every odd factor.
// Output has count*columns carried coordinates then columns final remainders.
// Scratch is (12*capacity+1)*lanes.
extern "C" __global__ void hnn_word_exact_carry(
    const uint64_t *input_arena,uint64_t input_words,const HnnWordExactOutput *input_meta,
    const HnnWordExactResult *input_result,uint64_t input_capacity,
    const uint64_t *divisor_arena,uint64_t divisor_words,HnnWordExactWord divisor_word,
    uint64_t count,uint64_t columns,int64_t shift,uint32_t reverse,uint64_t capacity,
    uint64_t *output,uint64_t output_words,HnnWordExactOutput *meta,
    uint64_t *scratch,uint64_t scratch_words,HnnWordExactResult *result) {
    using namespace hnn_word_exact_detail;
    if(!result)return;
    auto grid=cooperative_groups::this_grid();
    const uint64_t lane=(uint64_t)blockIdx.x*blockDim.x+threadIdx.x,lanes=(uint64_t)gridDim.x*blockDim.x;
    uint64_t inputs=0,input_slots=0,required_input=0,plus_one=0,entries=0,slots=0,required_output=0,stride=0,required_scratch=0;
    const bool extents=count&&columns&&input_capacity&&capacity&&shift>=0&&reverse<=1
        &&mul_size(count,columns,&inputs)&&mul_size(inputs,2,&input_slots)&&mul_size(input_slots,input_capacity,&required_input)
        &&add_size(count,1,&plus_one)&&mul_size(plus_one,columns,&entries)
        &&mul_size(entries,2,&slots)&&mul_size(slots,capacity,&required_output)
        &&mul_size(capacity,12,&stride)&&add_size(stride,1,&stride)&&mul_size(stride,lanes,&required_scratch);
    HnnExactConst divisor;
    const bool divisor_valid=input(divisor_word,divisor_arena,divisor_words,&divisor)
        &&divisor.size&&!divisor.negative;
    if(lane==0) {
        *result={OK,0,0,UINT64_MAX};
        if(!extents)fail(result,EXTENT,0,0);
        else if(!input_arena||!input_meta||!input_result||!output||!meta||!scratch||!divisor_valid)
            fail(result,BAD_VIEW,0,0);
        else if(input_result->status!=OK||input_result->committed!=1)fail(result,BAD_VIEW,0,0);
        else if(input_words<required_input||output_words<required_output||scratch_words<required_scratch)
            fail(result,EXTENT,0,0);
        else if(divisor.size>capacity)fail(result,CAPACITY,divisor.size,0);
    }
    grid.sync();
    if(result->status==OK)for(uint64_t i=lane;i<inputs;i+=lanes) {
        HnnExactConst value,bound;
        if(!staged(i,input_arena,input_capacity,input_meta,&value,&bound))fail(result,BAD_VIEW,0,i);
    }
    grid.sync();
    if(result->status==OK)for(uint64_t i=lane;i<columns;i+=lanes)
        carry(i,count,columns,reverse!=0,shift,divisor,input_capacity,input_arena,input_meta,
              capacity,output,meta,scratch+lane*stride,result);
    grid.sync();
    if(lane==0&&result->status==OK)atomicExch((unsigned int*)&result->committed,1u);
}
