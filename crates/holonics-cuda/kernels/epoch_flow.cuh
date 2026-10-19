// Exact producer-record aggregation for one locus at its receiver crossing.
//
// Inputs are actual producer integers, re-expressed EXACTLY on shared feature F
// and covector C lattices. Covector row c retains its declared odd divisor D_c.
// The kernel changes no exponent/divisor and introduces no face partition:
//   G_ij = sum_t g_ti f_tj, denominator 2^(F+C) D_i
//   H_ij = sum_t f_ti f_tj, denominator 2^(2F).
// G entries precede H entries in row-major order. Each signed sum keeps the
// exact l1 sum of its actual product terms, including terms that cancel.
//
// This is a component of the learner, not forward/comparison/certification or
// deposition. All writes are STAGING. The caller exposes no result unless
// status==OK && committed==1, written after the cooperative precommit barrier.
// Failure never mutates a retained constitution and never invokes a host fallback.
#pragma once
#include "exact_integer.cuh"
#include <cooperative_groups.h>
#include <stddef.h>
#include <stdint.h>

struct HnnEpochFlowWord {
    uint64_t offset;
    uint64_t size;
    uint32_t negative;
    uint32_t reserved;
};
struct HnnEpochFlowOutput {
    uint64_t value_size;
    uint64_t bound_size;
    uint32_t negative;
    uint32_t reserved;
};
struct HnnEpochFlowResult {
    uint32_t status;
    uint32_t committed;
    uint64_t required_words; // required PER-VALUE capacity, never a byte count
    uint64_t failing_entry;
};
static_assert(sizeof(HnnEpochFlowWord)==24, "epoch input ABI");
static_assert(sizeof(HnnEpochFlowOutput)==24, "epoch output ABI");
static_assert(sizeof(HnnEpochFlowResult)==24, "epoch result ABI");
static_assert(offsetof(HnnEpochFlowWord,negative)==16, "epoch input sign ABI");
static_assert(offsetof(HnnEpochFlowOutput,negative)==16, "epoch output sign ABI");
static_assert(offsetof(HnnEpochFlowResult,required_words)==8, "epoch capacity ABI");
static_assert(sizeof(size_t)==sizeof(uint64_t), "epoch limb arena uses 64-bit offsets");

enum : uint32_t {
    HNN_EPOCH_FLOW_OK=0,
    HNN_EPOCH_FLOW_NEED_CAPACITY=1,
    HNN_EPOCH_FLOW_BAD_VIEW=2,
    HNN_EPOCH_FLOW_EXTENT=3,
    HNN_EPOCH_FLOW_NOT_RUN=4
};

namespace hnn_epoch_flow_detail {
__device__ __forceinline__ bool multiply_size(uint64_t a,uint64_t b,uint64_t *out) {
    if(a && b>UINT64_MAX/a)return false;
    *out=a*b;return true;
}
__device__ __forceinline__ bool add_size(uint64_t a,uint64_t b,uint64_t *out) {
    if(b>UINT64_MAX-a)return false;
    *out=a+b;return true;
}
__device__ __forceinline__ void fail(HnnEpochFlowResult *result,uint32_t status,
                                    uint64_t required,uint64_t entry) {
    atomicCAS((unsigned int*)&result->status,HNN_EPOCH_FLOW_OK,status);
    atomicMax((unsigned long long*)&result->required_words,(unsigned long long)required);
    atomicMin((unsigned long long*)&result->failing_entry,(unsigned long long)entry);
}
__device__ __forceinline__ bool check(HnnExactResult op,HnnEpochFlowResult *result,uint64_t entry) {
    if(op.status==HNN_XINT_OK)return true;
    fail(result,op.status==HNN_XINT_NEED_CAPACITY?HNN_EPOCH_FLOW_NEED_CAPACITY:HNN_EPOCH_FLOW_BAD_VIEW,
         op.status==HNN_XINT_NEED_CAPACITY?op.required:0,entry);
    return false;
}
__device__ __forceinline__ bool input_view(HnnEpochFlowWord word,const uint64_t *arena,
    uint64_t words,HnnExactConst *view) {
    if(word.reserved || word.negative>1 || word.offset>words || word.size>words-word.offset
       || (word.size&&!arena))return false;
    *view={word.size?arena+word.offset:nullptr,(size_t)word.size,word.negative!=0};
    return hnn_xvalid(*view);
}
__device__ __forceinline__ HnnExactConst view(const HnnExactMut &x) {
    return {x.size?x.limb:nullptr,x.size,x.negative};
}

// One lane's nonoverlapping bank: term, two signed accumulators, two l1
// accumulators, then 2*capacity+1 operation-work limbs. Input views never alias
// this bank; ping-pong accumulators never alias an operation's output.
__device__ __forceinline__ void aggregate(uint64_t entry,uint64_t records,uint64_t rows,
    uint64_t columns,uint64_t capacity,const uint64_t *arena,uint64_t arena_words,
    const HnnEpochFlowWord *features,const HnnEpochFlowWord *covectors,
    uint64_t *output,HnnEpochFlowOutput *meta,uint64_t *bank,HnnEpochFlowResult *result) {
    const uint64_t g_entries=rows*columns;
    const bool gram=entry>=g_entries;
    const uint64_t at=gram?entry-g_entries:entry;
    const uint64_t row=at/columns,column=at%columns;
    HnnExactMut term{bank,(size_t)capacity,0,false};
    HnnExactMut sums[2]={{bank+capacity,(size_t)capacity,0,false},
                        {bank+2*capacity,(size_t)capacity,0,false}};
    HnnExactMut bounds[2]={{bank+3*capacity,(size_t)capacity,0,false},
                          {bank+4*capacity,(size_t)capacity,0,false}};
    uint64_t *work=bank+5*capacity;
    const size_t work_capacity=(size_t)(2*capacity+1);
    unsigned current=0;
    for(uint64_t t=0;t<records;++t) {
        HnnExactConst left,right;
        const HnnEpochFlowWord left_word=gram?features[t*columns+row]:covectors[t*rows+row];
        if(!input_view(left_word,arena,arena_words,&left)
           || !input_view(features[t*columns+column],arena,arena_words,&right)) {
            fail(result,HNN_EPOCH_FLOW_BAD_VIEW,0,entry);return;
        }
        if(!check(hnn_exact_mul(left,right,&term,work,work_capacity),result,entry))return;
        const unsigned next=1-current;
        if(!check(hnn_exact_add(view(sums[current]),view(term),&sums[next],work,work_capacity),result,entry))return;
        HnnExactConst magnitude=view(term);magnitude.negative=false;
        if(!check(hnn_exact_add(view(bounds[current]),magnitude,&bounds[next],work,work_capacity),result,entry))return;
        current=next;
    }
    if(!hnn_exact_certified_valid({view(sums[current]),view(bounds[current])})) {
        fail(result,HNN_EPOCH_FLOW_BAD_VIEW,0,entry);return;
    }
    uint64_t *value=capacity?output+(2*entry)*capacity:nullptr;
    uint64_t *bound=capacity?value+capacity:nullptr;
    for(size_t i=0;i<sums[current].size;++i)value[i]=sums[current].limb[i];
    for(size_t i=0;i<bounds[current].size;++i)bound[i]=bounds[current].limb[i];
    meta[entry]={(uint64_t)sums[current].size,(uint64_t)bounds[current].size,
                 sums[current].negative?1u:0u,0u};
}
} // namespace hnn_epoch_flow_detail

// Must be launched cooperatively with a resident grid. Every lane joins all
// three grid barriers, including lanes with no entry or a failed operation.
// Features and covectors are record-major, m*columns and m*rows respectively.
// Output integer slots use stride capacity, alternating value and l1 bound.
// Scratch is (7*capacity+1)*LAUNCHED_LANES limbs, including idle grid lanes.
extern "C" __global__ void hnn_epoch_flow(
    const uint64_t *input_arena,uint64_t input_words,
    const HnnEpochFlowWord *features,const HnnEpochFlowWord *covectors,
    uint64_t records,uint64_t rows,uint64_t columns,uint64_t capacity,
    uint64_t *output_arena,uint64_t output_words,HnnEpochFlowOutput *output_meta,
    uint32_t *support,uint64_t *scratch,uint64_t scratch_words,HnnEpochFlowResult *result) {
    namespace cg=cooperative_groups;
    using namespace hnn_epoch_flow_detail;
    if(!result)return; // uniform over the whole grid; no barrier is entered
    cg::grid_group grid=cg::this_grid();
    const uint64_t lane=(uint64_t)blockIdx.x*blockDim.x+threadIdx.x;
    const uint64_t lanes=(uint64_t)gridDim.x*blockDim.x;
    uint64_t g_entries=0,h_entries=0,entries=0,feature_entries=0,covector_entries=0;
    uint64_t scratch_stride=0,required_scratch=0,required_output=0,slots=0,input_entries=0;
    const bool extents=rows&&columns&&lanes
        && multiply_size(rows,columns,&g_entries)
        && multiply_size(columns,columns,&h_entries)
        && add_size(g_entries,h_entries,&entries)
        && multiply_size(records,columns,&feature_entries)
        && multiply_size(records,rows,&covector_entries)
        && add_size(feature_entries,covector_entries,&input_entries)
        && multiply_size(capacity,7,&scratch_stride)
        && add_size(scratch_stride,1,&scratch_stride)
        && multiply_size(lanes,scratch_stride,&required_scratch)
        && multiply_size(entries,2,&slots)
        && multiply_size(slots,capacity,&required_output);
    if(lane==0) {
        result->status=HNN_EPOCH_FLOW_OK;result->committed=0;
        result->required_words=0;result->failing_entry=UINT64_MAX;
        if(!extents)fail(result,HNN_EPOCH_FLOW_EXTENT,0,0);
        else if((input_words&&!input_arena)||(feature_entries&&!features)
            ||(covector_entries&&!covectors)||!output_meta||!support
            ||(required_output&&!output_arena)||!scratch)
            fail(result,HNN_EPOCH_FLOW_BAD_VIEW,0,0);
        else if(output_words<required_output||scratch_words<required_scratch)
            fail(result,HNN_EPOCH_FLOW_EXTENT,0,0);
    }
    grid.sync(); // 1: initialized failure/publication state is visible
    if(result->status==HNN_EPOCH_FLOW_OK) {
        for(uint64_t i=lane;i<input_entries;) {
            HnnExactConst x;
            const HnnEpochFlowWord word=i<feature_entries?features[i]:covectors[i-feature_entries];
            if(!input_view(word,input_arena,input_words,&x))fail(result,HNN_EPOCH_FLOW_BAD_VIEW,0,i);
            else if(word.size>capacity)fail(result,HNN_EPOCH_FLOW_NEED_CAPACITY,word.size,i);
            if(input_entries-i<=lanes)break;
            i+=lanes;
        }
    }
    grid.sync(); // 2: all producer views admitted before product terms are read
    if(result->status==HNN_EPOCH_FLOW_OK) {
        uint64_t *bank=scratch+lane*scratch_stride;
        for(uint64_t i=lane;i<entries;) {
            aggregate(i,records,rows,columns,capacity,input_arena,input_words,
                      features,covectors,output_arena,output_meta,bank,result);
            if(entries-i<=lanes)break;
            i+=lanes;
        }
        for(uint64_t column=lane;column<columns;) {
            uint32_t reached=0;
            for(uint64_t t=0;t<records;++t)reached|=features[t*columns+column].size!=0;
            support[column]=reached;
            if(columns-column<=lanes)break;
            column+=lanes;
        }
    }
    grid.sync(); // 3: no result is published before every staged sum has finished
    if(lane==0&&result->status==HNN_EPOCH_FLOW_OK)atomicExch((unsigned int*)&result->committed,1u);
}
