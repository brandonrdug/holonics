// Arithmetic smoke for scalar (1x1) epoch deposition. This is not the listener forward,
// comparison, certificate, or a completed cooperative epoch circuit. Each CUDA lane owns one
// independent locus and walks its supplied crossings in order; there is no grid barrier because
// loci do not read one another's state. Widths and all arenas are caller-derived at runtime.
#include "exact_integer.cuh"

enum HnnEpochStatus : uint32_t {
    HNN_EPOCH_OK = 0,
    HNN_EPOCH_NEED_CAPACITY = 1,
    HNN_EPOCH_BAD_VIEW = 2,
    HNN_EPOCH_ZERO_CONDUCTANCE = 3,
    HNN_EPOCH_EXPONENT_OVERFLOW = 4,
    HNN_EPOCH_NOT_RUN = 6,
    HNN_EPOCH_NON_DESCENDING_DEFECT = 7
};

// Spans address one caller-owned limb arena. Inputs are immutable during a launch. State and
// record output spans are disjoint from inputs, each other, and every lane's scratch range.
struct HnnEpochWord {
    size_t offset;
    size_t size;
    size_t capacity;
    bool negative;
};
struct HnnEpochScalarState {
    HnnEpochWord w, h, r;
    int64_t w_exponent, h_exponent, r_exponent;
};
struct HnnEpochScalarInput {
    HnnEpochWord delta_h, g, gamma_numerator;
    int64_t delta_h_exponent, g_exponent, gamma_exponent, map_exponent;
};
struct HnnEpochScalarRecord {
    HnnEpochWord step, fall, eta_denominator;
    HnnEpochWord w_after, h_after, r_after;
    int64_t step_exponent, fall_exponent;
    int64_t w_after_exponent, h_after_exponent, r_after_exponent;
    uint32_t status;
    size_t required_words;
    size_t required_scratch;
};

static constexpr size_t HNN_EPOCH_STAGE_SLOTS = 19;

__device__ __forceinline__ bool epoch_add_size(size_t a, size_t b, size_t *out) {
    if (b > SIZE_MAX - a) return false;
    *out = a + b;
    return true;
}
__device__ __forceinline__ bool epoch_mul_size(size_t a, size_t b, size_t *out) {
    if (a && b > SIZE_MAX / a) return false;
    *out = a * b;
    return true;
}
__device__ __forceinline__ bool epoch_span_valid(HnnEpochWord w, size_t arena_words) {
    if (w.offset > arena_words || w.size > w.capacity) return false;
    if (w.capacity > arena_words - w.offset) return false;
    return true;
}
__device__ __forceinline__ bool epoch_view(HnnEpochWord w, const uint64_t *arena,
                                            size_t arena_words, HnnExactConst *out) {
    if (!epoch_span_valid(w, arena_words) || (w.capacity && !arena)) return false;
    const uint64_t *limbs = w.size ? arena + w.offset : (w.capacity ? arena + w.offset : nullptr);
    HnnExactConst view{limbs, w.size, w.negative};
    if (!hnn_xvalid(view)) return false;
    *out = view;
    return true;
}
__device__ __forceinline__ HnnExactMut epoch_stage(uint64_t *scratch, size_t value_capacity,
                                                   size_t slot) {
    HnnExactMut out{value_capacity ? scratch + slot * value_capacity : nullptr,
                    value_capacity, 0, false};
    return out;
}
__device__ __forceinline__ bool epoch_const(HnnExactMut value, HnnExactConst *out) {
    HnnExactConst view{value.size ? value.limb : nullptr, value.size, value.negative};
    if (!hnn_xvalid(view)) return false;
    *out = view;
    return true;
}
__device__ __forceinline__ void epoch_need(HnnEpochScalarRecord *record, HnnExactResult result,
                                            size_t value_capacity, size_t op_capacity) {
    if (result.status == HNN_XINT_NEED_CAPACITY) {
        record->status = HNN_EPOCH_NEED_CAPACITY;
        if (result.required > value_capacity && result.required > record->required_words)
            record->required_words = result.required;
        if (result.required > op_capacity && result.required > record->required_scratch)
            record->required_scratch = result.required;
    } else {
        record->status = HNN_EPOCH_BAD_VIEW;
    }
}
__device__ __forceinline__ bool epoch_shift(HnnExactConst value, int64_t bits,
    HnnExactMut *out, uint64_t *op, size_t op_capacity, size_t value_capacity,
    HnnEpochScalarRecord *record) {
    HnnExactResult result = hnn_exact_shift(value, bits, out, op, op_capacity);
    if (result.status == HNN_XINT_OK) return true;
    epoch_need(record, result, value_capacity, op_capacity);
    return false;
}
__device__ __forceinline__ bool epoch_add(HnnExactConst a, int64_t ae, HnnExactConst b,
    int64_t be, bool subtract, HnnExactMut *out, HnnExactMut *aligned_a,
    HnnExactMut *aligned_b, uint64_t *op, size_t op_capacity, size_t value_capacity,
    int64_t *out_exponent, HnnEpochScalarRecord *record) {
    if (ae < 0 || be < 0) { record->status = HNN_EPOCH_BAD_VIEW; return false; }
    const int64_t exponent = ae > be ? ae : be;
    HnnExactConst left = a, right = b;
    if (exponent != ae) {
        if (!epoch_shift(a, exponent - ae, aligned_a, op, op_capacity,
                                              value_capacity, record)) return false;
        if (!epoch_const(*aligned_a, &left)) { record->status=HNN_EPOCH_BAD_VIEW; return false; }
    }
    if (exponent != be) {
        if (!epoch_shift(b, exponent - be, aligned_b, op, op_capacity,
                                              value_capacity, record)) return false;
        if (!epoch_const(*aligned_b, &right)) { record->status=HNN_EPOCH_BAD_VIEW; return false; }
    }
    HnnExactResult result = subtract
        ? hnn_exact_sub(left, right, out, op, op_capacity)
        : hnn_exact_add(left, right, out, op, op_capacity);
    if (result.status != HNN_XINT_OK) {
        epoch_need(record, result, value_capacity, op_capacity);
        return false;
    }
    *out_exponent = exponent;
    return true;
}
__device__ __forceinline__ bool epoch_mul(HnnExactConst a, HnnExactConst b,
    HnnExactMut *out, uint64_t *op, size_t op_capacity, size_t value_capacity,
    int64_t ae, int64_t be, int64_t *out_exponent, HnnEpochScalarRecord *record) {
    if (ae < 0 || be < 0 || be > INT64_MAX - ae) {
        record->status = HNN_EPOCH_EXPONENT_OVERFLOW; return false;
    }
    HnnExactResult result=hnn_exact_mul(a,b,out,op,op_capacity);
    if(result.status!=HNN_XINT_OK){epoch_need(record,result,value_capacity,op_capacity);return false;}
    *out_exponent=ae+be;
    return true;
}
__device__ __forceinline__ size_t epoch_bit_length(HnnExactConst value) {
    if (!value.size) return 0;
    const uint64_t top=value.limb[value.size-1];
    return (value.size-1)*64 + 64 - __clzll(top);
}
__device__ __forceinline__ bool epoch_power_of_two(HnnExactConst value) {
    bool seen=false;
    for(size_t i=0;i<value.size;++i){
        const uint64_t v=value.limb[i];
        if(v){ if(seen || (v & (v-1)))return false; seen=true; }
    }
    return seen;
}
__device__ __forceinline__ bool epoch_ceil_log2(HnnExactConst value, int64_t *bits) {
    const size_t length=epoch_bit_length(value);
    if(!length){*bits=0;return true;}
    size_t result=length-1 + (epoch_power_of_two(value)?0:1);
    if(result>static_cast<size_t>(INT64_MAX))return false;
    *bits=static_cast<int64_t>(result); return true;
}
__device__ __forceinline__ bool epoch_copy(HnnExactConst in, HnnExactMut *out,
    uint64_t *op, size_t op_capacity, size_t value_capacity, HnnEpochScalarRecord *record) {
    HnnExactResult result=hnn_exact_shift(in,0,out,op,op_capacity);
    if(result.status==HNN_XINT_OK)return true;
    epoch_need(record,result,value_capacity,op_capacity); return false;
}

// One lane owns one scalar locus and its caller-provided arena ranges. Each crossing is fully
// staged before state or trace spans are changed. A capacity result reports the exact limb need;
// the caller widens/rebases and retries the same crossing. No width refusal or partial crossing.
extern "C" __global__ void hnn_epoch_scalar_persistent(
    HnnEpochScalarState *states, const HnnEpochScalarInput *inputs,
    HnnEpochScalarRecord *records, size_t locus_count, size_t crossing_count,
    uint64_t *value_arena, size_t value_arena_words,
    uint64_t *scratch_arena, size_t scratch_arena_words,
    size_t scratch_stride, size_t value_capacity) {
    if((locus_count && (!states || !records)) || (crossing_count && locus_count && !inputs) ||
       (locus_count && crossing_count>SIZE_MAX/locus_count) ||
       (scratch_arena_words && !scratch_arena))return;
    const size_t locus=static_cast<size_t>(blockIdx.x)*blockDim.x+threadIdx.x;
    if(locus>=locus_count)return;
    size_t slot_words;
    if(!scratch_stride || !epoch_mul_size(HNN_EPOCH_STAGE_SLOTS,value_capacity,&slot_words) ||
       scratch_stride<slot_words || locus>SIZE_MAX/scratch_stride ||
       locus*scratch_stride>scratch_arena_words || scratch_stride>scratch_arena_words-locus*scratch_stride){
        for(size_t e=0;e<crossing_count;++e){HnnEpochScalarRecord &rec=records[e*locus_count+locus];rec.status=HNN_EPOCH_BAD_VIEW;rec.required_words=0;rec.required_scratch=0;}
        return;
    }
    uint64_t *lane_scratch=scratch_arena+locus*scratch_stride;
    const size_t op_capacity=scratch_stride-slot_words;
    uint64_t *op=lane_scratch+slot_words;
    HnnEpochScalarState &state=states[locus];

    for(size_t epoch=0;epoch<crossing_count;++epoch){
        HnnEpochScalarRecord &record=records[epoch*locus_count+locus];
        if(epoch && records[(epoch-1)*locus_count+locus].status!=HNN_EPOCH_OK){
            for(size_t later=epoch;later<crossing_count;++later){
                HnnEpochScalarRecord &pending=records[later*locus_count+locus];
                pending.status=HNN_EPOCH_NOT_RUN;pending.required_words=0;pending.required_scratch=0;
            }
            break;
        }
        record.status=HNN_EPOCH_OK;record.required_words=0;record.required_scratch=0;
        do {
        const HnnEpochScalarInput &input=inputs[epoch*locus_count+locus];
        HnnExactConst w,h,r,dh,g,gamma_num;
        if(!epoch_span_valid(state.w,value_arena_words)||!epoch_span_valid(state.h,value_arena_words)||
           !epoch_span_valid(state.r,value_arena_words)||!epoch_view(state.w,value_arena,value_arena_words,&w)||
           !epoch_view(state.h,value_arena,value_arena_words,&h)||!epoch_view(state.r,value_arena,value_arena_words,&r)||
           !epoch_view(input.delta_h,value_arena,value_arena_words,&dh)||!epoch_view(input.g,value_arena,value_arena_words,&g)||
           !epoch_view(input.gamma_numerator,value_arena,value_arena_words,&gamma_num)||
           input.delta_h_exponent<0||input.g_exponent<0||input.gamma_exponent<0||input.map_exponent<0||
           state.w_exponent<0||state.h_exponent<0||state.r_exponent<0){
            record.status=HNN_EPOCH_BAD_VIEW;break;
        }
        // All 19 stage slots are spans in the lane's dynamically sized scratch arena.
        HnnExactMut s[HNN_EPOCH_STAGE_SLOTS];
        for(size_t i=0;i<HNN_EPOCH_STAGE_SLOTS;++i)s[i]=epoch_stage(lane_scratch,value_capacity,i);
        int64_t eh=0, er=0, eg=0;
        if(input.g_exponent>INT64_MAX-input.gamma_exponent){record.status=HNN_EPOCH_EXPONENT_OVERFLOW;break;}
        if(!epoch_add(h,state.h_exponent,dh,input.delta_h_exponent,false,&s[0],&s[16],&s[17],op,op_capacity,value_capacity,&eh,&record))break;
        if(!epoch_mul(g,gamma_num,&s[1],op,op_capacity,value_capacity,input.g_exponent,input.gamma_exponent,&eg,&record))break;
        HnnExactConst rg;
        if(!epoch_const(s[1],&rg)||!epoch_add(r,state.r_exponent,rg,eg,false,&s[2],&s[16],&s[17],op,op_capacity,value_capacity,&er,&record))break;
        HnnExactConst hp,rp;
        if(!epoch_const(s[0],&hp)||!epoch_const(s[2],&rp)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        if(hp.negative){record.status=HNN_EPOCH_BAD_VIEW;break;}
        if(!hp.size){record.status=HNN_EPOCH_ZERO_CONDUCTANCE;break;}
        int64_t log_share;
        if(!epoch_ceil_log2(hp,&log_share)){
            record.status=HNN_EPOCH_EXPONENT_OVERFLOW;break;
        }
        const int64_t share_exponent=log_share-eh;
        int64_t direction_exponent=er;
        HnnExactConst direction=rp;
        if(share_exponent>0){
            if(er>INT64_MAX-share_exponent){record.status=HNN_EPOCH_EXPONENT_OVERFLOW;break;}
            direction_exponent=er+share_exponent;
        } else if(share_exponent<0){
            if(share_exponent==INT64_MIN||!epoch_shift(rp,-share_exponent,&s[3],op,op_capacity,value_capacity,&record))break;
            if(!epoch_const(s[3],&direction)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        }
        // eta is fixed at one: the represented step is the exact quotient of D on W's lattice.
        if(!hnn_xscratch_valid(op,op_capacity)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        HnnExactConst numerator;
        numerator=direction;
        int64_t lattice_shift=input.map_exponent-direction_exponent;
        if((direction_exponent>0 && input.map_exponent<INT64_MIN+direction_exponent) ||
           (direction_exponent<0 && input.map_exponent>INT64_MAX+direction_exponent)){
            record.status=HNN_EPOCH_EXPONENT_OVERFLOW;break;
        }
        if(lattice_shift>0){
            if(!epoch_shift(numerator,lattice_shift,&s[15],op,op_capacity,value_capacity,&record))break;
            if(!epoch_const(s[15],&numerator)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        }
        uint64_t unit_eta_limb=1;
        HnnExactConst unit_eta{&unit_eta_limb,1,false};
        if(!epoch_copy(unit_eta,&s[5],op,op_capacity,value_capacity,&record))break;
        HnnExactConst divisor=unit_eta;
        if(lattice_shift<0){
            if(lattice_shift==INT64_MIN||!epoch_shift(unit_eta,-lattice_shift,&s[18],op,op_capacity,value_capacity,&record))break;
            if(!epoch_const(s[18],&divisor)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        }
        HnnExactMut remainder=s[7];
        HnnExactDivResult divided=hnn_exact_divrem(numerator,divisor,&s[6],&remainder,op,op_capacity);
        if(divided.status!=HNN_XINT_OK){
            record.status=divided.status==HNN_XINT_NEED_CAPACITY?HNN_EPOCH_NEED_CAPACITY:HNN_EPOCH_BAD_VIEW;
            record.required_words=divided.quotient_required>divided.remainder_required?divided.quotient_required:divided.remainder_required;
            record.required_scratch=divided.scratch_required;break;
        }
        HnnExactConst step,rem;
        if(!epoch_const(s[6],&step)||!epoch_const(remainder,&rem)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        (void)rem;
        int64_t linear_exp, square_exp, quad_exp;
        if(input.map_exponent>INT64_MAX-er || input.map_exponent>INT64_MAX-input.map_exponent){record.status=HNN_EPOCH_EXPONENT_OVERFLOW;break;}
        linear_exp=input.map_exponent+er;
        square_exp=input.map_exponent+input.map_exponent;
        if(eh>INT64_MAX-square_exp-1){record.status=HNN_EPOCH_EXPONENT_OVERFLOW;break;}
        quad_exp=square_exp+eh+1;
        int64_t fall_exp;
        if(!epoch_mul(step,rp,&s[8],op,op_capacity,value_capacity,input.map_exponent,er,&linear_exp,&record)||
           !epoch_mul(step,step,&s[9],op,op_capacity,value_capacity,input.map_exponent,input.map_exponent,&square_exp,&record))break;
        HnnExactConst sq;
        if(!epoch_const(s[9],&sq)||!epoch_mul(sq,hp,&s[10],op,op_capacity,value_capacity,square_exp,eh,&quad_exp,&record))break;
        HnnExactConst lin,quad;
        if(!epoch_const(s[8],&lin)||!epoch_const(s[10],&quad)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        if(quad_exp==INT64_MAX){record.status=HNN_EPOCH_EXPONENT_OVERFLOW;break;}
        ++quad_exp;
        if(!epoch_add(lin,linear_exp,quad,quad_exp,true,&s[11],&s[16],&s[17],op,op_capacity,value_capacity,&fall_exp,&record))break;
        HnnExactConst fall;
        if(!epoch_const(s[11],&fall)){record.status=HNN_EPOCH_BAD_VIEW;break;}
        if(step.size && (fall.negative||!fall.size)){
            record.status=HNN_EPOCH_NON_DESCENDING_DEFECT;break;
        }
        const int64_t accepted_fall_exponent=fall_exp;

        HnnExactConst final_eta;
        if(!epoch_const(s[5],&final_eta)){
            record.status=HNN_EPOCH_BAD_VIEW;break;
        }
        int64_t new_w_exp,new_r_exp,step_h_exp;
        HnnExactConst step_h;
        if(!epoch_add(w,state.w_exponent,step,input.map_exponent,false,&s[12],&s[16],&s[17],op,op_capacity,value_capacity,&new_w_exp,&record)||
           !epoch_mul(step,hp,&s[13],op,op_capacity,value_capacity,input.map_exponent,eh,&step_h_exp,&record))break;
        if(!epoch_const(s[13],&step_h)||!epoch_add(rp,er,step_h,step_h_exp,true,&s[14],&s[16],&s[17],op,op_capacity,value_capacity,&new_r_exp,&record))break;
        // Check every state and trace capacity before the first externally visible write.
        HnnExactMut *staged[]={&s[12],&s[0],&s[14],&s[6],&s[11],&s[5],&s[12],&s[0],&s[14]};
        HnnEpochWord *dest[]={&state.w,&state.h,&state.r,&record.step,&record.fall,&record.eta_denominator,
                              &record.w_after,&record.h_after,&record.r_after};
        size_t required=0;
        for(size_t i=0;i<9;++i){
            if(!epoch_span_valid(*dest[i],value_arena_words) || (dest[i]->capacity && !value_arena)){
                record.status=HNN_EPOCH_BAD_VIEW;break;
            }
            if(staged[i]->size>dest[i]->capacity && staged[i]->size>required)required=staged[i]->size;
        }
        if(record.status!=HNN_EPOCH_OK)break;
        if(required){record.status=HNN_EPOCH_NEED_CAPACITY;record.required_words=required;break;}
        // Crossing publication: state and all per-crossing diagnostics fit before any are written.
        HnnExactMut outputs[9];
        for(size_t i=0;i<9;++i){outputs[i]={dest[i]->capacity?value_arena+dest[i]->offset:nullptr,dest[i]->capacity,0,false};
            hnn_xcommit(&outputs[i],staged[i]->limb,staged[i]->size,staged[i]->negative);
            dest[i]->size=outputs[i].size;dest[i]->negative=outputs[i].negative;}
        state.w_exponent=new_w_exp;state.h_exponent=eh;state.r_exponent=new_r_exp;
        record.step_exponent=input.map_exponent;record.fall_exponent=accepted_fall_exponent;
        record.w_after_exponent=new_w_exp;record.h_after_exponent=eh;record.r_after_exponent=new_r_exp;
        (void)final_eta;
        } while(false);
        if(record.status!=HNN_EPOCH_OK){
            for(size_t later=epoch+1;later<crossing_count;++later){
                HnnEpochScalarRecord &pending=records[later*locus_count+locus];
                pending.status=HNN_EPOCH_NOT_RUN;pending.required_words=0;pending.required_scratch=0;
            }
            break;
        }
    }
}
