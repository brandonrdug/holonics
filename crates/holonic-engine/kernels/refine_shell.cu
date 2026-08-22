// **The exact quotient, and one material that feeds it.**
//
// This file carries TWO kernels and the separation between them is the point. `claim_identities` is
// the LAW: given a class per cell and an exact key per cell, it returns the identity of the pair
// `(class, key)`. It knows nothing about streams, occurrences, windows or language. Any organ with a
// front expresses its step as `(classes, keys)` and this enacts it.
//
// `shell_keys` is one MATERIAL: it computes the key an occurrence carries at causal shell `k` from
// the corpus stream. A second material — a generation state, a relation pair, a conic — writes its
// own key kernel and reuses the law unchanged.
//
// **Splitting them is the correction, and it is ontological rather than tactical.** The governing
// record fixes it: *"CPU/RAM and GPU/VRAM are local charts of the same caused body."* One body, one
// law, many materials. A device path per organ is the cabinet-of-organs failure one level down —
// `canon/THE_HOLOBROCHOS_SPINE.md` convicts it for organs and it is no better for carriers.
//
// **This is the front's own law, and it belongs on the device.** `token_invariance` refines a
// population of occurrences one causal shell at a time: at depth `k`, two occurrences stay together
// exactly when the declared receiver family reads the same thing at `−k` and at `+k`. Every
// occurrence's shell reading is independent of every other's, and the grouping is a quotient by an
// exact key. That is one lane per occurrence, no reduction, no ordering, no atomic on the reading
// itself — the shape a card exists for.
//
// # Exactness, and why the key is one 64-bit word
//
// A receiver's reading of a surface is `[kind, weight, density, conduct token]`. Two occurrences
// agree at an offset exactly when those four words agree, so the cpu assigns each DISTINCT reading
// a dense identity once, over the whole corpus, and hands the device a `reading_id` per surface.
// Equality of readings is then equality of identities, exactly, and a shell key is
//
//     key = (reading_id at −k) << 32 | (reading_id at +k)
//
// with `ABSENT` standing for an offset that has run off the end of its whole. `ABSENT` is a
// distinguished identity and not a magic number: a terminus is family-invariant — deleting a
// receiver never merges "the whole ended" with a reading — so it must be a value no reading can
// take, and the cpu reserves identity zero for it before assigning any other.
//
// # The quotient is a hash join, not a sort
//
// Refining by sorting would impose an order the material does not have. The new class of an
// occurrence is the identity of the pair `(current class, shell key)`, and identities are claimed
// in an open-addressed table by `atomicCAS`. The atomic is on the CLAIM, never on the reading:
// lanes that compute the same pair converge on one slot, and the slot's index is the new class.
//
// **The table cannot fill.** The number of distinct pairs is at most the number of occupied
// occurrences, so a capacity above that always leaves an empty slot and every probe terminates.
// The cpu sizes it as the next power of two strictly above the occurrence count — derived from
// the material, with no load factor and no number chosen.

#include <stdint.h>

// The identity reserved for an offset past the end of a whole. The cpu assigns every real reading
// an identity at or above one, so this can collide with nothing.
#define REFINE_ABSENT 0u

// An empty table slot. A claimed slot holds `(class, key)` and can never be this, because a class
// identity is at or above one on the cpu side.
#define REFINE_EMPTY 0xffffffffffffffffULL

__device__ __forceinline__ uint64_t refine_mix(uint64_t value) {
    // A bijective 64-bit finalizer. It is a permutation, so it cannot merge two distinct pairs; it
    // only decides where a probe begins. Nothing about the returned partition depends on it.
    value ^= value >> 33;
    value *= 0xff51afd7ed558ccdULL;
    value ^= value >> 33;
    value *= 0xc4ceb9fe1a85ec53ULL;
    value ^= value >> 33;
    return value;
}

/// **The material: one lane per occurrence, writing the exact key it carries at shell `depth`.**
///
/// Nothing here quotients. It reads the stream and returns a key; what the key MEANS is the law's
/// business and the law does not care.
extern "C" __global__ void shell_keys(
    const uint32_t *site_whole,
    const uint32_t *site_position,
    const uint32_t *whole_offset,
    const uint32_t *whole_length,
    const uint32_t *stream,
    const uint32_t *reading_id,
    uint64_t *key_out,
    uint32_t site_count,
    uint32_t depth)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= site_count) {
        return;
    }
    const uint32_t whole = site_whole[at];
    const int64_t position = (int64_t)site_position[at];
    const int64_t length = (int64_t)whole_length[whole];
    const uint32_t base = whole_offset[whole];
    const int64_t step = (int64_t)depth;
    const int64_t left_site = position - step;
    const int64_t right_site = position + step;
    const uint32_t left = (left_site < 0 || left_site >= length)
                              ? REFINE_ABSENT
                              : reading_id[stream[base + (uint32_t)left_site]];
    const uint32_t right = (right_site < 0 || right_site >= length)
                               ? REFINE_ABSENT
                               : reading_id[stream[base + (uint32_t)right_site]];
    key_out[at] = ((uint64_t)left << 32) | (uint64_t)right;
}

/// **The law: one lane per cell, claiming the identity of `(class, key)`.**
///
/// This is the whole of one 32-bit face of the exact quotient. It is material-free by construction
/// — its only inputs are a class and a key face per cell — so every organ with a front shares it
/// rather than growing a device path of its own. A wider key crosses as successive exact faces.
extern "C" __global__ void claim_identities(
    const uint32_t *cell_class,
    const uint32_t *cell_key,
    uint64_t *table_pair,
    uint32_t *cell_next_class,
    uint32_t cell_count,
    uint32_t capacity_mask)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint64_t pair = ((uint64_t)cell_class[at] << 32) | (uint64_t)cell_key[at];
    uint64_t probe = refine_mix(pair) & (uint64_t)capacity_mask;
    for (;;) {
        const uint64_t seen = ((volatile uint64_t *)table_pair)[probe];
        if (seen == pair) {
            cell_next_class[at] = (uint32_t)probe;
            return;
        }
        if (seen == REFINE_EMPTY) {
            const uint64_t won = atomicCAS(
                (unsigned long long *)&table_pair[probe],
                (unsigned long long)REFINE_EMPTY,
                (unsigned long long)pair);
            if (won == REFINE_EMPTY) {
                cell_next_class[at] = (uint32_t)probe;
                return;
            }
            if (won == pair) {
                cell_next_class[at] = (uint32_t)probe;
                return;
            }
        }
        probe = (probe + 1) & (uint64_t)capacity_mask;
    }
}

/// **The quotient action: one lane carries one native state through a complete ordered word.**
///
/// The table is the complete row-major family `U_i : Q -> Q`. The word and every table enter once;
/// the card composes the noncommuting word locally. No host callback selects a semantic phase
/// between generators, and no invariant table is re-uploaded per step.
extern "C" __global__ void conduct_native_word(
    const uint32_t *generator_table,
    const uint32_t *word,
    const uint32_t *native_start,
    uint32_t *native_end,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t word_length)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    uint32_t state = native_start[at];
    for (uint32_t step = 0; step < word_length; ++step) {
        state = generator_table[word[step] * state_count + state];
    }
    native_end[at] = state;
}

/// **The same quotient action with every intermediate boundary retained for one terminal read.**
///
/// Each lane owns one starting occurrence and writes its complete ordered trace. The word, total
/// action, and starting population cross once; no apparatus callback observes or selects an
/// intermediate state. `trace_stride` is `word_length + 1`, derived by the caller from the word it
/// is enacting rather than supplied as a second aperture.
extern "C" __global__ void conduct_native_trace(
    const uint32_t *generator_table,
    const uint32_t *word,
    const uint32_t *native_start,
    uint32_t *native_trace,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t word_length,
    uint32_t trace_stride)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    uint32_t state = native_start[at];
    const uint64_t trace_at = (uint64_t)at * (uint64_t)trace_stride;
    native_trace[trace_at] = state;
    for (uint32_t step = 0; step < word_length; ++step) {
        state = generator_table[word[step] * state_count + state];
        native_trace[trace_at + (uint64_t)step + 1ULL] = state;
    }
}

__device__ __forceinline__ uint32_t recurrent_native_trace(
    const uint32_t *generator_table,
    uint32_t generator,
    uint32_t start,
    uint32_t state_count,
    bool apply_delta,
    uint32_t delta_from,
    uint32_t delta_to,
    uint32_t *trace)
{
    uint32_t state = start;
    trace[0] = state;
    for (uint32_t step = 0; step < state_count; ++step) {
        uint32_t next = generator_table[generator * state_count + state];
        if (apply_delta && state == delta_from) {
            next = delta_to;
        }
        trace[step + 1] = next;
        bool repeated = false;
        for (uint32_t prior = 0; prior <= step; ++prior) {
            repeated = repeated || trace[prior] == next;
        }
        if (repeated) {
            for (uint32_t fill = step + 2; fill <= state_count; ++fill) {
                trace[fill] = next;
            }
            return step + 2;
        }
        state = next;
    }
    return 0;
}

/// **An exterior return deposits one local difference and every recurrence closes on the card.**
///
/// The finite native population derives the only traversal bound: a total endomap must repeat by
/// `state_count + 1` visited boundaries. Each lane owns one entering occurrence and returns the
/// predecessor, committed-successor and targeted-ablation traces. The returned exterior current
/// decides commit versus decline once; no host callback inspects a boundary or supplies a response
/// extent. The ablation is the same base action enacted beside the successor, not a rebuilt body.
extern "C" __global__ void return_and_recur_native(
    const uint32_t *generator_table,
    const uint32_t *native_start,
    uint32_t *predecessor_trace,
    uint32_t *successor_trace,
    uint32_t *ablated_trace,
    uint32_t *predecessor_lengths,
    uint32_t *successor_lengths,
    uint32_t *ablated_lengths,
    uint32_t *decision,
    uint32_t *control_pair,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t generator,
    uint64_t returned_difference_octets,
    uint32_t delta_from,
    uint32_t delta_to,
    uint32_t control_from)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint32_t stride = state_count + 1U;
    const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
    const bool committed = returned_difference_octets > 0ULL;
    predecessor_lengths[at] = recurrent_native_trace(
        generator_table,
        generator,
        native_start[at],
        state_count,
        false,
        delta_from,
        delta_to,
        predecessor_trace + trace_at);
    successor_lengths[at] = recurrent_native_trace(
        generator_table,
        generator,
        native_start[at],
        state_count,
        committed,
        delta_from,
        delta_to,
        successor_trace + trace_at);
    ablated_lengths[at] = recurrent_native_trace(
        generator_table,
        generator,
        native_start[at],
        state_count,
        false,
        delta_from,
        delta_to,
        ablated_trace + trace_at);
    if (at == 0U) {
        decision[0] = committed ? 1U : 0U;
        const uint32_t predecessor = generator_table[generator * state_count + control_from];
        control_pair[0] = predecessor;
        control_pair[1] = committed && control_from == delta_from ? delta_to : predecessor;
    }
}

__device__ __forceinline__ uint32_t condensed_recurrent_trace(
    const uint32_t *successor_table,
    uint32_t start,
    uint32_t state_count,
    bool predecessor_route,
    bool withdraw_generator,
    uint32_t predecessor_from,
    uint32_t predecessor_to,
    uint32_t *seen,
    uint32_t *trace)
{
    uint32_t state = start;
    trace[0] = state;
    seen[state >> 5U] |= 1U << (state & 31U);
    for (uint32_t step = 0; step < state_count; ++step) {
        uint32_t next = withdraw_generator ? state : successor_table[state];
        if (!withdraw_generator && predecessor_route && state == predecessor_from) {
            next = predecessor_to;
        }
        trace[step + 1U] = next;
        const uint32_t word = next >> 5U;
        const uint32_t bit = 1U << (next & 31U);
        if ((seen[word] & bit) != 0U) {
            for (uint32_t fill = step + 2U; fill <= state_count; ++fill) {
                trace[fill] = next;
            }
            return step + 2U;
        }
        seen[word] |= bit;
        state = next;
    }
    return 0U;
}

/// **The condensed successor, its retained predecessor route, and shared-generator withdrawal
/// recur through one resident front.**
///
/// The visited incidence is a bitset whose extent is derived from the native population. This
/// removes the quadratic trace scan without imposing a fixed state capacity. Each lane owns one
/// admitted starting occurrence; the three route rows are disjoint and therefore interchangeable.
/// Withdrawing the shared generator leaves the same body at its entering boundary instead of
/// constructing a fallback action.
extern "C" __global__ void conduct_condensed_recurrences(
    const uint32_t *successor_table,
    const uint32_t *native_start,
    uint32_t *predecessor_trace,
    uint32_t *successor_trace,
    uint32_t *withdrawn_trace,
    uint32_t *predecessor_lengths,
    uint32_t *successor_lengths,
    uint32_t *withdrawn_lengths,
    uint32_t *seen,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t seen_words,
    uint32_t predecessor_from,
    uint32_t predecessor_to)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint32_t stride = state_count + 1U;
    const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
    const uint64_t predecessor_seen = (uint64_t)at * (uint64_t)seen_words;
    const uint64_t successor_seen =
        ((uint64_t)cell_count + (uint64_t)at) * (uint64_t)seen_words;
    const uint64_t withdrawn_seen =
        (2ULL * (uint64_t)cell_count + (uint64_t)at) * (uint64_t)seen_words;
    predecessor_lengths[at] = condensed_recurrent_trace(
        successor_table,
        native_start[at],
        state_count,
        true,
        false,
        predecessor_from,
        predecessor_to,
        seen + predecessor_seen,
        predecessor_trace + trace_at);
    successor_lengths[at] = condensed_recurrent_trace(
        successor_table,
        native_start[at],
        state_count,
        false,
        false,
        predecessor_from,
        predecessor_to,
        seen + successor_seen,
        successor_trace + trace_at);
    withdrawn_lengths[at] = condensed_recurrent_trace(
        successor_table,
        native_start[at],
        state_count,
        false,
        true,
        predecessor_from,
        predecessor_to,
        seen + withdrawn_seen,
        withdrawn_trace + trace_at);
}

__device__ __forceinline__ uint64_t contact_abs_i64(int64_t value) {
    // Avoid negating INT64_MIN. The host admission proves the declared differences fit the square
    // aperture; this expression is nevertheless total over the full wire.
    return value < 0 ? (uint64_t)(-(value + 1)) + 1ULL : (uint64_t)value;
}

__device__ __forceinline__ uint8_t contact_class_of_pair(
    const int64_t *lower_xyz,
    const int64_t *upper_xyz,
    uint32_t left,
    uint32_t right,
    uint64_t aperture_squared)
{
    uint64_t minimum = 0ULL;
    uint64_t maximum = 0ULL;
    for (uint32_t axis = 0; axis < 3; ++axis) {
        const uint64_t left_at = (uint64_t)left * 3ULL + axis;
        const uint64_t right_at = (uint64_t)right * 3ULL + axis;
        const int64_t low = lower_xyz[left_at] - upper_xyz[right_at];
        const int64_t high = upper_xyz[left_at] - lower_xyz[right_at];
        const uint64_t low_abs = contact_abs_i64(low);
        const uint64_t high_abs = contact_abs_i64(high);
        const uint64_t far = low_abs > high_abs ? low_abs : high_abs;
        const uint64_t near = (low <= 0 && high >= 0)
                                  ? 0ULL
                                  : (low_abs < high_abs ? low_abs : high_abs);
        minimum += near * near;
        maximum += far * far;
    }
    if (maximum <= aperture_squared) {
        return 1u; // Inside, including the exact boundary.
    }
    if (minimum > aperture_squared) {
        return 0u; // Outside.
    }
    return 2u; // Open: the coordinate box crosses the receiver aperture.
}

/// One lane classifies one addressed pair from exact integer coordinate boxes. The common
/// denominator has already been carried into `aperture_squared`; no division and no float occurs.
extern "C" __global__ void classify_contact_pairs(
    const int64_t *lower_xyz,
    const int64_t *upper_xyz,
    const uint32_t *left_vertex,
    const uint32_t *right_vertex,
    uint8_t *class_out,
    uint32_t pair_count,
    uint64_t aperture_squared)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= pair_count) {
        return;
    }
    class_out[at] = contact_class_of_pair(
        lower_xyz,
        upper_xyz,
        left_vertex[at],
        right_vertex[at],
        aperture_squared);
}

/// Compare two matched presentation readings while the contact population remains resident. The
/// exact ordered pair is retained as `3*left + right`; unequal classes are not collapsed to a bit.
extern "C" __global__ void compare_contact_presentations(
    const uint8_t *contact_class,
    const uint32_t *left_reading,
    const uint32_t *right_reading,
    uint8_t *paired_class_out,
    uint32_t comparison_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= comparison_count) {
        return;
    }
    const uint8_t left = contact_class[left_reading[at]];
    const uint8_t right = contact_class[right_reading[at]];
    paired_class_out[at] = (uint8_t)(3u * left + right);
}

/// Retained: the fused material-and-law entry, kept because the separation front already conducts
/// through it and a working carrier is not withdrawn to make a point about factoring.
extern "C" __global__ void refine_shell(
    const uint32_t *site_whole,      // per site: which whole it lives in
    const uint32_t *site_position,   // per site: its index inside that whole
    const uint32_t *site_class,      // per site: its class at shell k-1
    const uint32_t *whole_offset,    // per whole: where its stream begins in `stream`
    const uint32_t *whole_length,    // per whole: how long its stream is
    const uint32_t *stream,          // every whole's surface ids, concatenated
    const uint32_t *reading_id,      // per surface: the dense identity of its reading
    uint64_t *table_pair,            // capacity slots of (class,key), REFINE_EMPTY when free
    uint64_t *table_key,             // capacity slots: the key half, for the second comparand
    uint32_t *site_next_class,       // per site: the claimed slot index
    uint32_t site_count,
    uint32_t depth,
    uint32_t capacity_mask)          // capacity - 1; capacity is a power of two
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= site_count) {
        return;
    }

    const uint32_t whole = site_whole[at];
    const int64_t position = (int64_t)site_position[at];
    const int64_t length = (int64_t)whole_length[whole];
    const uint32_t base = whole_offset[whole];
    const int64_t step = (int64_t)depth;

    const int64_t left_site = position - step;
    const int64_t right_site = position + step;
    const uint32_t left = (left_site < 0 || left_site >= length)
                              ? REFINE_ABSENT
                              : reading_id[stream[base + (uint32_t)left_site]];
    const uint32_t right = (right_site < 0 || right_site >= length)
                               ? REFINE_ABSENT
                               : reading_id[stream[base + (uint32_t)right_site]];

    const uint64_t key = ((uint64_t)left << 32) | (uint64_t)right;
    const uint64_t klass = (uint64_t)site_class[at];

    // Claim the identity of (class, key). Both halves are compared, so a slot is shared only by
    // occurrences that agree on BOTH — which is exactly the refinement condition.
    uint64_t probe = refine_mix(klass * 0x9e3779b97f4a7c15ULL + key) & (uint64_t)capacity_mask;
    for (;;) {
        const uint64_t seen = ((volatile uint64_t *)table_pair)[probe];
        if (seen == klass) {
            // **The claim and the key are two stores, so a reader can see the first without the
            // second.** Falling through here was a real defect: a lane that found its own class in
            // a slot whose key had not yet landed walked on and claimed a SECOND slot for the same
            // pair, splitting one class in two. Measured on `"of"` at shell one: 1,794 classes on
            // the card against 1,787 on the cpu, the card finer by exactly the races it lost.
            //
            // The wait is bounded by one store from a lane that has already won its exchange, and
            // `key` can never be the empty marker: it is two 32-bit reading identities and the
            // marker is all ones.
            while (((volatile uint64_t *)table_key)[probe] == REFINE_EMPTY) {
            }
            if (((volatile uint64_t *)table_key)[probe] == key) {
                site_next_class[at] = (uint32_t)probe;
                return;
            }
            probe = (probe + 1) & (uint64_t)capacity_mask;
            continue;
        }
        if (seen == REFINE_EMPTY) {
            const uint64_t won = atomicCAS(
                (unsigned long long *)&table_pair[probe],
                (unsigned long long)REFINE_EMPTY,
                (unsigned long long)klass);
            if (won == REFINE_EMPTY) {
                table_key[probe] = key;
                __threadfence();
                site_next_class[at] = (uint32_t)probe;
                return;
            }
            // Another lane took the slot between the read and the exchange. Re-examine it: if it
            // took it for this same pair we join it, otherwise we walk on.
            if (won == klass) {
                // Same wait as above: the winner claimed for this class, and its key becomes
                // visible one store later.
                while (((volatile uint64_t *)table_key)[probe] == REFINE_EMPTY) {
                }
                if (((volatile uint64_t *)table_key)[probe] == key) {
                    site_next_class[at] = (uint32_t)probe;
                    return;
                }
            }
        }
        probe = (probe + 1) & (uint64_t)capacity_mask;
    }
}

/// One lane per slot. Marks which table slots were claimed, so the cpu can compact the sparse slot
/// indices into a dense class numbering without scanning the sites.
extern "C" __global__ void refine_claimed(
    const uint64_t *table_pair,
    uint32_t *claimed,
    uint32_t capacity)
{
    uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= capacity) {
        return;
    }
    claimed[at] = (table_pair[at] == REFINE_EMPTY) ? 0u : 1u;
}
