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

/// **Plural addressed words cross one resident front without padding or a host phase loop.**
///
/// `word_offset` and `trace_offset` are exact prefix sums derived from the admitted word family.
/// One lane owns one complete ordered word.  Shared immutable action is mounted once; disjoint
/// trace intervals are the apparatus footprint which licenses the co-present front.  Different
/// words are never reordered or padded into an authored context extent.
extern "C" __global__ void conduct_native_ragged_trace(
    const uint32_t *generator_table,
    const uint32_t *words,
    const uint32_t *word_offset,
    const uint32_t *native_start,
    const uint32_t *trace_offset,
    uint32_t *native_trace,
    uint32_t front_count,
    uint32_t state_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= front_count) {
        return;
    }
    const uint32_t word_begin = word_offset[at];
    const uint32_t word_end = word_offset[at + 1U];
    const uint32_t trace_begin = trace_offset[at];
    uint32_t state = native_start[at];
    native_trace[trace_begin] = state;
    for (uint32_t step = word_begin; step < word_end; ++step) {
        state = generator_table[words[step] * state_count + state];
        native_trace[trace_begin + (step - word_begin) + 1U] = state;
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

__device__ __forceinline__ uint32_t dynamic_morphology_trace(
    const uint32_t *action,
    uint32_t start,
    uint32_t state_count,
    uint32_t *trace)
{
    uint32_t state = start;
    trace[0] = state;
    for (uint32_t step = 0; step < state_count; ++step) {
        const uint32_t next = action[state];
        trace[step + 1U] = next;
        bool repeated = false;
        for (uint32_t prior = 0; prior <= step; ++prior) {
            repeated = repeated || trace[prior] == next;
        }
        if (repeated) {
            for (uint32_t fill = step + 2U; fill <= state_count; ++fill) {
                trace[fill] = next;
            }
            return step + 2U;
        }
        state = next;
    }
    return 0U;
}

/// **Returned receiver current founds one local morphology on the card.**
///
/// `support_incidence` is the complete receiver-by-native-state incidence of the returned world
/// occurrences and `receiver_covector` is their oriented exact current. Lane zero forms the
/// integer adjoint `A^T r`, admits a commit only when every declared return is positive and its
/// support is one local face, extends the finite action by the returned-constraint boundary, and
/// changes only that supported relation. The remaining lanes then carry development and held-out
/// starts through predecessor, successor, and exact withdrawal. Extent is the supplied incidence
/// and finite state population; there is no authored trace depth or host phase callback.
extern "C" __global__ void cultivate_dynamic_morphology(
    const uint32_t *predecessor_action,
    const int32_t *support_incidence,
    const int32_t *receiver_covector,
    const uint32_t *native_start,
    int64_t *returned_adjoint,
    uint32_t *predecessor_extended,
    uint32_t *successor_action,
    uint32_t *withdrawn_action,
    uint32_t *predecessor_trace,
    uint32_t *successor_trace,
    uint32_t *withdrawn_trace,
    uint32_t *predecessor_lengths,
    uint32_t *successor_lengths,
    uint32_t *withdrawn_lengths,
    uint32_t *decision,
    uint32_t *support_state,
    uint32_t predecessor_state_count,
    uint32_t return_count,
    uint32_t start_count)
{
    if (blockIdx.x != 0U) {
        return;
    }
    const uint32_t lane = threadIdx.x;
    const uint32_t successor_state_count = predecessor_state_count + 1U;
    if (lane == 0U) {
        bool all_positive = return_count > 0U && predecessor_state_count > 0U;
        uint32_t nonzero_support = 0U;
        uint32_t supported = 0xffffffffU;
        for (uint32_t receiver = 0; receiver < return_count; ++receiver) {
            all_positive = all_positive && receiver_covector[receiver] > 0;
        }
        for (uint32_t state = 0; state < predecessor_state_count; ++state) {
            int64_t current = 0;
            for (uint32_t receiver = 0; receiver < return_count; ++receiver) {
                const uint64_t at = (uint64_t)receiver * (uint64_t)predecessor_state_count
                                  + (uint64_t)state;
                current += (int64_t)support_incidence[at]
                         * (int64_t)receiver_covector[receiver];
            }
            returned_adjoint[state] = current;
            if (current != 0) {
                ++nonzero_support;
                supported = state;
                all_positive = all_positive && current > 0;
            }
        }
        const bool committed = all_positive && nonzero_support == 1U;
        decision[0] = committed ? 1U : 0U;
        support_state[0] = supported;
        for (uint32_t state = 0; state < predecessor_state_count; ++state) {
            predecessor_extended[state] = predecessor_action[state];
            successor_action[state] = predecessor_action[state];
            withdrawn_action[state] = predecessor_action[state];
        }
        const uint32_t returned_state = predecessor_state_count;
        predecessor_extended[returned_state] = returned_state;
        successor_action[returned_state] = returned_state;
        withdrawn_action[returned_state] = returned_state;
        if (committed) {
            successor_action[supported] = returned_state;
        }
    }
    __syncthreads();

    for (uint32_t at = lane; at < start_count; at += blockDim.x) {
        const uint64_t trace_at = (uint64_t)at * (uint64_t)(successor_state_count + 1U);
        predecessor_lengths[at] = dynamic_morphology_trace(
            predecessor_extended,
            native_start[at],
            successor_state_count,
            predecessor_trace + trace_at);
        successor_lengths[at] = dynamic_morphology_trace(
            successor_action,
            native_start[at],
            successor_state_count,
            successor_trace + trace_at);
        withdrawn_lengths[at] = dynamic_morphology_trace(
            withdrawn_action,
            native_start[at],
            successor_state_count,
            withdrawn_trace + trace_at);
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

/// **One shared world-state generator crosses every typed port while local faces remain local.**
///
/// `decoder` is family-major, port-major, state-minor.  Each lane owns one family/port cell.  The
/// shared withdrawal returns every cell to its predecessor consequence.  The local-ablation matrix
/// has one column per port: withdrawing port `p` returns only cells of `p` to their predecessor and
/// leaves every other port on the shared successor.  Thus a shared generator is enacted once; it
/// is not copied into one modality-specific table per port.
extern "C" __global__ void conduct_heterogeneous_fusion(
    const uint32_t *successor_action,
    const uint32_t *decoder,
    const uint32_t *native_start,
    uint32_t *predecessor_consequence,
    uint32_t *successor_consequence,
    uint32_t *shared_ablated_consequence,
    uint32_t *local_ablated_consequence,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t port_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const uint32_t start = native_start[at];
    const uint32_t next = successor_action[start];
    const uint64_t decoder_at = (uint64_t)at * (uint64_t)state_count;
    const uint32_t before = decoder[decoder_at + start];
    const uint32_t after = decoder[decoder_at + next];
    predecessor_consequence[at] = before;
    successor_consequence[at] = after;
    shared_ablated_consequence[at] = before;

    const uint32_t local_port = at % port_count;
    const uint64_t local_at = (uint64_t)at * (uint64_t)port_count;
    for (uint32_t withdrawn_port = 0; withdrawn_port < port_count; ++withdrawn_port) {
        local_ablated_consequence[local_at + withdrawn_port] =
            local_port == withdrawn_port ? before : after;
    }
}

/// **Every source correspondence contributes to one addressed anchor/port population.**
///
/// The exterior codec has already replaced long occurrence addresses by exact local indices.  A
/// lane owns one `(anchor, port)` cell and visits the complete pair population; no atomics, winner,
/// confidence threshold, or collection order can change the returned multiplicity.
extern "C" __global__ void derive_media_candidate_counts(
    const uint32_t *pair_anchor,
    const uint32_t *pair_port,
    uint32_t *candidate_counts,
    uint32_t anchor_count,
    uint32_t port_count,
    uint32_t pair_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    const uint64_t cell_count = (uint64_t)anchor_count * (uint64_t)port_count;
    if ((uint64_t)at >= cell_count) {
        return;
    }
    const uint32_t anchor = at / port_count;
    const uint32_t port = at % port_count;
    uint32_t count = 0U;
    for (uint32_t pair = 0; pair < pair_count; ++pair) {
        if (pair_anchor[pair] == anchor && pair_port[pair] == port) {
            ++count;
        }
    }
    candidate_counts[at] = count;
}

/// **One shared media subcomplex crosses every port and every held-out anchor.**
///
/// The first population is anchor-major/port-minor and retains correspondence multiplicity.  A
/// joint anchor exists only when every typed port has a nonempty fibre.  The second population is
/// family-major/port-major/state-minor and returns the shared and local withdrawals.  Both laws
/// cross one launch so a host callback cannot choose whether the media faces meet.
extern "C" __global__ void conduct_joint_media_transport(
    const uint32_t *candidate_counts,
    uint32_t *joint_anchor,
    uint32_t *shared_ablated_joint_anchor,
    uint32_t *local_ablated_joint_anchor,
    uint32_t anchor_count,
    const uint32_t *successor_action,
    const uint32_t *decoder,
    const uint32_t *native_start,
    uint32_t *predecessor_consequence,
    uint32_t *successor_consequence,
    uint32_t *shared_ablated_consequence,
    uint32_t *local_ablated_consequence,
    uint32_t cell_count,
    uint32_t state_count,
    uint32_t port_count)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < anchor_count) {
        uint32_t joint = 1U;
        const uint64_t count_at = (uint64_t)at * (uint64_t)port_count;
        for (uint32_t port = 0; port < port_count; ++port) {
            if (candidate_counts[count_at + port] == 0U) {
                joint = 0U;
            }
        }
        joint_anchor[at] = joint;
        shared_ablated_joint_anchor[at] = 0U;
        const uint64_t local_at = (uint64_t)at * (uint64_t)port_count;
        for (uint32_t withdrawn_port = 0; withdrawn_port < port_count; ++withdrawn_port) {
            local_ablated_joint_anchor[local_at + withdrawn_port] = 0U;
        }
    }
    if (at >= cell_count) {
        return;
    }
    const uint32_t start = native_start[at];
    const uint32_t next = successor_action[start];
    const uint64_t decoder_at = (uint64_t)at * (uint64_t)state_count;
    const uint32_t before = decoder[decoder_at + start];
    const uint32_t after = decoder[decoder_at + next];
    predecessor_consequence[at] = before;
    successor_consequence[at] = after;
    shared_ablated_consequence[at] = before;
    const uint32_t local_port = at % port_count;
    const uint64_t local_at = (uint64_t)at * (uint64_t)port_count;
    for (uint32_t withdrawn_port = 0; withdrawn_port < port_count; ++withdrawn_port) {
        local_ablated_consequence[local_at + withdrawn_port] =
            local_port == withdrawn_port ? before : after;
    }
}

/// **R6's plural production fronts remain disjoint until one typed reduction.**
///
/// Retained-context words, returned-constraint morphology, and held-out mathematical-media
/// sections occupy disjoint output footprints.  The only shared writes are exact commutative
/// additions inside the media population itself.  Extents come from the mounted rests and the
/// entering inquiry; no response, context, or derivation capacity is supplied.
extern "C" __global__ void conduct_production_aperture_fronts(
    const uint32_t *context_table,
    const uint32_t *context_word,
    const uint32_t *context_start,
    uint32_t *context_trace,
    uint32_t *context_boundary_withdrawn_trace,
    uint32_t context_cells,
    uint32_t context_states,
    uint32_t context_word_length,
    const uint32_t *derivation_predecessor_action,
    const uint32_t *derivation_successor_action,
    const uint32_t *derivation_start,
    uint32_t *derivation_predecessor_trace,
    uint32_t *derivation_successor_trace,
    uint32_t *derivation_selected_trace,
    uint32_t *derivation_generator_withdrawn_trace,
    uint32_t *derivation_predecessor_length,
    uint32_t *derivation_successor_length,
    uint32_t *derivation_selected_length,
    uint32_t *derivation_generator_withdrawn_length,
    uint32_t derivation_cells,
    uint32_t derivation_states,
    const uint32_t *media_candidate_species,
    uint64_t *media_species_totals,
    uint64_t *media_joint_anchors,
    uint32_t media_anchors,
    uint32_t media_species,
    uint32_t committed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < context_cells) {
        const uint32_t stride = context_word_length + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        uint32_t state = context_start[at];
        context_trace[trace_at] = state;
        context_boundary_withdrawn_trace[trace_at] = state;
        for (uint32_t step = 0; step < context_word_length; ++step) {
            state = context_table[context_word[step] * context_states + state];
            context_trace[trace_at + (uint64_t)step + 1ULL] = state;
            context_boundary_withdrawn_trace[trace_at + (uint64_t)step + 1ULL] =
                context_start[at];
        }
    }
    if (at < derivation_cells) {
        const uint32_t stride = derivation_states + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        const uint32_t start = derivation_start[at];
        derivation_predecessor_length[at] = dynamic_morphology_trace(
            derivation_predecessor_action,
            start,
            derivation_states,
            derivation_predecessor_trace + trace_at);
        derivation_successor_length[at] = dynamic_morphology_trace(
            derivation_successor_action,
            start,
            derivation_states,
            derivation_successor_trace + trace_at);
        derivation_selected_length[at] = dynamic_morphology_trace(
            committed == 0U ? derivation_predecessor_action : derivation_successor_action,
            start,
            derivation_states,
            derivation_selected_trace + trace_at);
        // Withdrawing the generator is the identity endomap.  It is distinct from withdrawing
        // cultivation, which restores the predecessor action above.
        uint32_t *withdrawn = derivation_generator_withdrawn_trace + trace_at;
        withdrawn[0] = start;
        withdrawn[1] = start;
        for (uint32_t fill = 2U; fill <= derivation_states; ++fill) {
            withdrawn[fill] = start;
        }
        derivation_generator_withdrawn_length[at] = 2U;
    }
    if (at < media_anchors) {
        bool joint = true;
        const uint64_t base = (uint64_t)at * (uint64_t)media_species;
        for (uint32_t species = 0; species < media_species; ++species) {
            const uint32_t count = media_candidate_species[base + species];
            joint = joint && count != 0U;
            atomicAdd(
                (unsigned long long *)&media_species_totals[species],
                (unsigned long long)count);
        }
        if (joint) {
            atomicAdd((unsigned long long *)media_joint_anchors, 1ULL);
        }
    }
}

/// **One typed junction joins the independent R6 fronts after their complete resident return.**
///
/// The reduction keeps each media species, their shared and local withdrawals, the oriented
/// raster difference, and its hand.  It never selects a candidate or collapses the reconstruction
/// fibres.  Default-stream order is the exact predecessor relation from the front launch.
extern "C" __global__ void reduce_production_aperture_fronts(
    const uint64_t *media_species_totals,
    const uint32_t *media_species_port,
    uint64_t *media_shared_withdrawn_totals,
    uint64_t *media_local_withdrawn_totals,
    uint64_t *total_joint_incidence,
    int64_t *oriented_difference,
    uint64_t *difference_magnitude,
    int32_t *difference_hand,
    uint32_t *selected_cultivation_state,
    uint32_t media_species,
    uint32_t media_ports,
    uint32_t left_species,
    uint32_t right_species,
    uint32_t committed)
{
    if (blockIdx.x != 0U || threadIdx.x != 0U) {
        return;
    }
    uint64_t total = 0ULL;
    for (uint32_t species = 0; species < media_species; ++species) {
        const uint64_t count = media_species_totals[species];
        total += count;
        media_shared_withdrawn_totals[species] = 0ULL;
        for (uint32_t withdrawn_port = 0; withdrawn_port < media_ports; ++withdrawn_port) {
            const uint64_t at = (uint64_t)species * (uint64_t)media_ports + withdrawn_port;
            media_local_withdrawn_totals[at] =
                media_species_port[species] == withdrawn_port ? 0ULL : count;
        }
    }
    const uint64_t left = media_species_totals[left_species];
    const uint64_t right = media_species_totals[right_species];
    const bool positive = left >= right;
    total_joint_incidence[0] = total;
    difference_magnitude[0] = positive ? left - right : right - left;
    difference_hand[0] = left == right ? 0 : (positive ? 1 : -1);
    oriented_difference[0] = positive
        ? (int64_t)(left - right)
        : -(int64_t)(right - left);
    selected_cultivation_state[0] = committed;
}

/// Transport homogeneous binary quadratic sections through their declared integer chart maps.
///
/// Each section carries the coefficient face `a*x^2 + b*x*y + c*y^2` and one complete two-axis
/// map. The card returns the exact coefficient face after substitution. Equality is a receiver
/// face of that transport; it does not identify the entering and returned occurrences.
extern "C" __global__ void conduct_quadratic_section_transport(
    const int64_t *coefficients,
    const int64_t *transforms,
    int64_t *transported_coefficients,
    uint32_t *invariant,
    uint32_t *selected_route,
    uint32_t *ablated_route,
    uint32_t sections,
    uint32_t cultivated)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= sections) {
        return;
    }
    const uint64_t coefficient_at = (uint64_t)at * 3ULL;
    const uint64_t transform_at = (uint64_t)at * 4ULL;
    const int64_t a = coefficients[coefficient_at];
    const int64_t b = coefficients[coefficient_at + 1ULL];
    const int64_t c = coefficients[coefficient_at + 2ULL];
    const int64_t p = transforms[transform_at];
    const int64_t q = transforms[transform_at + 1ULL];
    const int64_t r = transforms[transform_at + 2ULL];
    const int64_t s = transforms[transform_at + 3ULL];

    // The returned L0 morphology is the central-inversion fixed-locus route.  Once rested, this
    // exact chart family carries the entering degree-two coefficient face directly.  Withdrawal
    // leaves the expanded substitution below intact; no host branch or relaunch reconstructs it.
    if (cultivated != 0U && p == -1LL && q == 0LL && r == 0LL && s == -1LL) {
        transported_coefficients[coefficient_at] = a;
        transported_coefficients[coefficient_at + 1ULL] = b;
        transported_coefficients[coefficient_at + 2ULL] = c;
        invariant[at] = 1U;
        selected_route[at] = 1U;
        ablated_route[at] = 0U;
        return;
    }

    const int64_t returned_a = a * p * p + b * p * r + c * r * r;
    const int64_t returned_b =
        2LL * a * p * q + b * (p * s + q * r) + 2LL * c * r * s;
    const int64_t returned_c = a * q * q + b * q * s + c * s * s;
    transported_coefficients[coefficient_at] = returned_a;
    transported_coefficients[coefficient_at + 1ULL] = returned_b;
    transported_coefficients[coefficient_at + 2ULL] = returned_c;
    const uint32_t held =
        returned_a == a && returned_b == b && returned_c == c ? 1U : 0U;
    invariant[at] = held;
    selected_route[at] = held == 0U ? 2U : 0U;
    ablated_route[at] = held == 0U ? 2U : 0U;
}

/// **The recurrent passage and every conserved modality face cross one inference front.**
///
/// I3 and I4 retain different state spaces. Their only identification is the explicit binary
/// cultivation decision. Distinct ports, traces, and reconstruction addresses remain distinct.
extern "C" __global__ void conduct_inference_ecology(
    const uint32_t *recurrent_action,
    const uint32_t *recurrent_start,
    uint32_t *recurrent_predecessor_trace,
    uint32_t *recurrent_successor_trace,
    uint32_t *recurrent_withdrawn_trace,
    uint32_t *recurrent_selected_trace,
    uint32_t *recurrent_predecessor_length,
    uint32_t *recurrent_successor_length,
    uint32_t *recurrent_withdrawn_length,
    uint32_t *recurrent_selected_length,
    uint32_t *recurrent_seen,
    uint32_t recurrent_cells,
    uint32_t recurrent_states,
    uint32_t recurrent_seen_words,
    uint32_t recurrent_predecessor_from,
    uint32_t recurrent_predecessor_to,
    const uint32_t *world_action,
    const uint32_t *world_decoder,
    const uint32_t *world_start,
    uint32_t *world_predecessor_consequence,
    uint32_t *world_successor_consequence,
    uint32_t *world_selected_consequence,
    uint32_t *world_shared_ablated_consequence,
    uint32_t *world_local_ablated_consequence,
    uint32_t world_cells,
    uint32_t world_states,
    uint32_t world_ports,
    uint32_t committed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < recurrent_cells) {
        const uint32_t stride = recurrent_states + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        const uint64_t seen_stride = (uint64_t)recurrent_cells * recurrent_seen_words;
        const uint64_t seen_at = (uint64_t)at * recurrent_seen_words;
        recurrent_predecessor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, true, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_at, recurrent_predecessor_trace + trace_at);
        recurrent_successor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, false, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_stride + seen_at, recurrent_successor_trace + trace_at);
        recurrent_withdrawn_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, false, true,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 2ULL * seen_stride + seen_at,
            recurrent_withdrawn_trace + trace_at);
        recurrent_selected_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start[at], recurrent_states, committed == 0U, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 3ULL * seen_stride + seen_at,
            recurrent_selected_trace + trace_at);
    }
    if (at < world_cells) {
        const uint32_t start = world_start[at];
        const uint32_t next = world_action[start];
        const uint64_t decoder_at = (uint64_t)at * (uint64_t)world_states;
        const uint32_t before = world_decoder[decoder_at + start];
        const uint32_t after = world_decoder[decoder_at + next];
        world_predecessor_consequence[at] = before;
        world_successor_consequence[at] = after;
        world_selected_consequence[at] = committed == 0U ? before : after;
        world_shared_ablated_consequence[at] = before;
        const uint32_t local_port = at % world_ports;
        const uint64_t local_at = (uint64_t)at * (uint64_t)world_ports;
        for (uint32_t withdrawn_port = 0; withdrawn_port < world_ports; ++withdrawn_port) {
            world_local_ablated_consequence[local_at + withdrawn_port] =
                local_port == withdrawn_port ? before : after;
        }
    }
}

__device__ __forceinline__ uint32_t first_equal_payload(
    const uint64_t *face_key,
    uint32_t face,
    uint32_t *comparison_count)
{
    const uint64_t at = (uint64_t)face * 4ULL;
    uint32_t compared = 0U;
    for (uint32_t candidate = 0U; candidate <= face; ++candidate) {
        const uint64_t candidate_at = (uint64_t)candidate * 4ULL;
        ++compared;
        bool equal = true;
        for (uint32_t word = 0U; word < 4U; ++word) {
            equal = equal && face_key[at + word] == face_key[candidate_at + word];
        }
        if (equal) {
            *comparison_count = compared;
            return candidate + 1U;
        }
    }
    *comparison_count = compared;
    return face + 1U;
}

/// One rich-intake pullback crosses the unchanged inference ecology.  Payload equality, situated
/// face contact, M1 entry lineage, recurrent sections, and world consequences are one resident
/// front.  Every presentation branch crosses every admitted start; the kernel selects no semantic
/// representative and returns both recurrence alternatives and all I5 withdrawals.
extern "C" __global__ void conduct_material_operation_world_tube(
    const uint64_t *face_key,
    const uint32_t *face_branch,
    const uint64_t *branch_staging_event,
    const uint64_t *branch_terminal_event,
    const uint32_t *contact_from,
    const uint32_t *contact_to,
    const uint32_t *contact_relation,
    uint32_t *face_payload_class,
    uint32_t *face_comparison_count,
    uint64_t *face_staging_event,
    uint64_t *face_terminal_event,
    uint32_t *contact_left_class,
    uint32_t *contact_right_class,
    uint32_t *contact_relation_out,
    uint64_t *recurrence_staging_event,
    uint64_t *recurrence_terminal_event,
    uint32_t face_count,
    uint32_t contact_count,
    uint32_t branch_count,
    uint32_t recurrence_cells_per_branch,
    const uint32_t *recurrent_action,
    const uint32_t *recurrent_start,
    uint32_t *recurrent_predecessor_trace,
    uint32_t *recurrent_successor_trace,
    uint32_t *recurrent_withdrawn_trace,
    uint32_t *recurrent_selected_trace,
    uint32_t *recurrent_predecessor_length,
    uint32_t *recurrent_successor_length,
    uint32_t *recurrent_withdrawn_length,
    uint32_t *recurrent_selected_length,
    uint32_t *recurrent_seen,
    uint32_t recurrent_cells,
    uint32_t recurrent_states,
    uint32_t recurrent_seen_words,
    uint32_t recurrent_predecessor_from,
    uint32_t recurrent_predecessor_to,
    const uint32_t *world_action,
    const uint32_t *world_decoder,
    const uint32_t *world_start,
    uint32_t *world_predecessor_consequence,
    uint32_t *world_successor_consequence,
    uint32_t *world_selected_consequence,
    uint32_t *world_shared_ablated_consequence,
    uint32_t *world_local_ablated_consequence,
    uint32_t world_cells,
    uint32_t world_cells_per_branch,
    uint32_t world_states,
    uint32_t world_ports,
    uint32_t committed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at < face_count) {
        uint32_t comparisons = 0U;
        face_payload_class[at] = first_equal_payload(face_key, at, &comparisons);
        face_comparison_count[at] = comparisons;
        const uint32_t branch = face_branch[at];
        if (branch >= branch_count) {
            return;
        }
        face_staging_event[at] = branch_staging_event[branch];
        face_terminal_event[at] = branch_terminal_event[branch];
    }
    if (at < contact_count) {
        uint32_t ignored = 0U;
        contact_left_class[at] = first_equal_payload(face_key, contact_from[at], &ignored);
        contact_right_class[at] = first_equal_payload(face_key, contact_to[at], &ignored);
        contact_relation_out[at] = contact_relation[at];
    }
    if (at < recurrent_cells) {
        const uint32_t branch = at / recurrence_cells_per_branch;
        if (branch >= branch_count) {
            return;
        }
        recurrence_staging_event[at] = branch_staging_event[branch];
        recurrence_terminal_event[at] = branch_terminal_event[branch];
        const uint32_t stride = recurrent_states + 1U;
        const uint64_t trace_at = (uint64_t)at * (uint64_t)stride;
        const uint64_t seen_stride = (uint64_t)recurrent_cells * recurrent_seen_words;
        const uint64_t seen_at = (uint64_t)at * recurrent_seen_words;
        const uint32_t recurrent_start_at = recurrent_start[at % recurrence_cells_per_branch];
        recurrent_predecessor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, true, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_at, recurrent_predecessor_trace + trace_at);
        recurrent_successor_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, false, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + seen_stride + seen_at, recurrent_successor_trace + trace_at);
        recurrent_withdrawn_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, false, true,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 2ULL * seen_stride + seen_at,
            recurrent_withdrawn_trace + trace_at);
        recurrent_selected_length[at] = condensed_recurrent_trace(
            recurrent_action, recurrent_start_at, recurrent_states, committed == 0U, false,
            recurrent_predecessor_from, recurrent_predecessor_to,
            recurrent_seen + 3ULL * seen_stride + seen_at,
            recurrent_selected_trace + trace_at);
    }
    if (at < world_cells) {
        const uint32_t world_at = at % world_cells_per_branch;
        const uint32_t start = world_start[world_at];
        const uint32_t next = world_action[start];
        const uint64_t decoder_at = (uint64_t)world_at * (uint64_t)world_states;
        const uint32_t before = world_decoder[decoder_at + start];
        const uint32_t after = world_decoder[decoder_at + next];
        world_predecessor_consequence[at] = before;
        world_successor_consequence[at] = after;
        world_selected_consequence[at] = committed == 0U ? before : after;
        world_shared_ablated_consequence[at] = before;
        const uint32_t local_port = at % world_ports;
        const uint64_t local_at = (uint64_t)at * (uint64_t)world_ports;
        for (uint32_t withdrawn_port = 0; withdrawn_port < world_ports; ++withdrawn_port) {
            world_local_ablated_consequence[local_at + withdrawn_port] =
                local_port == withdrawn_port ? before : after;
        }
    }
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
