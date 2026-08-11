// The partition refinement shell, enacted on the card.
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
// agree at an offset exactly when those four words agree, so the host assigns each DISTINCT reading
// a dense identity once, over the whole corpus, and hands the device a `reading_id` per surface.
// Equality of readings is then equality of identities, exactly, and a shell key is
//
//     key = (reading_id at −k) << 32 | (reading_id at +k)
//
// with `ABSENT` standing for an offset that has run off the end of its whole. `ABSENT` is a
// distinguished identity and not a magic number: a terminus is family-invariant — deleting a
// receiver never merges "the whole ended" with a reading — so it must be a value no reading can
// take, and the host reserves identity zero for it before assigning any other.
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
// The host sizes it as the next power of two strictly above the occurrence count — derived from
// the material, with no load factor and no number chosen.

#include <stdint.h>

// The identity reserved for an offset past the end of a whole. The host assigns every real reading
// an identity at or above one, so this can collide with nothing.
#define REFINE_ABSENT 0u

// An empty table slot. A claimed slot holds `(class, key)` and can never be this, because a class
// identity is at or above one on the host side.
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

/// One lane per occupied occurrence. Computes the shell key and claims the identity of
/// `(class, key)`, writing the claimed slot as the occurrence's new class.
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
            // the card against 1,787 on the host, the card finer by exactly the races it lost.
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

/// One lane per slot. Marks which table slots were claimed, so the host can compact the sparse slot
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
