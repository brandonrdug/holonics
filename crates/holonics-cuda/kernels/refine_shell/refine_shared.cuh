// Shared preamble, arithmetic, and device helper definitions for the refine-shell owners.
#pragma once

// **The exact quotient and its resident materials.**
//
// `claim_identities` is the material-free law: given a class per cell and an exact key per cell, it
// returns the identity of `(class, key)`. `refine_shell` is the still-live fused corpus material;
// the unused stand-alone `shell_keys` entry has departed. Other resident materials expose their own
// keys and reuse the same quotient law.
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


/// **The law: one lane per cell, claiming the identity of `(class, key)`.**
///
/// This is the whole of one 32-bit face of the exact quotient. It is material-free by construction
/// — its only inputs are a class and a key face per cell — so every organ with a front shares it
/// rather than growing a device path of its own. A wider key crosses as successive exact faces.


/// **The quotient action: one lane carries one native state through a complete ordered word.**
///
/// The table is the complete row-major family `U_i : Q -> Q`. The word and every table enter once;
/// the card composes the noncommuting word locally. No host callback selects a semantic phase
/// between generators, and no invariant table is re-uploaded per step.


/// **One oriented incidence section carrying exact complex coefficient current.**
///
/// `incidence` is the row-major real map `B : Node -> Branch` presented by one captured
/// receiver section.  Every lane owns one `(front, branch)` output and accumulates both local
/// phase coordinates through the same incidence row.  The host admits the complete row-mass
/// bound before launch, so the wide accumulator and returned signed word are exact.  Relative
/// phase remains present; this kernel performs no sign, winner, or finite-state quotient.


/// **One coupled causal-adjoint-pulled Complex-Parametron body.**
///
/// The resident primary rows are the exact covectors returned after the receiver constitutive
/// form and reverse causal word have already acted.  This kernel therefore does not receive a
/// metric chart or attempt a second `M` multiplication.  It carries each exact complex coefficient
/// pair through those rows and then adds the retained finite-Leibniz mixed contacts.  An active
/// factor aperture removes both its primary row and every mixed term incident to it on-card.
///
__device__ int compare_magnitude(const uint32_t *left, const uint32_t *right, uint32_t limbs)
{
    for (uint32_t at = limbs; at > 0; --at) {
        const uint32_t index = at - 1;
        if (left[index] < right[index]) return -1;
        if (left[index] > right[index]) return 1;
    }
    return 0;
}

__device__ void add_signed_magnitude(
    uint8_t *acc_sign, uint32_t *accumulator,
    uint8_t term_sign, const uint32_t *term, uint32_t limbs)
{
    if (term_sign == 0) return;
    bool term_is_zero = true;
    for (uint32_t limb = 0; limb < limbs; ++limb) {
        if (term[limb] != 0U) {
            term_is_zero = false;
            break;
        }
    }
    // Signed magnitude has one zero face.  A nonzero coefficient multiplying an annihilated
    // current still contributes zero; carrying the coefficient sign onto that null magnitude
    // would manufacture positive/negative zero and break exact receiver decoding.
    if (term_is_zero) return;
    if (*acc_sign == 0) {
        for (uint32_t limb = 0; limb < limbs; ++limb) accumulator[limb] = term[limb];
        *acc_sign = term_sign;
        return;
    }
    if (*acc_sign == term_sign) {
        uint64_t carry = 0;
        for (uint32_t limb = 0; limb < limbs; ++limb) {
            const uint64_t sum = (uint64_t)accumulator[limb] + (uint64_t)term[limb] + carry;
            accumulator[limb] = (uint32_t)sum;
            carry = sum >> 32;
        }
        return;
    }
    const int comparison = compare_magnitude(accumulator, term, limbs);
    if (comparison == 0) {
        for (uint32_t limb = 0; limb < limbs; ++limb) accumulator[limb] = 0;
        *acc_sign = 0;
        return;
    }
    const uint32_t *larger = comparison > 0 ? accumulator : term;
    const uint32_t *smaller = comparison > 0 ? term : accumulator;
    uint64_t borrow = 0;
    for (uint32_t limb = 0; limb < limbs; ++limb) {
        const uint64_t subtrahend = (uint64_t)smaller[limb] + borrow;
        const uint64_t minuend = (uint64_t)larger[limb];
        accumulator[limb] = (uint32_t)(minuend - subtrahend);
        borrow = minuend < subtrahend;
    }
    if (comparison < 0) *acc_sign = term_sign;
}

/// Add a signed-magnitude term whose carrier may be narrower than the accumulator.  Missing
/// high limbs are exact zero extension; the operation therefore changes only the apparatus
/// width, not the represented current.  This is the native passage needed when a generator
/// fibre enlarges the admitted bound without changing the source section's reconstruction face.
__device__ void add_signed_magnitude_width(
    uint8_t *acc_sign, uint32_t *accumulator, uint32_t accumulator_limbs,
    uint8_t term_sign, const uint32_t *term, uint32_t term_limbs)
{
    if (term_sign == 0U || accumulator_limbs == 0U) return;
    bool term_is_zero = true;
    for (uint32_t limb = 0U; limb < term_limbs; ++limb) {
        if (term[limb] != 0U) {
            term_is_zero = false;
            break;
        }
    }
    if (term_is_zero) return;
    if (*acc_sign == 0U) {
        for (uint32_t limb = 0U; limb < accumulator_limbs; ++limb) {
            accumulator[limb] = limb < term_limbs ? term[limb] : 0U;
        }
        *acc_sign = term_sign;
        return;
    }
    if (*acc_sign == term_sign) {
        uint64_t carry = 0ULL;
        for (uint32_t limb = 0U; limb < accumulator_limbs; ++limb) {
            const uint64_t term_word = limb < term_limbs ? (uint64_t)term[limb] : 0ULL;
            const uint64_t sum = (uint64_t)accumulator[limb] + term_word + carry;
            accumulator[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        return;
    }
    int comparison = 0;
    for (uint32_t at = accumulator_limbs; at > 0U; --at) {
        const uint32_t limb = at - 1U;
        const uint32_t term_word = limb < term_limbs ? term[limb] : 0U;
        if (accumulator[limb] < term_word) {
            comparison = -1;
            break;
        }
        if (accumulator[limb] > term_word) {
            comparison = 1;
            break;
        }
    }
    if (comparison == 0) {
        for (uint32_t limb = 0U; limb < accumulator_limbs; ++limb) accumulator[limb] = 0U;
        *acc_sign = 0U;
        return;
    }
    uint64_t borrow = 0ULL;
    if (comparison > 0) {
        for (uint32_t limb = 0U; limb < accumulator_limbs; ++limb) {
            const uint64_t term_word = limb < term_limbs ? (uint64_t)term[limb] : 0ULL;
            const uint64_t subtrahend = term_word + borrow;
            const uint64_t minuend = (uint64_t)accumulator[limb];
            accumulator[limb] = (uint32_t)(minuend - subtrahend);
            borrow = minuend < subtrahend;
        }
        return;
    }
    for (uint32_t limb = 0U; limb < accumulator_limbs; ++limb) {
        const uint64_t term_word = limb < term_limbs ? (uint64_t)term[limb] : 0ULL;
        const uint64_t subtrahend = (uint64_t)accumulator[limb] + borrow;
        accumulator[limb] = (uint32_t)(term_word - subtrahend);
        borrow = term_word < subtrahend;
    }
    *acc_sign = term_sign;
}

/// The mounted primary current and every exact mixed remainder are rebased at mount to one common
/// positive denominator.  No multiplication or metric reconstruction occurs here.  No winner,
/// sign, or binary receiver is taken here.


/// **One real receiver of an interval-valued potential incidence.**
///
/// Rows are the exact receiver-sufficient vocabulary cover and columns are addressed Parametron
/// coefficient nodes.  A block owns one coefficient front.  Its lanes contract signed interval
/// endpoints, reduce the greatest lower endpoint, and count the complete plural population whose
/// upper endpoint still meets that lower bound.  The returned address is the least row address at
/// the greatest lower endpoint; `plural_count != 1` preserves the unresolved receiver fibre.
/// Negative coefficients reverse the endpoint contribution rather than silently treating an
/// interval as a point.


/// **The same quotient action with every intermediate boundary retained for one terminal read.**
///
/// Each lane owns one starting occurrence and writes its complete ordered trace. The word, total
/// action, and starting population cross once; no apparatus callback observes or selects an
/// intermediate state. `trace_stride` is `word_length + 1`, derived by the caller from the word it
/// is enacting rather than supplied as a second aperture.


/// **Plural addressed words cross one resident front without padding or a host phase loop.**
///
/// `word_offset` and `trace_offset` are exact prefix sums derived from the admitted word family.
/// One lane owns one complete ordered word.  Shared immutable action is mounted once; disjoint
/// trace intervals are the apparatus footprint which licenses the co-present front.  Different
/// words are never reordered or padded into an authored context extent.


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


/// **One shared world-state generator crosses every typed port while local faces remain local.**
///
/// `decoder` is family-major, port-major, state-minor.  Each lane owns one family/port cell.  The
/// shared withdrawal returns every cell to its predecessor consequence.  The local-ablation matrix
/// has one column per port: withdrawing port `p` returns only cells of `p` to their predecessor and
/// leaves every other port on the shared successor.  Thus a shared generator is enacted once; it
/// is not copied into one modality-specific table per port.


/// **Every source correspondence contributes to one addressed anchor/port population.**
///
/// The exterior codec has already replaced long occurrence addresses by exact local indices.  A
/// lane owns one `(anchor, port)` cell and visits the complete pair population; no atomics, winner,
/// confidence threshold, or collection order can change the returned multiplicity.


/// **One shared media subcomplex crosses every port and every held-out anchor.**
///
/// The first population is anchor-major/port-minor and retains correspondence multiplicity.  A
/// joint anchor exists only when every typed port has a nonempty fibre.  The second population is
/// family-major/port-major/state-minor and returns the shared and local withdrawals.  Both laws
/// cross one launch so a host callback cannot choose whether the media faces meet.


/// **R6's plural production fronts remain disjoint until one typed reduction.**
///
/// Retained-context words, returned-constraint morphology, and held-out mathematical-media
/// sections occupy disjoint output footprints.  The only shared writes are exact commutative
/// additions inside the media population itself.  Extents come from the mounted rests and the
/// entering inquiry; no response, context, or derivation capacity is supplied.


/// **One typed junction joins the independent R6 fronts after their complete resident return.**
///
/// The reduction keeps each media species, their shared and local withdrawals, the oriented
/// raster difference, and its hand.  It never selects a candidate or collapses the reconstruction
/// fibres.  Default-stream order is the exact predecessor relation from the front launch.


/// Transport homogeneous binary quadratic sections through their declared integer chart maps.
///
/// Each section carries the coefficient face `a*x^2 + b*x*y + c*y^2` and one complete two-axis
/// map. The card returns the exact coefficient face after substitution. Equality is a receiver
/// face of that transport; it does not identify the entering and returned occurrences.


__device__ __forceinline__ int64_t canonical_mod(int64_t value, int64_t modulus)
{
    if (modulus == 0LL) {
        return value;
    }
    const int64_t residue = value % modulus;
    return residue < 0LL ? residue + modulus : residue;
}

/// Conduct a family of exact fixed-section passages under complete linear actions.
///
/// Each family carries one section, one square action, a row population of receiver constraints,
/// a modulus (`0` means the integer carrier), and one returned-cultivation bit.  A cultivated
/// current may take the direct fixed-section route only when every constraint vanishes.  The
/// exterior owner separately authenticates the universal factorization `A-I = L*C`; this front
/// evaluates the current and returns all expanded/condensed/obstructed alternatives.


/// Conduct the same fixed-section ecology after its dense action and repeated constraints have
/// condensed into one shared oriented generator relation `T = I + L*C`.
///
/// `constraint_orientation` and `factor_orientation` are incidences in {-1, 0, 1}.  The former
/// evaluates the shared covector `C`; the latter carries its returned residual through `L`.
/// Carrier moduli and cultivation occurrences remain family-local, so equal present sections do
/// not identify integer and finite-carrier successor histories.


/// Join the independently returned fixed-section families only after their complete routes stand.


/// **The recurrent passage and every conserved modality face cross one inference front.**
///
/// I3 and I4 retain different state spaces. Their only identification is the explicit binary
/// cultivation decision. Distinct ports, traces, and reconstruction addresses remain distinct.


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


/// Compare two matched presentation readings while the contact population remains resident. The
/// exact ordered pair is retained as `3*left + right`; unequal classes are not collapsed to a bit.


// One local optical incidence word. The low half is left->right and the high half is
// right->left. The word retains simultaneous roles; it is not a preferred segmentation.
static constexpr uint32_t OPTICAL_PROXIMITY = 1u << 0;
static constexpr uint32_t OPTICAL_BASELINE = 1u << 1;
static constexpr uint32_t OPTICAL_READING = 1u << 2;
static constexpr uint32_t OPTICAL_SUPERSCRIPT = 1u << 3;
static constexpr uint32_t OPTICAL_SUBSCRIPT = 1u << 4;
static constexpr uint32_t OPTICAL_FRACTION_NUMERATOR = 1u << 5;
static constexpr uint32_t OPTICAL_FRACTION_DENOMINATOR = 1u << 6;
static constexpr uint32_t OPTICAL_RADICAL = 1u << 7;
static constexpr uint32_t OPTICAL_DELIMITER = 1u << 8;
static constexpr uint32_t OPTICAL_MATRIX_ROW = 1u << 9;
static constexpr uint32_t OPTICAL_MATRIX_COLUMN = 1u << 10;
static constexpr uint32_t OPTICAL_ALIGNMENT = 1u << 11;
static constexpr uint32_t OPTICAL_DIAGRAM = 1u << 12;
static constexpr uint32_t OPTICAL_TERM_CONTACT = 1u << 13;
static constexpr uint32_t OPTICAL_LINE_CONTACT = 1u << 14;

__device__ __forceinline__ uint64_t optical_gap(
    int64_t left_lower,
    int64_t left_upper,
    int64_t right_lower,
    int64_t right_upper)
{
    if (left_upper < right_lower) {
        return (uint64_t)(right_lower - left_upper);
    }
    if (right_upper < left_lower) {
        return (uint64_t)(left_lower - right_upper);
    }
    return 0ULL;
}

__device__ __forceinline__ uint32_t optical_directed(
    uint32_t from,
    uint32_t left,
    uint32_t relation)
{
    return from == left ? relation : (relation << 16);
}

/// Classify the complete local optical-role word while the exact contact population remains on
/// the card. Scale apertures are order statistics read from the presented glyph/subfigure body;
/// the kernel owns no authored capacity or font constant.


/// Select the non-dominated situated-difference front incident to one addressed participant port.
/// `deed` is a typed receiver coordinate: 0 describes every outgoing fibre, 1 identifies through
/// copular fibres, and 2 infers through modal or genuinely returned fibres.  The partial order is
/// the product of addressed landmark support, retained occurrence mass, and chronology.  No word,
/// query, scalar score, top-k extent, or authored answer length enters this law.  Incomparable and
/// equal terminal sections remain plural in the returned reconstruction fibre.


/// Contract every arriving exact factor-current section with every cultivated affine cell.  One
/// lane owns one `(cell, context)` occurrence, so the complete overlap holon returns without an
/// atomic reduction, scalar score, or host-selected factor aperture.


__device__ __forceinline__ int compare_unsigned_sections(
    const uint32_t *left,
    const uint32_t *right,
    uint32_t limb_count)
{
    for (uint32_t reverse = limb_count; reverse > 0U; --reverse) {
        const uint32_t limb = reverse - 1U;
        if (left[limb] < right[limb]) return -1;
        if (left[limb] > right[limb]) return 1;
    }
    return 0;
}

/// Differentiate a plural projective current by removing the exact factorwise meet carried by
/// every alternative context.  The common section and every residual remain explicit; this is an
/// oriented current difference, not normalization, thresholding, or semantic feature selection.


__device__ __forceinline__ uint32_t scaled_unsigned_limb(
    const uint32_t *section,
    uint32_t limb_count,
    uint64_t scale,
    uint32_t requested_limb)
{
    unsigned __int128 carry = 0U;
    for (uint32_t limb = 0U; limb < limb_count; ++limb) {
        const unsigned __int128 total =
            (unsigned __int128)section[limb] * (unsigned __int128)scale + carry;
        if (limb == requested_limb) return (uint32_t)total;
        carry = total >> 32U;
    }
    for (uint32_t limb = limb_count; limb < limb_count + 2U; ++limb) {
        const uint32_t digit = (uint32_t)carry;
        if (limb == requested_limb) return digit;
        carry >>= 32U;
    }
    return 0U;
}

/// Compare `left / left_mass` with `right / right_mass` without a floating-point chart.
__device__ __forceinline__ int compare_barycentric_sections(
    const uint32_t *left,
    uint64_t left_mass,
    const uint32_t *right,
    uint64_t right_mass,
    uint32_t limb_count)
{
    for (uint32_t reverse = limb_count + 2U; reverse > 0U; --reverse) {
        const uint32_t limb = reverse - 1U;
        const uint32_t left_cross =
            scaled_unsigned_limb(left, limb_count, right_mass, limb);
        const uint32_t right_cross =
            scaled_unsigned_limb(right, limb_count, left_mass, limb);
        if (left_cross < right_cross) return -1;
        if (left_cross > right_cross) return 1;
    }
    return 0;
}

/// Return the complete non-dominated cell front under the arriving overlap section and the
/// exact barycentric capacity of each cultivated cell. `participant_only` is a receiver aperture
/// over already cultivated incidence; it does not alter current, morphology, or comparison.




/// Transport one situated material section through every cultivated affine cell.  Offsets and
/// multiplicities are the complete barycentric support population mounted with the rest.  Each
/// lane owns one cell, retains all of its landmark mass, and returns the augmented section beside
/// an exact reconstruction flag.  No cell is selected and no compatibility scalar is formed.


// The membrane word below is deliberately factored into three launches on one CUDA stream.
// `conduct_membrane_local_contacts` writes exact family currents; `gather_membrane_radiation`
// consumes those device buffers; `inject_membrane_boundary_current` consumes the gathered current.
// There is no host read or synchronization between them.  The split exposes two real dependency
// edges while allowing every population extent and limb extent to remain material-derived.

__device__ __forceinline__ uint8_t product_sign(uint8_t left, uint8_t right)
{
    if (left == 0U || right == 0U) return 0U;
    return left == right ? 1U : 2U;
}

__device__ __forceinline__ uint8_t opposite_sign(uint8_t sign)
{
    return sign == 1U ? 2U : (sign == 2U ? 1U : 0U);
}

__device__ void scale_unsigned_limbs(
    const uint32_t *source,
    uint32_t source_limbs,
    uint64_t scale,
    uint32_t *target,
    uint32_t target_limbs)
{
    for (uint32_t limb = 0U; limb < target_limbs; ++limb) target[limb] = 0U;
    unsigned __int128 carry = 0U;
    for (uint32_t limb = 0U; limb < source_limbs; ++limb) {
        const unsigned __int128 product =
            (unsigned __int128)source[limb] * (unsigned __int128)scale + carry;
        target[limb] = (uint32_t)product;
        carry = product >> 32U;
    }
    uint32_t at = source_limbs;
    while (carry != 0U && at < target_limbs) {
        target[at] = (uint32_t)carry;
        carry >>= 32U;
        ++at;
    }
}

__device__ void zero_unsigned_limbs(uint32_t *target, uint32_t limbs);
__device__ bool unsigned_limbs_are_zero(const uint32_t *value, uint32_t limbs);
__device__ void multiply_unsigned_limbs(
    const uint32_t *left, uint32_t left_limbs,
    const uint32_t *right, uint32_t right_limbs,
    uint32_t *target, uint32_t target_limbs);
__device__ void add_unsigned_limbs(
    uint32_t *accumulator, const uint32_t *term, uint32_t limbs);

/// Restrict two addressed affine cochains to their shared factor support, apply the exact
/// capacity/orientation form of every constitutive cell, and transport each existing complex
/// family return through the resulting local overlap.  Cell indices are receiver coordinates;
/// factors, capacities, orientations, multiplicities, and family currents were all mounted with
/// the singular rest.


/// Carry one complete positive factor-current section through the sparse source-neutral
/// relational incidence.  The two coordinates are the exact quotient of the three retained
/// chronological populations by common phase translation:
/// `(emanation - ingress, return - ingress)`.  Every constitutive family remains addressed.


__device__ __forceinline__ int64_t signed_family_phase(uint8_t sign)
{
    return sign == 1U ? 1LL : (sign == 2U ? -1LL : 0LL);
}

__device__ __forceinline__ void atomic_add_signed_i64(int64_t *target, int64_t value)
{
    atomicAdd((unsigned long long *)target, (unsigned long long)value);
}

/// Apply the phase face of each already-mounted constitutive family and return through the exact
/// transpose incidence.  One launch spans sparse-term/family occurrences; signed atomic addition
/// is exact modulo 2^64 under the host-proved strict i64 bound.


__device__ __forceinline__ uint64_t magnitude_i64(int64_t value)
{
    return value < 0 ? (uint64_t)(-(value + 1LL)) + 1ULL : (uint64_t)value;
}

__device__ void add_unsigned_limbs_checked(
    uint32_t *accumulator,
    const uint32_t *term,
    uint32_t accumulator_limbs,
    uint32_t term_limbs,
    uint32_t *overflow)
{
    uint64_t carry = 0ULL;
    for (uint32_t limb = 0U; limb < accumulator_limbs; ++limb) {
        const uint32_t addend = limb < term_limbs ? term[limb] : 0U;
        const uint64_t sum =
            (uint64_t)accumulator[limb] + (uint64_t)addend + carry;
        accumulator[limb] = (uint32_t)sum;
        carry = sum >> 32U;
    }
    if (carry != 0ULL) atomicExch(overflow, 1U);
}



/// Exact signed-magnitude generator transport for the relational current. One lane owns one
/// `(generator,target-factor)` coordinate and accumulates every source preimage into a limb
/// carrier. The generator map is the only cross-factor passage; state and generator addresses
/// remain explicit and no host representative is selected.



__device__ __forceinline__ uint8_t signed_i64_magnitude_sign(int64_t value);

/// Carry the arbitrary-width causal-adjoint current through the same HNN target junction as the
/// positive factor current.  One lane owns one `(target site, factor)` and reduces its complete
/// addressed local-current fibre in occurrence order.  The selected-slot population remains in
/// the inverse-incidence reconstruction chart; it is never materialized as a second hot
/// `[selected slot][factor]` state field.


__device__ __forceinline__ uint8_t signed_i64_magnitude_sign(int64_t value)
{
    return value < 0 ? 2U : (value > 0 ? 1U : 0U);
}

/// Widen the bounded bootstrap return into the resident signed-magnitude carrier. This is a
/// representation change only; signs and exact magnitudes are preserved without a host roundtrip.



/// Form the same addressed Hermitian boundary receiver from the productive arbitrary-width
/// relational current.  The current may occupy several addressed source states after a returned
/// passage.  A face therefore joins it only through exact state identity before the generator,
/// restriction, and quadratic current are contracted in the common target fibre.




__device__ void multiply_unsigned_limbs_in_place(
    uint32_t *value, uint32_t value_limbs,
    const uint32_t *scale, uint32_t scale_limbs,
    uint32_t *scratch)
{
    multiply_unsigned_limbs(
        value, value_limbs, scale, scale_limbs, scratch, value_limbs);
    for (uint32_t limb = 0U; limb < value_limbs; ++limb) value[limb] = scratch[limb];
}

/// The outward radiation section is the exact sum of every family current written by the prior
/// launch.  One lane owns this small constitutive population; no atomic order or scalar winner can
/// change the returned integer.


__device__ void scale_and_accumulate(
    uint8_t *accumulator_sign,
    uint32_t *accumulator,
    uint8_t source_sign,
    const uint32_t *source,
    uint32_t source_limbs,
    uint8_t scalar_sign,
    uint64_t scalar,
    bool reverse,
    uint32_t *scratch,
    uint32_t target_limbs)
{
    uint8_t sign = product_sign(source_sign, scalar_sign);
    if (reverse) sign = opposite_sign(sign);
    scale_unsigned_limbs(source, source_limbs, scalar, scratch, target_limbs);
    add_signed_magnitude(accumulator_sign, accumulator, sign, scratch, target_limbs);
}

/// Multiply the gathered native radiation by one exact complex boundary current.  This is the
/// final device-side dependency: the exterior current does not select a family or topology; it
/// acts on the plural native section already returned by the interior.


/// Conduct every support of one oriented boundary section in one launch.  Each support pairs the
/// boundary receiver reflected into the native factor chart against the complete signed action
/// difference `U_i J - J`. This is the finite integration-by-reflection pairing. Supports are
/// already grouped by addressed exterior port; no lane chooses or ranks a port.


/// Form one exact weighted second-moment field for every addressed exterior port directly from
/// the sparse native-current and boundary-restriction axes.  The tensor-product support family is
/// the reconstruction fibre of this contraction; it is never materialized as hot state.


__device__ int64_t find_sparse_factor(
    const uint32_t *factors, uint64_t begin, uint64_t end, uint32_t target)
{
    while (begin < end) {
        const uint64_t middle = begin + (end - begin) / 2ULL;
        const uint32_t held = factors[middle];
        if (held < target) begin = middle + 1ULL;
        else if (target < held) end = middle;
        else return (int64_t)middle;
    }
    return -1LL;
}

/// Pull the boundary restrictions named by one later current from the total resident restriction
/// atlas.  The rectangular `(local port, boundary state)` apparatus chart is deliberately allowed
/// to contain absent pairs: those pairs return the exact zero section and therefore contribute no
/// quadratic current.  No host reconstruction of transition factor sections occurs between
/// resident words.


/// Contract one exact primitive integral receiver-form frame against a weighted rank-one current
/// family.  Each lane owns one complete form and accumulates its signed result locally; forms are
/// independent and no semantic phase or host pivot enters the word.


/// Apply one exact addressed integral factor per output coordinate.  This is used both by a
/// descended generator and by a present receiver projection.  `0xffffffff` with zero scale is the
/// exact zero form; every other address is a resident coordinate.


__device__ int compare_widened_magnitude(
    const uint32_t *left,
    uint32_t left_limbs,
    const uint32_t *right,
    uint32_t right_limbs)
{
    const uint32_t limbs = left_limbs > right_limbs ? left_limbs : right_limbs;
    for (uint32_t reverse = limbs; reverse > 0U; --reverse) {
        const uint32_t at = reverse - 1U;
        const uint32_t left_value = at < left_limbs ? left[at] : 0U;
        const uint32_t right_value = at < right_limbs ? right[at] : 0U;
        if (left_value < right_value) return -1;
        if (left_value > right_value) return 1;
    }
    return 0;
}

/// Add one signed-magnitude value into a wider private accumulator.  The target extent is derived
/// by the host from the maximal exact preimage population; leaving that extent would therefore be
/// an apparatus bug rather than a saturating arithmetic case.
__device__ void add_widened_signed_magnitude(
    uint8_t *target_sign,
    uint32_t *target,
    uint32_t target_limbs,
    uint8_t source_sign,
    const uint32_t *source,
    uint32_t source_limbs,
    uint32_t *overflow)
{
    if (source_sign == 0U || unsigned_limbs_are_zero(source, source_limbs)) return;
    if (*target_sign == 0U || unsigned_limbs_are_zero(target, target_limbs)) {
        zero_unsigned_limbs(target, target_limbs);
        for (uint32_t limb = 0U; limb < source_limbs; ++limb) target[limb] = source[limb];
        *target_sign = source_sign;
        return;
    }
    if (*target_sign == source_sign) {
        uint64_t carry = 0ULL;
        uint32_t limb = 0U;
        for (; limb < source_limbs; ++limb) {
            const uint64_t sum = (uint64_t)target[limb] + (uint64_t)source[limb] + carry;
            target[limb] = (uint32_t)sum;
            carry = sum >> 32U;
        }
        while (carry != 0ULL && limb < target_limbs) {
            const uint64_t sum = (uint64_t)target[limb] + carry;
            target[limb] = (uint32_t)sum;
            carry = sum >> 32U;
            ++limb;
        }
        if (carry != 0ULL) atomicExch(overflow, 1U);
        return;
    }
    const int order = compare_widened_magnitude(target, target_limbs, source, source_limbs);
    if (order == 0) {
        zero_unsigned_limbs(target, target_limbs);
        *target_sign = 0U;
        return;
    }
    if (order > 0) {
        uint64_t borrow = 0ULL;
        for (uint32_t limb = 0U; limb < target_limbs; ++limb) {
            const uint64_t subtrahend =
                (limb < source_limbs ? (uint64_t)source[limb] : 0ULL) + borrow;
            const uint64_t held = (uint64_t)target[limb];
            target[limb] = (uint32_t)(held - subtrahend);
            borrow = held < subtrahend ? 1ULL : 0ULL;
        }
        if (borrow != 0ULL) atomicExch(overflow, 1U);
        return;
    }
    uint64_t borrow = 0ULL;
    for (uint32_t limb = 0U; limb < target_limbs; ++limb) {
        const uint64_t minuend = limb < source_limbs ? (uint64_t)source[limb] : 0ULL;
        const uint64_t subtrahend = (uint64_t)target[limb] + borrow;
        target[limb] = (uint32_t)(minuend - subtrahend);
        borrow = minuend < subtrahend ? 1ULL : 0ULL;
    }
    if (borrow != 0ULL) atomicExch(overflow, 1U);
    *target_sign = source_sign;
}

/// Carry the integral incidence leg of one resident factored moment through every addressed
/// generator. One lane owns one `(generator, source-image)` row, so non-injective factor maps and
/// signed cancellation remain private exact arithmetic. The row order itself is the complete
/// generator/source-image occurrence map.


/// Identify the first exactly equal rooted history block.  One block is the complete ordered
/// `(root-coordinate, factor)` incidence section; equality of a digest or endpoint is never used.


/// Compact the exact history quotient and sum the complete ordered-history multiplicity fibre.
/// Candidate order is `(generator, source-history)`; `candidate_to_target` retains that joining
/// map while only one equal incidence block remains productive.
