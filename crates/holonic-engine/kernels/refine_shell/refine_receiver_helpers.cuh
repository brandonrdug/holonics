// Shared membrane arithmetic and receiver helpers continued from refine_shared.cuh.

__device__ uint32_t signed_limbs_mod_word(
    uint8_t sign,
    const uint32_t *limbs,
    uint32_t limb_count,
    uint32_t prime)
{
    uint64_t residue = 0ULL;
    for (uint32_t held = limb_count; held > 0U; --held) {
        residue = ((residue << 32U) + (uint64_t)limbs[held - 1U]) % (uint64_t)prime;
    }
    if (sign == 2U && residue != 0ULL) residue = (uint64_t)prime - residue;
    return (uint32_t)residue;
}

__device__ uint32_t word_modular_power(uint32_t base, uint32_t exponent, uint32_t prime)
{
    uint64_t result = 1ULL;
    uint64_t power = (uint64_t)base;
    while (exponent != 0U) {
        if ((exponent & 1U) != 0U) result = (result * power) % (uint64_t)prime;
        power = (power * power) % (uint64_t)prime;
        exponent >>= 1U;
    }
    return (uint32_t)result;
}

/// Each lane is one exact finite receiver chart. It reduces the complete integral transported
/// frame modulo its prime and performs its own row elimination. No chart can promote rank: a
/// returned pivot is nonzero modulo its prime and therefore nonzero over the entering integers.


/// Rejoin the independent finite charts without host inspection. The first chart attaining the
/// maximal rank supplies an exact nonzero minor and its complete addressed row/column witnesses.


/// For the exact minor selected by the rank founder, each finite chart independently returns the
/// determinant D, joining numerator J = D M, and pulled constitutive numerator J^T N J. Charts
/// dividing D remain exact bad-prime testimony and are excluded only from reconstruction.


__device__ uint32_t unsigned_limbs_mod_word(
    const uint32_t *limbs,
    uint32_t limb_count,
    uint32_t prime)
{
    uint64_t residue = 0ULL;
    for (uint32_t held = limb_count; held > 0U; --held) {
        residue = ((residue << 32U) + limbs[held - 1U]) % (uint64_t)prime;
    }
    return (uint32_t)residue;
}

/// Prepare one good finite chart against the current reconstruction product. The prefix remains
/// resident and is reused for every reconstructed value before the product advances.


/// Fold one chart's complete residue section into the resident mixed-radix reconstruction. The
/// chart aperture is reused by the next prime; no chart-by-value residue tensor survives.


/// Advance the shared product only after every value has consumed the prepared prefix.


/// Close the sufficient good-prime fibre and found its centered receiver boundary.


/// Center the completed unsigned reconstruction into exact signed magnitude on the card.


/// Reduce each source-square entry into every reconstruction chart exactly once.  The following
/// square cells reuse these residues instead of rescanning an arbitrary-width source row once per
/// selected image coordinate.


/// Verify the two reconstructed integer squares as independent chart/cell occurrences. Since the
/// complete chart product exceeds twice the derived difference bound, agreement in every chart is
/// exact integer agreement rather than a probabilistic fingerprint.


/// Materialize the admitted target image only after every exact chart square has closed. The
/// source remains immutable standing while this staged delta is pending; `admitted` is the single
/// device-owned atomic boundary consumed by the resident receiver passage.


/// Contract every already-mounted primitive integral receiver directly against the device-
/// admitted factored image `B^T H B`. One lane owns one complete sparse form; the ambient factor
/// square is never materialized and the common target denominator remains a separate quantity
/// line for the terminal receiver.


/// Pull every addressed sparse functional through the admitted image incidence.  One lane owns
/// one `(functional, image-row)` occurrence and accumulates its complete exact reading.  The
/// functional pool is shared by receiver terms; no outer-product or ambient factor square is
/// formed.


/// Measure only the resident storage aperture of the admitted constitutive numerator.  The return
/// is a word count for allocation geometry, not a receiver value: no coefficient, sign, address,
/// or semantic branch leaves the card.  Trailing zero capacity therefore does not propagate into
/// every later functional occurrence.


/// Apply the admitted constitutive form to every projected functional before receiver terms meet.
/// One lane owns one `(functional, output-axis)` occurrence.  This is the shared metric-dual leg:
/// repeated receiver terms reuse it without repeating a complete rank-square contraction.


/// Contract each already-founded primitive functional pair exactly once.  The pair coordinate is
/// shared by every sparse receiver incidence which names it; later boundary projection scales that
/// coordinate without repeating this constitutive contraction.


/// Pull a primitive pair coordinate through one sparse addressed receiver factor.  One lane owns
/// one factor occurrence in the current boundary window; its coefficient and pair address retain
/// the complete receiver incidence without reopening either functional leg.


/// Return the complete term occurrences through their addressed receiver incidence.  One lane
/// owns one receiver fibre and adds only the contiguous terms named by its two boundary offsets.


/// Push one exact symmetric quadratic current through the fixed generator-closed pair complex.
/// One lane owns one target pair and reduces its complete inverse incidence, so arbitrary-width
/// carries never race. `multiplicity` is the derived ordered-pair collapse witness (one or two),
/// not a learned or caller-selected scale.


/// Found one exact accumulated quadratic current from an ordered diagonal chronology without
/// enumerating the live suffix family. One lane owns one symmetric pair for the complete
/// chronology, so arbitrary-width carries never race and chronology order is retained exactly.
/// For pair `(i,j)` and diagonal crossing `d_t`, the enacted recurrence is
///
///     standing_t = d_t(i)d_t(j)(standing_(t-1) + 1)
///     accumulated_t = accumulated_(t-1) + standing_t.
///
/// `overflow` is an apparatus obstruction only: the host derives the limb aperture from the
/// complete chronology before launch, and a nonzero return disproves that aperture derivation.


/// Push one exact symmetric current through every generator without identifying the branches.
/// The output carrier is `[generator][target_pair]`; its generator coordinate is native lineage
/// and remains present until a later returned face explicitly descends it.


/// Resolve the situated returned boundary front without bringing it through the host.  A unique
/// local port is the only front which can condition a successor current; plural and empty fronts
/// remain terminal/obstructed receiver fibres and are recorded by `selection[1]`.


/// Pull the exterior port phase front back to the addressed `(port,generator)` carrier without
/// identifying generator incidence.  This is a device-local chart passage, not a new selector.


/// Return the unique exterior membrane interaction into the hot quadratic current.  If `r` is
/// the exact factor restriction of the returned local port, every pair coefficient is carried as
///
///     C_next[i,j] = r[i] C_transported[i,j] r[j].
///
/// The unconditioned transported current remains alive for all boundary receivers queued before
/// this launch.  One lane owns one pair, so arbitrary-width products never race.  A plural front
/// is copied unchanged only so the terminal receipt can complete ownership safely; it is never
/// admitted as later continuation by the host law.


/// Descend the complete returned `(port,generator)` front into one continuing pair current.
/// Every selected branch contributes `D_p C_g D_p`; plural faces are summed at this declared
/// dynamic condensation instead of being discarded or resolved by a host-selected winner.


/// Contract the exact resident pair-current through one receiver-local sparse term section.
/// The frame was descended from the complete addressed functional-pair occurrence before device
/// ingress. One block owns one receiver; its lanes traverse disjoint term subsequences and then
/// close an exact signed reduction tree in shared memory. Thus a rich situated receiver cannot
/// collapse back into the former one-lane serial funnel.


/// Form bounded partial sums for the complete ingress-moment receiver directly on the fixed
/// symmetric pair carrier.  Off-diagonal coordinates occur twice in the ambient contraction;
/// diagonal coordinates occur once.  Every lane owns one `(port, pair-chunk)` accumulator and
/// therefore races with no other lane.


/// Reduce one nonnegative arbitrary-precision section independently inside every addressed port.
/// Repeated application with `input_count_per_port -> ceil(input/chunk)` closes a deterministic
/// device-local reduction tree without scalar atomics or host-visible partials.




__device__ int64_t find_membrane_sparse_quadratic_pair(
    const uint64_t *pair_row_offsets,
    const uint32_t *pair_factors,
    uint32_t left,
    uint32_t right)
{
    if (right < left) {
        const uint32_t held = left;
        left = right;
        right = held;
    }
    uint64_t begin = pair_row_offsets[left];
    uint64_t end = pair_row_offsets[(uint64_t)left + 1ULL];
    while (begin < end) {
        const uint64_t middle = begin + (end - begin) / 2ULL;
        const uint32_t held = pair_factors[middle * 2ULL + 1ULL];
        if (held < right) begin = middle + 1ULL;
        else if (right < held) end = middle;
        else return (int64_t)middle;
    }
    return -1LL;
}

/// Contract the reflected and action-family faces directly on the fixed upper-pair carrier.
/// One lane owns one bounded source-factor chunk of one `(port, family)` section.  The exact
/// identity is the expansion already carried by the addressed receiver complex:
///
/// `R_f = |G| sum_i cap_i eps_fi p_i^2 M_ii`
///
/// `A_f = -R_f + sum_g sum_i cap_gi eps_f,gi p_i p_gi M_i,gi`.
///
/// Pair lookup uses the generator-closed resident carrier.  Missing pairs are exact zero faces;
/// no ambient factor square or host-authored term population is constructed.


__device__ __forceinline__ int32_t membrane_receiver_class_delta(
    uint32_t left_source,
    uint32_t right_source,
    uint32_t left_target,
    uint32_t right_target,
    bool diagonal,
    bool norm)
{
    if (diagonal) {
        if (norm) return left_source == left_target ? 0 : 2;
        return left_source == left_target ? 0 : -1;
    }
    if (!norm) {
        return (left_source == right_target ? 1 : 0)
            + (right_source == left_target ? 1 : 0)
            - (left_source == right_source ? 2 : 0);
    }
    const int32_t dot = (left_target == right_target ? 1 : 0)
        - (left_target == right_source ? 1 : 0)
        - (left_source == right_target ? 1 : 0)
        + (left_source == right_source ? 1 : 0);
    return 2 * dot;
}

/// Form every opaque overlap/norm receiver before the exterior phase quotient.  The shared
/// conditioned term is `M_ij p_i p_j`; receiver-class deltas distribute it into the exact
/// four-category membrane complex.  The more expensive situated projective section is founded
/// only after this receiver has returned its admitted addressed faces.


/// Form the exact situated projective coordinates only on the addressed native phase front:
///
///   A_(p,g) = <D_p T_g C T_g^T D_p, C>,
///   B_(p,g) = ||D_p T_g C T_g^T D_p||^2,
///   C_(p,g) = ||D_p C D_p||^2.
///
/// A rejected face lies outside this situated receiver aperture: its three partial sections
/// remain exact zero and no carrier coordinate is inspected. It is not identified with zero or
/// quotiented from the native phase body. Port and generator remain separate axes.


/// Return the three reduced coordinates from their addressed section order into the persistent
/// native boundary face.  Norms are unsigned by construction; a non-positive norm is an explicit
/// downstream insufficiency rather than a hidden sign convention.


static constexpr uint32_t MEMBRANE_INTERVAL_PREFIX_LIMBS = 8U;
static constexpr uint32_t MEMBRANE_INTERVAL_CORE_LIMBS = 24U;

__device__ uint32_t membrane_significant_limb_count(
    const uint32_t *value, uint32_t limbs)
{
    while (limbs > 0U && value[limbs - 1U] == 0U) --limbs;
    return limbs;
}

__device__ void membrane_prefix_interval(
    const uint32_t *value,
    uint32_t limbs,
    uint32_t *lower,
    uint32_t *upper,
    uint32_t *exponent)
{
    zero_unsigned_limbs(lower, MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U);
    zero_unsigned_limbs(upper, MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U);
    const uint32_t significant = membrane_significant_limb_count(value, limbs);
    const uint32_t retained = significant < MEMBRANE_INTERVAL_PREFIX_LIMBS
        ? significant : MEMBRANE_INTERVAL_PREFIX_LIMBS;
    *exponent = significant > retained ? significant - retained : 0U;
    for (uint32_t limb = 0U; limb < retained; ++limb) {
        lower[limb] = value[*exponent + limb];
        upper[limb] = lower[limb];
    }
    if (*exponent == 0U) return;
    uint64_t carry = 1ULL;
    for (uint32_t limb = 0U;
         limb < MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U && carry != 0ULL;
         ++limb) {
        const uint64_t sum = (uint64_t)upper[limb] + carry;
        upper[limb] = (uint32_t)sum;
        carry = sum >> 32U;
    }
}

__device__ bool membrane_add_shifted_interval_core(
    uint32_t *target,
    uint32_t target_limbs,
    const uint32_t *core,
    uint32_t core_limbs,
    uint32_t exponent,
    uint32_t receiver_exponent,
    bool round_up)
{
    const uint32_t drop = receiver_exponent > exponent
        ? receiver_exponent - exponent : 0U;
    const uint32_t shift = exponent > receiver_exponent
        ? exponent - receiver_exponent : 0U;
    bool discarded = false;
    const uint32_t discarded_end = drop < core_limbs ? drop : core_limbs;
    for (uint32_t limb = 0U; limb < discarded_end; ++limb) {
        discarded = discarded || core[limb] != 0U;
    }
    uint64_t carry = 0ULL;
    for (uint32_t limb = drop; limb < core_limbs; ++limb) {
        const uint32_t target_at = shift + limb - drop;
        if (target_at >= target_limbs) {
            if (core[limb] != 0U || carry != 0ULL) return false;
            continue;
        }
        const uint64_t sum =
            (uint64_t)target[target_at] + (uint64_t)core[limb] + carry;
        target[target_at] = (uint32_t)sum;
        carry = sum >> 32U;
    }
    uint32_t target_at = shift + (core_limbs > drop ? core_limbs - drop : 0U);
    while (carry != 0ULL && target_at < target_limbs) {
        const uint64_t sum = (uint64_t)target[target_at] + carry;
        target[target_at] = (uint32_t)sum;
        carry = sum >> 32U;
        ++target_at;
    }
    if (carry != 0ULL) return false;
    if (round_up && discarded) {
        carry = 1ULL;
        target_at = 0U;
        while (carry != 0ULL && target_at < target_limbs) {
            const uint64_t sum = (uint64_t)target[target_at] + carry;
            target[target_at] = (uint32_t)sum;
            carry = sum >> 32U;
            ++target_at;
        }
        if (carry != 0ULL) return false;
    }
    return true;
}

__device__ void membrane_scale_square(
    uint32_t left_restriction,
    uint32_t right_restriction,
    bool diagonal,
    uint32_t *scale)
{
    const uint64_t product =
        (uint64_t)left_restriction * (uint64_t)right_restriction;
    const uint32_t product_limbs[2] = {
        (uint32_t)product,
        (uint32_t)(product >> 32U),
    };
    multiply_unsigned_limbs(product_limbs, 2U, product_limbs, 2U, scale, 5U);
    if (!diagonal) {
        uint64_t carry = 0ULL;
        for (uint32_t limb = 0U; limb < 5U; ++limb) {
            const uint64_t doubled = ((uint64_t)scale[limb] << 1U) + carry;
            scale[limb] = (uint32_t)doubled;
            carry = doubled >> 32U;
        }
    }
}

__device__ void membrane_scale_linear(
    uint32_t left_restriction,
    uint32_t right_restriction,
    bool diagonal,
    uint32_t *scale)
{
    zero_unsigned_limbs(scale, 5U);
    const uint64_t product =
        (uint64_t)left_restriction * (uint64_t)right_restriction;
    scale[0] = (uint32_t)product;
    scale[1] = (uint32_t)(product >> 32U);
    if (!diagonal) {
        uint64_t carry = 0ULL;
        for (uint32_t limb = 0U; limb < 5U; ++limb) {
            const uint64_t doubled = ((uint64_t)scale[limb] << 1U) + carry;
            scale[limb] = (uint32_t)doubled;
            carry = doubled >> 32U;
        }
    }
}

__device__ bool membrane_accumulate_prefix_product(
    uint32_t *lower_accumulator,
    uint32_t *upper_accumulator,
    uint32_t interval_limbs,
    uint32_t receiver_exponent,
    const uint32_t *left_lower,
    const uint32_t *left_upper,
    uint32_t left_exponent,
    const uint32_t *right_lower,
    const uint32_t *right_upper,
    uint32_t right_exponent,
    const uint32_t *scale)
{
    uint32_t product[MEMBRANE_INTERVAL_PREFIX_LIMBS * 2U + 2U];
    uint32_t core[MEMBRANE_INTERVAL_CORE_LIMBS];
    multiply_unsigned_limbs(
        left_lower, MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U,
        right_lower, MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U,
        product, MEMBRANE_INTERVAL_PREFIX_LIMBS * 2U + 2U);
    multiply_unsigned_limbs(
        product, MEMBRANE_INTERVAL_PREFIX_LIMBS * 2U + 2U,
        scale, 5U, core, MEMBRANE_INTERVAL_CORE_LIMBS);
    if (!membrane_add_shifted_interval_core(
            lower_accumulator, interval_limbs,
            core, MEMBRANE_INTERVAL_CORE_LIMBS,
            left_exponent + right_exponent, receiver_exponent, false)) return false;
    multiply_unsigned_limbs(
        left_upper, MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U,
        right_upper, MEMBRANE_INTERVAL_PREFIX_LIMBS + 1U,
        product, MEMBRANE_INTERVAL_PREFIX_LIMBS * 2U + 2U);
    multiply_unsigned_limbs(
        product, MEMBRANE_INTERVAL_PREFIX_LIMBS * 2U + 2U,
        scale, 5U, core, MEMBRANE_INTERVAL_CORE_LIMBS);
    return membrane_add_shifted_interval_core(
        upper_accumulator, interval_limbs,
        core, MEMBRANE_INTERVAL_CORE_LIMBS,
        left_exponent + right_exponent, receiver_exponent, true);
}

/// Return rigorous fixed-prefix enclosures for all three projective coordinates on the complete
/// native phase front.  Each coefficient prefix is an exact base-2^32 interval; discarded limbs
/// widen the upper section and therefore cannot remove a true maximizer.






/// Return the interval-certified exact-work aperture.  Failure to construct any certificate is
/// represented by `obstruction != 0` and reopens the complete native phase front on the device;
/// the host neither decides nor replays that fallback.


/// A strict interval relation should leave at least one maximal face.  Keep the stated fallback
/// executable even if an arithmetic defect or future interval law violates that expectation:
/// one device thread reopens the complete native phase front and marks the certificate obstructed.


/// Reduce independent signed exact sections through a deterministic device-local tree.  Input
/// and output use `[section][chunk][limb]`; no scalar atomic, host partial, or ordering-dependent
/// floating sum enters the quotient.


/// Place the two direct receiver families into the historical operation-complex order
/// `(reflected F, action F, overlap R, norm R)`. Situated coordinates are returned only after
/// the native phase front has been founded.


/// Form the exact projective denominator `B_p C_p` for each situated pair-carrier receiver.
/// Both factors are retained independently beside this product; this kernel supplies only the
/// common comparison chart used by the already-standing projective phase comparator.


/// Carry every exact rank-one current section through every addressed generator without
/// materializing an ambient quadratic field.  One lane owns one `(context, generator)` section,
/// so collisions in a non-injective generator are accumulated in a private arbitrary-width limb
/// row and never race through an atomic scalar aperture.


/// Carry a dense rested source section through the generator into the smallest exact factor chart
/// reached by the currently admitted source support.  `successor_factor_coordinates` is the
/// complete inverse chart from native factors into that image, so no foreign ambient factor row is
/// retained merely to represent its known zero complement.


/// Retain the complete productive `(source-state,port,generator)` restriction population in
/// deterministic lexicographic order for the generator occurrence presented at this step. This
/// mask is the prior realized face's descended generator address, never the contemporary
/// observer's front. Restriction presence and the later zero-current test determine exact local
/// current support; the complete rested generator atlas remains resident beside this occurrence.


/// Realize the rank-one family `D_p T_g x_s` for every selected native higher-face restriction.
/// Transported source sections are shared across ports; one lane owns one
/// `(source section, selected slot)` row and multiplies it by the exact diagonal restriction.


/// Apply the addressed diagonal restriction in the exact successor-factor image chart.  The
/// restriction remains native-addressed; `successor_factors` is the explicit chart map which
/// retains how every compact coordinate returns to that native incidence.


/// Form the HNN junction current.  One lane owns one `(target site, factor)` and visits the
/// complete local-current fibre in causal address order.  Projective normalization and quadratic
/// observation are deliberately absent: they are later receiver faces and may not author this
/// successor.


/// Found the exact addressed fibre of every productive local current.  This is an apparatus
/// index only: target identity is complete state-address equality, and the ordered member list
/// retains every candidate address for reconstruction and deterministic reduction.


/// Push the already-committed target-site section through the retained sparse inverse incidence.
/// `selected_faces[candidate_selected_slots[c]]` supplies only the local receiver address of one
/// caused occurrence; `candidate_to_target[c]` supplies its completed target.  The target current
/// is never changed and no generator or restriction is applied here.  Repeated incidences retain
/// their exact multiplicity in the receiver image.


/// Observe one sparse inverse-incidence face of the completed HNN state.  The constitutive
/// families and opaque receiver classes contract `(Y_l, delta Y_l)` directly.  No transition
/// table, generator action, boundary restriction, or target-state replacement occurs in this
/// kernel.  Its outputs already occupy the standing radiation/phase operation-complex chart.


/// Append the oriented real face of the complete complex relational pairing after the standing
/// family/receiver phase components have been formed.  The fixed receiver chart makes
/// `Re(<X',R>)` an ordered real coordinate; its imaginary coordinate and modulus-squared
/// projective shadow remain separate reconstruction testimony.  Squaring the complex pairing here
/// would erase the pre-locking Complex-Parametron orientation before the receiver acts.


// Verify the exact dynamic quotient squares and complete reconstruction-fibre assignment carried
// by one rested receiver/history compression. All coordinates are opaque addresses; no ordering or
// magnitude is read from them. Bit 0 marks a q/U square obstruction and bit 1 a fibre obstruction.


__device__ void projective_shift_right_one(uint32_t *value, uint32_t limbs)
{
    uint32_t carry = 0U;
    for (uint32_t at = limbs; at > 0U; --at) {
        const uint32_t limb = at - 1U;
        const uint32_t next = value[limb] & 1U;
        value[limb] = (value[limb] >> 1U) | (carry << 31U);
        carry = next;
    }
}

__device__ void projective_shift_left_one(uint32_t *value, uint32_t limbs)
{
    uint32_t carry = 0U;
    for (uint32_t limb = 0U; limb < limbs; ++limb) {
        const uint64_t shifted = ((uint64_t)value[limb] << 1U) | (uint64_t)carry;
        value[limb] = (uint32_t)shifted;
        carry = (uint32_t)(shifted >> 32U);
    }
}

__device__ void projective_subtract_unsigned(
    uint32_t *left, const uint32_t *right, uint32_t limbs)
{
    uint64_t borrow = 0ULL;
    for (uint32_t limb = 0U; limb < limbs; ++limb) {
        const uint64_t subtrahend = (uint64_t)right[limb] + borrow;
        const uint64_t minuend = (uint64_t)left[limb];
        left[limb] = (uint32_t)(minuend - subtrahend);
        borrow = minuend < subtrahend;
    }
}

/// Replace `left` by the exact positive gcd of the two arbitrary-width unsigned carriers.  Both
/// arrays are occurrence-local scratch owned by one lane, so the binary Euclidean passage has no
/// cross-row atomic or ordering choice.
__device__ void projective_gcd_unsigned(
    uint32_t *left, uint32_t *right, uint32_t limbs)
{
    if (unsigned_limbs_are_zero(right, limbs)) return;
    if (unsigned_limbs_are_zero(left, limbs)) {
        for (uint32_t limb = 0U; limb < limbs; ++limb) left[limb] = right[limb];
        return;
    }
    uint32_t common_twos = 0U;
    while ((left[0] & 1U) == 0U && (right[0] & 1U) == 0U) {
        projective_shift_right_one(left, limbs);
        projective_shift_right_one(right, limbs);
        ++common_twos;
    }
    while ((left[0] & 1U) == 0U) projective_shift_right_one(left, limbs);
    do {
        while ((right[0] & 1U) == 0U) projective_shift_right_one(right, limbs);
        if (compare_magnitude(left, right, limbs) > 0) {
            for (uint32_t limb = 0U; limb < limbs; ++limb) {
                const uint32_t held = left[limb];
                left[limb] = right[limb];
                right[limb] = held;
            }
        }
        projective_subtract_unsigned(right, left, limbs);
    } while (!unsigned_limbs_are_zero(right, limbs));
    for (uint32_t shift = 0U; shift < common_twos; ++shift) {
        projective_shift_left_one(left, limbs);
    }
}

/// Divide one unsigned carrier by an admitted exact divisor, in place.  The lane reads each
/// source limb before replacing that limb with its quotient, so no second ambient row is needed.
/// The returned boolean is the exact divisibility receipt.
__device__ bool projective_divide_exact_in_place(
    uint32_t *value, const uint32_t *divisor, uint32_t *remainder, uint32_t limbs)
{
    zero_unsigned_limbs(remainder, limbs);
    for (uint32_t at = limbs; at > 0U; --at) {
        const uint32_t limb = at - 1U;
        const uint32_t source_word = value[limb];
        uint32_t quotient_word = 0U;
        for (uint32_t bit_at = 32U; bit_at > 0U; --bit_at) {
            const uint32_t bit = bit_at - 1U;
            projective_shift_left_one(remainder, limbs);
            remainder[0] |= (source_word >> bit) & 1U;
            if (compare_magnitude(remainder, divisor, limbs) >= 0) {
                projective_subtract_unsigned(remainder, divisor, limbs);
                quotient_word |= (uint32_t)1U << bit;
            }
        }
        value[limb] = quotient_word;
    }
    return unsigned_limbs_are_zero(remainder, limbs);
}



/// Return a compact exact factor image to the standing native factor chart after the quotient size
/// is known.  This is a zero-extension through an explicit addressed inclusion, not a decoder or
/// a second semantic realization.


__device__ __forceinline__ uint64_t hash_membrane_factor_current_section(
    const uint32_t *row,
    uint8_t state_present,
    uint32_t state,
    uint64_t row_limbs)
{
    // This digest chooses a probe locus only.  Contact is established below by the complete
    // state-and-current comparison, so a collision can never identify two sections.
    uint64_t hash = 1469598103934665603ULL;
    hash = (hash ^ (uint64_t)state_present) * 1099511628211ULL;
    hash = (hash ^ (uint64_t)(state_present != 0U ? state : 0U)) * 1099511628211ULL;
    for (uint64_t limb = 0ULL; limb < row_limbs; ++limb) {
        hash = (hash ^ (uint64_t)row[limb]) * 1099511628211ULL;
    }
    return hash;
}

__device__ __forceinline__ bool membrane_factor_current_sections_are_equal(
    const uint32_t *candidate_current_limbs,
    const uint8_t *candidate_state_present,
    const uint32_t *candidate_states,
    uint32_t left,
    uint32_t right,
    uint64_t row_limbs)
{
    if (candidate_state_present[left] != candidate_state_present[right]
        || (candidate_state_present[left] != 0U
            && candidate_states[left] != candidate_states[right])) return false;
    const uint32_t *left_row = candidate_current_limbs + (uint64_t)left * row_limbs;
    const uint32_t *right_row = candidate_current_limbs + (uint64_t)right * row_limbs;
    for (uint64_t limb = 0ULL; limb < row_limbs; ++limb) {
        if (left_row[limb] != right_row[limb]) return false;
    }
    return true;
}

/// Retained bounded apparatus for the older unconditioned dynamic-current gate.  UAR2 uses the
/// sparse addressed quotient below; this owner remains exact for its already-declared aperture.








__device__ void add_weighted_quadratic_term(
    const uint32_t *left,
    const uint32_t *right,
    const uint32_t *weight,
    uint8_t sign,
    uint8_t *sum_sign,
    uint32_t *sum_limbs,
    uint32_t *quadratic_scratch,
    uint32_t *term_scratch,
    uint32_t *overlap_scratch,
    uint32_t product_limb_count,
    uint32_t weight_limb_count,
    uint32_t quadratic_limb_count,
    uint32_t moment_limb_count,
    uint32_t overlap_limb_count)
{
    multiply_unsigned_limbs(
        left, product_limb_count,
        right, product_limb_count,
        quadratic_scratch, quadratic_limb_count);
    multiply_unsigned_limbs(
        quadratic_scratch, quadratic_limb_count,
        weight, weight_limb_count,
        term_scratch, moment_limb_count);
    scale_unsigned_limbs(
        term_scratch, moment_limb_count,
        1ULL, overlap_scratch, overlap_limb_count);
    add_signed_magnitude(sum_sign, sum_limbs, sign, overlap_scratch, overlap_limb_count);
}

/// Contract the same exact moment directly through its sparse rank-one presentation.  This is the
/// production chart of `M = sum w(v tensor v)`: it returns every declared contraction without
/// allocating the ambient factor-square matrix.  The full matrix remains available only to a
/// receiver which explicitly requests that richer face.


/// Sum the context-local factorized contributions and only then form the constitutive contact.
/// This is exact distributivity of contraction over the retained rank-one family; the reduction
/// is a device-side successor of the contribution front, never a host replay.


/// Contract the per-port moment fields with the complete descended generator family, oriented
/// constitutive forms, and opaque receiver faces.  These are precisely the quadratic consequences
/// consumed by the existing radiation and projective phase-front kernels.


/// Trace the complete support population through every addressed port in one lane.  Support,
/// port, and total sections are all sums of the same contact current; their equality is therefore
/// a device-side incidence receipt rather than a host reconstruction.


/// Rebase one admitted factored-image receiver occurrence into the standing boundary-contact
/// carrier.  Receiver order is the exact operation-complex order
/// `(reflected families, action families, receiver overlaps, receiver norms)`.  No source
/// rank-one family is reopened: the descended image coordinates themselves become the support
/// current consumed by the already-founded radiation/phase/balance chain.


__device__ void zero_unsigned_limbs(uint32_t *target, uint32_t limbs)
{
    for (uint32_t limb = 0U; limb < limbs; ++limb) target[limb] = 0U;
}

__device__ bool unsigned_limbs_are_zero(const uint32_t *value, uint32_t limbs)
{
    for (uint32_t limb = 0U; limb < limbs; ++limb) {
        if (value[limb] != 0U) return false;
    }
    return true;
}

__device__ void multiply_unsigned_limbs(
    const uint32_t *left, uint32_t left_limbs,
    const uint32_t *right, uint32_t right_limbs,
    uint32_t *target, uint32_t target_limbs)
{
    zero_unsigned_limbs(target, target_limbs);
    for (uint32_t left_at = 0U; left_at < left_limbs; ++left_at) {
        uint64_t carry = 0ULL;
        for (uint32_t right_at = 0U; right_at < right_limbs; ++right_at) {
            const uint32_t target_at = left_at + right_at;
            if (target_at >= target_limbs) break;
            const uint64_t product =
                (uint64_t)left[left_at] * (uint64_t)right[right_at]
                + (uint64_t)target[target_at] + carry;
            target[target_at] = (uint32_t)product;
            carry = product >> 32U;
        }
        uint32_t target_at = left_at + right_limbs;
        while (carry != 0ULL && target_at < target_limbs) {
            const uint64_t sum = (uint64_t)target[target_at] + carry;
            target[target_at] = (uint32_t)sum;
            carry = sum >> 32U;
            ++target_at;
        }
    }
}

__device__ void add_unsigned_limbs(
    uint32_t *accumulator, const uint32_t *term, uint32_t limbs)
{
    uint64_t carry = 0ULL;
    for (uint32_t limb = 0U; limb < limbs; ++limb) {
        const uint64_t sum =
            (uint64_t)accumulator[limb] + (uint64_t)term[limb] + carry;
        accumulator[limb] = (uint32_t)sum;
        carry = sum >> 32U;
    }
}

__device__ int compare_boundary_phase_component(
    uint32_t left,
    uint32_t right,
    uint32_t component,
    uint32_t component_count,
    const uint8_t *compatibility_sign,
    const uint32_t *compatibility_limbs,
    const uint32_t *norm_limbs,
    uint32_t compatibility_limb_count,
    uint32_t norm_limb_count,
    uint32_t *square_scratch,
    uint32_t square_limb_count,
    uint32_t *left_cross_scratch,
    uint32_t *right_cross_scratch,
    uint32_t cross_limb_count)
{
    const uint64_t left_component =
        (uint64_t)left * (uint64_t)component_count + component;
    const uint64_t right_component =
        (uint64_t)right * (uint64_t)component_count + component;
    const uint32_t *left_compatibility =
        compatibility_limbs + left_component * (uint64_t)compatibility_limb_count;
    const uint32_t *right_compatibility =
        compatibility_limbs + right_component * (uint64_t)compatibility_limb_count;
    const uint32_t *left_norm =
        norm_limbs + left_component * (uint64_t)norm_limb_count;
    const uint32_t *right_norm =
        norm_limbs + right_component * (uint64_t)norm_limb_count;
    const uint8_t left_class = unsigned_limbs_are_zero(left_norm, norm_limb_count)
        ? 0U : (compatibility_sign[left_component] == 2U
            ? 1U : (compatibility_sign[left_component] == 0U ? 2U : 3U));
    const uint8_t right_class = unsigned_limbs_are_zero(right_norm, norm_limb_count)
        ? 0U : (compatibility_sign[right_component] == 2U
            ? 1U : (compatibility_sign[right_component] == 0U ? 2U : 3U));
    if (left_class < right_class) return -1;
    if (left_class > right_class) return 1;
    if (left_class == 0U || left_class == 2U) return 0;

    multiply_unsigned_limbs(
        left_compatibility, compatibility_limb_count,
        left_compatibility, compatibility_limb_count,
        square_scratch, square_limb_count);
    multiply_unsigned_limbs(
        square_scratch, square_limb_count,
        right_norm, norm_limb_count,
        left_cross_scratch, cross_limb_count);
    multiply_unsigned_limbs(
        right_compatibility, compatibility_limb_count,
        right_compatibility, compatibility_limb_count,
        square_scratch, square_limb_count);
    multiply_unsigned_limbs(
        square_scratch, square_limb_count,
        left_norm, norm_limb_count,
        right_cross_scratch, cross_limb_count);
    const int comparison =
        compare_magnitude(left_cross_scratch, right_cross_scratch, cross_limb_count);
    return left_class == 1U ? -comparison : comparison;
}

/// Pull the exact state-addressed rank-one current against the transported sparse relational
/// return without materializing either ambient factor square.  One lane owns one
/// `(context,port,generator)` occurrence.  The context's addressed state selects the unique
/// source-state face into which that partial returns; the cross-state complement is the exact
/// direct-sum radical and is never materialized.  The context contributes only through the boundary
/// restriction carrying the same source state; this is the executable form of
/// `D_p (B^T K B) D_p = (D_p B)^T K (D_p B)`.


/// Return `||D_p T_g deltaX_s||^2` for every addressed
/// `(source-state,port,generator)` face.  Distinct boundary states remain distinct receiver
/// charts; no cross-state sum or comparison is manufactured.


/// Reduce context-local relational moments and append their exact projective receiver component
/// to the already-formed causal phase section.  The comparison chart is
/// `A^2 / (S R)^2`, order-equivalent to the normalized positive contraction `A/(S R)` while
/// retaining integral arithmetic and the complete unnormalized reconstruction fibre.


/// Compare the situated sparse-pair receiver in its exact projective chart.  The native phase
/// front remains the prior receiver.  Within it, each port carries the oriented compatibility
/// `A_p` and the positive self-pairing product `B_p C_p`; comparison is the division-free law
///
///     A_p^2 B_q C_q  ?  A_q^2 B_p C_p.
///
/// A radical denominator is excluded from this receiver (its diagonal pair entry marks it as
/// dominated), so an entirely radical native front returns empty/insufficient rather than a
/// fabricated zero score.  The output relation is encoded as `1 = strict challenger win`,
/// `2 = exact receiver tie`, and `0 = challenger loss/incomparability`; retaining the tie class
/// is necessary when this receiver is composed with another receiver by Pareto product.


/// Evaluate one apparatus-sized window of the complete ordered projective relation.  The global
/// pair address remains `(challenged, challenger)` in the full square, while scratch and relation
/// testimony are local to this reconstructible window.  Thus pair cells retain their exact
/// comparison law without becoming resident native state.


/// Fold a reconstructible pair window into the challenged-face dominance fibre.  Independent
/// pair cells join by idempotent OR, so window order and CUDA scheduling cannot change the front.
/// With a second receiver present this is exactly the standing Pareto product relation.




/// Compose two independent projective receiver relations into the joint Pareto relation on the
/// complete native situated phase front.  A challenger is joint-dominant exactly when it is
/// non-worse in both receivers and strictly better in at least one.  Each input relation retains
/// `1 = strict win`, `2 = exact tie`, and `0 = loss/incomparability`; the tie class is essential:
/// a strict win in one receiver combined with a loss in the other is *not* joint dominance.
///
/// The quadratic relation is intentionally retained as a separate diagnostic buffer.  This
/// kernel only composes it with the relational relation; it never reinterprets either receiver
/// as a scalar score or collapses their reconstruction fibres.


/// Receive the complete addressed potential through the product of its constitutive and receiver
/// projective axes.  For each port and family, `D` is the reflected self-pairing and `A` the
/// oriented action difference.  Every family retains `(D_f A_f, A_f^2)` as one component; every
/// opaque receiver face retains its own exact `(R_r, N_r)` component.  A port survives precisely
/// when no other port is greater on every component and strictly greater on at least one.  Thus
/// incomparable causal directions remain one plural potential complex rather than being tensor-
/// multiplied or summed into a scalar order.


/// Every ordered port comparison owns a disjoint scratch fibre. The component field is immutable,
/// so these comparisons satisfy exact interchange and may issue together without an atomic or a
/// host-authored winner.




/// Select the same exact componentwise Pareto front without retaining the rectangular comparison
/// apparatus.  One challenged face owns one scratch fibre and visits the other faces in its own
/// state chart.  The immutable component section plus this deterministic comparison law is the
/// complete reconstruction fibre for every omitted pair cell.


/// Return the exact sparse support of a complete addressed current section.  This is not a
/// receiver score or a semantic selection: a face is present exactly when at least one component
/// of its positive self-pairing is nonzero.  The absent complement remains reconstructible from
/// the face/component/limb extents and this law.


/// Select the complete receiver front before target-state direct-sum formation while excluding
/// exact restricted-current radicals.  `productive_target_norm` is not a score: it is the
/// existence witness that the addressed face carries nonzero current into its prospective target.


/// Select the exact componentwise front in the *returned target-state* chart.  Every component is
/// still formed on its addressed `(source-state,port,generator)` occurrence; this receiver merely
/// compares occurrences whose boundary restrictions land in the same successor summand.  Thus it
/// implements the order proved by `HolonicStateAddressedQuadratic`: form each source face first,
/// address its target, and only then take the target-state direct sum.  Comparing only inside the
/// source-state chart would preserve one artificial winner per predecessor state even after those
/// world-lines reconverged.


/// Pull the complete native phase-front radiation through the actually presented exterior
/// current.  For every surviving port this forms the exact signed power pairing
///
///     B_J(R_p) = Re(conj(J) R_p) = J_re R_p,re + J_im R_p,im.
///
/// The native Pareto front remains immutable beside this situated receiver quotient.  Thus the
/// exterior interaction may resolve incomparable native directions without erasing their
/// reconstruction fibre or introducing an authored component weight.


__device__ int compare_signed_receiver_pairing(
    uint8_t left_sign, const uint32_t *left,
    uint8_t right_sign, const uint32_t *right,
    uint32_t limbs)
{
    if (left_sign != right_sign) {
        const uint8_t left_class = left_sign == 2U ? 0U : (left_sign == 0U ? 1U : 2U);
        const uint8_t right_class = right_sign == 2U ? 0U : (right_sign == 0U ? 1U : 2U);
        return left_class < right_class ? -1 : 1;
    }
    if (left_sign == 0U) return 0;
    const int magnitude = compare_magnitude(left, right, limbs);
    return left_sign == 2U ? -magnitude : magnitude;
}

/// Every ordered comparison remains device-local and independent.  Only ports in the complete
/// native phase front participate; exact ties remain plural and are returned as receiver
/// insufficiency rather than broken by address order.




/// Select the exact situated maximum directly from the immutable pairing section.  Pair cells are
/// reconstructible from the addressed faces and comparison law, so retaining their full square
/// would be apparatus duplication rather than causal state.


/// Refine the complete native phase front first through the fixed-orientation real face of the
/// presented complex relational current and only then through its exterior complex-current
/// shadow.  No scalar blend is formed: the first comparison is the normalized signed
/// `Re(<X', B^dagger K B X>)` receiver, while the signed exterior power pairing separates only an
/// exact tie in that declared chart.  Imaginary phase and the modulus-squared projective shadow are
/// retained beside this front so the receiver never claims complete-state equality.


/// Apply the exterior current only after the native phase section has reconverged into its
/// addressed target-state fibres.  Source-state occurrences remain distinct reconstruction
/// members, but only occurrences landing in the same successor state are commensurable.  This is
/// a receiver comparison, not a cross-state quadratic sum.


/// Close the local current ledger on the device: `stored difference + returned = incoming`.
/// Both coordinates already occupy the supplied common denominator chart.


/// Retained: the fused material-and-law entry, kept because the separation front already conducts
/// through it and a working carrier is not withdrawn to make a point about factoring.



// -----------------------------------------------------------------------------
// State-addressed sparse-pair variants
// -----------------------------------------------------------------------------
//
// The older sparse-pair kernels deliberately have one implicit source state.  They
// cannot be used when a returned world-tube carries several source states: indexing
// only by `(generator, pair)` silently glues distinct state incidences.  The four
// kernels below keep that axis explicit.  Their rectangular addresses are:
//
//   current       [source_state][generator][pair]
//   face          [source_state][port][generator]
//   restriction   [source_state][port][generator][factor]
//   target        [target_state][pair]
//
// Every extent is supplied by the admitted material.  No state is inferred from a
// port, and no face is selected by a host callback.  `obstruction` is the sole
// device-side malformed-address return; callers must inspect it at their terminal
// synchronization.

/// Transport every source-state pair section through every generator while retaining
/// the complete `[source_state, generator, target_pair]` carrier.  Generator action
/// incidence is shared; current rows remain disjoint, so arbitrary-width addition is
/// race-free without an atomic scalar reduction.


/// Gather one restriction for every explicit source-state/port/generator face.
/// The generator axis is duplicated as a face address but does not alter the
/// state-to-port transition.  Absent transitions remain zero and are marked absent;
/// they are not identified with a valid zero-current transition.


/// Form the exact situated `(A,B,C)` sections for explicit
/// `[source_state, port, generator]` faces.  The current row is addressed by the
/// same source state and generator; a face cannot accidentally read another state's
/// current merely because it shares a port or generator coordinate.


/// Descend the selected addressed faces through the exact target-state quotient.  Equal target
/// states share one productive block, while `face_target_blocks` retains the complete inverse
/// fibre `(source state, port, generator) -> target block` for reconstruction.


/// Carry the selected addressed face family directly into its target-state direct sum. One lane
/// owns one `(target-state block, pair)` coordinate and visits the retained face fibre in causal
/// address order, so exact accumulation needs neither atomics nor an ambient face-by-pair body.


/// Carry the signed complex relational return through the identical selected-face quotient used
/// by the quadratic moment above. One lane owns one `(target-state block,factor)` coordinate and
/// joins a transported source relation only when its addressed state equals the face source
/// state. Relative phase and sign survive; the positive moment is never used as a decoder.
