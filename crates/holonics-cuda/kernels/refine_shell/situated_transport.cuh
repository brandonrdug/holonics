// Contact and situated/projective transport.
// This fragment is included by refine_shell.cu after refine_shared.cuh.

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

extern "C" __global__ void classify_optical_incidence(
    const int64_t *lower_xyz,
    const int64_t *upper_xyz,
    const uint32_t *left_vertex,
    const uint32_t *right_vertex,
    const uint8_t *contact_class,
    uint32_t *incidence_out,
    uint32_t pair_count,
    uint64_t term_gap,
    uint64_t line_gap)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= pair_count) {
        return;
    }
    if (contact_class[at] == 0u) {
        incidence_out[at] = 0u;
        return;
    }

    const uint32_t left = left_vertex[at];
    const uint32_t right = right_vertex[at];
    const uint64_t la = (uint64_t)left * 3ULL;
    const uint64_t ra = (uint64_t)right * 3ULL;
    const int64_t ll = lower_xyz[la];
    const int64_t lt = lower_xyz[la + 1ULL];
    const int64_t lr = upper_xyz[la];
    const int64_t lb = upper_xyz[la + 1ULL];
    const int64_t rl = lower_xyz[ra];
    const int64_t rt = lower_xyz[ra + 1ULL];
    const int64_t rr = upper_xyz[ra];
    const int64_t rb = upper_xyz[ra + 1ULL];

    const int64_t lw = lr - ll;
    const int64_t lh = lb - lt;
    const int64_t rw = rr - rl;
    const int64_t rh = rb - rt;
    const int64_t lcx = ll + lr;
    const int64_t lcy = lt + lb;
    const int64_t rcx = rl + rr;
    const int64_t rcy = rt + rb;
    const bool horizontal_overlap = ll < rr && rl < lr;
    const bool vertical_overlap = lt < rb && rt < lb;
    const uint64_t horizontal_gap = optical_gap(ll, lr, rl, rr);

    uint32_t word = OPTICAL_PROXIMITY | (OPTICAL_PROXIMITY << 16);
    const uint32_t earlier = lcx <= rcx ? left : right;
    const uint32_t later = earlier == left ? right : left;
    if (vertical_overlap) {
        word |= optical_directed(earlier, left,
                                 OPTICAL_BASELINE | OPTICAL_READING | OPTICAL_MATRIX_ROW);
        if (horizontal_gap <= term_gap) {
            word |= optical_directed(earlier, left, OPTICAL_TERM_CONTACT);
        }
        if (horizontal_gap <= line_gap) {
            word |= optical_directed(earlier, left, OPTICAL_LINE_CONTACT);
        }
    }
    if (horizontal_overlap) {
        const uint32_t above = lcy <= rcy ? left : right;
        const uint32_t below = above == left ? right : left;
        word |= optical_directed(above, left, OPTICAL_MATRIX_COLUMN | OPTICAL_ALIGNMENT);
        (void)below;
    }

    const int64_t earlier_height = earlier == left ? lh : rh;
    const int64_t later_height = later == left ? lh : rh;
    const int64_t earlier_y = earlier == left ? lcy : rcy;
    const int64_t later_y = later == left ? lcy : rcy;
    if (later_height < earlier_height) {
        if (later_y < earlier_y) {
            word |= optical_directed(earlier, left, OPTICAL_SUPERSCRIPT);
        } else if (later_y > earlier_y) {
            word |= optical_directed(earlier, left, OPTICAL_SUBSCRIPT);
        }
    }

    for (uint32_t orientation = 0; orientation < 2; ++orientation) {
        const uint32_t frame = orientation == 0 ? left : right;
        const uint32_t member = orientation == 0 ? right : left;
        const int64_t fw = orientation == 0 ? lw : rw;
        const int64_t fh = orientation == 0 ? lh : rh;
        const int64_t mw = orientation == 0 ? rw : lw;
        const int64_t mh = orientation == 0 ? rh : lh;
        const int64_t fcx = orientation == 0 ? lcx : rcx;
        const int64_t fcy = orientation == 0 ? lcy : rcy;
        const int64_t mcx = orientation == 0 ? rcx : lcx;
        const int64_t mcy = orientation == 0 ? rcy : lcy;
        const int64_t fl = orientation == 0 ? ll : rl;
        const int64_t ml = orientation == 0 ? rl : ll;
        if (fw > fh && horizontal_overlap) {
            word |= optical_directed(
                frame,
                left,
                mcy < fcy ? OPTICAL_FRACTION_NUMERATOR : OPTICAL_FRACTION_DENOMINATOR);
        }
        if (fh > fw && vertical_overlap) {
            word |= optical_directed(frame, left, OPTICAL_DELIMITER);
            if (fl <= ml) {
                word |= optical_directed(frame, left, OPTICAL_RADICAL);
            }
        }
        if (fw >= mw + mw || fh >= mh + mh) {
            word |= optical_directed(frame, left, OPTICAL_DIAGRAM);
        }
        (void)fcx;
        (void)mcx;
        (void)member;
    }
    incidence_out[at] = word;
}

extern "C" __global__ void select_participant_causal_front(
    const uint8_t *participant_subject,
    const uint8_t *copular,
    const uint8_t *has_modality,
    const uint8_t *has_return,
    const uint32_t *landmark_support,
    const uint64_t *occurrence_mass,
    const uint64_t *last_occurrence,
    uint8_t *selected,
    uint32_t cell_count,
    uint32_t deed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) {
        return;
    }
    const bool eligible = participant_subject[at] != 0u &&
        (deed == 0u ||
         (deed == 1u && copular[at] != 0u) ||
         (deed == 2u && (has_modality[at] != 0u || has_return[at] != 0u)));
    if (!eligible) {
        selected[at] = 0u;
        return;
    }
    const uint32_t support_at = landmark_support[at];
    const uint64_t mass_at = occurrence_mass[at];
    const uint64_t chronology_at = last_occurrence[at];
    for (uint32_t other = 0; other < cell_count; ++other) {
        if (other == at || participant_subject[other] == 0u) {
            continue;
        }
        const bool other_eligible = deed == 0u ||
            (deed == 1u && copular[other] != 0u) ||
            (deed == 2u &&
             (has_modality[other] != 0u || has_return[other] != 0u));
        const bool weakly_dominates = other_eligible &&
            landmark_support[other] >= support_at &&
            occurrence_mass[other] >= mass_at &&
            last_occurrence[other] >= chronology_at;
        const bool strictly_dominates = landmark_support[other] > support_at ||
            occurrence_mass[other] > mass_at ||
            last_occurrence[other] > chronology_at;
        if (weakly_dominates && strictly_dominates) {
            selected[at] = 0u;
            return;
        }
    }
    selected[at] = 1u;
}

extern "C" __global__ void contract_situated_current_affine_cells(
    const uint64_t *cell_offsets,
    const uint32_t *cell_factors,
    const uint64_t *cell_multiplicities,
    const uint32_t *current_limbs,
    uint32_t *overlap_limbs,
    uint32_t *overflow,
    uint32_t cell_count,
    uint32_t factor_count,
    uint32_t context_count,
    uint32_t current_limb_count,
    uint32_t overlap_limb_count)
{
    const uint64_t occurrence = (uint64_t)blockIdx.x * (uint64_t)blockDim.x + threadIdx.x;
    const uint64_t population = (uint64_t)cell_count * (uint64_t)context_count;
    if (occurrence >= population) return;
    const uint32_t cell = (uint32_t)(occurrence / context_count);
    const uint32_t context = (uint32_t)(occurrence % context_count);
    uint32_t *out = overlap_limbs + occurrence * overlap_limb_count;
    for (uint32_t limb = 0U; limb < overlap_limb_count; ++limb) out[limb] = 0U;
    for (uint64_t term = cell_offsets[cell]; term < cell_offsets[cell + 1U]; ++term) {
        const uint32_t factor = cell_factors[term];
        if (factor >= factor_count) {
            atomicExch(overflow, 1U);
            return;
        }
        const uint32_t *coefficient = current_limbs +
            ((uint64_t)context * (uint64_t)factor_count + factor) * current_limb_count;
        const uint64_t multiplicity = cell_multiplicities[term];
        unsigned __int128 carry = 0U;
        for (uint32_t limb = 0U; limb < current_limb_count; ++limb) {
            const unsigned __int128 total =
                (unsigned __int128)coefficient[limb] * (unsigned __int128)multiplicity +
                (unsigned __int128)out[limb] + carry;
            out[limb] = (uint32_t)total;
            carry = total >> 32U;
        }
        uint32_t limb = current_limb_count;
        while (carry != 0U && limb < overlap_limb_count) {
            const unsigned __int128 total = (unsigned __int128)out[limb] + carry;
            out[limb] = (uint32_t)total;
            carry = total >> 32U;
            ++limb;
        }
        if (carry != 0U) atomicExch(overflow, 1U);
    }
}

extern "C" __global__ void differentiate_situated_current_contexts(
    const uint32_t *current_limbs,
    uint32_t *common_limbs,
    uint32_t *residual_limbs,
    uint32_t factor_count,
    uint32_t context_count,
    uint32_t limb_count)
{
    const uint32_t factor = blockIdx.x * blockDim.x + threadIdx.x;
    if (factor >= factor_count) return;
    uint32_t *common = common_limbs + (uint64_t)factor * limb_count;
    const uint32_t *first = current_limbs + (uint64_t)factor * limb_count;
    if (context_count == 1U) {
        uint32_t *residual = residual_limbs + (uint64_t)factor * limb_count;
        for (uint32_t limb = 0U; limb < limb_count; ++limb) {
            common[limb] = 0U;
            residual[limb] = first[limb];
        }
        return;
    }
    for (uint32_t limb = 0U; limb < limb_count; ++limb) common[limb] = first[limb];
    for (uint32_t context = 1U; context < context_count; ++context) {
        const uint32_t *candidate = current_limbs +
            ((uint64_t)context * factor_count + factor) * limb_count;
        if (compare_unsigned_sections(candidate, common, limb_count) < 0) {
            for (uint32_t limb = 0U; limb < limb_count; ++limb) {
                common[limb] = candidate[limb];
            }
        }
    }
    for (uint32_t context = 0U; context < context_count; ++context) {
        const uint32_t *source = current_limbs +
            ((uint64_t)context * factor_count + factor) * limb_count;
        uint32_t *residual = residual_limbs +
            ((uint64_t)context * factor_count + factor) * limb_count;
        uint64_t borrow = 0U;
        for (uint32_t limb = 0U; limb < limb_count; ++limb) {
            const uint64_t minuend = source[limb];
            const uint64_t subtrahend = (uint64_t)common[limb] + borrow;
            if (minuend >= subtrahend) {
                residual[limb] = (uint32_t)(minuend - subtrahend);
                borrow = 0U;
            } else {
                residual[limb] = (uint32_t)((1ULL << 32U) + minuend - subtrahend);
                borrow = 1U;
            }
        }
    }
}

extern "C" __global__ void select_situated_current_structural_front(
    const uint8_t *participant_subject,
    const uint8_t *copular,
    const uint8_t *has_modality,
    const uint8_t *has_return,
    const uint32_t *landmark_support,
    const uint64_t *occurrence_mass,
    const uint64_t *last_occurrence,
    const uint32_t *overlap_limbs,
    uint8_t *candidate,
    uint32_t cell_count,
    uint32_t context_count,
    uint32_t overlap_limb_count,
    uint32_t participant_only,
    uint32_t deed)
{
    const uint32_t at = blockIdx.x * blockDim.x + threadIdx.x;
    if (at >= cell_count) return;
    const bool participant_eligible = participant_subject[at] != 0U &&
        (deed == 0U ||
         (deed == 1U && copular[at] != 0U) ||
         (deed == 2U && (has_modality[at] != 0U || has_return[at] != 0U)));
    const bool eligible = participant_only == 0U || participant_eligible;
    bool contacted = false;
    for (uint32_t context = 0U; context < context_count && !contacted; ++context) {
        const uint32_t *section = overlap_limbs +
            ((uint64_t)at * (uint64_t)context_count + context) * overlap_limb_count;
        for (uint32_t limb = 0U; limb < overlap_limb_count; ++limb) {
            if (section[limb] != 0U) {
                contacted = true;
                break;
            }
        }
    }
    if (!eligible || !contacted) {
        candidate[at] = 0U;
        return;
    }
    for (uint32_t other = 0U; other < cell_count; ++other) {
        if (other == at) continue;
        const bool other_participant_eligible = participant_subject[other] != 0U &&
            (deed == 0U ||
             (deed == 1U && copular[other] != 0U) ||
             (deed == 2U && (has_modality[other] != 0U || has_return[other] != 0U)));
        if (participant_only != 0U && !other_participant_eligible) continue;
        bool weakly_dominates = landmark_support[other] >= landmark_support[at] &&
            occurrence_mass[other] >= occurrence_mass[at] &&
            last_occurrence[other] >= last_occurrence[at];
        bool strictly_dominates = landmark_support[other] > landmark_support[at] ||
            occurrence_mass[other] > occurrence_mass[at] ||
            last_occurrence[other] > last_occurrence[at];
        for (uint32_t context = 0U; context < context_count && weakly_dominates; ++context) {
            const uint32_t *left = overlap_limbs +
                ((uint64_t)other * (uint64_t)context_count + context) * overlap_limb_count;
            const uint32_t *right = overlap_limbs +
                ((uint64_t)at * (uint64_t)context_count + context) * overlap_limb_count;
            const int comparison = compare_unsigned_sections(left, right, overlap_limb_count);
            weakly_dominates = comparison >= 0;
            strictly_dominates = strictly_dominates || comparison > 0;
        }
        if (weakly_dominates && strictly_dominates) {
            candidate[at] = 0U;
            return;
        }
    }
    candidate[at] = 1U;
}

extern "C" __global__ void select_situated_current_causal_front(
    const uint8_t *participant_subject,
    const uint8_t *copular,
    const uint8_t *has_modality,
    const uint8_t *has_return,
    const uint8_t *candidate,
    const uint64_t *cell_total_mass,
    const uint32_t *overlap_limbs,
    uint8_t *selected,
    uint32_t cell_count,
    uint32_t context_count,
    uint32_t overlap_limb_count,
    uint32_t participant_only,
    uint32_t deed)
{
    const uint32_t context = blockIdx.x * blockDim.x + threadIdx.x;
    if (context >= context_count) return;
    uint32_t winner = UINT32_MAX;
    for (uint32_t cell = 0U; cell < cell_count; ++cell) {
        if (candidate[cell] == 0U) continue;
        const bool participant_eligible = participant_subject[cell] != 0U &&
            (deed == 0U ||
             (deed == 1U && copular[cell] != 0U) ||
             (deed == 2U && (has_modality[cell] != 0U || has_return[cell] != 0U)));
        if (participant_only != 0U && !participant_eligible) continue;
        const uint32_t *section = overlap_limbs +
            ((uint64_t)cell * (uint64_t)context_count + context) * overlap_limb_count;
        bool contacted = false;
        for (uint32_t limb = 0U; limb < overlap_limb_count; ++limb) {
            if (section[limb] != 0U) {
                contacted = true;
                break;
            }
        }
        if (!contacted) continue;
        if (winner == UINT32_MAX) {
            winner = cell;
            continue;
        }
        const uint32_t *standing = overlap_limbs +
            ((uint64_t)winner * (uint64_t)context_count + context) * overlap_limb_count;
        if (compare_barycentric_sections(
                section,
                cell_total_mass[cell],
                standing,
                cell_total_mass[winner],
                overlap_limb_count) > 0) {
            winner = cell;
        }
    }
    if (winner == UINT32_MAX) return;
    const uint32_t *maximum = overlap_limbs +
        ((uint64_t)winner * (uint64_t)context_count + context) * overlap_limb_count;
    for (uint32_t cell = 0U; cell < cell_count; ++cell) {
        if (candidate[cell] == 0U) continue;
        const bool participant_eligible = participant_subject[cell] != 0U &&
            (deed == 0U ||
             (deed == 1U && copular[cell] != 0U) ||
             (deed == 2U && (has_modality[cell] != 0U || has_return[cell] != 0U)));
        if (participant_only != 0U && !participant_eligible) continue;
        const uint32_t *section = overlap_limbs +
            ((uint64_t)cell * (uint64_t)context_count + context) * overlap_limb_count;
        if (compare_barycentric_sections(
                section,
                cell_total_mass[cell],
                maximum,
                cell_total_mass[winner],
                overlap_limb_count) == 0) {
            selected[cell] = 1U;
        }
    }
}

extern "C" __global__ void conduct_affine_barycentric_transport(
    const uint64_t *cell_offsets,
    const uint64_t *multiplicities,
    const uint64_t *cell_total_mass,
    const int64_t *entering_section,
    int64_t *augmented_numerators,
    uint8_t *exact_reconstruction,
    uint32_t cell_count,
    uint32_t rank)
{
    const uint32_t cell = blockIdx.x * blockDim.x + threadIdx.x;
    if (cell >= cell_count) {
        return;
    }
    uint64_t returned_mass = 0ULL;
    for (uint64_t at = cell_offsets[cell]; at < cell_offsets[cell + 1U]; ++at) {
        returned_mass += multiplicities[at];
    }
    const uint64_t expected_mass = cell_total_mass[cell];
    bool exact = returned_mass == expected_mass && expected_mass > 0ULL;
    for (uint32_t coordinate = 0U; coordinate < rank; ++coordinate) {
        const int64_t returned = (int64_t)returned_mass * entering_section[coordinate];
        const int64_t expected = (int64_t)expected_mass * entering_section[coordinate];
        augmented_numerators[(uint64_t)cell * (uint64_t)rank + coordinate] = returned;
        exact = exact && returned == expected;
    }
    exact_reconstruction[cell] = exact ? 1U : 0U;
}
