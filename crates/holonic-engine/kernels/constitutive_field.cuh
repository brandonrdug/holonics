// One generic multi-port constitutive field recurrence.
//
// Each node transports its incoming current through the declared unit phase and scatters it
// against the held current.  The source face
// retains both branches, `[out.re, out.im, held.re, held.im]` per node, while the target face is the
// complete incoming field in the fixed root/exterior chart.  A linked occurrence pairs the
// actual retained prior source face with the current incoming field, then reads the newly emitted
// source through that changed local relation.  This header knows no text, bytes, codec, or answer.
//
// Scratch is exactly `3 * width + 6 * nodes` wide values: current query, prior query, formed row,
// and two three-word complex branch fields.  The complete source field is assembled before those
// branch fields are reused.  All source/current/branch conversions are checked before the one
// continuing memory/basis commit; a carrier or malformed refusal publishes no plausible successor.

__device__ void field_constitutive_prepare(
    const int64_t *seed, const int64_t *memory_lo, const int64_t *basis_lo,
    const int64_t *incoming, const int64_t *origin,
    const int64_t *current_frame, const int64_t *origin_frame,
    uint32_t nodes, uint32_t linked, int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count,
    wide *field_scratch
) {
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    if (!nodes || linked > 1 || nodes > UINT32_MAX / 6u) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    const uint32_t source_width = 4u * nodes;
    const uint32_t target_width = 2u * nodes;
    const uint32_t width = source_width + target_width;
    if (width < source_width || current_frame == nullptr
        || (linked && (origin == nullptr || origin_frame == nullptr))) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }

    // The current frame is a unit phase at every fixed node.  A linked prior source also carries
    // the frame in which it was emitted; its crossing is formed only after both frames pass this
    // exact validation.  The receiving field remains in the root chart throughout.
    for (uint32_t node = 0; node < nodes; ++node) {
        const int64_t *now = current_frame + 3u * node;
        wide now_norm = add_checked(product_checked((wide)now[0], (wide)now[0], slot),
            product_checked((wide)now[1], (wide)now[1], slot), slot);
        wide now_den = product_checked((wide)now[2], (wide)now[2], slot);
        if (now[2] <= 0 || *slot || now_norm != now_den) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        if (linked) {
            const int64_t *before = origin_frame + 3u * node;
            wide before_norm = add_checked(product_checked((wide)before[0], (wide)before[0], slot),
                product_checked((wide)before[1], (wide)before[1], slot), slot);
            wide before_den = product_checked((wide)before[2], (wide)before[2], slot);
            if (before[2] <= 0 || *slot || before_norm != before_den) {
                atomicOr(slot, REFUSED_MALFORMED);
                return;
            }
        }
    }

    wide *current_query = field_scratch;
    wide *prior_query = current_query + width;
    wide *formed = prior_query + width;
    wide *outward = formed + width;
    wide *held_departure = outward + 3u * nodes;
    for (uint32_t j = 0; j < width; ++j) {
        current_query[j] = 0;
        prior_query[j] = 0;
        formed[j] = 0;
    }

    // Every incoming node has its own exact denominator.  The source target face uses their
    // common denominator only when a linked relation row is formed.
    wide incoming_den = 1;
    for (uint32_t node = 0; node < nodes; ++node) {
        const int64_t *law = seed + 5u * node;
        const int64_t *held = memory_lo + 3u * node;
        const int64_t *arrived = incoming + 3u * node;
        if (law[0] <= 0 || law[1] <= 0 || law[4] <= 0 || held[2] <= 0 || arrived[2] <= 0) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        // The declared incoming transport is a unit phase.  Check it in the same wide hand used
        // for the scattering, rather than trusting an exterior declaration at the kernel mouth.
        wide unit_left = product_checked((wide)law[2], (wide)law[2], slot);
        wide unit_right = product_checked((wide)law[3], (wide)law[3], slot);
        wide unit_sum = add_checked(unit_left, unit_right, slot);
        wide unit_den = product_checked((wide)law[4], (wide)law[4], slot);
        if (*slot || unit_sum != unit_den) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        if (linked) incoming_den = fibre_lcm(incoming_den, (wide)arrived[2], slot);
        if (*slot) return;
    }

    // Scatter each node.  `outward` is the branch caused by the incoming field; the
    // `held_departure` is the successor branch retained as the next held state.
    for (uint32_t node = 0; node < nodes; ++node) {
        const int64_t *law = seed + 5u * node;
        const int64_t *held = memory_lo + 3u * node;
        const int64_t *arrived = incoming + 3u * node;
        wide incident[2] = {
            sub_checked(product_checked((wide)law[2], (wide)arrived[0], slot),
                product_checked((wide)law[3], (wide)arrived[1], slot), slot),
            add_checked(product_checked((wide)law[3], (wide)arrived[0], slot),
                product_checked((wide)law[2], (wide)arrived[1], slot), slot)
        };
        wide incident_den = product_checked((wide)law[4], (wide)arrived[2], slot);
        if (*slot) return;
        fibre_normalize(incident, 2, &incident_den, slot);
        wide common = fibre_lcm(incident_den, (wide)held[2], slot);
        wide admittance = add_checked((wide)law[0], (wide)law[1], slot);
        wide denominator = product_checked(common, admittance, slot);
        if (*slot) return;
        for (uint32_t component = 0; component < 2; ++component) {
            wide entering = product_checked(incident[component], common / incident_den, slot);
            wide retained = product_checked((wide)held[component], common / (wide)held[2], slot);
            wide velocity = product_checked(2, add_checked(
                product_checked((wide)law[0], entering, slot),
                product_checked((wide)law[1], retained, slot), slot), slot);
            outward[3u * node + component] = sub_checked(
                velocity, product_checked(admittance, entering, slot), slot);
            held_departure[3u * node + component] = sub_checked(
                velocity, product_checked(admittance, retained, slot), slot);
        }
        if (*slot) return;
        outward[3u * node + 2] = denominator;
        held_departure[3u * node + 2] = denominator;
        fibre_normalize(outward + 3u * node, 2, outward + 3u * node + 2, slot);
        fibre_normalize(held_departure + 3u * node, 2,
            held_departure + 3u * node + 2, slot);
        if (*slot) return;
    }

    // Form the complete source face before `outward`/`held_departure` can serve as branch scratch.
    wide source_den = 1;
    for (uint32_t node = 0; node < nodes; ++node) {
        source_den = fibre_lcm(source_den, outward[3u * node + 2], slot);
        source_den = fibre_lcm(source_den, held_departure[3u * node + 2], slot);
    }
    if (*slot) return;
    for (uint32_t node = 0; node < nodes; ++node) {
        for (uint32_t component = 0; component < 2; ++component) {
            current_query[4u * node + component] = product_checked(
                outward[3u * node + component],
                source_den / outward[3u * node + 2], slot);
            current_query[4u * node + 2u + component] = product_checked(
                held_departure[3u * node + component],
                source_den / held_departure[3u * node + 2], slot);
        }
    }
    fibre_normalize(current_query, source_width, &source_den, slot);
    if (*slot) return;

    // Publish the source face as the first output segment before current-query elimination reuses
    // its source coordinates.  The continuing memory/basis are still untouched.
    for (uint32_t j = 0; j < source_width; ++j) {
        output_lo[j] = output_hi[j] = to_word(current_query[j], slot);
    }
    output_lo[source_width] = output_hi[source_width] = to_word(source_den, slot);
    if (*slot) return;

    // Preserve the CURRENT held successor before the branch scratch is reused for a transported
    // historical source.  Its common source denominator is reduced per node just as in the
    // original scattering pass, and this copy is the only value eligible for the final commit.
    for (uint32_t node = 0; node < nodes; ++node) {
        outward[3u * node] = current_query[4u * node + 2u];
        outward[3u * node + 1u] = current_query[4u * node + 3u];
        outward[3u * node + 2u] = source_den;
        fibre_normalize(outward + 3u * node, 2, outward + 3u * node + 2, slot);
    }
    if (*slot) return;

    uint32_t prior_status = 3u, prior_rank = 0u;
    int64_t inserted = -1;
    wide prior_den = 1;
    if (linked) {
        wide origin_den = (wide)origin[source_width];
        if (origin_den <= 0) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        // Transport both retained source branches from their actual historical local frame to the
        // current local frame. `origin` is immutable and `outward` holds the current successor;
        // only `held_departure` is reused as historical branch scratch.
        prior_den = 1;
        // First pass determines the common denominator.  The temporary branch values are
        // intentionally recomputed below so no historical source can occupy the successor slot.
        for (uint32_t node = 0; node < nodes; ++node) {
            const int64_t *now = current_frame + 3u * node;
            const int64_t *before = origin_frame + 3u * node;
            wide crossing[3];
            fibre_phase_product((wide)now[0], (wide)now[1], (wide)now[2],
                (wide)before[0], -(wide)before[1], (wide)before[2], crossing, slot);
            if (*slot) return;
            fibre_phase_product(crossing[0], crossing[1], crossing[2],
                (wide)origin[4u * node], (wide)origin[4u * node + 1], (wide)origin_den,
                held_departure + 3u * node, slot);
            if (*slot) return;
            prior_den = fibre_lcm(prior_den, held_departure[3u * node + 2], slot);
            fibre_phase_product(crossing[0], crossing[1], crossing[2],
                (wide)origin[4u * node + 2], (wide)origin[4u * node + 3], (wide)origin_den,
                held_departure + 3u * node, slot);
            if (*slot) return;
            prior_den = fibre_lcm(prior_den, held_departure[3u * node + 2], slot);
        }
        if (*slot) return;
        wide paired_den = fibre_lcm(prior_den, incoming_den, slot);
        if (*slot) return;
        for (uint32_t node = 0; node < nodes; ++node) {
            const int64_t *now = current_frame + 3u * node;
            const int64_t *before = origin_frame + 3u * node;
            wide crossing[3];
            fibre_phase_product((wide)now[0], (wide)now[1], (wide)now[2],
                (wide)before[0], -(wide)before[1], (wide)before[2], crossing, slot);
            if (*slot) return;
            fibre_phase_product(crossing[0], crossing[1], crossing[2],
                (wide)origin[4u * node], (wide)origin[4u * node + 1], (wide)origin_den,
                held_departure + 3u * node, slot);
            if (*slot) return;
            for (uint32_t component = 0; component < 2; ++component) {
                prior_query[4u * node + component] = product_checked(
                    held_departure[3u * node + component], prior_den / held_departure[3u * node + 2], slot);
                formed[4u * node + component] = product_checked(
                    held_departure[3u * node + component], paired_den / held_departure[3u * node + 2], slot);
            }
            fibre_phase_product(crossing[0], crossing[1], crossing[2],
                (wide)origin[4u * node + 2], (wide)origin[4u * node + 3], (wide)origin_den,
                held_departure + 3u * node, slot);
            if (*slot) return;
            for (uint32_t component = 0; component < 2; ++component) {
                prior_query[4u * node + 2u + component] = product_checked(
                    held_departure[3u * node + component], prior_den / held_departure[3u * node + 2], slot);
                formed[4u * node + 2u + component] = product_checked(
                    held_departure[3u * node + component], paired_den / held_departure[3u * node + 2], slot);
            }
        }
        for (uint32_t node = 0; node < nodes; ++node) {
            for (uint32_t component = 0; component < 2; ++component) {
                formed[source_width + 2u * node + component] = product_checked(
                    (wide)incoming[3u * node + component],
                    paired_den / (wide)incoming[3u * node + 2], slot);
            }
        }
        if (*slot) return;
        fibre_query(basis_lo, source_width, width, prior_query, &prior_den, nullptr, -1,
            &prior_status, &prior_rank, slot);
        if (*slot) return;
        fibre_normalize(formed, width, nullptr, slot);
        inserted = fibre_stage(basis_lo, width, formed, slot);
        if (*slot) return;
    }

    uint32_t current_status = 0u, successor_rank = 0u;
    wide current_den = source_den;
    fibre_query(basis_lo, source_width, width, current_query, &current_den, formed, inserted,
        &current_status, &successor_rank, slot);
    if (*slot) return;
    for (uint32_t j = 0; j < width; ++j) {
        if (j >= source_width) {
            current_query[j] = -current_query[j];
            prior_query[j] = -prior_query[j];
        }
        to_word(current_query[j], slot);
        to_word(prior_query[j], slot);
        if (inserted >= 0) to_word(formed[j], slot);
    }
    to_word(current_den, slot);
    to_word(prior_den, slot);
    for (uint32_t j = 0; j < 3u * nodes; ++j) to_word(outward[j], slot);
    if (*slot) return;

    const uint32_t current_at = source_width + 1u;
    const uint32_t prior_at = current_at + width + 4u;
    for (uint32_t j = 0; j < width; ++j) {
        output_lo[current_at + j] = output_hi[current_at + j] = (int64_t)current_query[j];
        output_lo[prior_at + j] = output_hi[prior_at + j] = (int64_t)prior_query[j];
    }
    output_lo[current_at + width] = output_hi[current_at + width] = (int64_t)current_den;
    output_lo[current_at + width + 1] = output_hi[current_at + width + 1] = current_status;
    output_lo[current_at + width + 2] = output_hi[current_at + width + 2] = inserted;
    output_lo[current_at + width + 3] = output_hi[current_at + width + 3] = successor_rank;
    output_lo[prior_at + width] = output_hi[prior_at + width] = (int64_t)prior_den;
    output_lo[prior_at + width + 1] = output_hi[prior_at + width + 1] = prior_status;
    output_lo[prior_at + width + 2] = output_hi[prior_at + width + 2] = -1;
    output_lo[prior_at + width + 3] = output_hi[prior_at + width + 3] = prior_rank;

}

extern "C" __global__ void __launch_bounds__(512) section_constitutive_field(
    const int64_t *seed,
    int64_t *memory_lo, int64_t *memory_hi,
    int64_t *basis_lo, int64_t *basis_hi,
    const int64_t *incoming,
    const int64_t *origin,
    const int64_t *current_frame, const int64_t *origin_frame,
    uint32_t nodes, uint32_t linked, uint32_t coupled, uint32_t junction_grain, uint64_t occurrence,
    const int64_t *covariance, const int64_t *junction_held,
    int64_t *next_covariance_lo, int64_t *next_covariance_hi,
    int64_t *junction_report_lo, int64_t *junction_report_hi, wide *junction_workspace,
    uint32_t transport_enabled, wide *transport_lo, wide *transport_hi,
    const wide *origin_junction, const wide *origin_transport,
    wide *transport_delta_lo, wide *transport_delta_hi, wide *transport_report_lo, wide *transport_report_hi,
    const int64_t *refreshed_source_current,
    const int64_t *moment_table,uint32_t moment_count,int64_t *moment_weights,
    const int64_t *context_table,int64_t *context_weights,int64_t *context_evaluations,uint64_t source_ordinal,
    const int64_t *operative_table,
    uint32_t material_targets,uint32_t target_factor_width,
    int64_t *output_lo, int64_t *output_hi,
    uint32_t *slot, const uint32_t *census,
    const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0) return;
    extern __shared__ wide field_scratch[];
    // The dependent field word is prepared once. All continuing writes remain after the complete
    // coupled return; early returns inside this helper cannot strand a block barrier.
    if (threadIdx.x == 0) {
        if (coupled > 3 || transport_enabled > 7u || !material_targets
            || (target_factor_width && transport_enabled<6u) || (!target_factor_width && material_targets!=nodes)
            || (transport_enabled>=6u && !operative_table)
            || (transport_enabled>=4u && (!context_table || !context_weights || !context_evaluations || occurrence>=UINT32_MAX))
            || (transport_enabled==3u && (!moment_table || !moment_weights))
            || (transport_enabled && (coupled < 2u || !transport_lo || !transport_hi
                || !transport_delta_lo || !transport_delta_hi || !transport_report_lo || !transport_report_hi
                || (linked && (!origin_junction || !origin_transport))))
            || (coupled && (!covariance || !junction_held || !next_covariance_lo
            || !next_covariance_hi || !junction_report_lo || !junction_report_hi || !junction_workspace))) {
            atomicOr(slot, REFUSED_MALFORMED);
        } else {
            field_constitutive_prepare(seed, memory_lo, basis_lo, incoming, origin,
                current_frame, origin_frame, nodes, linked, output_lo, output_hi,
                slot, census, lineage, lineage_count, field_scratch);
        }
    }
    __syncthreads();
    if (*slot) return;
    if(operative_table) {
        field_operative_reflection_prepare(operative_table,output_lo,origin,incoming,current_frame,origin_frame,covariance,
            (const wide *)junction_held,nodes,linked,junction_grain,occurrence,next_covariance_lo,next_covariance_hi,
            (wide *)junction_report_lo,(wide *)junction_report_hi,junction_workspace,slot);
    } else if (coupled == 2 || coupled == 3) {
        // Every thread participates. Each independent LDL row keeps its original arithmetic
        // order; only a completed pivot column becomes input to the next one.
        field_enclosed_junction_prepare(output_lo, origin, incoming, current_frame, origin_frame,
            nodes, linked, occurrence, junction_grain, coupled == 3, covariance, (const wide *)junction_held,
            next_covariance_lo, next_covariance_hi, (wide *)junction_report_lo, (wide *)junction_report_hi,
            junction_workspace, slot);
    } else if (coupled == 1 && threadIdx.x == 0) {
        field_paired_junction_prepare(output_lo, origin, incoming, current_frame, origin_frame,
            nodes, linked, occurrence, covariance, junction_held,
            next_covariance_lo, next_covariance_hi, junction_report_lo, junction_report_hi,
            junction_workspace, slot);
    }
    __syncthreads();
    if (*slot) return;
    wide operative_radius=-1;
    if(operative_table && transport_enabled>=2u && transport_enabled<=5u){
        const wide *bounds=(const wide *)(uintptr_t)operative_table[7];
        const wide *details=(const wide *)((const int64_t *)(uintptr_t)operative_table[16]+18u*(size_t)(6u*nodes));
        if(bounds[0]!=0 || details[2]!=0){if(threadIdx.x==0)atomicOr(slot,REFUSED_MALFORMED);}
        operative_radius=details[5];
    }
    __syncthreads();if(*slot)return;
    if (transport_enabled == 2u && threadIdx.x == 0)
        complete_material_transport_prepare((const int64_t *)transport_lo,(const int64_t *)origin_transport,refreshed_source_current,
            output_lo,origin,incoming,current_frame,origin_frame,next_covariance_lo,(const wide *)junction_held,
            (const wide *)junction_report_lo,nodes,linked,junction_grain,occurrence,
            (int64_t *)transport_delta_lo,(int64_t *)transport_delta_hi,(int64_t *)transport_report_lo,(int64_t *)transport_report_hi,field_scratch,slot,operative_radius);
    else if (transport_enabled == 1u && threadIdx.x == 0)
        field_material_transport_prepare(transport_lo, origin_junction, origin_transport,
            (const wide *)junction_report_lo, incoming, nodes, linked, junction_grain,
            transport_delta_lo, transport_delta_hi, transport_report_lo, transport_report_hi, slot);
    if(transport_enabled==3u)
        moment_material_transport_prepare((const int64_t *)transport_lo,(const int64_t *)origin_transport,refreshed_source_current,
            moment_table,moment_count,moment_weights,output_lo,origin,incoming,current_frame,origin_frame,next_covariance_lo,
            (const wide *)junction_held,(const wide *)junction_report_lo,nodes,linked,junction_grain,occurrence,
            (int64_t *)transport_delta_lo,(int64_t *)transport_delta_hi,(int64_t *)transport_report_lo,(int64_t *)transport_report_hi,field_scratch,slot,operative_radius);
    if(transport_enabled>=4u)
        contextual_material_prepare((const int64_t *)transport_lo,(const int64_t *)origin_transport,context_table,(uint32_t)occurrence,source_ordinal,
            context_weights,context_evaluations,output_lo,origin,incoming,current_frame,origin_frame,next_covariance_lo,
            (const wide *)junction_held,(const wide *)junction_report_lo,nodes,linked,junction_grain,transport_enabled==7u?4u:transport_enabled==6u?3u:transport_enabled==5u?2u:1u,
            (int64_t *)transport_delta_lo,(int64_t *)transport_delta_hi,(int64_t *)transport_report_lo,(int64_t *)transport_report_hi,field_scratch,slot,
            transport_enabled>=6u?((const wide *)(uintptr_t)operative_table[7])[1]:operative_radius,
            transport_enabled>=6u?(const wide *)(uintptr_t)operative_table[5]:nullptr,transport_enabled>=6u?(uint32_t)operative_table[19]:0u,
            material_targets,target_factor_width);
    __syncthreads();
    if (*slot || threadIdx.x != 0) return;
    const uint32_t width = 6u * nodes;
    const uint32_t current_at = 4u * nodes + 1u;
    const int64_t inserted = output_lo[current_at + width + 2u];
    const wide *formed = field_scratch + 2u * width;
    const wide *held_departure = field_scratch + 3u * width;
    // The only continuing writes: neither a refused row nor a refused enclosure can publish a
    // partial successor. The staged source/relation/held conversions were all checked earlier.
    if (inserted >= 0) for (uint32_t j = 0; j < width; ++j) {
        size_t at = (size_t)inserted * width + j;
        basis_lo[at] = basis_hi[at] = (int64_t)formed[j];
    }
    for (uint32_t j = 0; j < 3u * nodes; ++j)
        memory_lo[j] = memory_hi[j] = (int64_t)held_departure[j];
    if (transport_enabled == 2u) {
        for (size_t i=0;i<complete_state_words(nodes);++i)
            ((int64_t *)transport_lo)[i]=((int64_t *)transport_hi)[i]=((const int64_t *)transport_delta_lo)[i];
    } else if(transport_enabled>=3u) {
        for(size_t i=0;i<moment_state_words(nodes);++i)
            ((int64_t *)transport_lo)[i]=((int64_t *)transport_hi)[i]=((const int64_t *)transport_delta_lo)[i];
    } else if (transport_enabled == 1u) {
        const size_t coefficients = (size_t)6u * nodes * nodes;
        // All sums and the complete current return were checked before any continuing write.
        for (size_t i = 0; i < coefficients; ++i)
            transport_lo[i] = transport_hi[i] = transport_lo[i] + transport_delta_lo[i];
        transport_lo[coefficients] = transport_hi[coefficients] = transport_delta_lo[coefficients];
    }
}

// Re-express the same fixed-node field relation under a rational unit-phase gauge.  The source
// face has two complex branches per node and the target face is the complete root input; only the
// source coordinates turn.  Every destination is fresh staging, so the continuing old state is
// never written while a checked conversion or relation row can still refuse.
extern "C" __global__ void __launch_bounds__(512) section_constitutive_field_rechart(
    const int64_t *seed, const int64_t *memory, const int64_t *root_frame,
    const int64_t *basis, const int64_t *change, uint32_t nodes,
    int64_t *seed_lo, int64_t *seed_hi, int64_t *memory_lo, int64_t *memory_hi,
    int64_t *frame_lo, int64_t *frame_hi, int64_t *basis_lo, int64_t *basis_hi,
    int64_t *report_lo, int64_t *report_hi,
    uint32_t *slot, const uint32_t *census, const uint32_t *lineage, uint32_t lineage_count
) {
    if (blockIdx.x != 0 || threadIdx.x != 0) return;
    if (upstream_refused(census, lineage, lineage_count, slot)) return;
    if (!nodes || nodes > UINT32_MAX / 6u) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    const uint32_t source_width = 4u * nodes;
    const uint32_t target_width = 2u * nodes;
    const uint32_t width = source_width + target_width;
    if (width < source_width || width < target_width) {
        atomicOr(slot, REFUSED_MALFORMED);
        return;
    }
    extern __shared__ wide field_rechart_scratch[];
    wide *row = field_rechart_scratch;
    wide common = 1;

    for (uint32_t node = 0; node < nodes; ++node) {
        const int64_t *g = change + 6u * node;
        const int64_t *law = seed + 5u * node;
        const int64_t *held = memory + 3u * node;
        const int64_t *old_frame = root_frame + 3u * node;
        wide unit = add_checked(product_checked((wide)g[0], (wide)g[0], slot),
            product_checked((wide)g[1], (wide)g[1], slot), slot);
        wide unit_den = product_checked((wide)g[2], (wide)g[2], slot);
        wide old_unit = add_checked(product_checked((wide)old_frame[0], (wide)old_frame[0], slot),
            product_checked((wide)old_frame[1], (wide)old_frame[1], slot), slot);
        wide old_den = product_checked((wide)old_frame[2], (wide)old_frame[2], slot);
        if (g[2] <= 0 || old_frame[2] <= 0 || law[0] <= 0 || law[1] <= 0
            || law[4] <= 0 || held[2] <= 0 || *slot
            || unit != unit_den || old_unit != old_den) {
            atomicOr(slot, REFUSED_MALFORMED);
            return;
        }
        common = fibre_lcm(common, (wide)g[2], slot);
        if (*slot) return;

        wide turn[3], held_after[3], frame_after[3], initial[3];
        fibre_phase_product((wide)g[0], (wide)g[1], (wide)g[2],
            (wide)law[2], (wide)law[3], (wide)law[4], turn, slot);
        fibre_phase_product((wide)g[0], (wide)g[1], (wide)g[2],
            (wide)held[0], (wide)held[1], (wide)held[2], held_after, slot);
        fibre_phase_product((wide)g[0], (wide)g[1], (wide)g[2],
            (wide)old_frame[0], (wide)old_frame[1], (wide)old_frame[2], frame_after, slot);
        fibre_phase_product((wide)g[0], (wide)g[1], (wide)g[2],
            (wide)g[3], (wide)g[4], (wide)g[5], initial, slot);
        if (*slot) return;

        // These are fresh staged charts.  No old seed, memory, frame, or relation word is changed.
        seed_lo[5u * node] = seed_hi[5u * node] = law[0];
        seed_lo[5u * node + 1u] = seed_hi[5u * node + 1u] = law[1];
        for (uint32_t j = 0; j < 3u; ++j) {
            seed_lo[5u * node + 2u + j] = seed_hi[5u * node + 2u + j] = to_word(turn[j], slot);
            memory_lo[3u * node + j] = memory_hi[3u * node + j] = to_word(held_after[j], slot);
            frame_lo[3u * node + j] = frame_hi[3u * node + j] = to_word(frame_after[j], slot);
            report_lo[9u * node + j] = report_hi[9u * node + j] = to_word(turn[j], slot);
            report_lo[9u * node + 3u + j] = report_hi[9u * node + 3u + j] = to_word(initial[j], slot);
            report_lo[9u * node + 6u + j] = report_hi[9u * node + 6u + j] = to_word(frame_after[j], slot);
        }
        if (*slot) return;
    }

    // The destination relation is staged independently.  Transform both complex source branches
    // at each node; target/root coordinates pass through the same common denominator unchanged.
    for (size_t j = 0; j < (size_t)width * width; ++j) basis_lo[j] = basis_hi[j] = 0;
    for (uint32_t p = 0; p < width; ++p) {
        if (!basis[(size_t)p * width + p]) continue;
        for (uint32_t node = 0; node < nodes; ++node) {
            const int64_t *g = change + 6u * node;
            wide x = (wide)basis[(size_t)p * width + 4u * node];
            wide y = (wide)basis[(size_t)p * width + 4u * node + 1u];
            row[4u * node] = product_checked(sub_checked(product_checked((wide)g[0], x, slot),
                product_checked((wide)g[1], y, slot), slot), common / (wide)g[2], slot);
            row[4u * node + 1u] = product_checked(add_checked(product_checked((wide)g[1], x, slot),
                product_checked((wide)g[0], y, slot), slot), common / (wide)g[2], slot);
            x = (wide)basis[(size_t)p * width + 4u * node + 2u];
            y = (wide)basis[(size_t)p * width + 4u * node + 3u];
            row[4u * node + 2u] = product_checked(sub_checked(product_checked((wide)g[0], x, slot),
                product_checked((wide)g[1], y, slot), slot), common / (wide)g[2], slot);
            row[4u * node + 3u] = product_checked(add_checked(product_checked((wide)g[1], x, slot),
                product_checked((wide)g[0], y, slot), slot), common / (wide)g[2], slot);
        }
        for (uint32_t j = source_width; j < width; ++j)
            row[j] = product_checked((wide)basis[(size_t)p * width + j], common, slot);
        if (*slot) return;
        fibre_normalize(row, width, nullptr, slot);
        if (*slot) return;
        int64_t inserted = fibre_stage(basis_lo, width, row, slot);
        if (*slot) return;
        if (inserted >= 0) {
            // Elimination may reduce a wide intermediate, so conversion follows the complete
            // staged row rather than narrowing before fibre_stage.  No destination row is written
            // until every coefficient has passed the checked exterior-word conversion.
            for (uint32_t j = 0; j < width; ++j) row[j] = (wide)to_word(row[j], slot);
            if (*slot) return;
            for (uint32_t j = 0; j < width; ++j) {
                size_t at = (size_t)inserted * width + j;
                basis_lo[at] = basis_hi[at] = (int64_t)row[j];
            }
        }
        if (*slot) return;
    }
}

// Exact resident ingress to the same field recurrence.
extern "C" __global__ void section_field_current_input(
    const int64_t *lo,const int64_t *hi,uint32_t at,uint32_t den_at,uint32_t status_at,
    uint32_t nodes,int64_t *out,int64_t *out_hi,
    uint32_t *slot,const uint32_t *census,const uint32_t *lineage,uint32_t lineage_count
) {
    if(blockIdx.x || threadIdx.x) return;
    if(upstream_refused(census,lineage,lineage_count,slot)) return;
    wide den=fibre_current_denominator(lo,hi,den_at,status_at,slot);
    for(uint32_t j=0;j<2u*nodes;++j) if(lo[at+j]!=hi[at+j]) atomicOr(slot,REFUSED_MALFORMED);
    if(*slot) return;
    for(uint32_t n=0;n<nodes;++n) {
        wide v[3]={lo[at+2u*n],lo[at+2u*n+1],den};
        fibre_normalize(v,2,v+2,slot);
        for(uint32_t j=0;j<3;++j) to_word(v[j],slot);
        if(*slot) return;
        for(uint32_t j=0;j<3;++j) out[3u*n+j]=out_hi[3u*n+j]=(int64_t)v[j];
    }
}
