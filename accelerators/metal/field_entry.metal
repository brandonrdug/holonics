// Entry to the same field operation after the target's exact junction helpers. The paired
// representation uses device scratch; its durable report retains the shared signed-word wire.
kernel void section_constitutive_field(
    device const long *seed [[buffer(0)]], device long *memory_lo [[buffer(1)]],
    device long *memory_hi [[buffer(2)]], device long *basis_lo [[buffer(3)]],
    device long *basis_hi [[buffer(4)]], device const long *incoming [[buffer(5)]],
    device const long *origin [[buffer(6)]], device const long *current_frame [[buffer(7)]],
    device const long *origin_frame [[buffer(8)]], constant uint &nodes [[buffer(9)]],
    constant uint &linked [[buffer(10)]], constant uint &coupled [[buffer(11)]],
    constant uint &junction_grain [[buffer(12)]], constant ulong &occurrence [[buffer(13)]],
    device const long *covariance [[buffer(14)]], device const long *junction_held [[buffer(15)]],
    device long *next_covariance_lo [[buffer(16)]], device long *next_covariance_hi [[buffer(17)]],
    device long *junction_report_lo [[buffer(18)]], device long *junction_report_hi [[buffer(19)]],
    device W *junction_workspace [[buffer(20)]], device long *output_lo [[buffer(21)]],
    device long *output_hi [[buffer(22)]], device uint *slot [[buffer(23)]],
    device const uint *census [[buffer(24)]], device const uint *lineage [[buffer(25)]],
    constant uint &lineage_count [[buffer(26)]], threadgroup W *scratch [[threadgroup(0)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z) return;
  if (coupled > 3 || (coupled && (!covariance || !junction_held || !next_covariance_lo
      || !next_covariance_hi || !junction_report_lo || !junction_report_hi || !junction_workspace))) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  field_constitutive_prepare(seed, memory_lo, basis_lo, incoming, origin, current_frame,
      origin_frame, nodes, linked, output_lo, output_hi, slot, census, lineage, lineage_count, scratch);
  if (*slot) return;
  if (coupled == 2 || coupled == 3) {
    field_enclosed_junction_prepare(output_lo, origin, incoming, current_frame, origin_frame,
        nodes, linked, occurrence, junction_grain, coupled == 3, covariance, junction_held,
        next_covariance_lo, next_covariance_hi, junction_report_lo, junction_report_hi,
        junction_workspace, slot);
  } else if (coupled == 1) {
    field_paired_junction_prepare(output_lo, origin, incoming, current_frame, origin_frame,
        nodes, linked, occurrence, covariance, junction_held, next_covariance_lo,
        next_covariance_hi, junction_report_lo, junction_report_hi, junction_workspace, slot);
  }
  if (*slot) return;
  const uint width = 6u * nodes;
  const long inserted = output_lo[4u * nodes + 1u + width + 2u];
  threadgroup W *formed = scratch + 2u * width;
  threadgroup W *held_departure = scratch + 3u * width;
  // The complete field and junction must succeed before either continuing memory is changed.
  if (inserted >= 0) for (uint j = 0; j < width; ++j) {
    ulong at = (ulong)inserted * width + j;
    basis_lo[at] = basis_hi[at] = toword(formed[j], slot);
  }
  for (uint j = 0; j < 3u * nodes; ++j)
    memory_lo[j] = memory_hi[j] = toword(held_departure[j], slot);
}

// A dependent lane normalizes an existing resident current into per-node phase triples.
kernel void section_field_current_input(
    device const long *lo [[buffer(0)]], device const long *hi [[buffer(1)]],
    constant uint &at [[buffer(2)]], constant uint &den_at [[buffer(3)]],
    constant uint &status_at [[buffer(4)]], constant uint &nodes [[buffer(5)]],
    device long *out [[buffer(6)]], device long *out_hi [[buffer(7)]],
    device uint *slot [[buffer(8)]], device const uint *census [[buffer(9)]],
    device const uint *lineage [[buffer(10)]], constant uint &lineage_count [[buffer(11)]],
    uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z) return;
  if (upstream(census, lineage, lineage_count, slot)) return;
  W den = fibre_current_denominator(lo, hi, den_at, status_at, slot);
  for (uint j = 0; j < 2u * nodes; ++j) if (lo[at+j] != hi[at+j])
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
  if (*slot) return;
  for (uint n = 0; n < nodes; ++n) {
    W v[3] = {fromword(lo[at+2u*n]), fromword(lo[at+2u*n+1]), den};
    wnorm(v, 2, v+2, slot);
    for (uint j = 0; j < 3; ++j) toword(v[j], slot);
    if (*slot) return;
    for (uint j = 0; j < 3; ++j) out[3u*n+j] = out_hi[3u*n+j] = toword(v[j], slot);
  }
}
