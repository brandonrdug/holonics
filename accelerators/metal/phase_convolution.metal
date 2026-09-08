// Scalable resident causal convolution. This file is concatenated after the paired and
// enclosed junction helpers, which provide the checked W arithmetic and phase product.
// Products are private resident scratch; the owner launches normalize and pack only after
// the preceding command has completed, and discards the private output whenever slot refuses.

// Causal convolution of two resident complex polynomial currents. The two
// raw extents are the active coefficient populations; coordinates after them
// must be structural zero and cannot conceal an unadmitted current.
// Both placements use the same checked arithmetic.
kernel void section_phase_convolution(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]],
    device const long *response_lo [[buffer(5)]], device const long *response_hi [[buffer(6)]],
    constant uint &response_at [[buffer(7)]], constant uint &response_denominator_at [[buffer(8)]],
    constant uint &response_disposition_at [[buffer(9)]],
    constant uint &source_complex_coordinates [[buffer(10)]],
    constant uint &response_complex_coordinates [[buffer(11)]],
    constant uint &source_raw_extent [[buffer(12)]], constant uint &response_raw_extent [[buffer(13)]],
    device long *output_lo [[buffer(14)]], device long *output_hi [[buffer(15)]],
    device uint *slot [[buffer(16)]], device const uint *census [[buffer(17)]],
    device const uint *lineage [[buffer(18)]], constant uint &lineage_count [[buffer(19)]],
    threadgroup W *scratch [[threadgroup(0)]], uint3 tid [[thread_position_in_threadgroup]]) {
  if (tid.x || tid.y || tid.z)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  ulong source_complex = (ulong)source_complex_coordinates;
  ulong response_complex = (ulong)response_complex_coordinates;
  ulong source_raw = (ulong)source_raw_extent;
  ulong response_raw = (ulong)response_raw_extent;
  if (!source_complex || !response_complex || !source_raw || !response_raw
      || source_raw > source_complex || response_raw > response_complex
      || source_complex > 0x7ffffffful || response_complex > 0x7ffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong output_extent64 = source_raw + response_raw - 1ul;
  if (output_extent64 > 0x7ffffffful
      || output_extent64 > (0xfffffffful - 1ul) / 2ul) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint source_complex_count = (uint)source_complex;
  uint response_complex_count = (uint)response_complex;
  uint source_raw_count = (uint)source_raw;
  uint response_raw_count = (uint)response_raw;
  uint output_extent = (uint)output_extent64;
  uint output_width = 2u * output_extent + 1u;

  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W response_den = fibre_current_denominator(response_lo, response_hi,
                                             response_denominator_at,
                                             response_disposition_at, slot);
  if (*slot)
    return;
  for (uint coordinate = 0; coordinate < source_complex_count; ++coordinate) {
    uint at = source_at + 2u * coordinate;
    if (source_lo[at] != source_hi[at] || source_lo[at + 1u] != source_hi[at + 1u]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    if (coordinate >= source_raw_count
        && (source_lo[at] != 0 || source_lo[at + 1u] != 0)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  for (uint coordinate = 0; coordinate < response_complex_count; ++coordinate) {
    uint at = response_at + 2u * coordinate;
    if (response_lo[at] != response_hi[at] || response_lo[at + 1u] != response_hi[at + 1u]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
    if (coordinate >= response_raw_count
        && (response_lo[at] != 0 || response_lo[at + 1u] != 0)) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  W common = field_product_checked(source_den, response_den, slot);
  if (*slot)
    return;
  for (uint target = 0; target < output_extent; ++target) {
    W real = wzero(), imaginary = wzero();
    uint source_first = target >= response_raw_count
        ? target - response_raw_count + 1u
        : 0u;
    uint source_last = min(target, source_raw_count - 1u);
    for (uint source = source_first; source <= source_last; ++source) {
      uint response = target - source;
      W product[3];
      field_phase_product(fromword(source_lo[source_at + 2u * source]),
                fromword(source_lo[source_at + 2u * source + 1u]), source_den,
                fromword(response_lo[response_at + 2u * response]),
                fromword(response_lo[response_at + 2u * response + 1u]), response_den,
                product, slot);
      if (*slot)
        return;
      W factor = wdiv(common, product[2], slot);
      real = field_add_checked(real, field_product_checked(product[0], factor, slot), slot);
      imaginary = field_add_checked(imaginary, field_product_checked(product[1], factor, slot), slot);
      if (*slot)
        return;
    }
    scratch[2u * target] = real;
    scratch[2u * target + 1u] = imaginary;
  }
  wnorm(scratch, output_width - 1u, &common, slot);
  if (*slot)
    return;
  for (uint j = 0; j < output_width - 1u; ++j)
    toword(scratch[j], slot);
  toword(common, slot);
  if (*slot)
    return;
  for (uint j = 0; j < output_width - 1u; ++j)
    output_lo[j] = output_hi[j] = toword(scratch[j], slot);
  output_lo[output_width - 1u] = output_hi[output_width - 1u] = toword(common, slot);
}

// Validate the complete declared current before any parallel product lane starts. This serial
// admission makes malformed/disposition refusal deterministic; product lanes can then publish
// only carrier failures into private workspace coordinates.
kernel void section_phase_convolution_validate(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]],
    device const long *response_lo [[buffer(5)]], device const long *response_hi [[buffer(6)]],
    constant uint &response_at [[buffer(7)]], constant uint &response_denominator_at [[buffer(8)]],
    constant uint &response_disposition_at [[buffer(9)]],
    constant uint &source_complex_coordinates [[buffer(10)]],
    constant uint &response_complex_coordinates [[buffer(11)]],
    constant uint &source_raw_extent [[buffer(12)]], constant uint &response_raw_extent [[buffer(13)]],
    device W *workspace [[buffer(14)]], device uint *slot [[buffer(15)]],
    device const uint *census [[buffer(16)]], device const uint *lineage [[buffer(17)]],
    constant uint &lineage_count [[buffer(18)]], uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot))
    return;
  ulong source_complex = (ulong)source_complex_coordinates;
  ulong response_complex = (ulong)response_complex_coordinates;
  ulong source_raw = (ulong)source_raw_extent;
  ulong response_raw = (ulong)response_raw_extent;
  if (!source_complex || !response_complex || !source_raw || !response_raw
      || source_raw > source_complex || response_raw > response_complex
      || source_complex > 0x7ffffffful || response_complex > 0x7ffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  ulong output_extent64 = source_raw + response_raw - 1ul;
  if (output_extent64 > 0x7ffffffful
      || output_extent64 > (0xfffffffful - 1ul) / 2ul) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  uint source_complex_count = (uint)source_complex;
  uint response_complex_count = (uint)response_complex;
  uint source_raw_count = (uint)source_raw;
  uint response_raw_count = (uint)response_raw;
  uint output_extent = (uint)output_extent64;
  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W response_den = fibre_current_denominator(response_lo, response_hi,
                                             response_denominator_at,
                                             response_disposition_at, slot);
  if (*slot)
    return;
  for (uint coordinate = 0; coordinate < source_complex_count; ++coordinate) {
    uint at = source_at + 2u * coordinate;
    if (source_lo[at] != source_hi[at] || source_lo[at + 1u] != source_hi[at + 1u]
        || (coordinate >= source_raw_count
            && (source_lo[at] != 0 || source_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  for (uint coordinate = 0; coordinate < response_complex_count; ++coordinate) {
    uint at = response_at + 2u * coordinate;
    if (response_lo[at] != response_hi[at]
        || response_lo[at + 1u] != response_hi[at + 1u]
        || (coordinate >= response_raw_count
            && (response_lo[at] != 0 || response_lo[at + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                               memory_order_relaxed);
      return;
    }
  }
  W common = field_product_checked(source_den, response_den, slot);
  if (*slot)
    return;
  workspace[2u * output_extent] = common;
}

kernel void section_phase_convolution_products(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]],
    device const long *response_lo [[buffer(5)]], device const long *response_hi [[buffer(6)]],
    constant uint &response_at [[buffer(7)]], constant uint &response_denominator_at [[buffer(8)]],
    constant uint &response_disposition_at [[buffer(9)]],
    constant uint &source_complex_coordinates [[buffer(10)]],
    constant uint &response_complex_coordinates [[buffer(11)]],
    constant uint &source_raw_extent [[buffer(12)]], constant uint &response_raw_extent [[buffer(13)]],
    device W *workspace [[buffer(14)]], device uint *slot [[buffer(15)]],
    device const uint *census [[buffer(16)]], device const uint *lineage [[buffer(17)]],
    constant uint &lineage_count [[buffer(18)]], uint gid [[thread_position_in_grid]]) {
  if (*slot)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  uint output_extent = source_raw_extent + response_raw_extent - 1u;
  if (gid >= output_extent)
    return;
  uint source_raw_count = source_raw_extent;
  uint response_raw_count = response_raw_extent;
  uint width = 2u * output_extent;
  W source_den = fibre_current_denominator(source_lo, source_hi,
                                           source_denominator_at,
                                           source_disposition_at, slot);
  W response_den = fibre_current_denominator(response_lo, response_hi,
                                             response_denominator_at,
                                             response_disposition_at, slot);
  W common = workspace[width];

  uint source_first = gid >= response_raw_count
      ? gid - response_raw_count + 1u
      : 0u;
  uint source_last = min(gid, source_raw_count - 1u);
  W real = wzero(), imaginary = wzero();
  for (uint source = source_first; source <= source_last; ++source) {
    uint response = gid - source;
    W product[3];
    field_phase_product(
        fromword(source_lo[(ulong)source_at + 2ul * (ulong)source]),
        fromword(source_lo[(ulong)source_at + 2ul * (ulong)source + 1ul]), source_den,
        fromword(response_lo[(ulong)response_at + 2ul * (ulong)response]),
        fromword(response_lo[(ulong)response_at + 2ul * (ulong)response + 1ul]), response_den,
        product, slot);
    if (*slot)
      return;
    W factor = wdiv(common, product[2], slot);
    real = field_add_checked(real, field_product_checked(product[0], factor, slot), slot);
    imaginary = field_add_checked(imaginary,
                                 field_product_checked(product[1], factor, slot), slot);
    if (*slot)
      return;
  }
  if (!*slot) {
    workspace[2u * gid] = real;
    workspace[2u * gid + 1u] = imaginary;
  }
}

kernel void section_phase_convolution_normalize(
    device W *workspace [[buffer(0)]], constant uint &width [[buffer(1)]],
    device uint *slot [[buffer(2)]], device const uint *census [[buffer(3)]],
    device const uint *lineage [[buffer(4)]], constant uint &lineage_count [[buffer(5)]],
    uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot)
    return;
  if (upstream(census, lineage, lineage_count, slot))
    return;
  if (!width) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W denominator = workspace[width];
  if (wzero_p(denominator) || wneg_p(denominator)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W gcd = denominator;
  for (uint j = 0; j < width && !ueq(gcd.m, uone()); ++j) {
    gcd = wgcd(gcd, workspace[j], slot);
    if (*slot)
      return;
  }
  if (wzero_p(gcd) || wneg_p(gcd)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  workspace[width] = wdiv(denominator, gcd, slot);
  if (*slot)
    return;
  workspace[width + 1u] = gcd;
}

kernel void section_phase_convolution_pack(
    device const W *workspace [[buffer(0)]], constant uint &width [[buffer(1)]],
    device long *output_lo [[buffer(2)]], device long *output_hi [[buffer(3)]],
    device uint *slot [[buffer(4)]], device const uint *census [[buffer(5)]],
    device const uint *lineage [[buffer(6)]], constant uint &lineage_count [[buffer(7)]],
    uint gid [[thread_position_in_grid]]) {
  uint previous = *slot;
  bool inherited = upstream(census, lineage, lineage_count, slot);
  if (previous || inherited || *slot || gid > width)
    return;
  if (!width) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W gcd = workspace[width + 1u];
  if (wzero_p(gcd) || wneg_p(gcd)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED,
                             memory_order_relaxed);
    return;
  }
  W normalized = gid < width
      ? wdiv(workspace[gid], gcd, slot)
      : workspace[width];
  if (*slot)
    return;
  long value = toword(normalized, slot);
  if (*slot)
    return;
  output_lo[gid] = output_hi[gid] = value;
}
