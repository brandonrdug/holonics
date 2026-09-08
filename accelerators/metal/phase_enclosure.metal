// Resident dyadic phase enclosures.  This file is concatenated after the resident W helpers.
// Ball centres are numerical dyadic values; they are never exposed as exact point currents.

inline W phase_enclosure_read(device const long *wire, ulong at) {
  return field_wire_read(wire, at);
}

inline W phase_enclosure_one() { return wi64(1); }

inline void phase_enclosure_write(device long *lo, device long *hi, ulong at, W value,
                                  device uint *slot) {
  field_wire_write(lo, hi, at, value, slot);
}

inline W phase_enclosure_product_with_error(W left, W right, uint grain,
                                            thread W &error, device uint *slot) {
  W floor_value = field_product_shift(left, right, grain, false, slot);
  W ceil_value = field_product_shift(left, right, grain, true, slot);
  if (*slot) return wzero();
  if (!ueq(floor_value.m, ceil_value.m) || floor_value.neg != ceil_value.neg)
    error = field_add_checked(error, phase_enclosure_one(), slot);
  return left.neg != right.neg ? ceil_value : floor_value;
}

inline bool phase_enclosure_validate_point(
    device const long *lo, device const long *hi, uint at, uint denominator_at,
    uint disposition_at, uint complex_coordinates, uint raw_extent, thread W &denominator,
    device uint *slot) {
  if (!complex_coordinates || !raw_extent || raw_extent > complex_coordinates
      || (ulong)at + 2ul * (ulong)complex_coordinates > 0xfffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return false;
  }
  denominator = fibre_current_denominator(lo, hi, denominator_at, disposition_at, slot);
  if (*slot) return false;
  for (uint coordinate = 0; coordinate < complex_coordinates; ++coordinate) {
    uint index = at + 2u * coordinate;
    if (lo[index] != hi[index] || lo[index + 1u] != hi[index + 1u]
        || (coordinate >= raw_extent && (lo[index] != 0 || lo[index + 1u] != 0))) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return false;
    }
  }
  return true;
}

inline bool phase_enclosure_validate_ball(
    device const long *lo, device const long *hi, uint wide_at, uint complex_extent,
    thread W &radius, device uint *slot) {
  ulong values = 2ul * (ulong)complex_extent + 1ul;
  if (!complex_extent || values > 0x7ffffffful
      || (ulong)wide_at + values > 0x7ffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return false;
  }
  for (ulong value = 0; value < values; ++value) {
    ulong base = 2ul * ((ulong)wide_at + value);
    if (lo[base] != hi[base] || lo[base + 1ul] != hi[base + 1ul]) {
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
      return false;
    }
  }
  radius = phase_enclosure_read(lo, (ulong)wide_at + 2ul * (ulong)complex_extent);
  if (wneg_p(radius)) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return false;
  }
  return true;
}

kernel void section_phase_enclosure_lift(
    device const long *input_lo [[buffer(0)]], device const long *input_hi [[buffer(1)]],
    constant uint &input_at [[buffer(2)]], constant uint &input_denominator_at [[buffer(3)]],
    constant uint &input_disposition_at [[buffer(4)]], constant uint &input_complex_coordinates [[buffer(5)]],
    constant uint &raw_extent [[buffer(6)]], constant uint &grain [[buffer(7)]],
    device long *output_lo [[buffer(8)]], device long *output_hi [[buffer(9)]],
    device uint *slot [[buffer(10)]], device const uint *census [[buffer(11)]],
    device const uint *lineage [[buffer(12)]], constant uint &lineage_count [[buffer(13)]],
    uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot)) return;
  if (grain < 1u || grain > 120u || !raw_extent || raw_extent > input_complex_coordinates
      || raw_extent > 0x3fffffffu || input_complex_coordinates > 0x7fffffffu) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  W denominator;
  if (!phase_enclosure_validate_point(input_lo, input_hi, input_at, input_denominator_at,
                                      input_disposition_at, input_complex_coordinates,
                                      raw_extent, denominator, slot)) return;
  W radius = wzero();
  uint coordinates = 2u * raw_extent;
  for (uint coordinate = 0; coordinate < coordinates; ++coordinate) {
    W numerator = fromword(input_lo[(ulong)input_at + coordinate]);
    W floor_value = field_signed_product_divide_2(
        numerator, wof(field_pow2(grain - 1u), false, slot), denominator, false, slot);
    W ceil_value = field_signed_product_divide_2(
        numerator, wof(field_pow2(grain - 1u), false, slot), denominator, true, slot);
    if (*slot) return;
    W centre = numerator.neg ? ceil_value : floor_value;
    phase_enclosure_write(output_lo, output_hi, coordinate, centre, slot);
    if (!ueq(floor_value.m, ceil_value.m) || floor_value.neg != ceil_value.neg)
      radius = field_add_checked(radius, phase_enclosure_one(), slot);
  }
  if (!*slot) phase_enclosure_write(output_lo, output_hi, coordinates, radius, slot);
}

kernel void section_phase_enclosed_convolution_validate(
    device const long *source_lo [[buffer(0)]], device const long *source_hi [[buffer(1)]],
    constant uint &source_at [[buffer(2)]], constant uint &source_denominator_at [[buffer(3)]],
    constant uint &source_disposition_at [[buffer(4)]], device const long *response_lo [[buffer(5)]],
    device const long *response_hi [[buffer(6)]], constant uint &response_wide_at [[buffer(7)]],
    constant uint &source_complex_coordinates [[buffer(8)]], constant uint &source_raw_extent [[buffer(9)]],
    constant uint &response_raw_extent [[buffer(10)]], constant uint &grain [[buffer(11)]],
    device W *workspace [[buffer(12)]], device uint *slot [[buffer(13)]],
    device const uint *census [[buffer(14)]], device const uint *lineage [[buffer(15)]],
    constant uint &lineage_count [[buffer(16)]], uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot)) return;
  if (grain < 1u || grain > 120u || !response_raw_extent
      || source_raw_extent > 0x3fffffffu || response_raw_extent > 0x3fffffffu) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  W source_den;
  if (!phase_enclosure_validate_point(source_lo, source_hi, source_at, source_denominator_at,
                                      source_disposition_at, source_complex_coordinates,
                                      source_raw_extent, source_den, slot)) return;
  W radius;
  if (!phase_enclosure_validate_ball(response_lo, response_hi, response_wide_at,
                                     response_raw_extent, radius, slot)) return;
  ulong source_coordinates = 2ul * source_raw_extent;
  ulong output_extent = (ulong)source_raw_extent + response_raw_extent - 1ul;
  if (output_extent > 0x7ffffffful || source_coordinates > 0x7ffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  uint scalar_at = 4u * source_raw_extent + (uint)output_extent;
  W l1 = wzero();
  for (uint coordinate = 0; coordinate < (uint)source_coordinates; ++coordinate)
    l1 = field_add_checked(l1, field_of_magnitude(fromword(source_lo[(ulong)source_at + coordinate]).m, false), slot);
  W h_l1 = wzero();
  for (uint coordinate = 0; coordinate < 2u * response_raw_extent; ++coordinate)
    h_l1 = field_add_checked(h_l1, field_of_magnitude(
        phase_enclosure_read(response_lo, (ulong)response_wide_at + coordinate).m, false), slot);
  if (*slot) return;
  workspace[scalar_at] = source_den;
  workspace[scalar_at + 1u] = l1;
  workspace[scalar_at + 2u] = h_l1;
  workspace[scalar_at + 3u] = radius;
}

kernel void section_phase_enclosed_convolution_lift(
    device const long *source_lo [[buffer(0)]], constant uint &source_at [[buffer(1)]],
    constant uint &source_denominator_at [[buffer(2)]], constant uint &source_raw_extent [[buffer(3)]],
    constant uint &response_raw_extent [[buffer(4)]], constant uint &grain [[buffer(5)]],
    device W *workspace [[buffer(6)]], device uint *slot [[buffer(7)]],
    device const uint *census [[buffer(8)]], device const uint *lineage [[buffer(9)]],
    constant uint &lineage_count [[buffer(10)]], uint gid [[thread_position_in_grid]]) {
  if (*slot || upstream(census, lineage, lineage_count, slot)) return;
  if (gid >= 2u * source_raw_extent) return;
  uint output_extent = source_raw_extent + response_raw_extent - 1u;
  W denominator = workspace[4u * source_raw_extent + output_extent];
  uint coordinate = gid;
  W numerator = fromword(source_lo[(ulong)source_at + coordinate]);
  W floor_value = field_signed_product_divide_2(
      numerator, wof(field_pow2(grain - 1u), false, slot), denominator, false, slot);
  W ceil_value = field_signed_product_divide_2(
      numerator, wof(field_pow2(grain - 1u), false, slot), denominator, true, slot);
  if (*slot) return;
  workspace[coordinate] = numerator.neg ? ceil_value : floor_value;
  workspace[2u * source_raw_extent + coordinate] =
      (!ueq(floor_value.m, ceil_value.m) || floor_value.neg != ceil_value.neg)
          ? phase_enclosure_one() : wzero();
}

kernel void section_phase_enclosed_convolution_products(
    device const long *response_lo [[buffer(0)]], constant uint &response_wide_at [[buffer(1)]],
    constant uint &source_raw_extent [[buffer(2)]], constant uint &response_raw_extent [[buffer(3)]],
    constant uint &grain [[buffer(4)]], device W *workspace [[buffer(5)]],
    device long *output_lo [[buffer(6)]], device long *output_hi [[buffer(7)]],
    device uint *slot [[buffer(8)]], device const uint *census [[buffer(9)]],
    device const uint *lineage [[buffer(10)]], constant uint &lineage_count [[buffer(11)]],
    uint gid [[thread_position_in_grid]]) {
  if (*slot || upstream(census, lineage, lineage_count, slot)) return;
  ulong output_extent64 = (ulong)source_raw_extent + response_raw_extent - 1ul;
  if (output_extent64 > 0x7ffffffful || (ulong)gid >= output_extent64) {
    if (output_extent64 > 0x7ffffffful)
      atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  uint output_extent = (uint)output_extent64;
  uint first = gid >= response_raw_extent ? gid - response_raw_extent + 1u : 0u;
  uint last = gid < source_raw_extent ? gid : source_raw_extent - 1u;
  W error = wzero(), real = wzero(), imaginary = wzero();
  for (uint source = first; source <= last; ++source) {
    uint response = gid - source;
    W ar = workspace[2u * source], ai = workspace[2u * source + 1u];
    W br = phase_enclosure_read(response_lo, (ulong)response_wide_at + 2ul * response);
    W bi = phase_enclosure_read(response_lo, (ulong)response_wide_at + 2ul * response + 1ul);
    real = field_add_checked(real, phase_enclosure_product_with_error(ar, br, grain, error, slot), slot);
    real = field_sub_checked(real, phase_enclosure_product_with_error(ai, bi, grain, error, slot), slot);
    imaginary = field_add_checked(imaginary, phase_enclosure_product_with_error(ar, bi, grain, error, slot), slot);
    imaginary = field_add_checked(imaginary, phase_enclosure_product_with_error(ai, br, grain, error, slot), slot);
    if (*slot) return;
  }
  phase_enclosure_write(output_lo, output_hi, 2u * gid, real, slot);
  phase_enclosure_write(output_lo, output_hi, 2u * gid + 1u, imaginary, slot);
  workspace[4u * source_raw_extent + gid] = error;
}

kernel void section_phase_enclosed_convolution_finish(
    device W *workspace [[buffer(0)]], constant uint &source_raw_extent [[buffer(1)]],
    constant uint &response_raw_extent [[buffer(2)]], constant uint &grain [[buffer(3)]],
    device long *output_lo [[buffer(4)]], device long *output_hi [[buffer(5)]],
    device uint *slot [[buffer(6)]], device const uint *census [[buffer(7)]],
    device const uint *lineage [[buffer(8)]], constant uint &lineage_count [[buffer(9)]],
    uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot)) return;
  ulong output_extent64 = (ulong)source_raw_extent + response_raw_extent - 1ul;
  if (output_extent64 > 0x7ffffffful) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  uint output_extent = (uint)output_extent64;
  uint scalar_at = 4u * source_raw_extent + output_extent;
  W xden = workspace[scalar_at], x_l1 = workspace[scalar_at + 1u];
  W h_l1 = workspace[scalar_at + 2u], rho_h = workspace[scalar_at + 3u];
  W source_error = wzero();
  for (uint coordinate = 0; coordinate < 2u * source_raw_extent; ++coordinate)
    source_error = field_add_checked(source_error, workspace[2u * source_raw_extent + coordinate], slot);
  W product_error = wzero();
  for (uint target = 0; target < output_extent; ++target)
    product_error = field_add_checked(product_error, workspace[4u * source_raw_extent + target], slot);
  W twice_xden = field_product_checked(wi64(2), xden, slot);
  W twice_scale = wof(field_pow2(grain + 1u), false, slot);
  W radius_source = field_signed_product_divide_2(x_l1, rho_h, twice_xden, true, slot);
  W radius_rounding = field_signed_product_divide_2(source_error, h_l1, twice_scale, true, slot);
  W radius = field_add_checked(field_add_checked(radius_source, radius_rounding, slot), product_error, slot);
  if (!*slot && !wneg_p(radius)) phase_enclosure_write(output_lo, output_hi,
                                                         2u * output_extent, radius, slot);
}

kernel void section_phase_enclosed_difference_validate(
    device const long *predicted_lo [[buffer(0)]], device const long *predicted_hi [[buffer(1)]],
    constant uint &predicted_wide_at [[buffer(2)]], constant uint &predicted_raw_extent [[buffer(3)]],
    device const long *observed_lo [[buffer(4)]], device const long *observed_hi [[buffer(5)]],
    constant uint &observed_at [[buffer(6)]], constant uint &observed_denominator_at [[buffer(7)]],
    constant uint &observed_disposition_at [[buffer(8)]], constant uint &observed_complex_coordinates [[buffer(9)]],
    constant uint &observed_raw_extent [[buffer(10)]], constant uint &predicted_from [[buffer(11)]],
    constant uint &observed_from [[buffer(12)]], constant uint &extent [[buffer(13)]],
    constant uint &grain [[buffer(14)]], device W *workspace [[buffer(15)]],
    device uint *slot [[buffer(16)]], device const uint *census [[buffer(17)]],
    device const uint *lineage [[buffer(18)]], constant uint &lineage_count [[buffer(19)]],
    uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot)) return;
  if (grain < 1u || grain > 120u || !predicted_raw_extent || !observed_raw_extent || !extent
      || (ulong)predicted_from + extent > predicted_raw_extent
      || (ulong)observed_from + extent > observed_raw_extent
      || predicted_raw_extent > 0x3fffffffu || observed_raw_extent > 0x3fffffffu
      || extent > 0x3fffffffu) {
    atomic_fetch_or_explicit((device atomic_uint *)slot, REFUSED_MALFORMED, memory_order_relaxed);
    return;
  }
  W radius, denominator;
  if (!phase_enclosure_validate_ball(predicted_lo, predicted_hi, predicted_wide_at,
                                     predicted_raw_extent, radius, slot)) return;
  if (!phase_enclosure_validate_point(observed_lo, observed_hi, observed_at,
                                      observed_denominator_at, observed_disposition_at,
                                      observed_complex_coordinates, observed_raw_extent,
                                      denominator, slot)) return;
  workspace[2u * extent] = denominator;
  workspace[2u * extent + 1u] = radius;
}

kernel void section_phase_enclosed_difference_products(
    device const long *predicted_lo [[buffer(0)]], constant uint &predicted_wide_at [[buffer(1)]],
    device const long *observed_lo [[buffer(2)]], constant uint &observed_at [[buffer(3)]],
    constant uint &predicted_from [[buffer(4)]], constant uint &observed_from [[buffer(5)]],
    constant uint &extent [[buffer(6)]], constant uint &grain [[buffer(7)]], device W *workspace [[buffer(8)]],
    device long *output_lo [[buffer(9)]], device long *output_hi [[buffer(10)]],
    device uint *slot [[buffer(11)]], device const uint *census [[buffer(12)]],
    device const uint *lineage [[buffer(13)]], constant uint &lineage_count [[buffer(14)]],
    uint gid [[thread_position_in_grid]]) {
  if (*slot || upstream(census, lineage, lineage_count, slot)) return;
  uint width = 2u * extent;
  if (gid >= width) return;
  W denominator = workspace[width];
  W numerator = fromword(observed_lo[(ulong)observed_at + 2ul * observed_from + gid]);
  W floor_value = field_signed_product_divide_2(
      numerator, wof(field_pow2(grain - 1u), false, slot), denominator, false, slot);
  W ceil_value = field_signed_product_divide_2(
      numerator, wof(field_pow2(grain - 1u), false, slot), denominator, true, slot);
  if (*slot) return;
  W observed = numerator.neg ? ceil_value : floor_value;
  W predicted = phase_enclosure_read(predicted_lo, (ulong)predicted_wide_at + 2ul * predicted_from + gid);
  phase_enclosure_write(output_lo, output_hi, gid, field_sub_checked(observed, predicted, slot), slot);
  workspace[gid] = (!ueq(floor_value.m, ceil_value.m) || floor_value.neg != ceil_value.neg)
      ? phase_enclosure_one() : wzero();
}

kernel void section_phase_enclosed_difference_finish(
    device W *workspace [[buffer(0)]], constant uint &extent [[buffer(1)]],
    device long *output_lo [[buffer(2)]], device long *output_hi [[buffer(3)]],
    device uint *slot [[buffer(4)]], device const uint *census [[buffer(5)]],
    device const uint *lineage [[buffer(6)]], constant uint &lineage_count [[buffer(7)]],
    uint gid [[thread_position_in_grid]]) {
  if (gid != 0 || *slot || upstream(census, lineage, lineage_count, slot)) return;
  uint width = 2u * extent;
  W radius = workspace[width + 1u];
  for (uint coordinate = 0; coordinate < width; ++coordinate)
    radius = field_add_checked(radius, workspace[coordinate], slot);
  if (!*slot && !wneg_p(radius)) phase_enclosure_write(output_lo, output_hi, width, radius, slot);
}
