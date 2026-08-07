#include <new>

#include <holonics/apparatus/arithmetic_spectral_resident.hpp>
#include <holonics/organ/arithmetic_aperture_law.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_arithmetic(const arithmetic_spectral_mount* mount,
    event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_arithmetic_spectral{
      mount->foundation, mount->inherited, observation->predecessor_remount};
  observation->inquiry.question = mount->question;
  organ::arithmetic_spectral_detail::mount_sources(mount->foundation, observation->inquiry);
}

__global__ void derive_fields(event::arithmetic_spectral_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::arithmetic_base_count) { return; }
  const auto slot = static_cast<std::uint8_t>(threadIdx.x);
  const std::uint16_t prime = slot == 0 ? 5 : 13;
  organ::arithmetic_field_detail::discover_tower(prime,
      exact::word{observation->inquiry.mounted.lineage.value() + 100U + slot},
      observation->inquiry.towers[slot]);
}

__global__ void derive_curves(event::arithmetic_spectral_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::arithmetic_curve_count) { return; }
  const auto slot = static_cast<std::uint8_t>(threadIdx.x); auto& curve = observation->inquiry.curves[slot];
  curve.discriminant = -64LL * curve.source.coefficient * curve.source.coefficient * curve.source.coefficient;
  curve.smooth = organ::arithmetic_field_detail::reduced(curve.discriminant, curve.source.prime) != 0;
  curve.imaginary_unit = observation->inquiry.towers[curve.source.prime == 5 ? 0 : 1].imaginary_unit;
  for (auto& count : curve.fixed_counts) { count = 1; }
  curve.lineage = exact::word{curve.source.lineage.value() + 500U};
}

__global__ void derive_fixed(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) {
  const auto global = blockIdx.x * blockDim.x + threadIdx.x;
  if (global >= organ::arithmetic_fixed_capacity) { return; }
  std::uint8_t curve = 0; std::uint8_t degree = 0; std::uint32_t x = 0;
  if (!organ::arithmetic_aperture_detail::fixed_coordinate(
      observation->inquiry, global, curve, degree, x)) { return; }
  auto& receipt = workspace->fixed[global];
  organ::arithmetic_curve_detail::fixed_contribution(observation->inquiry, curve, degree, x, receipt);
  atomicAdd(&observation->inquiry.curves[curve].fixed_counts[degree - 1U], receipt.point_count);
}

__global__ void derive_candidates(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) {
  const auto global = blockIdx.x * blockDim.x + threadIdx.x;
  if (global >= organ::arithmetic_curve_count * organ::arithmetic_candidate_count) { return; }
  const auto coordinate = exact::divide_unsigned(global, organ::arithmetic_candidate_count);
  const auto curve = static_cast<std::uint8_t>(coordinate.quotient);
  const auto candidate = static_cast<std::uint8_t>(coordinate.remainder);
  organ::arithmetic_curve_detail::evaluate_candidate(
      observation->inquiry, curve, candidate, workspace->candidates[curve][candidate]);
}

__global__ void compose_curves(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::arithmetic_curve_count) { return; }
  const auto curve = static_cast<std::uint8_t>(threadIdx.x); std::uint8_t selected = 0;
  std::uint8_t matches = 0;
  for (std::uint8_t candidate = 0; candidate < organ::arithmetic_candidate_count; ++candidate) {
    const auto& value = workspace->candidates[curve][candidate];
    if (value.norm_matches && value.mismatches == 0) { selected = candidate; ++matches; }
  }
  if (matches != 1) { observation->inquiry.obstruction =
      organ::arithmetic_spectral_obstruction::correspondence_refused; return; }
  workspace->candidates[curve][selected].selected = true;
  organ::arithmetic_spectral_detail::form_carrier(
      observation->inquiry.curves[curve], workspace->candidates[curve][selected]);
}

__global__ void derive_points(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) {
  const auto global = blockIdx.x * blockDim.x + threadIdx.x;
  if (global >= organ::arithmetic_point_pair_capacity) { return; }
  std::uint8_t curve = 0; std::uint32_t pair = 0;
  if (!organ::arithmetic_aperture_detail::pair_coordinate(
      observation->inquiry, global, curve, pair)) { return; }
  auto& out = workspace->points[global]; out.curve = curve;
  const auto& source = observation->inquiry.curves[curve];
  const auto& field = organ::arithmetic_curve_detail::field_for(observation->inquiry,
      source.source.prime, 2);
  if (pair == 0) {
    out.pair_encoding = 0; out.source.infinite = true; out.frobenius.infinite = true;
    out.gaussian.infinite = true; out.on_curve = true; out.equal = true;
  } else {
    --pair; out.pair_encoding = pair; const auto q = field.order;
    const auto coordinate = exact::divide_unsigned(pair, q);
    out.source = {organ::arithmetic_field_detail::element(
        static_cast<std::uint32_t>(coordinate.quotient), field),
        organ::arithmetic_field_detail::element(
          static_cast<std::uint32_t>(coordinate.remainder), field), false};
    out.on_curve = organ::arithmetic_curve_detail::on_curve(
        out.source, source.source.coefficient, field);
    if (out.on_curve) {
      out.frobenius = organ::arithmetic_curve_detail::frobenius(out.source, field);
      out.gaussian = organ::arithmetic_curve_detail::gaussian_image(out.source,
          static_cast<std::int8_t>(source.frobenius.real),
          static_cast<std::int8_t>(source.frobenius.imaginary), source.source.coefficient,
          source.imaginary_unit, field);
      out.equal = organ::arithmetic_curve_detail::point_equal(out.frobenius, out.gaussian, field);
    }
  }
  out.lineage = exact::word{source.lineage.value() + 900'000U + pair};
}

__global__ void derive_currents(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) {
  const auto global = blockIdx.x * blockDim.x + threadIdx.x;
  if (global >= organ::arithmetic_curve_count * organ::arithmetic_norm_current_count) { return; }
  const auto coordinate = exact::divide_unsigned(global, organ::arithmetic_norm_current_count);
  const auto curve = static_cast<std::uint8_t>(coordinate.quotient);
  const auto current = static_cast<std::uint16_t>(coordinate.remainder);
  organ::arithmetic_test_detail::norm_current(
      observation->inquiry.curves[curve], curve, current, workspace->norm_currents[curve][current]);
  if (current < organ::arithmetic_trace_current_count) {
    organ::arithmetic_test_detail::trace_current(observation->inquiry.curves[curve], curve,
        static_cast<std::uint8_t>(current), workspace->trace_currents[curve][current]);
  }
}

__global__ void close_arithmetic(event::arithmetic_spectral_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::arithmetic_realization_detail::close(observation->inquiry);
  }
}

__global__ void form_arithmetic(event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { static_cast<void>(production->form(*observation)); }
}

__global__ void resume_arithmetic(const event::checker_raw_return* raw,
    event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { static_cast<void>(production->resume(*raw, *observation)); }
}

__global__ void rest_arithmetic(event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_rest_record* rest, event::arithmetic_spectral_rest_record* handoff,
    event::arithmetic_spectral_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest);
  ::new (static_cast<void*>(production)) event::resident_arithmetic_spectral{*rest, observation->remount};
  observation->final_head = production->head(); observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue(); observation->handoff = production->rest(*handoff);
}

__global__ void observe_arithmetic(const event::arithmetic_spectral_observation* resident,
    event::arithmetic_spectral_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_arithmetic_mount(const arithmetic_spectral_mount* mount,
    event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) noexcept {
  mount_arithmetic<<<1,1>>>(mount, production, observation); return cudaGetLastError();
}
cudaError_t launch_arithmetic_fields(event::arithmetic_spectral_observation* observation) noexcept {
  derive_fields<<<1,organ::arithmetic_base_count>>>(observation); return cudaGetLastError();
}
cudaError_t launch_arithmetic_curves(event::arithmetic_spectral_observation* observation) noexcept {
  derive_curves<<<1,organ::arithmetic_curve_count>>>(observation); return cudaGetLastError();
}
cudaError_t launch_arithmetic_fixed(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept {
  derive_fixed<<<611,256>>>(observation, workspace); return cudaGetLastError();
}
cudaError_t launch_arithmetic_candidates(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept {
  derive_candidates<<<5,128>>>(observation, workspace); return cudaGetLastError();
}
cudaError_t launch_arithmetic_compose(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept {
  compose_curves<<<1,organ::arithmetic_curve_count>>>(observation, workspace); return cudaGetLastError();
}
cudaError_t launch_arithmetic_points(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept {
  derive_points<<<563,256>>>(observation, workspace); return cudaGetLastError();
}
cudaError_t launch_arithmetic_currents(event::arithmetic_spectral_observation* observation,
    organ::arithmetic_spectral_workspace* workspace) noexcept {
  derive_currents<<<7,256>>>(observation, workspace); return cudaGetLastError();
}
cudaError_t launch_arithmetic_close(event::arithmetic_spectral_observation* observation) noexcept {
  close_arithmetic<<<1,1>>>(observation); return cudaGetLastError();
}
cudaError_t launch_arithmetic_form(event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) noexcept {
  form_arithmetic<<<1,1>>>(production, observation); return cudaGetLastError();
}
cudaError_t launch_arithmetic_resume(const event::checker_raw_return* raw,
    event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_observation* observation) noexcept {
  resume_arithmetic<<<1,1>>>(raw, production, observation); return cudaGetLastError();
}
cudaError_t launch_arithmetic_rest(event::resident_arithmetic_spectral* production,
    event::arithmetic_spectral_rest_record* rest, event::arithmetic_spectral_rest_record* handoff,
    event::arithmetic_spectral_observation* observation) noexcept {
  rest_arithmetic<<<1,1>>>(production, rest, handoff, observation); return cudaGetLastError();
}
cudaError_t launch_arithmetic_observe(const event::arithmetic_spectral_observation* resident,
    event::arithmetic_spectral_observation* returned) noexcept {
  observe_arithmetic<<<1,1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
