#include <new>

#include <holonics/apparatus/expression_geometry_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_expression(const expression_geometry_mount* mount,
    event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_expression_geometry{
      mount->foundation, mount->inherited, observation->predecessor_remount};
  observation->inquiry.question = mount->question;
}

__global__ void derive_sources(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::expression_presentation_capacity) { return; }
  organ::expression_geometry_detail::derive_presentation(mount->foundation,
      static_cast<std::uint8_t>(threadIdx.x), observation->inquiry.presentations[threadIdx.x]);
}

__global__ void derive_changed_sources(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= 2) { return; }
  organ::expression_geometry_detail::derive_presentation(mount->changed_foundation,
      static_cast<std::uint8_t>(threadIdx.x), observation->changed.presentations[threadIdx.x]);
}

__global__ void compose_sources(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::expression_geometry_detail::compose(mount->foundation, observation->inquiry);
  }
}

__global__ void close_changed(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  auto& changed = observation->changed; changed.rechart =
      organ::expression_geometry_detail::search_rechart(mount->changed_foundation.card.presentations[0],
          mount->changed_foundation.card.presentations[1],
          mount->changed_foundation.card.chart_min, mount->changed_foundation.card.chart_max, false);
  changed.discriminant_changed = !organ::expression_exact_detail::same_polynomial(
      observation->inquiry.presentations[0].ideal.resultant,
      changed.presentations[0].ideal.resultant);
  changed.series_changed = !organ::expression_exact_detail::equal(
      observation->inquiry.presentations[0].scalar.series[0][5],
      changed.presentations[0].scalar.series[0][5]);
  changed.source_sensitive = changed.presentations[0].exact && changed.presentations[1].exact &&
      changed.rechart.exact && changed.discriminant_changed && changed.series_changed;
  changed.exact = changed.source_sensitive; observation->changed_sensitive = changed.exact;
  observation->inquiry.controls.changed_source_sensitive = changed.exact;
  observation->inquiry.controls.exact = observation->inquiry.controls.exact && changed.exact;
  observation->inquiry.all_exact = observation->inquiry.all_exact && changed.exact;
  observation->inquiry.theory_formed = observation->inquiry.all_exact;
}

__global__ void form_expression(event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { static_cast<void>(production->form(*observation)); }
}

__global__ void resume_expression(const event::checker_raw_return* raw,
    event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    static_cast<void>(production->resume(*raw, *observation));
  }
}

__global__ void rest_expression(event::resident_expression_geometry* production,
    event::expression_geometry_rest_record* rest,
    event::expression_geometry_rest_record* handoff,
    event::expression_geometry_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest); if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_expression_geometry{*rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_expression(const event::expression_geometry_observation* resident,
    event::expression_geometry_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_expression_geometry_mount(const expression_geometry_mount* mount,
    event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) noexcept {
  mount_expression<<<1,1>>>(mount, production, observation); return cudaGetLastError();
}
cudaError_t launch_expression_geometry_sources(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept {
  derive_sources<<<1,organ::expression_presentation_capacity>>>(mount, observation);
  return cudaGetLastError();
}
cudaError_t launch_expression_geometry_changed(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept {
  derive_changed_sources<<<1,2>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_expression_geometry_compose(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept {
  compose_sources<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_expression_geometry_changed_close(const expression_geometry_mount* mount,
    event::expression_geometry_observation* observation) noexcept {
  close_changed<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_expression_geometry_form(event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) noexcept {
  form_expression<<<1,1>>>(production, observation); return cudaGetLastError();
}
cudaError_t launch_expression_geometry_resume(const event::checker_raw_return* raw,
    event::resident_expression_geometry* production,
    event::expression_geometry_observation* observation) noexcept {
  resume_expression<<<1,1>>>(raw, production, observation); return cudaGetLastError();
}
cudaError_t launch_expression_geometry_rest(event::resident_expression_geometry* production,
    event::expression_geometry_rest_record* rest, event::expression_geometry_rest_record* handoff,
    event::expression_geometry_observation* observation) noexcept {
  rest_expression<<<1,1>>>(production, rest, handoff, observation); return cudaGetLastError();
}
cudaError_t launch_expression_geometry_observe(
    const event::expression_geometry_observation* resident,
    event::expression_geometry_observation* returned) noexcept {
  observe_expression<<<1,1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
