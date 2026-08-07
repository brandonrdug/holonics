#include <new>

#include <holonics/apparatus/hodge_realization_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_hodge(const hodge_realization_mount* mount,
    event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_hodge_realization{
      mount->foundation, mount->inherited, observation->predecessor_remount};
  observation->inquiry.mounted = mount->foundation.card;
  observation->inquiry.question = mount->question;
}

__global__ void derive_factors(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::hodge_factor_capacity) { return; }
  organ::hodge_factor_detail::derive(mount->foundation, static_cast<std::uint8_t>(threadIdx.x),
      observation->inquiry.factors[threadIdx.x]);
}

__global__ void derive_product(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::hodge_product_detail::derive(observation->inquiry.factors,
        mount->foundation.card, observation->inquiry.product);
  }
}

__global__ void derive_translations(const hodge_realization_mount*,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= organ::hodge_translation_capacity) { return; }
  organ::hodge_correspondence_detail::derive_translation(observation->inquiry.factors[0],
      static_cast<std::uint8_t>(threadIdx.x), observation->inquiry.cycles.translations[threadIdx.x]);
}

__global__ void derive_cycles(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    organ::hodge_cycle_detail::close(mount->foundation.card,
        observation->inquiry.product, observation->inquiry.cycles);
  }
}

__global__ void derive_blowups(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x >= 2) { return; }
  const auto center = threadIdx.x == 0 ? mount->foundation.card.center_selector :
      mount->foundation.card.changed_center_selector;
  auto& target = threadIdx.x == 0 ? observation->inquiry.blowup : observation->changed;
  organ::hodge_blowup_detail::derive(observation->inquiry.product,
      observation->inquiry.cycles, center, mount->foundation.card.lineage.value(), target);
}

__global__ void close_hodge(event::hodge_realization_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->changed_sensitive = observation->changed.exact &&
      observation->changed.center_selector != observation->inquiry.blowup.center_selector &&
      observation->changed.through_center[observation->changed.center_selector] &&
      !observation->changed.through_center[observation->inquiry.blowup.center_selector];
  organ::hodge_realization_detail::close(observation->inquiry, observation->changed);
}

__global__ void form_hodge(event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { static_cast<void>(production->form(*observation)); }
}

__global__ void resume_hodge(const event::checker_raw_return* raw,
    event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0) {
    static_cast<void>(production->resume(*raw, *observation));
  }
}

__global__ void rest_hodge(event::resident_hodge_realization* production,
    event::hodge_realization_rest_record* rest, event::hodge_realization_rest_record* handoff,
    event::hodge_realization_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->rest = production->rest(*rest); if (!observation->rest.returned) { return; }
  ::new (static_cast<void*>(production)) event::resident_hodge_realization{*rest, observation->remount};
  observation->final_head = production->head(); observation->final_continuation = production->continuation();
  observation->final_can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
}

__global__ void observe_hodge(const event::hodge_realization_observation* resident,
    event::hodge_realization_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_hodge_mount(const hodge_realization_mount* mount,
    event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) noexcept {
  mount_hodge<<<1,1>>>(mount, production, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_factors(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept {
  derive_factors<<<1,organ::hodge_factor_capacity>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_product(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept {
  derive_product<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_translations(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept {
  derive_translations<<<1,organ::hodge_translation_capacity>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_cycles(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept {
  derive_cycles<<<1,1>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_blowups(const hodge_realization_mount* mount,
    event::hodge_realization_observation* observation) noexcept {
  derive_blowups<<<1,2>>>(mount, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_close(event::hodge_realization_observation* observation) noexcept {
  close_hodge<<<1,1>>>(observation); return cudaGetLastError();
}
cudaError_t launch_hodge_form(event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) noexcept {
  form_hodge<<<1,1>>>(production, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_resume(const event::checker_raw_return* raw,
    event::resident_hodge_realization* production,
    event::hodge_realization_observation* observation) noexcept {
  resume_hodge<<<1,1>>>(raw, production, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_rest(event::resident_hodge_realization* production,
    event::hodge_realization_rest_record* rest, event::hodge_realization_rest_record* handoff,
    event::hodge_realization_observation* observation) noexcept {
  rest_hodge<<<1,1>>>(production, rest, handoff, observation); return cudaGetLastError();
}
cudaError_t launch_hodge_observe(const event::hodge_realization_observation* resident,
    event::hodge_realization_observation* returned) noexcept {
  observe_hodge<<<1,1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
