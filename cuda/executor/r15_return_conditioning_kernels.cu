#include <new>

#include <holonics/apparatus/return_conditioning_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_returned_body(const return_conditioning_mount* mount,
    event::resident_theorem_production* production,
    event::return_conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_theorem_production{
      mount->foundation, mount->inherited, observation->production_remount};
  observation->production = production->probe(mount->question, false);
  observation->production_head = production->head();
  observation->source_detached = true;
}

__global__ void project_and_probe_ablation(const return_conditioning_mount* mount,
    event::theorem_production_rest_record* projected,
    event::resident_theorem_production* ablation,
    event::dependent_theorem_setup* setup,
    event::return_conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->exclusion = event::exclude_returned_theorem_fiber(mount->inherited, *projected);
  ::new (static_cast<void*>(ablation)) event::resident_theorem_production{
      mount->foundation, *projected, observation->ablation_remount};
  observation->ablated = ablation->probe(mount->question, false);
  observation->ablation_head = ablation->head();
  *setup = {mount->question, exact::word{152'200}, exact::word{162'200},
      exact::word{172'200}, exact::word{182'200}, observation->production.consequence,
      2, true, true, observation->production.available && !observation->ablated.available, 0};
  setup->integrity = event::dependent_setup_integrity(*setup);
  observation->setup = *setup;
  observation->behavior_changed = observation->production.available &&
      !observation->ablated.available &&
      observation->production.consequence != observation->ablated.consequence;
  observation->dependency_exact = observation->exclusion.exact &&
      setup->question.required_returned_fiber == observation->exclusion.excluded_fiber &&
      setup->factors_through_returned_fiber;
}

__global__ void rest_returned_body(event::resident_theorem_production* production,
    event::theorem_production_rest_record* handoff,
    event::return_conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->handoff = production->rest(*handoff);
  observation->handoff_continuation_valid =
      observation->handoff.returned && handoff->body.continuation != 0;
}

__global__ void observe_conditioning(
    const event::return_conditioning_observation* resident,
    event::return_conditioning_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_return_conditioning_mount(const return_conditioning_mount* mount,
    event::resident_theorem_production* production,
    event::return_conditioning_observation* observation) noexcept {
  mount_returned_body<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_return_conditioning_ablation(const return_conditioning_mount* mount,
    event::theorem_production_rest_record* projected,
    event::resident_theorem_production* ablation,
    event::dependent_theorem_setup* setup,
    event::return_conditioning_observation* observation) noexcept {
  project_and_probe_ablation<<<1, 1>>>(mount, projected, ablation, setup, observation);
  return cudaGetLastError();
}

cudaError_t launch_return_conditioning_rest(event::resident_theorem_production* production,
    event::theorem_production_rest_record* handoff,
    event::return_conditioning_observation* observation) noexcept {
  rest_returned_body<<<1, 1>>>(production, handoff, observation); return cudaGetLastError();
}

cudaError_t launch_return_conditioning_observe(
    const event::return_conditioning_observation* resident,
    event::return_conditioning_observation* returned) noexcept {
  observe_conditioning<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
