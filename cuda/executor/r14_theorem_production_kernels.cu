#include <new>

#include <holonics/apparatus/theorem_production_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void stage_production(const theorem_production_mount* mount,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_theorem_production{
      mount->foundation, mount->body_seed, mount->regions,
      mount->mathematical_admitted_tally, mount->codec_admitted_tally};
  observation->before = production->probe(mount->held_probe, false);
  static_cast<void>(production->generate_and_stage(mount->question, *observation));
}

__global__ void resume_production(const event::checker_raw_return* returned,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_production(event::resident_theorem_production* production,
    event::theorem_production_rest_record* rest,
    event::theorem_production_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->generation.exclusion.source_detached_at_rest = true;
  observation->rest = production->rest(*rest);
}

__global__ void remount_probe(const theorem_production_mount* mount,
    const event::theorem_production_rest_record* rest,
    event::theorem_production_rest_record* handoff,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_theorem_production{
      mount->foundation, *rest, observation->remount};
  observation->after = production->probe(mount->held_probe, false);
  observation->ablation.excluded_delta = production->acquired().admitted_tally_delta;
  observation->ablation.excluded_fiber = production->acquired().identity;
  observation->ablation.production = observation->after;
  observation->ablation.ablated = production->probe(mount->held_probe, true);
  observation->ablation.exact_exclusion =
      observation->ablation.excluded_fiber == mount->held_probe.required_returned_fiber;
  observation->ablation.consequence_lost = observation->after.available &&
      !observation->ablation.ablated.available &&
      observation->ablation.ablated.consequence != observation->after.consequence;
  observation->behavior_changed = !observation->before.available &&
      observation->after.available &&
      observation->before.obstruction ==
          organ::theorem_production_obstruction::returned_fiber_absent &&
      observation->after.obstruction == organ::theorem_production_obstruction::none;
  observation->final_head = production->head();
  observation->final_continuation = exact::word{rest->body.continuation};
  observation->handoff = production->rest(*handoff);
  observation->handoff_continuation_valid = observation->handoff.returned &&
      handoff->body.continuation != 0;
}

__global__ void observe_production(
    const event::theorem_production_observation* resident,
    event::theorem_production_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_theorem_production_stage(const theorem_production_mount* mount,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) noexcept {
  stage_production<<<1, 1>>>(mount, production, observation); return cudaGetLastError();
}

cudaError_t launch_theorem_production_resume(const event::checker_raw_return* returned,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) noexcept {
  resume_production<<<1, 1>>>(returned, production, observation); return cudaGetLastError();
}

cudaError_t launch_theorem_production_rest(event::resident_theorem_production* production,
    event::theorem_production_rest_record* rest,
    event::theorem_production_observation* observation) noexcept {
  rest_production<<<1, 1>>>(production, rest, observation); return cudaGetLastError();
}

cudaError_t launch_theorem_production_remount_probe(const theorem_production_mount* mount,
    const event::theorem_production_rest_record* rest,
    event::theorem_production_rest_record* handoff,
    event::resident_theorem_production* production,
    event::theorem_production_observation* observation) noexcept {
  remount_probe<<<1, 1>>>(mount, rest, handoff, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_theorem_production_observe(
    const event::theorem_production_observation* resident,
    event::theorem_production_observation* returned) noexcept {
  observe_production<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
