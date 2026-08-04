#include <new>

#include <holonics/apparatus/terminal_theorem_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void stage_terminal_theorem(const terminal_theorem_mount* mount,
    event::theorem_production_rest_record* projected,
    event::resident_dependent_theorem_production* production,
    event::resident_dependent_theorem_production* ablation,
    event::terminal_theorem_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->setup_integrity_exact =
      mount->setup.integrity == event::dependent_setup_integrity(mount->setup);
  observation->exclusion =
      event::exclude_returned_theorem_fiber(mount->inherited, *projected);
  ::new (static_cast<void*>(ablation)) event::resident_dependent_theorem_production{
      mount->foundation, *projected, observation->ablation_remount};
  observation->ablation_generation_refused =
      !ablation->attempt(mount->setup, observation->ablated_generation) &&
      observation->ablated_generation.obstruction ==
          organ::theorem_production_obstruction::returned_fiber_absent;
  observation->ablation_source_bytes = 0;
  ::new (static_cast<void*>(production)) event::resident_dependent_theorem_production{
      mount->foundation, mount->inherited, observation->production_remount};
  const bool generated = production->generate_and_stage(mount->setup, *observation);
  observation->source_detached = true;
  observation->dependency_exact = generated && observation->setup_integrity_exact &&
      observation->exclusion.exact && observation->ablation_generation_refused &&
      observation->generation.dependency_exact &&
      observation->generation.inherited_returned_fiber ==
          observation->exclusion.excluded_fiber;
}

__global__ void resume_terminal_theorem(const event::checker_raw_return* returned,
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  static_cast<void>(production->resume(*returned, *observation));
}

__global__ void rest_terminal_theorem(
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_rest_record* rest,
    event::terminal_theorem_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->generation.exclusion.source_detached_at_rest = true;
  observation->rest = production->rest(*rest);
}

__global__ void remount_terminal_theorem(const terminal_theorem_mount* mount,
    const event::terminal_theorem_rest_record* rest,
    event::terminal_theorem_rest_record* handoff,
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_dependent_theorem_production{
      mount->foundation, *rest, observation->remount};
  observation->final_head = production->head();
  observation->final_continuation = exact::word{rest->body.continuation};
  const bool can_continue = production->can_continue();
  observation->handoff = production->rest(*handoff);
  observation->handoff_continuation_valid =
      can_continue && observation->handoff.returned && handoff->body.continuation != 0;
}

__global__ void observe_terminal_theorem(
    const event::terminal_theorem_observation* resident,
    event::terminal_theorem_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_terminal_theorem_stage(const terminal_theorem_mount* mount,
    event::theorem_production_rest_record* projected,
    event::resident_dependent_theorem_production* production,
    event::resident_dependent_theorem_production* ablation,
    event::terminal_theorem_observation* observation) noexcept {
  stage_terminal_theorem<<<1, 1>>>(mount, projected, production, ablation, observation);
  return cudaGetLastError();
}

cudaError_t launch_terminal_theorem_resume(const event::checker_raw_return* returned,
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_observation* observation) noexcept {
  resume_terminal_theorem<<<1, 1>>>(returned, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_terminal_theorem_rest(
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_rest_record* rest,
    event::terminal_theorem_observation* observation) noexcept {
  rest_terminal_theorem<<<1, 1>>>(production, rest, observation);
  return cudaGetLastError();
}

cudaError_t launch_terminal_theorem_remount(const terminal_theorem_mount* mount,
    const event::terminal_theorem_rest_record* rest,
    event::terminal_theorem_rest_record* handoff,
    event::resident_dependent_theorem_production* production,
    event::terminal_theorem_observation* observation) noexcept {
  remount_terminal_theorem<<<1, 1>>>(mount, rest, handoff, production, observation);
  return cudaGetLastError();
}

cudaError_t launch_terminal_theorem_observe(
    const event::terminal_theorem_observation* resident,
    event::terminal_theorem_observation* returned) noexcept {
  observe_terminal_theorem<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
