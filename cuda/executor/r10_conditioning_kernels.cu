#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/conditioning_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_production(
    const conditioning_foundation* foundation,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_conditioned_organ{
      foundation->morphology, foundation->production_seed, foundation->regions, true};
  observation->obstruction = production->obstruction();
  observation->mounting = production->mounting();
}

__global__ void train_production(
    const conditioning_passage* passage,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->before = production->probe(*held_out);
  observation->exposure = production->expose(passage->exposure);
  observation->reference = production->consult(passage->reference);
  observation->training = production->train(passage->training);
  if (observation->training.obstruction != organ::conditioning_obstruction::none) {
    observation->obstruction = observation->training.obstruction;
  }
}

__global__ void rest_production(
    event::resident_conditioned_organ* production,
    event::conditioned_organ_rest_record* rest,
    conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->source_access.reusable_native_morphology =
      production->morphology().response_weight == observation->training.after.response_weight;
  observation->source_access.source_detached = true;
  observation->rest = production->rest(*rest);
  if (observation->rest.obstruction != organ::conditioning_obstruction::none) {
    observation->obstruction = observation->rest.obstruction;
  }
}

__global__ void remount_production(
    const event::conditioned_organ_rest_record* rest,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(production)) event::resident_conditioned_organ{
      *rest, observation->remount};
  observation->after = production->probe(*held_out);
  observation->final_head = production->head();
  observation->final_region = production->region(0);
  observation->final_continuation_valid = production->can_continue();
  observation->behavior_changed =
      observation->before.consequence.response != observation->after.consequence.response &&
      observation->before.consequence.incidence != observation->after.consequence.incidence &&
      observation->before.consequence.transport != observation->after.consequence.transport &&
      observation->before.consequence.codec != observation->after.consequence.codec &&
      observation->before.consequence.obstruction != observation->after.consequence.obstruction;
}

__global__ void found_ablation(
    const conditioning_foundation* foundation,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* ablation,
    conditioning_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(ablation)) event::resident_conditioned_organ{
      foundation->morphology, foundation->ablation_seed, foundation->regions, true};
  observation->ablation.production_body = observation->final_head;
  observation->ablation.ablation_body = ablation->head();
  observation->ablation.excluded = observation->training.delta;
  observation->ablation.production = observation->after;
  observation->ablation.ablated = ablation->probe(*held_out);
  observation->ablation.separately_founded =
      observation->ablation.production_body != observation->ablation.ablation_body;
  observation->ablation.consequence_lost =
      observation->ablation.ablated.consequence.response ==
          observation->before.consequence.response &&
      observation->ablation.ablated.consequence.obstruction ==
          observation->before.consequence.obstruction &&
      observation->ablation.ablated.consequence.response !=
          observation->ablation.production.consequence.response;
}

__global__ void observe_conditioning(
    const conditioning_observation* resident,
    conditioning_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_conditioning_mount(const conditioning_foundation* foundation,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) noexcept {
  mount_production<<<1, 1>>>(foundation, production, observation); return cudaGetLastError();
}
cudaError_t launch_conditioning_train(const conditioning_passage* passage,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) noexcept {
  train_production<<<1, 1>>>(passage, held_out, production, observation); return cudaGetLastError();
}
cudaError_t launch_conditioning_rest(event::resident_conditioned_organ* production,
    event::conditioned_organ_rest_record* rest,
    conditioning_observation* observation) noexcept {
  rest_production<<<1, 1>>>(production, rest, observation); return cudaGetLastError();
}
cudaError_t launch_conditioning_remount(const event::conditioned_organ_rest_record* rest,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* production,
    conditioning_observation* observation) noexcept {
  remount_production<<<1, 1>>>(rest, held_out, production, observation); return cudaGetLastError();
}
cudaError_t launch_conditioning_ablation(const conditioning_foundation* foundation,
    const receiver::conditioning_question* held_out,
    event::resident_conditioned_organ* ablation,
    conditioning_observation* observation) noexcept {
  found_ablation<<<1, 1>>>(foundation, held_out, ablation, observation); return cudaGetLastError();
}
cudaError_t launch_conditioning_observe(const conditioning_observation* resident,
    conditioning_observation* returned) noexcept {
  observe_conditioning<<<1, 1>>>(resident, returned); return cudaGetLastError();
}

}  // namespace holonics::apparatus
