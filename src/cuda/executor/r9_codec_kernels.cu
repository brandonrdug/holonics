#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/reflective_codec_resident.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_codec(
    const reflective_codec_mount* mount,
    event::resident_reflective_codec* body,
    reflective_codec_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(body)) event::resident_reflective_codec{
      mount->environment, mount->body_seed, mount->regions, mount->source_detached};
  observation->obstruction = body->obstruction();
  observation->storage_semantics_invariant =
      mount->original_material == mount->relocated_material &&
      mount->original_path != mount->relocated_path;
  observation->source_detached = mount->source_detached && body->source_detached();
}

__global__ void revise_and_rest(
    const reflective_codec_deed* deed,
    event::resident_reflective_codec* body,
    event::reflective_codec_rest_record* rest,
    reflective_codec_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->before = body->behavior(
      deed->probe, deed->render_core, 90'100U, 90'200U);
  observation->reflection = body->reflect(
      deed->reflection_occurrence, deed->reflection_lineage);
  observation->revision = body->apply_revision(
      deed->revision, observation->reflection, deed->probe);
  observation->rest = body->rest(*rest);
  observation->reflection_exact =
      observation->reflection.obstruction == codec::codec_obstruction::none &&
      observation->reflection.continuation.pending &&
      observation->reflection.continuation.reified_view_only &&
      !observation->reflection.environment_cloned &&
      !observation->reflection.continuation_cloned;
  observation->syntax_not_core_identity =
      observation->before.parsed.source_face !=
          observation->before.unrelated_parsed.source_face &&
      observation->before.parsed.input.first !=
          observation->before.unrelated_parsed.input.first &&
      observation->before.parsed.core_value ==
          observation->before.unrelated_parsed.core_value &&
      observation->before.parsed.core_occurrence ==
          observation->before.unrelated_parsed.core_occurrence;
}

__global__ void remount_codec(
    const reflective_codec_deed* deed,
    const event::reflective_codec_rest_record* rest,
    event::resident_reflective_codec* body,
    reflective_codec_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(body)) event::resident_reflective_codec{
      *rest, observation->remount};
  observation->after = body->behavior(
      deed->probe, deed->render_core, 90'300U, 90'400U);
  observation->final_head = body->head();
  observation->final_region = body->region(0);
  observation->revision_changed_conduct = observation->revision.committed &&
      observation->before.parsed.core_value != observation->after.parsed.core_value &&
      observation->before.parsed.version != observation->after.parsed.version &&
      observation->before.transduced.output.second !=
          observation->after.transduced.output.second;
  observation->same_body_remounted = observation->remount.same_body &&
      !observation->remount.source_replayed &&
      observation->revision.successor == observation->final_head;
  observation->local_law_without_registry =
      codec::valid_program(body->environment().operative) &&
      codec::valid_program(body->environment().unrelated);
  if (observation->revision.obstruction != codec::codec_obstruction::none ||
      observation->rest.obstruction != codec::codec_obstruction::none ||
      observation->remount.obstruction != codec::codec_obstruction::none) {
    observation->obstruction = codec::codec_obstruction::rest_refused;
  }
}

__global__ void observe_codec(
    const reflective_codec_observation* resident,
    reflective_codec_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_reflective_codec_mount(
    const reflective_codec_mount* mount,
    event::resident_reflective_codec* body,
    reflective_codec_observation* observation) noexcept {
  mount_codec<<<1, 1>>>(mount, body, observation);
  return cudaGetLastError();
}

cudaError_t launch_reflective_codec_revise_rest(
    const reflective_codec_deed* deed,
    event::resident_reflective_codec* body,
    event::reflective_codec_rest_record* rest,
    reflective_codec_observation* observation) noexcept {
  revise_and_rest<<<1, 1>>>(deed, body, rest, observation);
  return cudaGetLastError();
}

cudaError_t launch_reflective_codec_remount(
    const reflective_codec_deed* deed,
    const event::reflective_codec_rest_record* rest,
    event::resident_reflective_codec* body,
    reflective_codec_observation* observation) noexcept {
  remount_codec<<<1, 1>>>(deed, rest, body, observation);
  return cudaGetLastError();
}

cudaError_t launch_reflective_codec_observe(
    const reflective_codec_observation* resident,
    reflective_codec_observation* returned) noexcept {
  observe_codec<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
