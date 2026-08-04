#include <cstddef>
#include <new>

#include <cuda_runtime.h>

#include <holonics/apparatus/mathematical_ecology_resident.hpp>

namespace holonics::apparatus {
namespace {

[[nodiscard]] __device__ bool same_semantic_neighborhood(
    const organ::mathematical_neighborhood_receipt& left,
    const organ::mathematical_neighborhood_receipt& right) noexcept {
  if (left.environment != right.environment ||
      left.source_material_testimony != right.source_material_testimony ||
      left.intersection_type != right.intersection_type || left.proof_term != right.proof_term ||
      left.proof_provenance != right.proof_provenance ||
      left.declaration_count != right.declaration_count ||
      left.dependency_count != right.dependency_count ||
      left.dependency_joins != right.dependency_joins ||
      left.transport_alternatives != right.transport_alternatives ||
      left.substitutions != right.substitutions || left.unknown_count != right.unknown_count ||
      left.obstruction != right.obstruction || left.term_match != right.term_match ||
      left.constraint_intersection != right.constraint_intersection ||
      left.proof_structurally_closed != right.proof_structurally_closed ||
      left.inherited_checked_example != right.inherited_checked_example ||
      left.goal_open != right.goal_open || left.source_detached != right.source_detached) {
    return false;
  }
  for (std::size_t slot = 0; slot < left.declaration_count; ++slot) {
    if (left.declaration_ids[slot] != right.declaration_ids[slot]) { return false; }
  }
  for (std::size_t slot = 0; slot < left.dependency_count; ++slot) {
    if (left.dependency_lineages[slot] != right.dependency_lineages[slot]) { return false; }
  }
  return true;
}

__global__ void mount_ecologies(
    const mathematical_ecology_mount* mount,
    event::resident_mathematical_ecology* canonical,
    event::resident_mathematical_ecology* reordered,
    mathematical_ecology_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  ::new (static_cast<void*>(canonical)) event::resident_mathematical_ecology{
      mount->canonical, mount->canonical_body_seed, mount->regions, true};
  ::new (static_cast<void*>(reordered)) event::resident_mathematical_ecology{
      mount->reordered, mount->reordered_body_seed, mount->regions, true};
  observation->canonical_mount = canonical->obstruction();
  observation->reordered_mount = reordered->obstruction();
}

__global__ void reconstruct_neighborhoods(
    const mathematical_ecology_mount* mount,
    const event::resident_mathematical_ecology* canonical,
    const event::resident_mathematical_ecology* reordered,
    mathematical_ecology_observation* observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0) { return; }
  observation->canonical = canonical->reconstruct(mount->held_out);
  observation->reordered = reordered->reconstruct(mount->held_out);
  observation->mismatch = canonical->reconstruct(mount->mismatch);
  observation->unsolved = canonical->reconstruct(mount->unsolved);
  observation->storage_order_invariant =
      same_semantic_neighborhood(observation->canonical, observation->reordered);
  observation->source_detached = observation->canonical.source_detached &&
      observation->reordered.source_detached;
  observation->exact_material_comparison =
      canonical->foundation().source_material_testimony ==
      reordered->foundation().source_material_testimony;
  observation->local_incidence_only = observation->canonical.global_declaration_scans == 0 &&
      observation->reordered.global_declaration_scans == 0;
  observation->final_continuations_valid = canonical->can_continue() && reordered->can_continue();
}

__global__ void observe_ecology(
    const mathematical_ecology_observation* resident,
    mathematical_ecology_observation* returned) {
  if (blockIdx.x == 0 && threadIdx.x == 0) { *returned = *resident; }
}

}  // namespace

cudaError_t launch_mathematical_ecology_mount(
    const mathematical_ecology_mount* mount,
    event::resident_mathematical_ecology* canonical,
    event::resident_mathematical_ecology* reordered,
    mathematical_ecology_observation* observation) noexcept {
  mount_ecologies<<<1, 1>>>(mount, canonical, reordered, observation);
  return cudaGetLastError();
}

cudaError_t launch_mathematical_ecology_reconstruction(
    const mathematical_ecology_mount* mount,
    const event::resident_mathematical_ecology* canonical,
    const event::resident_mathematical_ecology* reordered,
    mathematical_ecology_observation* observation) noexcept {
  reconstruct_neighborhoods<<<1, 1>>>(mount, canonical, reordered, observation);
  return cudaGetLastError();
}

cudaError_t launch_mathematical_ecology_observe(
    const mathematical_ecology_observation* resident,
    mathematical_ecology_observation* returned) noexcept {
  observe_ecology<<<1, 1>>>(resident, returned);
  return cudaGetLastError();
}

}  // namespace holonics::apparatus
