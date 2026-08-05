#include <new>

#include <holonics/apparatus/rederivation_resident.hpp>
#include <holonics/organ/rederivation_realization_law.hpp>

namespace holonics::apparatus {
namespace {

__global__ void mount_kernel(const rederivation_mount *mount,
                             unsigned char *production,
                             event::rederivation_observation *observation) {
  if (blockIdx.x != 0 || threadIdx.x != 0)
    return;
  auto *resident = ::new (static_cast<void *>(production))
      event::resident_rederivation(mount->foundation, mount->inherited,
                                   observation->predecessor_remount);
  observation->inquiry.matching_card = mount->foundation.matching;
  observation->inquiry.lattice_card = mount->foundation.lattice;
  observation->inquiry.cover_card = mount->foundation.cover;
  observation->inquiry.question = mount->question;
  if (!resident->admitted())
    observation->inquiry.obstruction =
        organ::rederivation_obstruction::card_refused;
}

__global__ void matching_kernel(event::rederivation_observation *observation,
                                organ::rederivation_workspace *workspace) {
  const auto i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < organ::rederivation_jacobian_count)
    organ::rederivation_matching_detail::derive_entry(
        observation->inquiry.matching_card, i, workspace->jacobian[i]);
}
__global__ void
matching_close_kernel(event::rederivation_observation *observation,
                      organ::rederivation_workspace *workspace) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    organ::rederivation_matching_detail::close(
        observation->inquiry.matching_card, *workspace,
        observation->inquiry.matching);
}
__global__ void geometry_kernel(event::rederivation_observation *observation,
                                organ::rederivation_workspace *workspace) {
  const auto i = blockIdx.x * blockDim.x + threadIdx.x;
  if (i < organ::rederivation_polygon_count)
    organ::rederivation_geometry_detail::derive_polygon(
        static_cast<std::uint8_t>(i), observation->inquiry.lattice_card,
        *workspace, observation->inquiry.polygons[i]);
}
__global__ void cover_kernel(event::rederivation_observation *observation,
                             organ::rederivation_workspace *workspace) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    organ::rederivation_cover_detail::derive(observation->inquiry.cover_card,
                                             *workspace,
                                             observation->inquiry.cover);
}
__global__ void compose_kernel(event::rederivation_observation *observation,
                               organ::rederivation_workspace *workspace) {
  if (blockIdx.x || threadIdx.x)
    return;
  organ::rederivation_potential_detail::derive(
      observation->inquiry.lattice_card, observation->inquiry.polygons[1],
      *workspace, observation->inquiry.potential);
  organ::rederivation_realization_detail::close(observation->inquiry);
}
__global__ void form_foil_kernel(unsigned char *production,
                                 event::rederivation_observation *observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    static_cast<void>(
        reinterpret_cast<event::resident_rederivation *>(production)
            ->form_foil(*observation));
}
__global__ void
resume_foil_kernel(const event::checker_raw_return *raw,
                   unsigned char *production,
                   event::rederivation_observation *observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    static_cast<void>(
        reinterpret_cast<event::resident_rederivation *>(production)
            ->resume_foil(*raw, *observation));
}
__global__ void
form_valid_kernel(unsigned char *production,
                  event::rederivation_observation *observation,
                  const organ::rederivation_workspace *workspace) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    static_cast<void>(
        reinterpret_cast<event::resident_rederivation *>(production)
            ->form_valid(*observation, *workspace));
}
__global__ void
resume_valid_kernel(const event::checker_raw_return *raw,
                    unsigned char *production,
                    event::rederivation_observation *observation) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    static_cast<void>(
        reinterpret_cast<event::resident_rederivation *>(production)
            ->resume_valid(*raw, *observation));
}
__global__ void rest_kernel(unsigned char *production,
                            event::rederivation_rest_record *rest,
                            event::rederivation_rest_record *handoff,
                            event::rederivation_observation *observation) {
  if (blockIdx.x || threadIdx.x)
    return;
  auto *resident = reinterpret_cast<event::resident_rederivation *>(production);
  observation->rest = resident->rest(*rest);
  event::rederivation_remount_receipt remount{};
  auto *resumed = ::new (static_cast<void *>(production))
      event::resident_rederivation(*rest, remount);
  observation->remount = remount;
  observation->final_head = resumed->head();
  observation->final_continuation = resumed->continuation();
  observation->final_can_continue = resumed->can_continue();
  observation->handoff = resumed->rest(*handoff);
}
__global__ void observe_kernel(const event::rederivation_observation *source,
                               event::rederivation_observation *destination) {
  if (blockIdx.x == 0 && threadIdx.x == 0)
    *destination = *source;
}

} // namespace

cudaError_t
launch_rederivation_mount(const rederivation_mount *m, unsigned char *p,
                          event::rederivation_observation *o) noexcept {
  mount_kernel<<<1, 1>>>(m, p, o);
  return cudaGetLastError();
}
cudaError_t launch_rederivation_matching(event::resident_rederivation *,
                                         event::rederivation_observation *o,
                                         organ::rederivation_workspace *w,
                                         cudaStream_t stream) noexcept {
  matching_kernel<<<10, 256, 0, stream>>>(o, w);
  return cudaGetLastError();
}
cudaError_t
launch_rederivation_matching_close(event::resident_rederivation *,
                                   event::rederivation_observation *o,
                                   organ::rederivation_workspace *w) noexcept {
  matching_close_kernel<<<1, 1>>>(o, w);
  return cudaGetLastError();
}
cudaError_t launch_rederivation_geometry(event::resident_rederivation *,
                                         event::rederivation_observation *o,
                                         organ::rederivation_workspace *w,
                                         cudaStream_t stream) noexcept {
  geometry_kernel<<<1, 4, 0, stream>>>(o, w);
  return cudaGetLastError();
}
cudaError_t launch_rederivation_cover(event::resident_rederivation *,
                                      event::rederivation_observation *o,
                                      organ::rederivation_workspace *w,
                                      cudaStream_t stream) noexcept {
  cover_kernel<<<1, 1, 0, stream>>>(o, w);
  return cudaGetLastError();
}
cudaError_t
launch_rederivation_compose(event::resident_rederivation *,
                            event::rederivation_observation *o,
                            organ::rederivation_workspace *w) noexcept {
  compose_kernel<<<1, 1>>>(o, w);
  return cudaGetLastError();
}
cudaError_t
launch_rederivation_form_foil(event::resident_rederivation *p,
                              event::rederivation_observation *o) noexcept {
  form_foil_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(p), o);
  return cudaGetLastError();
}
cudaError_t
launch_rederivation_resume_foil(const event::checker_raw_return *r,
                                event::resident_rederivation *p,
                                event::rederivation_observation *o) noexcept {
  resume_foil_kernel<<<1, 1>>>(r, reinterpret_cast<unsigned char *>(p), o);
  return cudaGetLastError();
}
cudaError_t launch_rederivation_form_valid(
    event::resident_rederivation *p, event::rederivation_observation *o,
    const organ::rederivation_workspace *w) noexcept {
  form_valid_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(p), o, w);
  return cudaGetLastError();
}
cudaError_t
launch_rederivation_resume_valid(const event::checker_raw_return *r,
                                 event::resident_rederivation *p,
                                 event::rederivation_observation *o) noexcept {
  resume_valid_kernel<<<1, 1>>>(r, reinterpret_cast<unsigned char *>(p), o);
  return cudaGetLastError();
}
cudaError_t
launch_rederivation_rest(event::resident_rederivation *p,
                         event::rederivation_rest_record *r,
                         event::rederivation_rest_record *h,
                         event::rederivation_observation *o) noexcept {
  rest_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(p), r, h, o);
  return cudaGetLastError();
}
cudaError_t
launch_rederivation_observe(const event::rederivation_observation *s,
                            event::rederivation_observation *d) noexcept {
  observe_kernel<<<1, 1>>>(s, d);
  return cudaGetLastError();
}

} // namespace holonics::apparatus
