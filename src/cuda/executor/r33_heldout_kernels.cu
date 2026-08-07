#include <new>

#include <holonics/apparatus/characteristic_hypergeometry_resident.hpp>

namespace holonics::apparatus {
namespace {
__global__ void mount_kernel(const characteristic_application_mount *m,
                             unsigned char *s,
                             event::heldout_characteristic_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  ::new (static_cast<void *>(s)) event::resident_characteristic_hypergeometry(
      m->inherited, o->predecessor_remount);
}
__global__ void source_kernel(const characteristic_application_mount *m,
                              event::heldout_characteristic_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  organ::characteristic_matrix_detail::heldout_faces(m->heldout, o->inquiry);
  o->inquiry.passage = exact::word{200'402};
  o->inquiry.lineage = m->heldout.metadata.lineage;
}
__global__ void predict_kernel(unsigned char *s,
                               event::heldout_characteristic_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  const auto *resident =
      reinterpret_cast<event::resident_characteristic_hypergeometry *>(s);
  organ::heldout_characteristic_detail::predict(resident->organ(), o->inquiry);
}
__global__ void compare_kernel(unsigned char *s,
                               const characteristic_application_mount *m,
                               event::heldout_characteristic_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  const auto *resident =
      reinterpret_cast<event::resident_characteristic_hypergeometry *>(s);
  organ::heldout_characteristic_detail::compare(resident->organ(), m->heldout,
                                                o->inquiry);
}
__global__ void form_kernel(unsigned char *s,
                            event::heldout_characteristic_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(
        reinterpret_cast<event::resident_characteristic_hypergeometry *>(s)
            ->form_heldout(*o));
}
__global__ void resume_kernel(const event::checker_raw_return *r,
                              unsigned char *s,
                              event::heldout_characteristic_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  auto *resident =
      reinterpret_cast<event::resident_characteristic_hypergeometry *>(s);
  static_cast<void>(resident->resume_heldout(*r, *o));
  static_cast<void>(codec::render_characteristic_dossier(
      event::rested_characteristic_surface(resident->law()),
      event::heldout_characteristic_surface(o->inquiry), o->dossier));
}
__global__ void rest_kernel(unsigned char *s,
                            event::characteristic_hypergeometry_rest_record *r,
                            event::characteristic_hypergeometry_rest_record *h,
                            event::heldout_characteristic_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  auto *resident =
      reinterpret_cast<event::resident_characteristic_hypergeometry *>(s);
  o->rest = resident->rest(*r);
  event::hypergeometry_remount_receipt remount{};
  auto *resumed = ::new (static_cast<void *>(s))
      event::resident_characteristic_hypergeometry(*r, remount);
  o->remount = remount;
  o->final_head = resumed->head();
  o->final_continuation = resumed->continuation();
  o->final_can_continue = resumed->can_continue();
  o->handoff = resumed->rest(*h);
}
__global__ void observe_kernel(
    const event::heldout_characteristic_observation *s,
    event::heldout_characteristic_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    *o = *s;
}
} // namespace

cudaError_t launch_characteristic_heldout_mount(
    const characteristic_application_mount *m, unsigned char *s,
    event::heldout_characteristic_observation *o) noexcept {
  mount_kernel<<<1, 1>>>(m, s, o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_heldout_source(
    const characteristic_application_mount *m,
    event::heldout_characteristic_observation *o, cudaStream_t s) noexcept {
  source_kernel<<<1, 1, 0, s>>>(m, o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_heldout_predict(
    event::resident_characteristic_hypergeometry *r,
    event::heldout_characteristic_observation *o, cudaStream_t s) noexcept {
  predict_kernel<<<1, 1, 0, s>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_heldout_compare(
    event::resident_characteristic_hypergeometry *r,
    const characteristic_application_mount *m,
    event::heldout_characteristic_observation *o) noexcept {
  compare_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), m, o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_heldout_form(
    event::resident_characteristic_hypergeometry *r,
    event::heldout_characteristic_observation *o) noexcept {
  form_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_heldout_resume(
    const event::checker_raw_return *x,
    event::resident_characteristic_hypergeometry *r,
    event::heldout_characteristic_observation *o) noexcept {
  resume_kernel<<<1, 1>>>(x, reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_heldout_rest(
    event::resident_characteristic_hypergeometry *r,
    event::characteristic_hypergeometry_rest_record *a,
    event::characteristic_hypergeometry_rest_record *b,
    event::heldout_characteristic_observation *o) noexcept {
  rest_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), a, b, o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_heldout_observe(
    const event::heldout_characteristic_observation *s,
    event::heldout_characteristic_observation *o) noexcept {
  observe_kernel<<<1, 1>>>(s, o);
  return cudaGetLastError();
}

} // namespace holonics::apparatus
