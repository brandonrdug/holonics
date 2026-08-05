#include <new>

#include <holonics/apparatus/trace_fiber_resident.hpp>

namespace holonics::apparatus {
namespace {
__global__ void mount_kernel(const trace_fiber_application_mount *m,
                             unsigned char *s,
                             event::heldout_trace_fiber_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  ::new (static_cast<void *>(s))
      event::resident_trace_fiber(m->inherited, o->predecessor_remount);
}
__global__ void source_kernel(const trace_fiber_application_mount *m,
                              trace_source_secret *secret) {
  if (!blockIdx.x && !threadIdx.x)
    organ::trace_fiber_matrix_detail::form_heldout(m->heldout, *secret);
}
__global__ void expose_kernel(
    const trace_source_secret *secret,
    event::heldout_trace_fiber_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  organ::heldout_trace_fiber_detail::expose(*secret, o->inquiry);
  o->inquiry.passage = exact::word{201'402};
}
__global__ void predict_kernel(unsigned char *s,
                               event::heldout_trace_fiber_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  const auto *resident = reinterpret_cast<event::resident_trace_fiber *>(s);
  organ::heldout_trace_fiber_detail::predict(resident->organ(0),
                                              resident->organ(1), o->inquiry);
}
__global__ void compare_kernel(
    unsigned char *s, const trace_fiber_application_mount *m,
    const trace_source_secret *secret,
    event::heldout_trace_fiber_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  const auto *resident = reinterpret_cast<event::resident_trace_fiber *>(s);
  organ::heldout_trace_fiber_detail::compare(
      resident->organ(0), resident->organ(1), m->heldout, *secret, o->inquiry);
}
__global__ void form_kernel(unsigned char *s,
                            event::heldout_trace_fiber_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(reinterpret_cast<event::resident_trace_fiber *>(s)
                          ->form_heldout(*o));
}
__global__ void resume_kernel(const event::checker_raw_return *r,
                              unsigned char *s,
                              event::heldout_trace_fiber_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  auto *resident = reinterpret_cast<event::resident_trace_fiber *>(s);
  static_cast<void>(resident->resume_heldout(*r, *o));
  static_cast<void>(codec::render_trace_fiber_dossier(
      event::rested_trace_fiber_surface(resident->law()),
      event::heldout_trace_fiber_surface(o->inquiry), o->dossier));
}
__global__ void rest_kernel(unsigned char *s, event::trace_fiber_rest_record *r,
                            event::trace_fiber_rest_record *h,
                            event::heldout_trace_fiber_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  auto *resident = reinterpret_cast<event::resident_trace_fiber *>(s);
  o->rest = resident->rest(*r);
  event::trace_fiber_remount_receipt remount{};
  auto *resumed = ::new (static_cast<void *>(s))
      event::resident_trace_fiber(*r, remount);
  o->remount = remount;
  o->final_head = resumed->head();
  o->final_continuation = resumed->continuation();
  o->final_can_continue = resumed->can_continue();
  o->handoff = resumed->rest(*h);
}
__global__ void observe_kernel(
    const event::heldout_trace_fiber_observation *source,
    event::heldout_trace_fiber_observation *out) {
  if (!blockIdx.x && !threadIdx.x)
    *out = *source;
}
} // namespace

cudaError_t launch_trace_fiber_heldout_mount(
    const trace_fiber_application_mount *m, unsigned char *s,
    event::heldout_trace_fiber_observation *o) noexcept {
  mount_kernel<<<1, 1>>>(m, s, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_source(
    const trace_fiber_application_mount *m, trace_source_secret *secret,
    cudaStream_t s) noexcept {
  source_kernel<<<1, 1, 0, s>>>(m, secret);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_expose(
    const trace_source_secret *secret,
    event::heldout_trace_fiber_observation *o, cudaStream_t s) noexcept {
  expose_kernel<<<1, 1, 0, s>>>(secret, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_predict(
    event::resident_trace_fiber *r,
    event::heldout_trace_fiber_observation *o, cudaStream_t s) noexcept {
  predict_kernel<<<1, 1, 0, s>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_compare(
    event::resident_trace_fiber *r, const trace_fiber_application_mount *m,
    const trace_source_secret *secret,
    event::heldout_trace_fiber_observation *o) noexcept {
  compare_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), m, secret, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_form(
    event::resident_trace_fiber *r,
    event::heldout_trace_fiber_observation *o) noexcept {
  form_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_resume(
    const event::checker_raw_return *x, event::resident_trace_fiber *r,
    event::heldout_trace_fiber_observation *o) noexcept {
  resume_kernel<<<1, 1>>>(x, reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_rest(
    event::resident_trace_fiber *r, event::trace_fiber_rest_record *a,
    event::trace_fiber_rest_record *b,
    event::heldout_trace_fiber_observation *o) noexcept {
  rest_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), a, b, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_heldout_observe(
    const event::heldout_trace_fiber_observation *s,
    event::heldout_trace_fiber_observation *o) noexcept {
  observe_kernel<<<1, 1>>>(s, o);
  return cudaGetLastError();
}
} // namespace holonics::apparatus
