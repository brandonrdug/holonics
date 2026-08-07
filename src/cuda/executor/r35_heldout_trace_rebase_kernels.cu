#include <new>

#include <holonics/apparatus/trace_rebase_resident.hpp>

namespace holonics::apparatus {
namespace {
__global__ void mount_kernel(const trace_rebase_application_mount *m,
                             unsigned char *s,
                             event::heldout_trace_rebase_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    ::new (static_cast<void *>(s))
        event::resident_trace_rebase(m->inherited, o->predecessor_remount);
}
__global__ void source_kernel(const trace_rebase_application_mount *m,
                              trace_rebase_source_secret *secret) {
  if (!blockIdx.x && !threadIdx.x)
    organ::heldout_trace_rebase_detail::form_source(m->heldout, *secret);
}
__global__ void expose_kernel(const trace_rebase_source_secret *secret,
                              event::heldout_trace_rebase_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    organ::heldout_trace_rebase_detail::expose(*secret, o->inquiry);
}
__global__ void predict_kernel(unsigned char *s,
                               const trace_rebase_application_mount *m,
                               event::heldout_trace_rebase_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  const auto *resident = reinterpret_cast<event::resident_trace_rebase *>(s);
  organ::heldout_trace_rebase_detail::predict(
      m->heldout, resident->fiber().organs, resident->law().maps, o->inquiry);
}
__global__ void compare_kernel(unsigned char *s,
                               const trace_rebase_source_secret *secret,
                               event::heldout_trace_rebase_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  static_cast<void>(s);
  organ::heldout_trace_rebase_detail::compare(*secret, o->inquiry);
}
__global__ void form_kernel(unsigned char *s,
                            event::heldout_trace_rebase_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(reinterpret_cast<event::resident_trace_rebase *>(s)
                          ->form_heldout(*o));
}
__global__ void resume_kernel(const event::checker_raw_return *r,
                              unsigned char *s,
                              event::heldout_trace_rebase_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  auto *resident = reinterpret_cast<event::resident_trace_rebase *>(s);
  static_cast<void>(resident->resume_heldout(*r, *o));
  static_cast<void>(codec::render_trace_rebase_dossier(
      event::rested_trace_rebase_surface(resident->law()),
      event::heldout_trace_rebase_surface(o->inquiry), o->dossier));
}
__global__ void rest_kernel(unsigned char *s, event::trace_rebase_rest_record *r,
                            event::trace_rebase_rest_record *h,
                            event::heldout_trace_rebase_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  auto *resident = reinterpret_cast<event::resident_trace_rebase *>(s);
  o->rest = resident->rest(*r);
  event::trace_rebase_remount_receipt remount{};
  auto *resumed = ::new (static_cast<void *>(s))
      event::resident_trace_rebase(*r, remount);
  o->remount = remount;
  o->final_head = resumed->head();
  o->final_continuation = resumed->continuation();
  o->final_can_continue = resumed->can_continue();
  o->handoff = resumed->rest(*h);
}
__global__ void observe_kernel(
    const event::heldout_trace_rebase_observation *source,
    event::heldout_trace_rebase_observation *out) {
  if (!blockIdx.x && !threadIdx.x)
    *out = *source;
}
} // namespace

cudaError_t launch_trace_rebase_heldout_mount(
    const trace_rebase_application_mount *m, unsigned char *s,
    event::heldout_trace_rebase_observation *o) noexcept {
  mount_kernel<<<1, 1>>>(m, s, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_source(
    const trace_rebase_application_mount *m,
    trace_rebase_source_secret *secret, cudaStream_t stream) noexcept {
  source_kernel<<<1, 1, 0, stream>>>(m, secret);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_expose(
    const trace_rebase_source_secret *secret,
    event::heldout_trace_rebase_observation *o, cudaStream_t stream) noexcept {
  expose_kernel<<<1, 1, 0, stream>>>(secret, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_predict(
    event::resident_trace_rebase *r, const trace_rebase_application_mount *m,
    event::heldout_trace_rebase_observation *o, cudaStream_t stream) noexcept {
  predict_kernel<<<1, 1, 0, stream>>>(reinterpret_cast<unsigned char *>(r), m, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_compare(
    event::resident_trace_rebase *r, const trace_rebase_source_secret *secret,
    event::heldout_trace_rebase_observation *o) noexcept {
  compare_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), secret, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_form(
    event::resident_trace_rebase *r,
    event::heldout_trace_rebase_observation *o) noexcept {
  form_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_resume(
    const event::checker_raw_return *x, event::resident_trace_rebase *r,
    event::heldout_trace_rebase_observation *o) noexcept {
  resume_kernel<<<1, 1>>>(x, reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_rest(
    event::resident_trace_rebase *r, event::trace_rebase_rest_record *a,
    event::trace_rebase_rest_record *b,
    event::heldout_trace_rebase_observation *o) noexcept {
  rest_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), a, b, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_heldout_observe(
    const event::heldout_trace_rebase_observation *source,
    event::heldout_trace_rebase_observation *out) noexcept {
  observe_kernel<<<1, 1>>>(source, out);
  return cudaGetLastError();
}

} // namespace holonics::apparatus
