#include <new>

#include <holonics/apparatus/trace_fiber_resident.hpp>

namespace holonics::apparatus {
namespace {
__global__ void mount_kernel(const trace_fiber_discovery_mount *m,
                             unsigned char *s,
                             event::trace_fiber_discovery_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  ::new (static_cast<void *>(s))
      event::resident_trace_fiber(m->cards, m->inherited,
                                  o->predecessor_remount);
}
__global__ void words_kernel(const trace_fiber_discovery_mount *m,
                             event::trace_fiber_discovery_observation *o,
                             std::uint8_t source) {
  if (!blockIdx.x && !threadIdx.x)
    organ::trace_fiber_matrix_detail::form_words(
        m->cards.sources[source], o->inquiry.words[source]);
}
__global__ void triples_kernel(event::trace_fiber_discovery_observation *o,
                               std::uint8_t source) {
  const auto local =
      static_cast<std::uint16_t>(blockIdx.x * blockDim.x + threadIdx.x);
  if (local >= organ::trace_fiber_triple_stride)
    return;
  const auto first = exact::small_rational_law::divide_unsigned(local, 144);
  const auto tail = exact::small_rational_law::divide_unsigned(
      static_cast<std::uint16_t>(first.remainder), 12);
  const auto a = static_cast<std::uint8_t>(first.quotient);
  const auto b = static_cast<std::uint8_t>(tail.quotient);
  const auto c = static_cast<std::uint8_t>(tail.remainder);
  const auto at = static_cast<std::uint16_t>(
      organ::trace_fiber_census_detail::offset(source) + local);
  organ::trace_fiber_matrix_detail::form_triple(
      o->inquiry.words[source].words[a],
      o->inquiry.words[source].words[b],
      o->inquiry.words[source].words[c], source, o->inquiry.triples[at]);
}
__global__ void close_kernel(const trace_fiber_discovery_mount *m,
                             event::trace_fiber_discovery_observation *o,
                             organ::trace_fiber_workspace *w) {
  if (blockIdx.x || threadIdx.x)
    return;
  o->inquiry.passage = exact::word{201'400};
  o->inquiry.lineage = exact::word{201'401};
  o->inquiry.development_ports_distinct = true;
  for (std::uint8_t i = 0; i < 3; ++i)
    for (std::uint8_t j = static_cast<std::uint8_t>(i + 1U); j < 3; ++j)
      o->inquiry.development_ports_distinct =
          o->inquiry.development_ports_distinct &&
          m->cards.sources[i].transitions.metadata.incoming_port !=
              m->cards.sources[j].transitions.metadata.incoming_port &&
          m->cards.sources[i].transitions.metadata.lineage !=
              m->cards.sources[j].transitions.metadata.lineage;
  organ::trace_fiber_close_detail::close(o->inquiry, *w);
}
__global__ void form_kernel(unsigned char *s,
                            event::trace_fiber_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(reinterpret_cast<event::resident_trace_fiber *>(s)
                          ->form_discovery(*o));
}
__global__ void resume_kernel(const event::checker_raw_return *r,
                              unsigned char *s,
                              event::trace_fiber_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(reinterpret_cast<event::resident_trace_fiber *>(s)
                          ->resume_discovery(*r, *o));
}
__global__ void rest_kernel(unsigned char *s, event::trace_fiber_rest_record *r,
                            event::trace_fiber_rest_record *h,
                            event::trace_fiber_discovery_observation *o) {
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
    const event::trace_fiber_discovery_observation *source,
    event::trace_fiber_discovery_observation *out) {
  if (!blockIdx.x && !threadIdx.x)
    *out = *source;
}
} // namespace

cudaError_t launch_trace_fiber_mount(
    const trace_fiber_discovery_mount *m, unsigned char *s,
    event::trace_fiber_discovery_observation *o) noexcept {
  mount_kernel<<<1, 1>>>(m, s, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_words(
    const trace_fiber_discovery_mount *m,
    event::trace_fiber_discovery_observation *o, std::uint8_t i,
    cudaStream_t s) noexcept {
  words_kernel<<<1, 1, 0, s>>>(m, o, i);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_triples(
    event::trace_fiber_discovery_observation *o, std::uint8_t i,
    cudaStream_t s) noexcept {
  triples_kernel<<<7, 256, 0, s>>>(o, i);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_close(
    const trace_fiber_discovery_mount *m,
    event::trace_fiber_discovery_observation *o,
    organ::trace_fiber_workspace *w) noexcept {
  close_kernel<<<1, 1>>>(m, o, w);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_form(
    event::resident_trace_fiber *r,
    event::trace_fiber_discovery_observation *o) noexcept {
  form_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_resume(
    const event::checker_raw_return *x, event::resident_trace_fiber *r,
    event::trace_fiber_discovery_observation *o) noexcept {
  resume_kernel<<<1, 1>>>(x, reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_rest(
    event::resident_trace_fiber *r, event::trace_fiber_rest_record *a,
    event::trace_fiber_rest_record *b,
    event::trace_fiber_discovery_observation *o) noexcept {
  rest_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), a, b, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_fiber_observe(
    const event::trace_fiber_discovery_observation *s,
    event::trace_fiber_discovery_observation *o) noexcept {
  observe_kernel<<<1, 1>>>(s, o);
  return cudaGetLastError();
}
} // namespace holonics::apparatus
