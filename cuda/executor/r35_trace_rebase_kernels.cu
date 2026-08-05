#include <new>

#include <holonics/apparatus/trace_rebase_resident.hpp>

namespace holonics::apparatus {
namespace {
__global__ void mount_kernel(const trace_rebase_discovery_mount *m,
                             unsigned char *s,
                             event::trace_rebase_discovery_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  ::new (static_cast<void *>(s))
      event::resident_trace_rebase(m->cards, m->inherited,
                                   o->predecessor_remount);
  o->inquiry.passage = exact::word{202'400};
  o->inquiry.lineage = exact::word{202'401};
  o->inquiry.source_ports_distinct = true;
  for (std::uint8_t i = 0; i < organ::trace_rebase_source_count; ++i)
    for (std::uint8_t j = static_cast<std::uint8_t>(i + 1U);
         j < organ::trace_rebase_source_count; ++j)
      o->inquiry.source_ports_distinct =
          o->inquiry.source_ports_distinct &&
          m->cards.sources[i].metadata.incoming_port !=
              m->cards.sources[j].metadata.incoming_port &&
          m->cards.sources[i].metadata.lineage !=
              m->cards.sources[j].metadata.lineage;
}
__global__ void states_kernel(const trace_rebase_discovery_mount *m,
                              event::trace_rebase_discovery_observation *o,
                              std::uint8_t source) {
  const auto local =
      static_cast<std::uint16_t>(blockIdx.x * blockDim.x + threadIdx.x);
  constexpr std::uint16_t per_source =
      organ::trace_rebase_seed_count * organ::trace_rebase_states_per_seed;
  if (local >= per_source)
    return;
  const auto division = exact::small_rational_law::divide_unsigned(
      local, organ::trace_rebase_states_per_seed);
  const auto seed = static_cast<std::uint8_t>(division.quotient);
  const auto state = static_cast<std::uint16_t>(source * per_source + local);
  organ::trace_rebase_matrix_detail::form_state(
      m->cards.sources[source], source, seed,
      static_cast<std::uint16_t>(division.remainder), o->inquiry.states[state]);
}
__global__ void edges_kernel(event::trace_rebase_discovery_observation *o,
                             std::uint8_t source) {
  const auto local =
      static_cast<std::uint16_t>(blockIdx.x * blockDim.x + threadIdx.x);
  constexpr std::uint16_t states_per_source =
      organ::trace_rebase_seed_count * organ::trace_rebase_states_per_seed;
  constexpr std::uint16_t edges_per_source =
      states_per_source * organ::trace_rebase_move_count;
  if (local >= edges_per_source)
    return;
  const auto division = exact::small_rational_law::divide_unsigned(
      local, organ::trace_rebase_move_count);
  const auto state = static_cast<std::uint16_t>(
      source * states_per_source + division.quotient);
  const auto edge = static_cast<std::uint16_t>(
      state * organ::trace_rebase_move_count + division.remainder);
  organ::trace_rebase_matrix_detail::form_edge(
      o->inquiry.states[state],
      static_cast<organ::trace_rebase_move>(division.remainder),
      o->inquiry.edges[edge]);
}
__global__ void close_kernel(unsigned char *s,
                             event::trace_rebase_discovery_observation *o,
                             organ::trace_rebase_workspace *w) {
  if (blockIdx.x || threadIdx.x)
    return;
  o->inquiry.state_count = organ::trace_rebase_state_capacity;
  o->inquiry.edge_count = organ::trace_rebase_edge_capacity;
  const auto *resident = reinterpret_cast<event::resident_trace_rebase *>(s);
  organ::trace_rebase_close_detail::close(resident->fiber().organs,
                                          o->inquiry, *w);
}
__global__ void form_kernel(unsigned char *s,
                            event::trace_rebase_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(reinterpret_cast<event::resident_trace_rebase *>(s)
                          ->form_discovery(*o));
}
__global__ void form_surface_kernel(
    unsigned char *s, event::trace_rebase_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(reinterpret_cast<event::resident_trace_rebase *>(s)
                          ->form_discovery_surface(*o));
}
__global__ void resume_kernel(const event::checker_raw_return *r,
                              unsigned char *s,
                              event::trace_rebase_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(reinterpret_cast<event::resident_trace_rebase *>(s)
                          ->resume_discovery(*r, *o));
}
__global__ void rest_kernel(unsigned char *s, event::trace_rebase_rest_record *r,
                            event::trace_rebase_rest_record *h,
                            event::trace_rebase_discovery_observation *o) {
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
    const event::trace_rebase_discovery_observation *source,
    event::trace_rebase_discovery_observation *out) {
  if (!blockIdx.x && !threadIdx.x)
    *out = *source;
}
} // namespace

cudaError_t launch_trace_rebase_mount(
    const trace_rebase_discovery_mount *m, unsigned char *s,
    event::trace_rebase_discovery_observation *o) noexcept {
  mount_kernel<<<1, 1>>>(m, s, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_states(
    const trace_rebase_discovery_mount *m,
    event::trace_rebase_discovery_observation *o, std::uint8_t source,
    cudaStream_t stream) noexcept {
  states_kernel<<<2, 256, 0, stream>>>(m, o, source);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_edges(
    event::trace_rebase_discovery_observation *o, std::uint8_t source,
    cudaStream_t stream) noexcept {
  edges_kernel<<<9, 256, 0, stream>>>(o, source);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_close(
    event::resident_trace_rebase *r,
    event::trace_rebase_discovery_observation *o,
    organ::trace_rebase_workspace *w) noexcept {
  close_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o, w);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_form(
    event::resident_trace_rebase *r,
    event::trace_rebase_discovery_observation *o) noexcept {
  form_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_form_surface(
    event::resident_trace_rebase *r,
    event::trace_rebase_discovery_observation *o) noexcept {
  form_surface_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_resume(
    const event::checker_raw_return *x, event::resident_trace_rebase *r,
    event::trace_rebase_discovery_observation *o) noexcept {
  resume_kernel<<<1, 1>>>(x, reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_rest(
    event::resident_trace_rebase *r, event::trace_rebase_rest_record *a,
    event::trace_rebase_rest_record *b,
    event::trace_rebase_discovery_observation *o) noexcept {
  rest_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), a, b, o);
  return cudaGetLastError();
}
cudaError_t launch_trace_rebase_observe(
    const event::trace_rebase_discovery_observation *source,
    event::trace_rebase_discovery_observation *out) noexcept {
  observe_kernel<<<1, 1>>>(source, out);
  return cudaGetLastError();
}

} // namespace holonics::apparatus
