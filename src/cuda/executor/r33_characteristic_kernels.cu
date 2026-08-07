#include <new>

#include <holonics/apparatus/characteristic_hypergeometry_resident.hpp>

namespace holonics::apparatus {
namespace {
__global__ void mount_kernel(const characteristic_discovery_mount *m,
                             unsigned char *s,
                             event::characteristic_discovery_observation *o) {
  if (blockIdx.x || threadIdx.x)
    return;
  ::new (static_cast<void *>(s)) event::resident_characteristic_hypergeometry(
      m->cards, m->inherited, o->predecessor_remount);
}
__global__ void words_kernel(const characteristic_discovery_mount *m,
                             event::characteristic_discovery_observation *o,
                             std::uint8_t source) {
  if (!blockIdx.x && !threadIdx.x)
    organ::characteristic_matrix_detail::form_words(m->cards.sources[source],
                                                    o->inquiry.words[source]);
}
__global__ void pairs_kernel(event::characteristic_discovery_observation *o,
                             std::uint8_t source) {
  const auto local =
      static_cast<std::uint16_t>(blockIdx.x * blockDim.x + threadIdx.x);
  const auto count = o->inquiry.words[source].count;
  const auto pair_count = static_cast<std::uint16_t>(count * count);
  if (local >= pair_count)
    return;
  const auto division =
      exact::small_rational_law::divide_unsigned(local, count);
  const auto left = static_cast<std::uint8_t>(division.quotient);
  const auto right = static_cast<std::uint8_t>(division.remainder);
  const auto at = static_cast<std::uint16_t>(
      organ::characteristic_census_detail::offset(source) + local);
  organ::characteristic_matrix_detail::form_pair(
      o->inquiry.words[source].words[left],
      o->inquiry.words[source].words[right], source, o->inquiry.pairs[at]);
}
__global__ void close_kernel(const characteristic_discovery_mount *m,
                             event::characteristic_discovery_observation *o,
                             organ::characteristic_workspace *w) {
  if (blockIdx.x || threadIdx.x)
    return;
  o->inquiry.passage = exact::word{200'400};
  o->inquiry.lineage = exact::word{200'401};
  o->inquiry.development_ports_distinct = true;
  for (std::uint8_t i = 0; i < 3; ++i)
    for (std::uint8_t j = i + 1U; j < 3; ++j)
      o->inquiry.development_ports_distinct =
          o->inquiry.development_ports_distinct &&
          m->cards.sources[i].metadata.incoming_port !=
              m->cards.sources[j].metadata.incoming_port &&
          m->cards.sources[i].metadata.lineage !=
              m->cards.sources[j].metadata.lineage;
  organ::characteristic_census_detail::close(o->inquiry, *w);
}
__global__ void form_kernel(unsigned char *s,
                            event::characteristic_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(
        reinterpret_cast<event::resident_characteristic_hypergeometry *>(s)
            ->form_discovery(*o));
}
__global__ void resume_kernel(const event::checker_raw_return *r,
                              unsigned char *s,
                              event::characteristic_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    static_cast<void>(
        reinterpret_cast<event::resident_characteristic_hypergeometry *>(s)
            ->resume_discovery(*r, *o));
}
__global__ void rest_kernel(unsigned char *s,
                            event::characteristic_hypergeometry_rest_record *r,
                            event::characteristic_hypergeometry_rest_record *h,
                            event::characteristic_discovery_observation *o) {
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
__global__ void
observe_kernel(const event::characteristic_discovery_observation *s,
               event::characteristic_discovery_observation *o) {
  if (!blockIdx.x && !threadIdx.x)
    *o = *s;
}

} // namespace

cudaError_t launch_characteristic_mount(
    const characteristic_discovery_mount *m, unsigned char *s,
    event::characteristic_discovery_observation *o) noexcept {
  mount_kernel<<<1, 1>>>(m, s, o);
  return cudaGetLastError();
}
cudaError_t
launch_characteristic_words(const characteristic_discovery_mount *m,
                            event::characteristic_discovery_observation *o,
                            std::uint8_t i, cudaStream_t s) noexcept {
  words_kernel<<<1, 1, 0, s>>>(m, o, i);
  return cudaGetLastError();
}
cudaError_t
launch_characteristic_pairs(event::characteristic_discovery_observation *o,
                            std::uint8_t i, cudaStream_t s) noexcept {
  pairs_kernel<<<16, 256, 0, s>>>(o, i);
  return cudaGetLastError();
}
cudaError_t
launch_characteristic_close(const characteristic_discovery_mount *m,
                            event::characteristic_discovery_observation *o,
                            organ::characteristic_workspace *w) noexcept {
  close_kernel<<<1, 1>>>(m, o, w);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_form(
    event::resident_characteristic_hypergeometry *r,
    event::characteristic_discovery_observation *o) noexcept {
  form_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_resume(
    const event::checker_raw_return *x,
    event::resident_characteristic_hypergeometry *r,
    event::characteristic_discovery_observation *o) noexcept {
  resume_kernel<<<1, 1>>>(x, reinterpret_cast<unsigned char *>(r), o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_rest(
    event::resident_characteristic_hypergeometry *r,
    event::characteristic_hypergeometry_rest_record *a,
    event::characteristic_hypergeometry_rest_record *b,
    event::characteristic_discovery_observation *o) noexcept {
  rest_kernel<<<1, 1>>>(reinterpret_cast<unsigned char *>(r), a, b, o);
  return cudaGetLastError();
}
cudaError_t launch_characteristic_observe(
    const event::characteristic_discovery_observation *s,
    event::characteristic_discovery_observation *o) noexcept {
  observe_kernel<<<1, 1>>>(s, o);
  return cudaGetLastError();
}
} // namespace holonics::apparatus
