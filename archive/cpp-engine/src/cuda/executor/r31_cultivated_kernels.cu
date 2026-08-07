#include <new>

#include <holonics/apparatus/cultivated_organ_resident.hpp>
#include <holonics/codec/cultivated_dossier_renderer.hpp>

namespace holonics::apparatus {
namespace {
__global__ void cultivation_mount_kernel(const cultivation_mount *mount, unsigned char *storage,
    event::cultivation_observation *out) {
  if (blockIdx.x || threadIdx.x) return;
  ::new (static_cast<void *>(storage)) event::resident_cultivated_organs(
      mount->cards, mount->inherited, out->predecessor_remount);
}
__global__ void cultivation_family_kernel(const cultivation_mount *mount,
    event::cultivation_observation *out, organ::cultivation_workspace *workspace,
    std::uint8_t family) {
  if (blockIdx.x || threadIdx.x) return;
  organ::shift_cultivation_detail::derive_family(mount->cards[family],
      workspace->matrices[family], out->inquiry.families[family]);
}
__global__ void cultivation_close_kernel(event::cultivation_observation *out,
    organ::cultivation_workspace *workspace) {
  if (blockIdx.x || threadIdx.x) return;
  organ::cultivation_realization_detail::close(out->inquiry, *workspace);
}
__global__ void cultivation_form_kernel(unsigned char *storage,
    event::cultivation_observation *out) {
  if (!blockIdx.x && !threadIdx.x) static_cast<void>(
      reinterpret_cast<event::resident_cultivated_organs *>(storage)->form_cultivation(*out));
}
__global__ void cultivation_resume_kernel(const event::checker_raw_return *raw,
    unsigned char *storage, event::cultivation_observation *out) {
  if (!blockIdx.x && !threadIdx.x) static_cast<void>(
      reinterpret_cast<event::resident_cultivated_organs *>(storage)->resume_cultivation(*raw, *out));
}
__global__ void cultivation_rest_kernel(unsigned char *storage,
    event::cultivated_organ_rest_record *rest, event::cultivated_organ_rest_record *handoff,
    event::cultivation_observation *out) {
  if (blockIdx.x || threadIdx.x) return;
  auto *resident = reinterpret_cast<event::resident_cultivated_organs *>(storage);
  out->rest = resident->rest(*rest); event::cultivated_organ_remount_receipt remount{};
  auto *resumed = ::new (static_cast<void *>(storage))
      event::resident_cultivated_organs(*rest, remount);
  out->remount = remount; out->final_head = resumed->head();
  out->final_continuation = resumed->continuation(); out->final_can_continue = resumed->can_continue();
  out->handoff = resumed->rest(*handoff);
}
__global__ void cultivation_observe_kernel(const event::cultivation_observation *source,
    event::cultivation_observation *out) { if (!blockIdx.x && !threadIdx.x) *out = *source; }

__global__ void application_mount_kernel(const cultivated_application_mount *mount,
    unsigned char *storage, event::cultivated_application_observation *out) {
  if (blockIdx.x || threadIdx.x) return;
  ::new (static_cast<void *>(storage)) event::resident_cultivated_organs(
      mount->inherited, out->predecessor_remount);
}
__global__ void application_source_kernel(const cultivated_application_mount *mount,
    unsigned char *storage, event::cultivated_application_observation *out, std::uint8_t family) {
  if (blockIdx.x || threadIdx.x) return;
  auto *resident = reinterpret_cast<event::resident_cultivated_organs *>(storage);
  const auto &organ = resident->organ(family);
  out->passage.acquired[family] = organ;
  if (family == 0) organ::cultivated_application_detail::derive_star(
      mount->structures.star, organ, out->inquiry.tails[family]);
  else if (family == 1) organ::cultivated_application_detail::derive_walk(
      mount->structures.walk, organ, out->inquiry.tails[family]);
  else if (family == 2) organ::cultivated_application_detail::derive_carrier(
      mount->structures.carrier, organ, out->inquiry.tails[family]);
  else organ::cultivated_application_detail::derive_graded(
      mount->structures.graded, organ, out->inquiry.tails[family]);
}
__global__ void application_close_kernel(const cultivated_application_mount *mount,
    event::cultivated_application_observation *out) {
  if (blockIdx.x || threadIdx.x) return;
  const exact::word lineages[4]{mount->structures.star.metadata.lineage,
      mount->structures.walk.metadata.lineage, mount->structures.carrier.metadata.lineage,
      mount->structures.graded.metadata.lineage};
  out->inquiry.structure_ports_distinct = true;
  for (std::uint8_t i = 0; i < 4; ++i) for (std::uint8_t j = i + 1U; j < 4; ++j)
    out->inquiry.structure_ports_distinct = out->inquiry.structure_ports_distinct && lineages[i] != lineages[j];
  organ::cultivated_application_detail::close(out->inquiry);
}
__global__ void application_form_kernel(unsigned char *storage,
    event::cultivated_application_observation *out) {
  if (!blockIdx.x && !threadIdx.x) static_cast<void>(
      reinterpret_cast<event::resident_cultivated_organs *>(storage)->form_application(*out));
}
__global__ void application_resume_kernel(const event::checker_raw_return *raw,
    unsigned char *storage, event::cultivated_application_observation *out) {
  if (blockIdx.x || threadIdx.x) return;
  auto *resident = reinterpret_cast<event::resident_cultivated_organs *>(storage);
  static_cast<void>(resident->resume_application(*raw, *out));
  static_cast<void>(codec::render_cultivated_dossier(
      event::cultivated_application_surface(out->inquiry, out->passage.acquired), out->dossier));
}
__global__ void application_rest_kernel(unsigned char *storage,
    event::cultivated_organ_rest_record *rest, event::cultivated_organ_rest_record *handoff,
    event::cultivated_application_observation *out) {
  if (blockIdx.x || threadIdx.x) return;
  auto *resident = reinterpret_cast<event::resident_cultivated_organs *>(storage);
  out->rest = resident->rest(*rest); event::cultivated_organ_remount_receipt remount{};
  auto *resumed = ::new (static_cast<void *>(storage))
      event::resident_cultivated_organs(*rest, remount);
  out->remount = remount; out->final_head = resumed->head();
  out->final_continuation = resumed->continuation(); out->final_can_continue = resumed->can_continue();
  out->handoff = resumed->rest(*handoff);
}
__global__ void application_observe_kernel(const event::cultivated_application_observation *source,
    event::cultivated_application_observation *out) { if (!blockIdx.x && !threadIdx.x) *out = *source; }
}  // namespace

cudaError_t launch_cultivation_mount(const cultivation_mount *m, unsigned char *s,
    event::cultivation_observation *o) noexcept { cultivation_mount_kernel<<<1,1>>>(m,s,o); return cudaGetLastError(); }
cudaError_t launch_cultivation_family(const cultivation_mount *m,
    event::cultivation_observation *o, organ::cultivation_workspace *w,
    std::uint8_t f, cudaStream_t stream) noexcept {
  cultivation_family_kernel<<<1,1,0,stream>>>(m,o,w,f); return cudaGetLastError(); }
cudaError_t launch_cultivation_close(event::cultivation_observation *o,
    organ::cultivation_workspace *w) noexcept { cultivation_close_kernel<<<1,1>>>(o,w); return cudaGetLastError(); }
cudaError_t launch_cultivation_form(event::resident_cultivated_organs *r,
    event::cultivation_observation *o) noexcept {
  cultivation_form_kernel<<<1,1>>>(reinterpret_cast<unsigned char *>(r),o); return cudaGetLastError(); }
cudaError_t launch_cultivation_resume(const event::checker_raw_return *raw,
    event::resident_cultivated_organs *r, event::cultivation_observation *o) noexcept {
  cultivation_resume_kernel<<<1,1>>>(raw,reinterpret_cast<unsigned char *>(r),o); return cudaGetLastError(); }
cudaError_t launch_cultivation_rest(event::resident_cultivated_organs *r,
    event::cultivated_organ_rest_record *rest, event::cultivated_organ_rest_record *handoff,
    event::cultivation_observation *o) noexcept {
  cultivation_rest_kernel<<<1,1>>>(reinterpret_cast<unsigned char *>(r),rest,handoff,o); return cudaGetLastError(); }
cudaError_t launch_cultivation_observe(const event::cultivation_observation *s,
    event::cultivation_observation *o) noexcept { cultivation_observe_kernel<<<1,1>>>(s,o); return cudaGetLastError(); }

cudaError_t launch_application_mount(const cultivated_application_mount *m, unsigned char *s,
    event::cultivated_application_observation *o) noexcept { application_mount_kernel<<<1,1>>>(m,s,o); return cudaGetLastError(); }
cudaError_t launch_application_source(const cultivated_application_mount *m,
    event::resident_cultivated_organs *r, event::cultivated_application_observation *o,
    std::uint8_t f, cudaStream_t stream) noexcept {
  application_source_kernel<<<1,1,0,stream>>>(m,reinterpret_cast<unsigned char *>(r),o,f); return cudaGetLastError(); }
cudaError_t launch_application_close(const cultivated_application_mount *m,
    event::cultivated_application_observation *o) noexcept {
  application_close_kernel<<<1,1>>>(m,o); return cudaGetLastError(); }
cudaError_t launch_application_form(event::resident_cultivated_organs *r,
    event::cultivated_application_observation *o) noexcept {
  application_form_kernel<<<1,1>>>(reinterpret_cast<unsigned char *>(r),o); return cudaGetLastError(); }
cudaError_t launch_application_resume(const event::checker_raw_return *raw,
    event::resident_cultivated_organs *r, event::cultivated_application_observation *o) noexcept {
  application_resume_kernel<<<1,1>>>(raw,reinterpret_cast<unsigned char *>(r),o); return cudaGetLastError(); }
cudaError_t launch_application_rest(event::resident_cultivated_organs *r,
    event::cultivated_organ_rest_record *rest, event::cultivated_organ_rest_record *handoff,
    event::cultivated_application_observation *o) noexcept {
  application_rest_kernel<<<1,1>>>(reinterpret_cast<unsigned char *>(r),rest,handoff,o); return cudaGetLastError(); }
cudaError_t launch_application_observe(const event::cultivated_application_observation *s,
    event::cultivated_application_observation *o) noexcept {
  application_observe_kernel<<<1,1>>>(s,o); return cudaGetLastError(); }

}  // namespace holonics::apparatus
