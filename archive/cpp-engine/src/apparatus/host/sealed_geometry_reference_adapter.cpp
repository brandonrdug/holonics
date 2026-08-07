#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/sealed_geometry_reference_adapter.hpp>

namespace holonics::apparatus {
namespace {

inline constexpr std::size_t reference_capacity = 65'536;
inline constexpr std::uint64_t fold_offset = 14'695'981'039'346'656'037ULL;
inline constexpr std::uint64_t fold_prime = 1'099'511'628'211ULL;

template<std::size_t Pattern>
[[nodiscard]] bool contains(const char* bytes, std::size_t used,
    const char (&pattern)[Pattern]) noexcept {
  constexpr std::size_t payload = Pattern - 1U;
  for (std::size_t start = 0; start + payload <= used; ++start) {
    bool same = true;
    for (std::size_t slot = 0; slot < payload; ++slot) {
      same = same && bytes[start + slot] == pattern[slot];
    }
    if (same) { return true; }
  }
  return false;
}

}  // namespace

sealed_geometry_comparison compare_sealed_geometry_reference(
    const char* path, bool kernel_returned) noexcept {
  sealed_geometry_comparison result{};
  if (path == nullptr || path[0] == '\0' || !kernel_returned) { return result; }
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0) { result.state = sealed_geometry_status::open_refused; return result; }
  char bytes[reference_capacity]{};
  std::size_t used = 0;
  std::uint64_t fold = fold_offset;
  for (;;) {
    if (used == reference_capacity) {
      static_cast<void>(::close(descriptor));
      result.state = sealed_geometry_status::capacity_refused;
      return result;
    }
    const auto count = ::read(descriptor, bytes + used, reference_capacity - used);
    if (count < 0 && errno == EINTR) { continue; }
    if (count < 0) {
      static_cast<void>(::close(descriptor));
      result.state = sealed_geometry_status::read_refused;
      return result;
    }
    if (count == 0) { break; }
    const auto amount = static_cast<std::size_t>(count);
    for (std::size_t slot = 0; slot < amount; ++slot) {
      fold ^= static_cast<unsigned char>(bytes[used + slot]);
      fold *= fold_prime;
    }
    used += amount;
  }
  if (::close(descriptor) != 0 || used == 0) {
    result.state = sealed_geometry_status::read_refused;
    return result;
  }
  result.state = sealed_geometry_status::returned;
  result.bytes = exact::word{used};
  result.observer_reads = exact::word{1};
  result.content_fold = fold;
  result.opened_after_kernel_return = true;
  result.affine_neighbor_present = contains(bytes, used, "swingPair_affine_coordinates");
  result.fractional_neighbor_present = contains(bytes, used, "crossRatio_mobius");
  result.body_resumed_after_open = false;
  return result;
}

}  // namespace holonics::apparatus
