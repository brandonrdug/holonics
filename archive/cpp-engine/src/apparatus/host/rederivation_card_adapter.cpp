#include <cerrno>
#include <cstddef>
#include <cstdint>
#include <fcntl.h>
#include <unistd.h>

#include <holonics/apparatus/rederivation_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
constexpr std::uint64_t offset = 14'695'981'039'346'656'037ULL;
constexpr std::uint64_t prime = 1'099'511'628'211ULL;
void octet(std::uint64_t &fold, unsigned char value) noexcept {
  fold ^= value;
  fold *= prime;
}
[[nodiscard]] std::uint64_t path_fold(const char *path) noexcept {
  std::uint64_t fold = offset;
  for (std::size_t i = 0; path[i] != '\0'; ++i)
    octet(fold, static_cast<unsigned char>(path[i]));
  return fold;
}
struct bytes final {
  char value[2048]{};
  std::uint32_t count{};
  std::uint64_t fold{offset};
};
[[nodiscard]] rederivation_store_status read_bytes(const char *path,
                                                   bytes &out) noexcept {
  if (path == nullptr || path[0] == '\0')
    return rederivation_store_status::invalid_aperture;
  const int descriptor = ::open(path, O_RDONLY);
  if (descriptor < 0)
    return rederivation_store_status::open_refused;
  for (;;) {
    if (out.count == sizeof(out.value)) {
      static_cast<void>(::close(descriptor));
      return rederivation_store_status::size_refused;
    }
    const auto got = ::read(descriptor, out.value + out.count,
                            sizeof(out.value) - out.count);
    if (got < 0 && errno == EINTR)
      continue;
    if (got < 0) {
      static_cast<void>(::close(descriptor));
      return rederivation_store_status::transfer_refused;
    }
    if (got == 0)
      break;
    const auto count = static_cast<std::size_t>(got);
    for (std::size_t i = 0; i < count; ++i)
      octet(out.fold, static_cast<unsigned char>(out.value[out.count + i]));
    out.count += static_cast<std::uint32_t>(count);
  }
  return ::close(descriptor) == 0 && out.count != 0
             ? rederivation_store_status::returned
             : rederivation_store_status::transfer_refused;
}
struct reader final {
  const bytes &source;
  std::uint32_t at{};
  [[nodiscard]] bool next(std::int64_t &value) noexcept {
    while (at < source.count &&
           (source.value[at] == ' ' || source.value[at] == '\n' ||
            source.value[at] == '\r' || source.value[at] == '\t'))
      ++at;
    if (at == source.count)
      return false;
    bool negative = false;
    if (source.value[at] == '-') {
      negative = true;
      ++at;
    }
    if (at == source.count || source.value[at] < '0' || source.value[at] > '9')
      return false;
    std::uint64_t magnitude = 0;
    while (at < source.count && source.value[at] >= '0' &&
           source.value[at] <= '9') {
      magnitude =
          magnitude * 10U + static_cast<std::uint64_t>(source.value[at] - '0');
      ++at;
    }
    if (magnitude > 9'223'372'036'854'775'807ULL)
      return false;
    value = negative ? -static_cast<std::int64_t>(magnitude)
                     : static_cast<std::int64_t>(magnitude);
    return true;
  }
  [[nodiscard]] bool finished() noexcept {
    std::int64_t unused = 0;
    const auto before = at;
    const bool more = next(unused);
    at = before;
    while (at < source.count &&
           (source.value[at] == ' ' || source.value[at] == '\n' ||
            source.value[at] == '\r' || source.value[at] == '\t'))
      ++at;
    return !more && at == source.count;
  }
};
[[nodiscard]] bool next(reader &r, std::int64_t &v, std::int64_t lo,
                        std::int64_t hi) noexcept {
  return r.next(v) && v >= lo && v <= hi;
}
void metadata(organ::rederivation_card_metadata &target, const bytes &source,
              const char *path, std::int64_t schema,
              std::int64_t occurrence) noexcept {
  target.schema = exact::word{static_cast<std::uint64_t>(schema)};
  target.occurrence = exact::word{static_cast<std::uint64_t>(occurrence)};
  target.byte_count = source.count;
  target.byte_fold = source.fold;
  target.path_fold = path_fold(path);
  target.lineage = exact::word{target.occurrence.value() + target.byte_fold};
  target.parsed = true;
}
rederivation_store_receipt
finish(const bytes &source,
       const organ::rederivation_card_metadata &metadata) noexcept {
  rederivation_store_receipt out{};
  out.state = rederivation_store_status::returned;
  out.bytes = exact::word{source.count};
  out.transfer_calls = exact::word{1};
  out.byte_fold = source.fold;
  out.path_fold = metadata.path_fold;
  out.integrity_exact = true;
  return out;
}
rederivation_store_receipt refused(rederivation_store_status state) noexcept {
  rederivation_store_receipt out{};
  out.state = state;
  return out;
}
} // namespace

rederivation_store_receipt
read_matching_problem_card(const char *path,
                           organ::matching_problem_card &card) noexcept {
  bytes source{};
  const auto state = read_bytes(path, source);
  if (state != rederivation_store_status::returned)
    return refused(state);
  reader r{source};
  std::int64_t schema = 0, occurrence = 0, n = 0, marked = 0, side = 0,
               external = 0;
  if (!next(r, schema, 300'030, 300'030) ||
      !next(r, occurrence, 1, 9'999'999) || !next(r, n, 13, 13) ||
      !next(r, marked, 6, 6) || !next(r, side, 3, 3) ||
      !next(r, external, 7, 7))
    return refused(rederivation_store_status::parse_refused);
  card.matrix_size = 13;
  card.marked_count = 6;
  card.side_count = 3;
  card.external_count = 7;
  for (std::uint8_t i = 0; i < 7; ++i) {
    std::int64_t value = 0;
    if (!next(r, value, 1, 64))
      return refused(rederivation_store_status::parse_refused);
    card.p[i] = static_cast<std::int16_t>(value);
  }
  for (std::uint8_t i = 0; i < 7; ++i) {
    std::int64_t value = 0;
    if (!next(r, value, 1, 64))
      return refused(rederivation_store_status::parse_refused);
    card.q[i] = static_cast<std::int16_t>(value);
  }
  if (!r.finished())
    return refused(rederivation_store_status::parse_refused);
  metadata(card.metadata, source, path, schema, occurrence);
  return finish(source, card.metadata);
}

rederivation_store_receipt
read_lattice_problem_card(const char *path,
                          organ::lattice_problem_card &card) noexcept {
  bytes source{};
  const auto state = read_bytes(path, source);
  if (state != rederivation_store_status::returned)
    return refused(state);
  reader r{source};
  std::int64_t schema = 0, occurrence = 0, count = 0;
  if (!next(r, schema, 300'031, 300'031) ||
      !next(r, occurrence, 1, 9'999'999) || !next(r, count, 4, 4))
    return refused(rederivation_store_status::parse_refused);
  for (std::uint8_t p = 0; p < 4; ++p) {
    std::int64_t vertices = 0;
    if (!next(r, vertices, 3, 6))
      return refused(rederivation_store_status::parse_refused);
    card.polygons[p].vertex_count = static_cast<std::uint8_t>(vertices);
    for (std::uint8_t v = 0; v < vertices; ++v) {
      std::int64_t x = 0, y = 0;
      if (!next(r, x, 0, 16) || !next(r, y, 0, 16))
        return refused(rederivation_store_status::parse_refused);
      card.polygons[p].vertices[v] = {static_cast<std::int16_t>(x),
                                      static_cast<std::int16_t>(y)};
    }
  }
  std::int64_t dilation = 0, selected = 0, cx = 0, cy = 0;
  if (!next(r, dilation, 4, 4) || !next(r, selected, 1, 1) ||
      !next(r, cx, -16, 16) || !next(r, cy, -16, 16) || !r.finished())
    return refused(rederivation_store_status::parse_refused);
  card.dilation_max = 4;
  card.potential_polygon = 1;
  card.boundary_x_coefficient = static_cast<std::int16_t>(cx);
  card.boundary_y_coefficient = static_cast<std::int16_t>(cy);
  metadata(card.metadata, source, path, schema, occurrence);
  for (std::uint8_t p = 0; p < 4; ++p) {
    card.polygons[p].identity = exact::word{197'310U + p};
    card.polygons[p].lineage =
        exact::word{card.metadata.lineage.value() + p + 1U};
  }
  return finish(source, card.metadata);
}

rederivation_store_receipt
read_cover_problem_card(const char *path,
                        organ::cover_problem_card &card) noexcept {
  bytes source{};
  const auto state = read_bytes(path, source);
  if (state != rederivation_store_status::returned)
    return refused(state);
  reader r{source};
  std::int64_t schema = 0, occurrence = 0, a = 0, w = 0, width = 0, subset = 0;
  if (!next(r, schema, 300'032, 300'032) ||
      !next(r, occurrence, 1, 9'999'999) || !next(r, a, 2, 2) ||
      !next(r, w, 8, 8) || !next(r, width, 3, 3) || !next(r, subset, 4, 4) ||
      !r.finished())
    return refused(rederivation_store_status::parse_refused);
  card.alphabet = 2;
  card.words = 8;
  card.maximum_width = 3;
  card.subset_size = 4;
  metadata(card.metadata, source, path, schema, occurrence);
  return finish(source, card.metadata);
}

} // namespace holonics::apparatus
