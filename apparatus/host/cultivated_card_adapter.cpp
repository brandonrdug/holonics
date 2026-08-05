#include <charconv>
#include <fcntl.h>
#include <fstream>
#include <string>
#include <unistd.h>

#include <holonics/apparatus/cultivated_organ_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
[[nodiscard]] cultivated_store_receipt finish(bool exact, std::uint64_t bytes) noexcept {
  cultivated_store_receipt receipt{};
  receipt.state = exact ? cultivated_store_status::returned : cultivated_store_status::transfer_refused;
  receipt.bytes = exact::word{bytes}; receipt.transfer_calls = exact::word{1};
  receipt.integrity_exact = exact; return receipt;
}
[[nodiscard]] bool opened(const char *path) noexcept {
  const int descriptor = ::open(path, O_RDONLY);
  return descriptor >= 0 && ::close(descriptor) == 0;
}
[[nodiscard]] bool metadata(std::istream &in, organ::cultivation_card_metadata &out) noexcept {
  std::uint64_t schema = 0, occurrence = 0, incoming = 0, returned = 0, lineage = 0;
  if (!(in >> schema >> occurrence >> incoming >> returned >> lineage)) return false;
  out = {exact::word{schema}, exact::word{occurrence}, exact::word{incoming},
         exact::word{returned}, exact::word{lineage}, true}; return true;
}
[[nodiscard]] bool rational(const std::string &text, exact::small_rational &out) noexcept {
  const auto slash = text.find('/');
  if (slash == std::string::npos) return false;
  std::int64_t numerator = 0, denominator = 0;
  const auto left = std::from_chars(text.data(), text.data() + slash, numerator);
  const auto right = std::from_chars(text.data() + slash + 1, text.data() + text.size(), denominator);
  if (left.ec != std::errc{} || left.ptr != text.data() + slash || right.ec != std::errc{} ||
      right.ptr != text.data() + text.size() || denominator == 0) return false;
  out = exact::small_rational_law::make(numerator, denominator); return true;
}
[[nodiscard]] bool exhausted(std::istream &in) noexcept {
  std::string excess{}; return !(in >> excess);
}
}  // namespace

cultivated_store_receipt read_developmental_stream_card(
    const char *path, organ::developmental_stream_card &card) noexcept {
  const bool aperture = opened(path); std::ifstream in{path};
  std::uint16_t family = 0, series = 0, samples = 0, order = 0, degree = 0;
  bool ok = aperture && in.good() && metadata(in, card.metadata) &&
      static_cast<bool>(in >> family >> series >> samples >> order >> degree) &&
      family < organ::cultivation_family_count && series > 0 &&
      series <= organ::cultivation_series_capacity && samples > 0 &&
      samples <= organ::cultivation_sample_capacity && order <= 3 && degree <= 2;
  card.family = static_cast<organ::cultivation_family>(family);
  card.series_count = static_cast<std::uint8_t>(series);
  card.maximum_order = static_cast<std::uint8_t>(order);
  card.maximum_degree = static_cast<std::uint8_t>(degree);
  for (std::uint8_t s = 0; ok && s < card.series_count; ++s) {
    card.sample_count[s] = static_cast<std::uint8_t>(samples);
    for (std::uint8_t i = 0; ok && i < samples; ++i) {
      std::string token{}; ok = static_cast<bool>(in >> token) && rational(token, card.samples[s][i]);
    }
  }
  ok = ok && exhausted(in); if (!ok) card.metadata.parsed = false;
  return finish(ok, sizeof(card));
}

cultivated_store_receipt read_star_structure_card(const char *path,
    organ::star_structure_card &card) noexcept {
  const bool aperture = opened(path); std::ifstream in{path}; std::int16_t first = 0, last = 0;
  const bool ok = aperture && in.good() && metadata(in, card.metadata) &&
      static_cast<bool>(in >> first >> last >> card.common_conductance >> card.changed_conductance) &&
      first > 0 && last >= first && last <= 10 && card.common_conductance > 0 &&
      card.changed_conductance > 0 && exhausted(in);
  card.first_branch_count = static_cast<std::uint8_t>(first);
  card.last_branch_count = static_cast<std::uint8_t>(last);
  if (!ok) card.metadata.parsed = false;
  return finish(ok, sizeof(card));
}

cultivated_store_receipt read_walk_structure_card(const char *path,
    organ::walk_structure_card &card) noexcept {
  const bool aperture = opened(path); std::ifstream in{path}; std::uint16_t steps = 0, horizon = 0;
  bool ok = aperture && in.good() && metadata(in, card.metadata) &&
      static_cast<bool>(in >> steps >> horizon) && steps == 4 && horizon == 8;
  card.step_count = static_cast<std::uint8_t>(steps);
  card.maximum_half_horizon = static_cast<std::uint8_t>(horizon);
  for (std::uint8_t i = 0; ok && i < card.step_count; ++i) {
    std::int16_t x = 0, y = 0; ok = static_cast<bool>(in >> x >> y) && x >= -1 && x <= 1 && y >= -1 && y <= 1;
    card.steps[i][0] = static_cast<std::int8_t>(x); card.steps[i][1] = static_cast<std::int8_t>(y);
  }
  ok = ok && exhausted(in);
  if (!ok) card.metadata.parsed = false;
  return finish(ok, sizeof(card));
}

cultivated_store_receipt read_signed_carrier_card(const char *path,
    organ::signed_carrier_card &card) noexcept {
  const bool aperture = opened(path); std::ifstream in{path}; std::uint16_t horizon = 0, slot = 0;
  bool ok = aperture && in.good() && metadata(in, card.metadata) &&
      static_cast<bool>(in >> horizon >> slot >> card.changed_value) && horizon == 8 && slot < 4;
  card.maximum_horizon = static_cast<std::uint8_t>(horizon);
  card.changed_slot = static_cast<std::uint8_t>(slot);
  for (auto &value : card.matrix) ok = ok && static_cast<bool>(in >> value);
  ok = ok && exhausted(in);
  if (!ok) card.metadata.parsed = false;
  return finish(ok, sizeof(card));
}

cultivated_store_receipt read_graded_structure_card(const char *path,
    organ::graded_structure_card &card) noexcept {
  const bool aperture = opened(path); std::ifstream in{path};
  std::uint16_t generators = 0, horizon = 0, changed = 0;
  const bool ok = aperture && in.good() && metadata(in, card.metadata) &&
      static_cast<bool>(in >> generators >> horizon >> changed) && generators == 2 &&
      horizon == 8 && changed == 3 && exhausted(in);
  card.generators = static_cast<std::uint8_t>(generators);
  card.maximum_horizon = static_cast<std::uint8_t>(horizon);
  card.changed_generators = static_cast<std::uint8_t>(changed);
  if (!ok) card.metadata.parsed = false;
  return finish(ok, sizeof(card));
}

}  // namespace holonics::apparatus
