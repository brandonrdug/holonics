#include <fcntl.h>
#include <fstream>
#include <string>
#include <unistd.h>

#include <holonics/apparatus/trace_rebase_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
[[nodiscard]] bool metadata(std::istream &in,
                            organ::cultivation_card_metadata &out) noexcept {
  std::uint64_t s = 0, o = 0, i = 0, r = 0, l = 0;
  if (!(in >> s >> o >> i >> r >> l))
    return false;
  out = {exact::word{s}, exact::word{o}, exact::word{i}, exact::word{r},
         exact::word{l}, true};
  return true;
}
[[nodiscard]] bool matrix(std::istream &in, organ::exact_matrix2 &out) noexcept {
  bool exact = true;
  for (auto &value : out.value)
    exact = exact && static_cast<bool>(in >> value);
  return exact;
}
[[nodiscard]] bool exhausted(std::istream &in) noexcept {
  std::string excess{};
  return !(in >> excess);
}
[[nodiscard]] cultivated_store_receipt finish(bool valid,
                                               std::uint64_t bytes) noexcept {
  cultivated_store_receipt out{};
  out.state = valid ? cultivated_store_status::returned
                    : cultivated_store_status::transfer_refused;
  out.bytes = exact::word{bytes};
  out.transfer_calls = exact::word{1};
  out.integrity_exact = valid;
  return out;
}
[[nodiscard]] bool opened(const char *path) noexcept {
  const int descriptor = ::open(path, O_RDONLY);
  return descriptor >= 0 && ::close(descriptor) == 0;
}
} // namespace
cultivated_store_receipt read_trace_rebase_source_card(
    const char *path, organ::trace_rebase_source_card &card) noexcept {
  const bool aperture = opened(path);
  std::ifstream in{path};
  bool exact = aperture && in.good() && metadata(in, card.metadata);
  for (auto &seed : card.seeds)
    for (auto &value : seed)
      exact = exact && matrix(in, value);
  exact = exact && exhausted(in);
  if (!exact)
    card.metadata.parsed = false;
  return finish(exact, sizeof(card));
}
cultivated_store_receipt read_heldout_trace_rebase_card(
    const char *path, organ::heldout_trace_rebase_card &card) noexcept {
  const bool aperture = opened(path);
  std::ifstream in{path};
  std::uint16_t path_length = 0, changed_matrix = 0, changed_slot = 0;
  bool exact = aperture && in.good() && metadata(in, card.metadata) &&
      static_cast<bool>(in >> path_length >> changed_matrix >> changed_slot >>
                        card.changed_value) &&
      path_length >= 8 &&
      path_length <= organ::trace_rebase_heldout_path_capacity &&
      changed_matrix < 3 && changed_slot < 4;
  card.path_length = static_cast<std::uint8_t>(path_length);
  card.changed_matrix = static_cast<std::uint8_t>(changed_matrix);
  card.changed_slot = static_cast<std::uint8_t>(changed_slot);
  for (auto &value : card.seed)
    exact = exact && matrix(in, value);
  for (std::uint8_t step = 0; step < card.path_length; ++step) {
    std::uint16_t move = 0;
    exact = exact && static_cast<bool>(in >> move) &&
            move < organ::trace_rebase_move_count;
    card.moves[step] = static_cast<organ::trace_rebase_move>(move);
  }
  exact = exact && exhausted(in);
  if (!exact)
    card.metadata.parsed = false;
  return finish(exact, sizeof(card));
}

} // namespace holonics::apparatus
