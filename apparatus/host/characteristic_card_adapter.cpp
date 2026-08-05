#include <fcntl.h>
#include <fstream>
#include <string>
#include <unistd.h>

#include <holonics/apparatus/characteristic_hypergeometry_store_adapter.hpp>

namespace holonics::apparatus {
namespace {
[[nodiscard]] bool opened(const char *path) noexcept {
  const int d = ::open(path, O_RDONLY);
  return d >= 0 && ::close(d) == 0;
}
[[nodiscard]] bool metadata(std::istream &in,
                            organ::cultivation_card_metadata &out) noexcept {
  std::uint64_t s = 0, o = 0, i = 0, r = 0, l = 0;
  if (!(in >> s >> o >> i >> r >> l))
    return false;
  out = {exact::word{s}, exact::word{o}, exact::word{i},
         exact::word{r}, exact::word{l}, true};
  return true;
}
[[nodiscard]] bool matrix(std::istream &in,
                          organ::exact_matrix2 &out) noexcept {
  bool ok = true;
  for (auto &v : out.value)
    ok = ok && static_cast<bool>(in >> v);
  return ok;
}
[[nodiscard]] bool exhausted(std::istream &in) noexcept {
  std::string excess{};
  return !(in >> excess);
}
[[nodiscard]] cultivated_store_receipt finish(bool ok,
                                              std::uint64_t bytes) noexcept {
  cultivated_store_receipt out{};
  out.state = ok ? cultivated_store_status::returned
                 : cultivated_store_status::transfer_refused;
  out.bytes = exact::word{bytes};
  out.transfer_calls = exact::word{1};
  out.integrity_exact = ok;
  return out;
}
} // namespace
cultivated_store_receipt
read_transition_source_card(const char *path,
                            organ::transition_source_card &card) noexcept {
  const bool aperture = opened(path);
  std::ifstream in{path};
  std::uint16_t alphabet = 0, length = 0, recharted = 0;
  bool ok = aperture && in.good() && metadata(in, card.metadata) &&
            static_cast<bool>(in >> alphabet >> length >> recharted) &&
            alphabet >= 2 && alphabet <= 4 && length >= 3 && length <= 4 &&
            recharted <= 1;
  card.alphabet_size = static_cast<std::uint8_t>(alphabet);
  card.maximum_length = static_cast<std::uint8_t>(length);
  card.recharted = recharted != 0;
  ok = ok && matrix(in, card.rechart);
  for (auto &generator : card.generators)
    ok = ok && matrix(in, generator);
  for (auto &inverse : card.inverse_letter) {
    std::uint16_t value = 0;
    ok = ok && static_cast<bool>(in >> value) && value <= 4;
    inverse = static_cast<std::uint8_t>(value);
  }
  ok = ok && exhausted(in);
  if (!ok)
    card.metadata.parsed = false;
  return finish(ok, sizeof(card));
}
cultivated_store_receipt read_heldout_local_system_card(
    const char *path, organ::heldout_local_system_card &card) noexcept {
  const bool aperture = opened(path);
  std::ifstream in{path};
  std::uint16_t count = 0, split = 0, slot = 0;
  bool ok =
      aperture && in.good() && metadata(in, card.metadata) &&
      static_cast<bool>(in >> count >> split >> slot >> card.changed_value) &&
      count == 5 && split > 0 && split < count && slot < 4;
  card.edge_count = static_cast<std::uint8_t>(count);
  card.split = static_cast<std::uint8_t>(split);
  card.changed_slot = static_cast<std::uint8_t>(slot);
  for (auto &edge : card.edges)
    ok = ok && matrix(in, edge);
  ok = ok && exhausted(in);
  if (!ok)
    card.metadata.parsed = false;
  return finish(ok, sizeof(card));
}

} // namespace holonics::apparatus
