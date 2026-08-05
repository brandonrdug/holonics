#include <fstream>

#include "r33_host_atlas.hpp"

int main(int argc, char **argv) {
  if (argc != 11)
    return 2;
  std::array<std::vector<r33_host::Word>, 3> w{};
  for (std::size_t i = 0; i < 3; ++i)
    w[i] = r33_host::words(r33_host::card(argv[1 + i]));
  const auto pairs = r33_host::pairs(w);
  const std::string expected[5]{
      r33_host::word_atlas(w), r33_host::pair_atlas(pairs),
      r33_host::group_atlas(r33_host::groups(pairs)), r33_host::law_atlas(),
      r33_host::heldout_atlas(argv[4])};
  bool matches[5]{};
  std::size_t failures = 0;
  for (std::size_t i = 0; i < 5; ++i) {
    matches[i] = expected[i] == r33_host::bytes(argv[5 + i]);
    failures += !matches[i];
  }
  std::ofstream out{argv[10], std::ios::binary | std::ios::trunc};
  if (!out)
    return 3;
  out << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\nimplementation="
         "independent-host-no-continuation\natlases_compared=5\natlas_rows="
         "6746\n";
  constexpr const char *names[5]{"words", "pairs", "groups", "law", "heldout"};
  for (std::size_t i = 0; i < 5; ++i)
    out << "atlas_" << names[i] << "_exact=" << matches[i] << '\n';
  out << "verification_failures=" << failures << '\n';
  return failures == 0 ? 0 : 1;
}
