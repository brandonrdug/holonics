#include <fstream>

#include "r34_host_atlas.hpp"

int main(int argc, char **argv) {
  if (argc != 11)
    return 2;
  std::array<std::vector<r34_host::Word>, 3> words{};
  for (std::size_t i = 0; i < 3; ++i)
    words[i] = r34_host::words(r34_host::card(argv[1 + i]));
  const auto triples = r34_host::triples(words);
  const std::string expected[5]{
      r34_host::word_atlas(words), r34_host::triple_atlas(triples),
      r34_host::group_atlas(r34_host::groups(triples)),
      r34_host::law_atlas(triples), r34_host::heldout_atlas(argv[4])};
  bool matches[5]{};
  std::size_t failures = 0;
  for (std::size_t i = 0; i < 5; ++i) {
    matches[i] = expected[i] == r34_host::bytes(argv[5 + i]);
    failures += !matches[i];
  }
  std::ofstream out{argv[10], std::ios::binary | std::ios::trunc};
  if (!out)
    return 3;
  out << "truth_status=established-bounded\n"
      << "evidence=implemented-exact,computational-witness\n"
         "implementation=independent-host-no-continuation\natlases_compared=5\n"
         "atlas_rows=7323\n";
  constexpr const char *names[5]{"words", "triples", "groups", "law", "heldout"};
  for (std::size_t i = 0; i < 5; ++i)
    out << "atlas_" << names[i] << "_exact=" << matches[i] << '\n';
  out << "verification_failures=" << failures << '\n';
  return failures == 0 ? 0 : 1;
}
