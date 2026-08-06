#include "r13_cases.hpp"

#include <fstream>

namespace holonics::tests {

apparatus::lean_checker_mount r13_case(const char* generated_source) noexcept {
  apparatus::lean_checker_mount mount{};
  mount.source.identity = exact::word{123'001};
  mount.source.passage = exact::word{150'100};
  std::ifstream input{generated_source, std::ios::binary};
  char byte = 0;
  while (input.get(byte)) {
    if (mount.source.byte_count == codec::formal_math_face_capacity) { return {}; }
    mount.source.bytes[mount.source.byte_count++] = byte;
  }
  if (!input.eof()) { return {}; }
  mount.regions[0] = {123, 150'100};
  mount.regions[1] = {121, 0};
  mount.regions[2] = {122, 0};
  mount.regions[3] = {123, 0};
  mount.body_seed = 13'001'000;
  mount.mathematical_admitted_tally = 40;
  mount.codec_admitted_tally = 30;
  return mount;
}

}  // namespace holonics::tests
