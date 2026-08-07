#include <holonics/codec/source_environment.hpp>

int main() {
  holonics::codec::source_environment first{};
  holonics::codec::source_environment second{first};
  return second.admitted() ? 0 : 1;
}
