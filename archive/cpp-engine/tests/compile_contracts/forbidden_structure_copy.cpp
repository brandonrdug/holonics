#include <holonics/structure/resident_complex.hpp>

int main() {
  holonics::structure::resident_complex first{1};
  auto second = first;
  return second.cell_count() == 0 ? 0 : 1;
}
