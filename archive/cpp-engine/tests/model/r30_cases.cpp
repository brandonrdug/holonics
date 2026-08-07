#include "r30_cases.hpp"

namespace holonics::tests {
apparatus::rederivation_mount
r30_case(const event::arithmetic_spectral_rest_record &inherited,
         const organ::matching_problem_card &matching,
         const organ::lattice_problem_card &lattice,
         const organ::cover_problem_card &cover) noexcept {
  return {{matching, lattice, cover, exact::word{141'300}, exact::word{141'301},
           exact::word{141'302},
           exact::word{matching.metadata.lineage.value() +
                       lattice.metadata.lineage.value() +
                       cover.metadata.lineage.value()}},
          {exact::word{151'300}, exact::word{151'301}, exact::word{151'302}},
          inherited};
}
organ::rederivation_foundation r30_host_foundation() noexcept {
  organ::rederivation_foundation f{};
  auto meta = [](std::uint64_t schema, std::uint64_t occurrence,
                 std::uint64_t lineage) {
    return organ::rederivation_card_metadata{
        exact::word{schema}, exact::word{occurrence}, 1,   lineage + 1U,
        lineage + 2U,        exact::word{lineage},    true};
  };
  f.matching.metadata = meta(300'030, 300'0301, 300'130);
  f.matching.matrix_size = 13;
  f.matching.marked_count = 6;
  f.matching.side_count = 3;
  f.matching.external_count = 7;
  for (std::uint8_t i = 0; i < 7; ++i) {
    f.matching.p[i] = static_cast<std::int16_t>(i + 1U);
    f.matching.q[i] = static_cast<std::int16_t>(i + 8U);
  }
  f.lattice.metadata = meta(300'031, 300'0311, 300'131);
  const std::uint8_t counts[4]{3, 4, 6, 3};
  const organ::rederivation_point vertices[4][6]{
      {{0, 0}, {4, 0}, {0, 3}},
      {{0, 0}, {3, 0}, {3, 2}, {0, 2}},
      {{0, 0}, {3, 0}, {3, 1}, {1, 1}, {1, 3}, {0, 3}},
      {{0, 0}, {5, 0}, {0, 3}}};
  for (std::uint8_t p = 0; p < 4; ++p) {
    f.lattice.polygons[p].vertex_count = counts[p];
    f.lattice.polygons[p].identity = exact::word{197'310U + p};
    f.lattice.polygons[p].lineage = exact::word{300'140U + p};
    for (std::uint8_t v = 0; v < counts[p]; ++v)
      f.lattice.polygons[p].vertices[v] = vertices[p][v];
  }
  f.lattice.dilation_max = 4;
  f.lattice.potential_polygon = 1;
  f.lattice.boundary_x_coefficient = 3;
  f.lattice.boundary_y_coefficient = 2;
  f.cover.metadata = meta(300'032, 300'0321, 300'132);
  f.cover.alphabet = 2;
  f.cover.words = 8;
  f.cover.maximum_width = 3;
  f.cover.subset_size = 4;
  f.event = exact::word{141'300};
  f.incoming_port = exact::word{141'301};
  f.return_port = exact::word{141'302};
  f.lineage = exact::word{900'403};
  return f;
}
} // namespace holonics::tests
