#include "r7_cases.hpp"

#include "r6_cases.hpp"

namespace holonics::tests {

apparatus::receiver_geometry_mount r7_case() noexcept {
  apparatus::receiver_geometry_mount mount{};
  mount.current = r6_cases().programs[0];
  auto& program = mount.receiver;
  program.identity = exact::word{7'001};
  program.swing.points[0] = exact::word{1};
  program.swing.points[1] = exact::word{2};
  program.swing.points[2] = exact::word{4};
  program.swing.points[3] = exact::word{8};
  program.swing.degenerate_points[0] = exact::word{1};
  program.swing.degenerate_points[1] = exact::word{1};
  program.swing.degenerate_points[2] = exact::word{4};
  program.swing.degenerate_points[3] = exact::word{8};
  program.swing.frame[0] = exact::word{3};
  program.swing.frame[1] = exact::word{1};
  program.swing.frame[2] = exact::word{1};
  program.swing.frame[3] = exact::word{1};
  program.swing.path = exact::word{7'011};
  program.swing.field_carrier = true;
  program.swing.counterexample_field_carrier = false;
  auto& same = program.sameness;
  same.occurrences[0] = exact::word{71};
  same.occurrences[1] = exact::word{72};
  same.diagram_incidence[0] = same.diagram_incidence[1] = exact::word{11};
  same.diagram_marks[0] = same.diagram_marks[1] = exact::word{12};
  same.receiver_faces[0][0] = same.receiver_faces[1][0] = exact::word{5};
  same.receiver_faces[0][1] = same.receiver_faces[1][1] = exact::word{7};
  same.receiver_faces[0][2] = exact::word{9};
  same.receiver_faces[1][2] = exact::word{10};
  same.receiver_successors[0][0] = same.receiver_successors[1][0] = exact::word{100};
  same.receiver_successors[0][1] = same.receiver_successors[1][1] = exact::word{101};
  same.receiver_successors[0][2] = exact::word{102};
  same.receiver_successors[1][2] = exact::word{103};
  same.presentations[0] = same.presentations[1] = exact::word{20};
  same.encodings[0] = same.encodings[1] = exact::word{0x1234};
  same.collision_encodings[0] = exact::word{0x1234};
  same.collision_encodings[1] = exact::word{0x1334};
  same.digest_mask = exact::word{0xff};
  same.diagram_bijection = true;
  same.quasi_inverse = true;
  same.unit_witness = true;
  same.counit_witness = true;
  auto& projection = program.projection;
  const std::uint64_t identities[4]{701, 702, 703, 704};
  const std::uint64_t geometry[4]{2, 3, 5, 7};
  const std::uint64_t propagation[4]{11, 13, 17, 19};
  for (std::size_t slot = 0; slot < 4; ++slot) {
    projection.source_occurrences[slot] = exact::word{identities[slot]};
    projection.geometry[slot] = exact::word{geometry[slot]};
    projection.propagation[slot] = exact::word{propagation[slot]};
  }
  projection.receiver_masks[0] = exact::word{3};
  projection.receiver_masks[1] = exact::word{6};
  projection.source_incidence = exact::word{77};
  projection.lineage = exact::word{7'021};
  auto& connection = program.connection;
  const std::uint64_t edges[4]{3, 5, 2, 4};
  const bool negative[4]{false, false, true, true};
  for (std::size_t slot = 0; slot < 4; ++slot) {
    connection.edge_magnitudes[slot] = exact::word{edges[slot]};
    connection.edge_negative[slot] = negative[slot];
  }
  connection.initial_fiber = exact::word{11};
  connection.start_endpoint = connection.end_endpoint = exact::word{99};
  connection.plaquette_boundary_support = connection.path_support = exact::word{15};
  connection.open_start = exact::word{1};
  connection.open_end = exact::word{2};
  connection.open_path_residual = exact::word{7};
  connection.lineage = exact::word{7'031};
  auto& hyper = program.hypergeometric;
  hyper.a = exact::word{1};
  hyper.b = exact::word{1};
  hyper.c = exact::word{2};
  hyper.initial_coefficient = {exact::word{1}, exact::word{1}};
  hyper.branch = exact::word{3};
  hyper.path = exact::word{7'041};
  hyper.lineage = exact::word{7'042};
  hyper.monodromy[0] = exact::word{1};
  hyper.monodromy[1] = exact::word{1};
  hyper.monodromy[2] = exact::word{0};
  hyper.monodromy[3] = exact::word{1};
  hyper.family = receiver::solution_family::gauss;
  hyper.term_count = 4;
  program.carrier = {exact::word{801}, exact::word{802}, exact::word{803},
      exact::word{811}, exact::word{812}, exact::word{821}, exact::word{822},
      exact::word{823}, exact::word{824}};
  auto& information = program.information;
  information.delta_time = exact::word{5};
  information.delta_space = exact::word{3};
  information.metric[0] = {exact::word{1}, exact::word{1}};
  information.metric[1] = {exact::word{1}, exact::word{1}};
  information.receiver_clocks[0] = {exact::word{2}, exact::word{3}};
  information.receiver_clocks[1] = {exact::word{3}, exact::word{4}};
  information.connection_delta = exact::word{5};
  information.carried_phase = exact::word{13};
  information.first_support = information.second_support = exact::word{1};
  information.missing_relativistic_obligations = exact::word{15};
  information.accelerometer_domain = exact::word{81};
  information.cycle_domain = exact::word{82};
  return mount;
}

}  // namespace holonics::tests
