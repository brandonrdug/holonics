#include <fstream>

#include "r35_host_atlas.hpp"

int main(int argc,char **argv) {
  if(argc!=11) return 2;
  std::array<r35_host::Card,3> cards{};
  for(std::size_t i=0;i<3;++i) cards[i]=r35_host::card(argv[i+1]);
  const auto states=r35_host::states(cards);
  const auto edges=r35_host::edges(states);
  const auto fiber=r35_host::discover_fiber(states);
  bool exact[5]{}; std::size_t law_rows=0,tangent_rows=0,heldout_rows=0;
  std::uint32_t heldout_mismatch_mask=0;
  exact[0]=r35_host::state_atlas(states)==r35_host::bytes(argv[5]);
  exact[1]=r35_host::edge_atlas(edges)==r35_host::bytes(argv[6]);
  std::array<r35_host::Map,5> maps{};
  exact[3]=fiber.valid&&r35_host::read_and_check_laws(argv[8],states,edges,fiber,maps,law_rows);
  exact[2]=r35_host::tangent_atlas(argv[7],states,edges,fiber,maps,tangent_rows);
  exact[4]=r35_host::heldout_atlas(argv[4],argv[9],fiber,maps,heldout_rows,
                                  heldout_mismatch_mask);
  std::size_t failures=0; for(const auto value:exact) failures+=!value;
  std::ofstream out{argv[10],std::ios::binary|std::ios::trunc};
  if(!out) return 3;
  out<<"truth_status=established-bounded\n"
        "evidence=implemented-exact,computational-witness\n"
        "implementation=independent-host-no-continuation\n"
     <<"matrix_discovered_fiber_relation="<<fiber.valid<<'\n'
     <<"atlases_compared=5\n"
     <<"atlas_rows="<<states.size()+edges.size()+tangent_rows+law_rows+heldout_rows<<'\n'
     <<"atlas_states_exact="<<exact[0]<<'\n'<<"atlas_edges_exact="<<exact[1]<<'\n'
     <<"atlas_tangents_exact="<<exact[2]<<'\n'<<"atlas_laws_exact="<<exact[3]<<'\n'
     <<"atlas_heldout_exact="<<exact[4]<<'\n'
     <<"heldout_mismatch_mask="<<heldout_mismatch_mask<<'\n'
     <<"verification_failures="<<failures<<'\n';
  return failures==0?0:1;
}
