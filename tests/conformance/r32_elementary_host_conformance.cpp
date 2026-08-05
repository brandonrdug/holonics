#include <fstream>

#include "r32_host_atlas.hpp"

int main(int argc,char** argv){if(argc!=15)return 2;
  const auto occurrence=r32_host::read_numbers(argv[1]);const auto composition=r32_host::read_numbers(argv[2]);
  const auto receiver=r32_host::read_numbers(argv[3]);const auto chart=r32_host::read_numbers(argv[4]);
  const auto conduct=r32_host::read_numbers(argv[5]);const auto heldout=r32_host::read_numbers(argv[6]);
  const std::string expected[7]{r32_host::occurrence_atlas(occurrence),r32_host::composition_atlas(composition),
    r32_host::receiver_atlas(receiver),r32_host::chart_atlas(chart),r32_host::conduct_atlas(conduct),
    r32_host::connected_atlas(occurrence,receiver,chart),r32_host::heldout_atlas(heldout)};
  bool matches[7]{};std::string actual[7]{};std::size_t failures=0;
  for(std::size_t i=0;i<7;++i){actual[i]=r32_host::read_bytes(argv[7+i]);matches[i]=actual[i]==expected[i];failures+=!matches[i];}
  std::ofstream receipt{argv[14],std::ios::binary|std::ios::trunc};if(!receipt)return 3;
  receipt<<"truth_status=established-bounded\nevidence=implemented-exact,computational-witness\n"
    <<"implementation=independent-host-no-continuation\natlases_compared=7\natlas_rows=2266\n";
  constexpr const char* names[7]{"identity_incidence","composition","receiver","chart","conduct","connected","heldout"};
  for(std::size_t i=0;i<7;++i)receipt<<"atlas_"<<names[i]<<"_exact="<<matches[i]<<'\n';
  if(!matches[5]){std::size_t offset=0;while(offset<actual[5].size()&&offset<expected[5].size()&&actual[5][offset]==expected[5][offset])++offset;
    receipt<<"connected_first_mismatch="<<offset<<"\nconnected_actual_byte="<<(offset<actual[5].size()?static_cast<unsigned>(static_cast<unsigned char>(actual[5][offset])):999U)
      <<"\nconnected_expected_byte="<<(offset<expected[5].size()?static_cast<unsigned>(static_cast<unsigned char>(expected[5][offset])):999U)<<'\n';}
  receipt<<"verification_failures="<<failures<<'\n';return failures==0?0:1;}
