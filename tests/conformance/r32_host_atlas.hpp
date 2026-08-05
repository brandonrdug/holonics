#pragma once

#include <array>
#include <bit>

#include "r32_host_exact.hpp"

namespace r32_host {

[[nodiscard]] inline std::string occurrence_atlas(const numbers& card) {
  std::uint64_t coordinates[6][5]{}; std::size_t cursor = 6;
  for (auto& row : coordinates) { for (auto& value : row) value=static_cast<std::uint64_t>(card[cursor++]); ++cursor; }
  std::int64_t b1[4][5]{}; std::int64_t b2[5][2]{};
  for (auto& row : b1) for (auto& value : row) value=card[cursor++];
  for (auto& row : b2) for (auto& value : row) value=card[cursor++];
  std::ostringstream out{};
  out<<"kind\tcandidate\tpopulation\tcollisions\tobstruction\tselected\tresidual\n";
  for (std::uint8_t mask=1;mask<32;++mask) { std::uint8_t collisions=0;
    for(std::uint8_t left=0;left<6;++left)for(std::uint8_t right=left+1U;right<6;++right){bool same=true;
      for(std::uint8_t field=0;field<5;++field)if((mask&(1U<<field))!=0)same=same&&coordinates[left][field]==coordinates[right][field];
      collisions+=static_cast<std::uint8_t>(same);}
    out<<"identity\t"<<static_cast<unsigned>(mask)<<'\t'<<std::popcount(mask)<<'\t'<<
      static_cast<unsigned>(collisions)<<'\t'<<(collisions==0?0:1)<<'\t'<<(mask==31)<<"\t-\n";
  }
  for(std::uint8_t candidate=0;candidate<4;++candidate){std::int64_t residual[4][2]{};bool zero=true;
    for(std::uint8_t vertex=0;vertex<4;++vertex)for(std::uint8_t face=0;face<2;++face)
      for(std::uint8_t edge=0;edge<5;++edge){auto one=b1[vertex][edge],two=b2[edge][face];
        if(candidate==1){if(one<0)one=-one;if(two<0)two=-two;}
        if(candidate==2&&edge==2){one=-one;two=-two;}if(candidate==3&&edge==2)one=-one;
        residual[vertex][face]+=one*two;}
    for(const auto& row:residual)for(const auto value:row)zero=zero&&value==0;
    out<<"boundary\t"<<static_cast<unsigned>(candidate)<<"\t-\t-\t"<<(zero?0:2)<<'\t'<<
      (candidate==0&&zero)<<'\t';for(const auto&row:residual)for(const auto value:row)out<<value<<',';out<<'\n';
  }
  return out.str();
}

[[nodiscard]] inline std::string composition_atlas(const numbers& card) {
  std::ostringstream out{};out<<"case\tcode\tvisible\tcontact\tpredecessor\tforward\treverse\tequal\tobstruction\tresidual\n";
  std::size_t cursor=6;for(std::uint8_t row=0;row<5;++row){const auto visible=card[cursor++];
    const bool contact=card[cursor++]!=0,predecessor=card[cursor++]!=0,fa=card[cursor++]!=0,ra=card[cursor++]!=0;
    std::int64_t f[4]{},r[4]{};for(auto&v:f)v=card[cursor++];for(auto&v:r)v=card[cursor++];
    const bool fc=fa&&f[1]==0,rc=ra&&r[1]==0,obstruction=f[1]!=0||r[1]!=0;bool equal=fc&&rc;
    std::int64_t residual[4]{};for(std::uint8_t i=0;i<4;++i){residual[i]=f[i]-r[i];equal=equal&&residual[i]==0;}
    const unsigned code=predecessor&&fc&&!ra?0:equal&&!obstruction?1:contact&&fc&&rc?2:obstruction&&!fc?3:4;
    out<<static_cast<unsigned>(row)<<'\t'<<code<<'\t'<<visible<<'\t'<<contact<<'\t'<<predecessor<<'\t'<<fc<<'\t'<<rc<<'\t'<<equal<<'\t'<<obstruction<<'\t';
    for(const auto value:residual) out<<value<<',';
    out<<'\n';
  }return out.str();
}

[[nodiscard]] inline std::string receiver_atlas(const numbers& card) {
  std::ostringstream out{};out<<"left\tright\tcoarse\tfine\tfirst\tstrict\n";
  for(std::uint8_t left=0;left<6;++left)for(std::uint8_t right=left+1U;right<6;++right)
    out<<static_cast<unsigned>(left)<<'\t'<<static_cast<unsigned>(right)<<'\t'<<(card[6+left]==card[6+right])<<'\t'<<
      (card[12+left]==card[12+right])<<'\t'<<(card[18+left]==card[18+right])<<'\t'<<(card[24+left]==card[24+right])<<'\n';
  return out.str();
}

inline void matrix_row(std::ostringstream& out,const char* name,const matrix2& matrix){out<<name;for(const auto value:matrix.v)out<<'\t'<<value;out<<'\n';}

[[nodiscard]] inline std::string chart_atlas(const numbers& card) {
  const auto a=matrix_at(card,5),b=matrix_at(card,9),ab=multiply(a,b),ba=multiply(b,a);
  const auto closed=multiply(multiply(multiply(a,b),inverse_unimodular(a)),inverse_unimodular(b));
  std::ostringstream out{};out<<"face\ta\tb\tc\td\n";matrix_row(out,"AB",ab);matrix_row(out,"BA",ba);
  matrix_row(out,"residual",subtract(ab,ba));matrix_row(out,"closed",closed);
  matrix_row(out,"flat",multiply(a,inverse_unimodular(a)));return out.str();
}

[[nodiscard]] inline std::string conduct_atlas(const numbers& card) {
  struct result{std::uint8_t conditions{},errors{};};std::array<result,2187> results{};
  std::uint8_t best=8;std::uint16_t selected=0,least=0;
  for(std::uint16_t code=0;code<2187;++code){auto residual=code;
    std::uint8_t conditions[7]{};for(auto& condition:conditions){condition=static_cast<std::uint8_t>(residual%3U);residual/=3U;if(condition!=0)++results[code].conditions;}
    for(std::uint8_t row=0;row<8;++row){bool predicted=true;for(std::uint8_t field=0;field<7;++field){const auto value=card[6+row*8U+field];
      if(conditions[field]==1) predicted=predicted&&value==0;
      if(conditions[field]==2) predicted=predicted&&value==1;}
      results[code].errors+=static_cast<std::uint8_t>(predicted!=(card[13+row*8U]!=0));}
    if(results[code].errors==0){if(results[code].conditions<best){best=results[code].conditions;selected=code;least=1;}
      else if(results[code].conditions==best)++least;}
  }
  std::ostringstream out{};out<<"code\tconditions\terrors\tselected\n";for(std::uint16_t code=0;code<2187;++code)
    out<<code<<'\t'<<static_cast<unsigned>(results[code].conditions)<<'\t'<<static_cast<unsigned>(results[code].errors)<<'\t'<<(least==1&&code==selected)<<'\n';
  return out.str();
}

[[nodiscard]] inline std::string connected_atlas(const numbers& occurrence,const numbers& receiver,
    const numbers& chart) {
  std::uint64_t coordinates[6][5]{};std::size_t occurrence_cursor=6;
  for(auto& row:coordinates){for(auto& value:row)value=static_cast<std::uint64_t>(occurrence[occurrence_cursor++]);++occurrence_cursor;}
  std::uint8_t selected_mask=0,best=6;
  for(std::uint8_t mask=1;mask<32;++mask){std::uint8_t collisions=0;
    for(std::uint8_t left=0;left<6;++left)for(std::uint8_t right=left+1U;right<6;++right){bool same=true;
      for(std::uint8_t field=0;field<5;++field)if((mask&(1U<<field))!=0)same=same&&coordinates[left][field]==coordinates[right][field];
      collisions+=static_cast<std::uint8_t>(same);}
    const auto fields=static_cast<std::uint8_t>(std::popcount(mask));if(collisions==0&&fields<best){best=fields;selected_mask=mask;}}
  const auto a=matrix_at(chart,5),b=matrix_at(chart,9);
  const auto closed=multiply(multiply(multiply(a,b),inverse_unimodular(a)),inverse_unimodular(b));
  const auto trace=traces(closed,8);std::uint8_t coarse=0,fine=0,witnesses=0;
  for(std::uint8_t i=0;i<6;++i){bool new_coarse=true,new_fine=true;for(std::uint8_t j=0;j<i;++j){new_coarse=new_coarse&&receiver[6+i]!=receiver[6+j];new_fine=new_fine&&receiver[12+i]!=receiver[12+j];}
    coarse+=static_cast<std::uint8_t>(new_coarse);fine+=static_cast<std::uint8_t>(new_fine);for(std::uint8_t j=i+1U;j<6;++j)witnesses+=static_cast<std::uint8_t>(receiver[6+i]==receiver[6+j]&&receiver[24+i]!=receiver[24+j]);}
  std::ostringstream out{};out<<"law\tvalue\tobstruction\nidentity_mask\t"<<static_cast<unsigned>(selected_mask)<<"\t0\ncoarse_fibers\t"<<static_cast<unsigned>(coarse)<<
    "\t0\nfine_fibers\t"<<static_cast<unsigned>(fine)<<"\t0\nstrict_witnesses\t"<<static_cast<unsigned>(witnesses)<<
    "\t0\nclosed_trace\t"<<closed.v[0]+closed.v[3]<<"\t0\n";
  for(std::size_t order=1;order<=3;++order){const auto r=recurrence_rank(trace,order),nullity=order+1U-r;
    out<<"organ_candidate_"<<order-1U<<'\t';
    if(nullity==1){for(const auto value:order_two_kernel(trace))out<<value<<',';}
    else {for(std::size_t i=0;i<=order;++i)out<<"0,";}
    out<<'\t'<<(nullity==0?2:nullity==1?0:3)<<'\n';}
  return out.str();
}

[[nodiscard]] inline std::string heldout_atlas(const numbers& card) {
  auto edge0=matrix_at(card,8),edge1=matrix_at(card,12),edge2=matrix_at(card,16);
  const auto source=traces(multiply(multiply(edge0,edge1),edge2),9);std::vector<std::int64_t> predicted(9);
  predicted[0]=source[0];predicted[1]=source[1];for(std::size_t i=2;i<9;++i)predicted[i]=3*predicted[i-1]-predicted[i-2];
  edge2.v[static_cast<std::size_t>(card[6])]=card[7];const auto changed=traces(multiply(multiply(edge0,edge1),edge2),9);
  bool changed_residual=false;for(std::size_t i=2;i<9;++i)changed_residual=changed_residual||(3*changed[i-1]-changed[i-2]!=changed[i]);
  std::ostringstream out{};out<<"index\tprefix\tsource\tpredicted\tequal\n";for(std::size_t i=0;i<9;++i)
    out<<i<<'\t'<<(i<2)<<'\t'<<source[i]<<"/1\t"<<predicted[i]<<"/1\t"<<(source[i]==predicted[i])<<'\n';
  out<<"control\tchanged\t-\t-\t"<<(changed_residual?8:0)<<"\ncontrol\texclusion\t-\t-\t10\n";return out.str();
}

}  // namespace r32_host
