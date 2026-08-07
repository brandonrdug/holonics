#pragma once

#include "r35_host_exact.hpp"

namespace r35_host {
struct Witness { std::uint16_t first{},second{}; Vector vector{},image{}; std::int64_t eigen{}; };
inline std::uint8_t augmented_rank(const std::vector<State> &states,
    const std::vector<Edge> &edges,std::uint8_t move,std::uint8_t target,
    std::uint8_t degree,int excluded=-1,int deleted=-1,bool with_target=true,
    std::size_t limit=1272) {
  Basis basis{}; const auto all_powers=exponents(); const auto count=monomial_count(degree);
  std::size_t columns=0;
  for(std::size_t i=0;i<std::min(limit,states.size());++i) if(states[i].source!=excluded) {
    const auto values=monomials(states[i].chart); std::vector<std::int64_t> row{};
    for(std::size_t term=0;term<count;++term)
      if(deleted<0||all_powers[term][static_cast<std::size_t>(deleted)]==0)
        row.push_back(residue(values[term]));
    if(with_target) row.push_back(residue(edges[i*5+move].target[target]));
    columns=row.size(); insert(basis,std::move(row),columns);
  } return static_cast<std::uint8_t>(basis.rows.size());
}
inline bool residual(const std::array<std::int64_t,121> &law,
                     const Chart &source,std::int64_t target) {
  const auto values=monomials(source); std::int64_t sum=law[120]*target;
  for(std::uint8_t i=0;i<120;++i)
    sum+=law[i]*values[i];
  return sum==0;
}
inline std::array<Witness,7> witnesses(const std::vector<State> &states,
    const std::vector<Edge> &edges,const std::array<Map,5> &maps,const Fiber &fiber) {
  std::array<Witness,7> out{};
  out[0]={};
  for(std::uint16_t i=0;i<states.size();++i) {
    if(out[1].first==0) {
      const auto first=predict(maps[0],0,states[i].chart), left=predict(maps[1],0,first);
      const auto second=predict(maps[1],0,states[i].chart), right=predict(maps[0],0,second);
      const auto basis=tangent(gradient(fiber,states[i].chart)).first;
      const auto j0=jacobian(maps[0],states[i].chart),j1=jacobian(maps[1],states[i].chart);
      const auto j01=jacobian(maps[1],first),j10=jacobian(maps[0],second);
      Vector v0{},v1{},tl{},tr{};
      for(std::uint8_t row=0;row<7;++row) for(std::uint8_t col=0;col<7;++col) {
        v0[row]+=j0[row][col]*basis[0][col]; v1[row]+=j1[row][col]*basis[0][col]; }
      for(std::uint8_t row=0;row<7;++row) for(std::uint8_t col=0;col<7;++col) {
        tl[row]+=j01[row][col]*v0[col]; tr[row]+=j10[row][col]*v1[col]; }
      bool different=false,tangent_different=false;
      for(std::uint8_t j=0;j<7;++j) { out[1].vector[j]=left[j]-right[j];
        out[1].image[j]=tl[j]-tr[j]; different|=left[j]!=right[j]; tangent_different|=tl[j]!=tr[j]; }
      if(different&&tangent_different) out[1].first=i; else out[1]={};
    }
    if(out[3].eigen==0&&states[i].branch) { const auto g=gradient(fiber,states[i].chart);
      if(g!=Vector{}&&g[6]==0) {
        const auto powers=exponents(4); std::int64_t quadratic=0;
        for(std::size_t term=0;term<powers.size();++term)
          if(powers[term][6]==2) { bool constant=true;
            for(std::uint8_t coordinate=0;coordinate<6;++coordinate)
              constant=constant&&powers[term][coordinate]==0;
            if(constant) quadratic=fiber.coefficients[term]; }
        if(quadratic!=0) { out[3].first=i; out[3].vector[6]=1;
          out[3].image[6]=(-quadratic)/quadratic;
          out[3].eigen=out[3].image[6]/out[3].vector[6]; }
      } }
    if(out[6].first==0&&out[6].second==0) {
      const auto base=static_cast<std::size_t>(i)*5U;
      const auto &a=edges[base],&b=edges[base+1U];
      bool different=false; for(std::uint8_t j=0;j<7;++j) {
        out[6].vector[j]=a.target[j]-b.target[j]; different|=a.target[j]!=b.target[j]; }
      if(different) { out[6].first=i*5; out[6].second=static_cast<std::uint16_t>(i*5+1); }
      else out[6]={}; }
  }
  for(std::uint16_t i=0;i<424&&out[2].first==0;++i) { const auto j=static_cast<std::uint16_t>(848+i);
    if(states[i].chart==states[j].chart&&states[i].matrices!=states[j].matrices)
      out[2]={i,j}; }
  for(std::uint16_t i=0;i<edges.size();++i) {
    if(out[4].first==0&&edges[i].source_branch&&!edges[i].target_branch) out[4]={i,i};
    if(out[5].first==0&&!edges[i].source_branch&&edges[i].target_branch) out[5]={i,i};
  }
  return out;
}
inline bool read_and_check_laws(const char *path,const std::vector<State> &states,
    const std::vector<Edge> &edges,const Fiber &fiber,std::array<Map,5> &maps,
    std::size_t &rows) {
  std::ifstream in{path}; std::string line; std::getline(in,line); bool exact=true; rows=0;
  std::vector<std::vector<std::string>> deferred{};
  while(std::getline(in,line)) { ++rows; const auto f=fields(line);
    if(f.size()!=10) { exact=false; continue; }
    if(f[0]!="map") { deferred.push_back(f); continue; }
    const auto move=static_cast<std::uint8_t>(std::stoul(f[1]));
    const auto target=static_cast<std::uint8_t>(std::stoul(f[2])); const auto values=list(f[9]);
    exact=exact&&move<5&&target<7&&values.size()==121;
    if(move>=5||target>=7||values.size()!=121) continue;
    for(std::uint8_t i=0;i<121;++i) maps[move].coefficients[target][i]=values[i];
    maps[move].degrees[target]=static_cast<std::uint8_t>(std::stoul(f[3]));
    const auto degree=maps[move].degrees[target], count=monomial_count(degree);
    exact=exact&&std::stoul(f[4])==static_cast<unsigned long>(count+1U)&&
      std::stoul(f[5])==count&&f[6]=="1"&&
      f[7]=="0"&&f[8]=="1"&&augmented_rank(states,edges,move,target,degree)==count;
    if(degree>0) exact=exact&&augmented_rank(states,edges,move,target,degree-1)==
      static_cast<std::uint8_t>(monomial_count(degree-1)+1);
    for(std::size_t state=0;state<states.size();++state)
      exact=exact&&residual(maps[move].coefficients[target],states[state].chart,
                           edges[state*5+move].target[target]);
  }
  const auto found=witnesses(states,edges,maps,fiber); std::array<std::array<std::uint16_t,4>,5> counts{};
  for(const auto &edge:edges) { auto &c=counts[edge.move]; const std::size_t slot=edge.source_branch?(edge.target_branch?3U:2U):(edge.target_branch?1U:0U); ++c[slot]; }
  std::size_t at=0;
  for(std::uint8_t move=0;move<5;++move) { const auto &f=deferred.at(at++); exact=exact&&f[0]=="transition"&&list(f[9])==std::vector<std::int64_t>(counts[move].begin(),counts[move].end());
    for(std::uint8_t source=0;source<3;++source) { std::array<std::uint16_t,4> local{};
      for(const auto &edge:edges) if(edge.move==move&&states[edge.state].source==source) { const std::size_t slot=edge.source_branch?(edge.target_branch?3U:2U):(edge.target_branch?1U:0U); ++local[slot]; }
      const auto &g=deferred.at(at++); exact=exact&&g[0]=="source-transition"&&std::stoul(g[2])==source&&list(g[9])==std::vector<std::int64_t>(local.begin(),local.end()); }
  }
  for(std::uint8_t source=0;source<3;++source) { const auto &f=deferred.at(at++); const auto v=list(f[9]);
    exact=exact&&f[0]=="source-holdout-rank"&&v.size()==4;
    for(std::uint8_t degree=0;degree<4;++degree) exact=exact&&v[degree]==feature_rank(states,degree,source); }
  for(std::uint8_t kind=0;kind<7;++kind) { const auto &f=deferred.at(at++); const auto v=list(f[9]);
    exact=exact&&f[0]=="witness"&&std::stoul(f[1])==kind&&v.size()==17&&v[0]==found[kind].first&&v[1]==found[kind].second;
    for(std::uint8_t j=0;j<7;++j) exact=exact&&v[2+j]==found[kind].vector[j]&&v[9+j]==found[kind].image[j];
    exact=exact&&v[16]==found[kind].eigen; }
  exact=exact&&deferred.at(at++)[5]==std::to_string(augmented_rank(states,edges,0,6,2));
  for(std::uint8_t deleted=0;deleted<7;++deleted) exact=exact&&deferred.at(at++)[5]==std::to_string(augmented_rank(states,edges,0,6,3,-1,deleted));
  exact=exact&&deferred.at(at++)[5]==std::to_string(augmented_rank(states,edges,0,6,3,-1,-1,false));
  exact=exact&&deferred.at(at++)[5]==std::to_string(augmented_rank(states,edges,0,6,3,-1,-1,true,119));
  const auto &height=deferred.at(at++); exact=exact&&height[9]=="1,64"&&at==deferred.size();
  return exact;
}
} // namespace r35_host
