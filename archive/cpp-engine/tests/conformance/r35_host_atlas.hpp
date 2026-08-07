#pragma once

#include "r35_host_audit.hpp"

namespace r35_host {
inline void vector_out(std::ostream &out,const auto &values) {
  for(const auto value:values) out<<value<<',';
}
inline std::string state_atlas(const std::vector<State> &states) {
  std::ostringstream out; out<<"ordinal\tsource\tseed\tdepth\tpath\tcoordinates\tmatrices\tbranch\tvalid\tlineage\n";
  for(const auto &state:states) { out<<state.ordinal<<'\t'<<static_cast<unsigned>(state.source)<<'\t'
      <<static_cast<unsigned>(state.seed)<<'\t'<<static_cast<unsigned>(state.depth)<<'\t';
    for(std::uint8_t i=0;i<state.depth;++i) out<<static_cast<unsigned>(state.path[i])<<',';
    out<<'\t'; vector_out(out,state.chart); out<<'\t';
    for(const auto &matrix:state.matrices) vector_out(out,matrix);
    out<<'\t'<<state.branch<<'\t'<<state.valid<<'\t'<<state.lineage<<'\n'; }
  return out.str();
}
inline std::string edge_atlas(const std::vector<Edge> &edges) {
  std::ostringstream out; out<<"edge\tstate\tmove\ttarget_coordinates\ttarget_matrices\tsource_branch\ttarget_branch\tvalid\n";
  for(std::size_t i=0;i<edges.size();++i) { const auto &edge=edges[i];
    out<<i<<'\t'<<edge.state<<'\t'<<static_cast<unsigned>(edge.move)<<'\t';
    vector_out(out,edge.target); out<<'\t'; for(const auto &matrix:edge.matrices) vector_out(out,matrix);
    out<<'\t'<<edge.source_branch<<'\t'<<edge.target_branch<<'\t'<<edge.valid<<'\n'; }
  return out.str();
}
inline bool tangent_atlas(const char *path,const std::vector<State> &states,
    const std::vector<Edge> &edges,const Fiber &fiber,const std::array<Map,5> &maps,
    std::size_t &rows) {
  std::ifstream in{path}; std::string line; std::getline(in,line); bool exact=true; rows=0;
  while(std::getline(in,line)) { const auto f=fields(line); const auto edge_index=rows++;
    if(f.size()!=13||edge_index>=edges.size()) { exact=false; continue; }
    const auto &edge=edges[edge_index]; const auto source_gradient=gradient(fiber,states[edge.state].chart);
    const auto target_gradient=gradient(fiber,edge.target); const auto j=jacobian(maps[edge.move],states[edge.state].chart);
    const auto source_tangent=tangent(source_gradient),target_tangent=tangent(target_gradient);
    const auto transported=transport(j,source_tangent.first); const auto transported_rank=row_rank(transported);
    std::vector<std::int64_t> flat_j{},flat_basis{},flat_transported{};
    for(const auto &row:j) flat_j.insert(flat_j.end(),row.begin(),row.end());
    for(const auto &row:source_tangent.first) flat_basis.insert(flat_basis.end(),row.begin(),row.end());
    for(const auto &row:transported) flat_transported.insert(flat_transported.end(),row.begin(),row.end());
    const bool singular=source_tangent.second==0||target_tangent.second==0;
    const bool chain_exact=!singular&&transported_rank==6&&chain(target_gradient,transported);
    exact=exact&&std::stoul(f[0])==edge_index&&list(f[1])==flat_j&&same(source_gradient,list(f[2]))&&
      same(target_gradient,list(f[3]))&&list(f[4])==flat_basis&&list(f[5])==flat_transported&&
      std::stoul(f[6])==source_tangent.second&&std::stoul(f[7])==target_tangent.second&&
      std::stoul(f[8])==transported_rank&&std::stoul(f[9])==(states[edge.state].branch?1U:0U)&&
      std::stoul(f[10])==(edge.target_branch?1U:0U)&&std::stoul(f[11])==(singular?13U:0U)&&
      std::stoul(f[12])==static_cast<unsigned>(chain_exact);
  }
  return exact&&rows==edges.size();
}
struct Heldout { std::array<Matrix,3> seed{}; std::array<std::uint8_t,12> moves{};
  std::uint8_t length{},changed_matrix{},changed_slot{}; std::int64_t changed_value{}; };
inline Heldout heldout_card(const char *path) {
  const auto v=numbers(path); std::size_t at=5; Heldout out{};
  out.length=static_cast<std::uint8_t>(v.at(at++)); out.changed_matrix=static_cast<std::uint8_t>(v.at(at++));
  out.changed_slot=static_cast<std::uint8_t>(v.at(at++)); out.changed_value=v.at(at++);
  for(auto &matrix:out.seed) matrix=r35_host::matrix(v,at);
  for(std::uint8_t i=0;i<out.length;++i)
    out.moves[i]=static_cast<std::uint8_t>(v.at(at++));
  return out;
}
inline bool heldout_atlas(const char *card_path,const char *atlas_path,
                          const Fiber &fiber,const std::array<Map,5> &maps,
                          std::size_t &rows,std::uint32_t &mismatch_mask) {
  const auto card=heldout_card(card_path); std::array<std::array<Matrix,3>,13> matrices{};
  std::array<Chart,13> source{},predicted{}; matrices[0]=card.seed; source[0]=chart(matrices[0]); predicted[0]=source[0];
  for(std::uint8_t step=0;step<card.length;++step) { matrices[step+1]=enact(card.moves[step],matrices[step]);
    source[step+1]=chart(matrices[step+1]); predicted[step+1]=predict(maps[card.moves[step]],0,predicted[step]); }
  std::ifstream in{atlas_path}; std::string line; std::getline(in,line); bool exact=true; rows=0;
  for(std::uint8_t step=0;step<=card.length;++step) { if(!std::getline(in,line)) {
      mismatch_mask|=32U; return false; }
    ++rows; const auto f=fields(line);
    if(f.size()!=9&&(step!=card.length||f.size()!=8)) {
      mismatch_mask|=32U; return false; }
    const auto g=gradient(fiber,predicted[step]);
    const auto source_tangent=tangent(g); const auto vertical=g[6]==0;
    const bool geometry=std::stoul(f[0])==step&&same(predicted[step],list(f[2]))&&
      same(source[step],list(f[3]));
    const bool tangent_exact=std::stoul(f[4])==source_tangent.second&&
      std::stoul(f[5])==vertical&&std::stoul(f[6])==vertical;
    mismatch_mask|=geometry?0U:1U; mismatch_mask|=tangent_exact?0U:2U;
    exact=exact&&geometry&&tangent_exact;
    if(step<card.length) { const auto j=jacobian(maps[card.moves[step]],predicted[step]);
      const auto transported=transport(j,source_tangent.first);
      const auto rank=row_rank(transported);
      const bool moved=std::stoul(f[1])==card.moves[step];
      const bool transport_exact=std::stoul(f[7])==rank&&std::stoul(f[8])==
        static_cast<unsigned>(rank==6&&chain(gradient(fiber,predicted[step+1]),transported));
      mismatch_mask|=moved?0U:4U; mismatch_mask|=transport_exact?0U:8U;
      exact=exact&&moved&&transport_exact; }
  }
  if(!std::getline(in,line)) {
    mismatch_mask|=32U;
    return false;
  }
  ++rows;
  const auto control=fields(line);
  auto foil=card.seed; foil[card.changed_matrix][card.changed_slot]=card.changed_value;
  const bool controls=control.size()==9&&control[0]=="controls"&&control[2]==
    std::string("8,9,10,11,")+(valid(foil)?"0":"12");
  mismatch_mask|=controls?0U:16U; exact=exact&&controls;
  return exact&&!std::getline(in,line);
}
} // namespace r35_host
