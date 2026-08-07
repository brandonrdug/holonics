#pragma once

#include <array>
#include <cstdint>
#include <fstream>
#include <sstream>
#include <string>
#include <vector>

namespace r35_host {
using Matrix = std::array<std::int64_t, 4>;
using Chart = std::array<std::int64_t, 7>;
using Vector = std::array<std::int64_t, 7>;
using Jacobian = std::array<Vector, 7>;
struct Card { std::uint64_t lineage{}; std::array<std::array<Matrix, 3>, 4> seeds{}; };
struct State {
  std::array<Matrix, 3> matrices{};
  Chart chart{};
  std::array<std::uint8_t, 3> path{};
  std::uint64_t lineage{};
  std::uint16_t ordinal{};
  std::uint8_t source{}, seed{}, depth{};
  bool branch{}, valid{};
};
struct Edge {
  std::array<Matrix, 3> matrices{};
  Chart target{};
  std::uint16_t state{};
  std::uint8_t move{};
  bool source_branch{}, target_branch{}, valid{};
};
struct Map {
  std::array<std::array<std::int64_t, 121>, 7> coefficients{};
  std::array<std::uint8_t, 7> degrees{};
};
struct Fiber { std::vector<std::int64_t> coefficients{}; bool valid{}; };
inline std::vector<std::int64_t> numbers(const char *path) {
  std::ifstream in{path}; std::vector<std::int64_t> out{}; std::int64_t x{};
  while (in >> x)
    out.push_back(x);
  return out;
}
inline std::string bytes(const char *path) {
  std::ifstream in{path, std::ios::binary}; std::ostringstream out;
  out << in.rdbuf(); return out.str();
}
inline Matrix matrix(const std::vector<std::int64_t> &v, std::size_t &at) {
  Matrix out{}; for (auto &x : out) x = v.at(at++); return out;
}
inline Matrix multiply(const Matrix &x, const Matrix &y) {
  return {x[0]*y[0]+x[1]*y[2], x[0]*y[1]+x[1]*y[3],
          x[2]*y[0]+x[3]*y[2], x[2]*y[1]+x[3]*y[3]};
}
inline Matrix inverse(const Matrix &x) { return {x[3],-x[1],-x[2],x[0]}; }
inline std::int64_t trace(const Matrix &x) { return x[0]+x[3]; }
inline std::int64_t determinant(const Matrix &x) { return x[0]*x[3]-x[1]*x[2]; }
inline Card card(const char *path) {
  const auto v=numbers(path); std::size_t at=4; Card out{};
  out.lineage=static_cast<std::uint64_t>(v.at(at++));
  for(auto &seed:out.seeds)
    for(auto &m:seed)
      m=matrix(v,at);
  return out;
}
inline std::array<Matrix,3> enact(std::uint8_t move,
                                  const std::array<Matrix,3> &source) {
  auto out=source;
  if(move==0) { out[0]=source[1]; out[1]=source[0]; }
  else if(move==1) { out[1]=source[2]; out[2]=source[1]; }
  else if(move==2) out[0]=inverse(source[0]);
  else if(move==3) out[0]=multiply(source[0],source[1]);
  else out[0]=multiply(source[0],inverse(source[1]));
  return out;
}
inline Chart chart(const std::array<Matrix,3> &m) {
  const auto ab=multiply(m[0],m[1]), ac=multiply(m[0],m[2]);
  const auto bc=multiply(m[1],m[2]);
  return {trace(m[0]),trace(m[1]),trace(m[2]),trace(ab),trace(ac),trace(bc),
          trace(multiply(ab,m[2]))};
}
inline bool branch(const std::array<Matrix,3> &m,const Chart &x) {
  return x[6]==trace(multiply(multiply(m[0],m[2]),m[1]));
}
inline bool valid(const std::array<Matrix,3> &m) {
  return determinant(m[0])==1 && determinant(m[1])==1 && determinant(m[2])==1;
}
inline std::uint8_t inverse_move(std::uint8_t move) {
  return move==3?4:(move==4?3:move);
}
inline std::uint8_t nth_allowed(std::uint8_t previous,std::uint8_t ordinal) {
  for(std::uint8_t move=0;move<5;++move) if(move!=inverse_move(previous)) {
    if(ordinal==0)
      return move;
    --ordinal;
  } return 0;
}
inline void decode(std::uint16_t local,State &out) {
  if(local==0) return;
  if(local<=5) { out.depth=1; out.path[0]=static_cast<std::uint8_t>(local-1); return; }
  if(local<=25) { const auto code=static_cast<std::uint8_t>(local-6);
    out.depth=2; out.path[0]=code/4; out.path[1]=nth_allowed(out.path[0],code%4); return; }
  const auto code=static_cast<std::uint8_t>(local-26); out.depth=3;
  out.path[0]=code/16; out.path[1]=nth_allowed(out.path[0],(code%16)/4);
  out.path[2]=nth_allowed(out.path[1],code%4);
}
inline std::vector<State> states(const std::array<Card,3> &cards) {
  std::vector<State> out(1272);
  for(std::uint8_t source=0;source<3;++source) for(std::uint8_t seed=0;seed<4;++seed)
    for(std::uint16_t local=0;local<106;++local) {
      State s{}; s.source=source; s.seed=seed;
      s.ordinal=static_cast<std::uint16_t>((source*4+seed)*106+local);
      s.lineage=cards[source].lineage+s.ordinal+1; decode(local,s);
      s.matrices=cards[source].seeds[seed];
      for(std::uint8_t i=0;i<s.depth;++i) s.matrices=enact(s.path[i],s.matrices);
      s.chart=chart(s.matrices); s.branch=branch(s.matrices,s.chart);
      s.valid=valid(s.matrices); out[s.ordinal]=s;
    }
  return out;
}
inline std::vector<Edge> edges(const std::vector<State> &states) {
  std::vector<Edge> out(6360);
  for(const auto &s:states) for(std::uint8_t move=0;move<5;++move) {
    Edge e{}; e.state=s.ordinal; e.move=move; e.matrices=enact(move,s.matrices);
    e.target=chart(e.matrices); e.source_branch=s.branch;
    e.target_branch=branch(e.matrices,e.target); e.valid=s.valid&&valid(e.matrices);
    out[static_cast<std::size_t>(s.ordinal)*5U+move]=e;
  } return out;
}
inline std::int64_t power(std::int64_t value,std::uint8_t exponent) {
  std::int64_t out=1; while(exponent--!=0) out*=value; return out;
}
inline std::vector<std::array<std::uint8_t,7>> exponents(std::uint8_t degree=3) {
  std::vector<std::array<std::uint8_t,7>> out{};
  for(std::uint8_t total=0;total<=degree;++total) for(std::uint8_t a=0;a<=total;++a)
   for(std::uint8_t b=0;b<=total-a;++b) for(std::uint8_t c=0;c<=total-a-b;++c)
    for(std::uint8_t d=0;d<=total-a-b-c;++d) for(std::uint8_t e=0;e<=total-a-b-c-d;++e)
     for(std::uint8_t f=0;f<=total-a-b-c-d-e;++f)
      out.push_back({a,b,c,d,e,f,static_cast<std::uint8_t>(total-a-b-c-d-e-f)});
  return out;
}
inline std::array<std::int64_t,120> monomials(const Chart &x) {
  std::array<std::int64_t,120> out{}; const auto powers=exponents();
  for(std::size_t i=0;i<out.size();++i) { out[i]=1;
    for(std::uint8_t j=0;j<7;++j) out[i]*=power(x[j],powers[i][j]); }
  return out;
}
inline std::vector<std::int64_t> monomial_values(const Chart &x,
                                                 std::uint8_t degree) {
  const auto powers=exponents(degree); std::vector<std::int64_t> out(powers.size(),1);
  for(std::size_t i=0;i<out.size();++i)
    for(std::uint8_t j=0;j<7;++j) out[i]*=power(x[j],powers[i][j]);
  return out;
}
inline Chart predict(const Map &map,std::uint8_t move_target,const Chart &x) {
  Chart out{}; const auto values=monomials(x); (void)move_target;
  for(std::uint8_t target=0;target<7;++target) { std::int64_t sum=0;
    for(std::uint8_t i=0;i<120;++i) sum+=map.coefficients[target][i]*values[i];
    out[target]=-sum/map.coefficients[target][120]; }
  return out;
}
} // namespace r35_host
