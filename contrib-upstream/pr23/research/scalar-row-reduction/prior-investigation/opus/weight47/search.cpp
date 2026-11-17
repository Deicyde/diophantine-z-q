// Exhaustive search for detector weight circuits in a monomial lattice model.
// Values are monomials x = prod g_i^{v_i} over generators; a gate creates one new
// coordinate v with z*v = Q, Q in Qset(S) (products x*y of stored items, plus
// extra "free quadratic" monomials), z in S (degree-1 items, incl. constant 1).
// Targets must all be stored at the end; budget = number of new coordinates.
#include <bits/stdc++.h>
using namespace std;
typedef array<int,3> V;  // up to 3 lattice dims
int DIM;
struct H{size_t operator()(const V&v)const{return ((size_t)(v[0]+100000)*1000003u)^((size_t)(v[1]+100000)*7919u)^(size_t)(v[2]+100000);}};
V add(V a,V b){V r;for(int i=0;i<3;i++)r[i]=a[i]+b[i];return r;}
V subv(V a,V b){V r;for(int i=0;i<3;i++)r[i]=a[i]-b[i];return r;}
vector<V> extraQ; // free quadratic monomials
vector<V> targets;
long long nodes=0, solutions=0; int maxSolPrint=20;
set<vector<V>> visited;
vector<pair<vector<V>,vector<V>>> sols;

bool constructible(const vector<V>&S,const unordered_set<V,H>&Sset,V t){
  // t = x+y-z, x,y,z in S (S includes constant 0)
  for(auto&z:S){V q=add(t,z);
    for(auto&e:extraQ) if(e==q) return true;
    for(auto&x:S){V y=subv(q,x); if(Sset.count(y)) return true;}}
  return false;
}
// closure: add constructible targets repeatedly; returns added list
void closure(vector<V>&S,unordered_set<V,H>&Sset,vector<V>&order){
  bool ch=true; while(ch){ch=false; for(auto&t:targets){ if(Sset.count(t))continue; if(constructible(S,Sset,t)){S.push_back(t);Sset.insert(t);order.push_back(t);ch=true;}}}
}
vector<V> candidates(const vector<V>&S,const unordered_set<V,H>&Sset){
  unordered_set<V,H> qs; for(size_t i=0;i<S.size();i++)for(size_t j=i;j<S.size();j++)qs.insert(add(S[i],S[j]));
  for(auto&e:extraQ)qs.insert(e);
  unordered_set<V,H> c; for(auto&q:qs)for(auto&z:S){V v=subv(q,z); if(!Sset.count(v))c.insert(v);}
  return vector<V>(c.begin(),c.end());
}
int budget;
vector<V> path;
void dfs(vector<V> S, unordered_set<V,H> Sset, int used, vector<V> order){
  nodes++;
  closure(S,Sset,order);
  int missing=0; for(auto&t:targets) if(!Sset.count(t)) missing++;
  int gatesNow = order.size(); // includes intermediates and targets
  if(missing==0){ if(gatesNow<=budget){solutions++; if((int)sols.size()<maxSolPrint) sols.push_back({order,path});} return;}
  if(gatesNow+missing+1>budget) return; // need at least one intermediate plus missing targets
  vector<V> key=S; sort(key.begin(),key.end()); if(visited.count(key))return; visited.insert(key);
  for(auto&c:candidates(S,Sset)){
    auto S2=S; auto Ss2=Sset; S2.push_back(c); Ss2.insert(c); auto o2=order; o2.push_back(c); path.push_back(c);
    dfs(S2,Ss2,used+1,o2); path.pop_back();
  }
}
int main(int argc,char**argv){
  // input: DIM, nS0, S0 vectors, nExtraQ, vectors, nTargets, vectors, budget
  int n; cin>>DIM>>n; vector<V> S; for(int i=0;i<n;i++){V v{0,0,0};for(int d=0;d<DIM;d++)cin>>v[d];S.push_back(v);}
  int m; cin>>m; for(int i=0;i<m;i++){V v{0,0,0};for(int d=0;d<DIM;d++)cin>>v[d];extraQ.push_back(v);}
  int k; cin>>k; for(int i=0;i<k;i++){V v{0,0,0};for(int d=0;d<DIM;d++)cin>>v[d];targets.push_back(v);}
  cin>>budget;
  S.push_back(V{0,0,0});
  unordered_set<V,H> Ss(S.begin(),S.end());
  dfs(S,Ss,0,{});
  printf("nodes=%lld solutions=%lld\n",nodes,solutions);
  for(auto&p:sols){printf("circuit:");for(auto&v:p.first){printf(" (");for(int d=0;d<DIM;d++)printf(d?",%d":"%d",v[d]);printf(")");}printf("\n");}
}
