// Exhaustive search with free delta-normalization (and optionally free A-normalization).
// Lattice coordinates: [A2 (exponent of C=sqrt A), e, delta]. Families:
//   q12 = (alpha12, 23, b12), mixedHigh = 2*q12   (b12 odd < 0; alpha12 even, =0 unless --freeA)
//   qN  = (alpha, 2N-1, b), qN^2 = 2*qN, qN^3 = 3*qN
// Gate: v = x + y - z, x,y in S∪{0} or extraQ (as x+y), z in S∪{0}. Budget counts all new coordinates.
#include <bits/stdc++.h>
using namespace std;
typedef array<int,3> V;
struct H{size_t operator()(const V&v)const{return ((size_t)(v[0]+100000)*1000003u)^((size_t)(v[1]+100000)*7919u)^(size_t)(v[2]+100000);}};
V add(V a,V b){return {a[0]+b[0],a[1]+b[1],a[2]+b[2]};}
V sub(V a,V b){return {a[0]-b[0],a[1]-b[1],a[2]-b[2]};}
V mulk(V a,int k){return {a[0]*k,a[1]*k,a[2]*k};}
vector<V> extraQ; int N, budget; bool freeA;
long long nodes=0, sols=0; vector<string> out;
struct Fam{int ea; vector<int> mult;}; // base e-exponent, multiples
Fam fams[2];
bool okParam(V p){ // base member: delta odd negative; A exponent even (C^even) and 0 unless freeA
  if(!(p[2]<0 && (p[2]%2!=0))) return false;
  if(freeA) return p[0]%2==0; return p[0]==0;}
unordered_set<V,H> reach(const vector<V>&S){
  unordered_set<V,H> qs; for(size_t i=0;i<S.size();i++)for(size_t j=i;j<S.size();j++)qs.insert(add(S[i],S[j]));
  for(auto&e:extraQ)qs.insert(e);
  unordered_set<V,H> c; for(auto&q:qs)for(auto&z:S)c.insert(sub(q,z)); return c;}
string str(V v){char b[64];snprintf(b,64,"(%d,%d,%d)",v[0],v[1],v[2]);return b;}
void dfs(vector<V> S, unordered_set<V,H> Ss, int used, bool fx[2], V par[2], vector<string> log){
  nodes++;
  // greedily add fixed-family targets
  bool ch=true;
  while(ch){ch=false; auto R=reach(S);
    for(int f=0;f<2;f++) if(fx[f]) for(int k:fams[f].mult){V t=mulk(par[f],k); if(!Ss.count(t)&&R.count(t)){S.push_back(t);Ss.insert(t);used++;log.push_back("T"+str(t));ch=true;}}}
  // branch on unset families: any reachable member fixes the parameter
  auto R=reach(S);
  for(int f=0;f<2;f++) if(!fx[f]){
    set<V> choices;
    for(auto&v:R) for(int k:fams[f].mult){ if(v[1]!=k*fams[f].ea) continue; if(v[0]%k||v[2]%k) continue; V p={v[0]/k,v[1]/k,v[2]/k}; if(okParam(p)) choices.insert(p);}
    for(auto&p:choices){ bool s2[2]={fx[0],fx[1]}; V p2[2]={par[0],par[1]}; s2[f]=true;p2[f]=p; auto l2=log; l2.push_back("fix"+to_string(f)+str(p)); dfs(S,Ss,used,s2,p2,l2);}
  }
  int missing=0; for(int f=0;f<2;f++) missing+= fx[f]? (int)count_if(fams[f].mult.begin(),fams[f].mult.end(),[&](int k){return !Ss.count(mulk(par[f],k));}) : (int)fams[f].mult.size();
  if(missing==0){ if(used<=budget){sols++; if(out.size()<40){string s; for(auto&x:log)s+=x+" "; out.push_back(s);}} return;}
  if(used+missing+1>budget) return;
  // intermediates
  for(auto&c:R){ if(Ss.count(c))continue; auto S2=S;auto Ss2=Ss;S2.push_back(c);Ss2.insert(c);auto l2=log;l2.push_back("I"+str(c)); dfs(S2,Ss2,used+1,fx,par,l2);}
}
int main(int argc,char**argv){
  int n; cin>>n; vector<V> S; for(int i=0;i<n;i++){V v;cin>>v[0]>>v[1]>>v[2];S.push_back(v);}
  int m; cin>>m; for(int i=0;i<m;i++){V v;cin>>v[0]>>v[1]>>v[2];extraQ.push_back(v);}
  int fa; cin>>N>>budget>>fa; freeA=fa;
  fams[0]={23,{1,2}}; fams[1]={2*N-1,{1,2,3}};
  S.push_back(V{0,0,0}); unordered_set<V,H> Ss(S.begin(),S.end());
  bool st[2]={false,false}; V par[2]={V{0,0,0},V{0,0,0}};
  dfs(S,Ss,0,st,par,{});
  printf("N=%d budget=%d freeA=%d nodes=%lld solutions=%lld\n",N,budget,fa,nodes,sols);
  for(auto&s:out)printf("  %s\n",s.c_str());
}
