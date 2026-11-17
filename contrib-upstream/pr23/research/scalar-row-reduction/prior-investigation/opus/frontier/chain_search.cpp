// Exhaustive IDDFS for minimal monomial weight circuits in exponent pairs (e, delta).
// Gate model (matches builder rm/rsq/rquot): new = X*Y/Z with X,Y,Z in avail U {1},
// where avail = stored coordinates plus affine aliases (delta, delta^2, delta^3).
// Targets: q_j=(2j-1,d1), q_j^2; q_k=(2k-1,d3), q_k^2, q_k^3, with d1,d3 in an allowed set.
// Usage: chain_search j k maxdepth "d1list" "d3list" [Dbound]
#include <bits/stdc++.h>
using namespace std;
struct V { int e, d; bool operator==(const V&o)const{return e==o.e&&d==o.d;} bool operator<(const V&o)const{return e!=o.e?e<o.e:d<o.d;} };
int J, K, MAXD, DB = 10, MAXE;
vector<int> D1, D3;
vector<V> avail; int nbase;
vector<V> best; long long nodes = 0; bool found = false;
vector<vector<V>> sols;
bool has(const vector<V>& s, V v){ for(auto&x:s) if(x==v) return true; return false; }
int missing(const vector<V>& s){
  int m1=99; for(int d:D1){ int m=!has(s,{2*J-1,d}) + !has(s,{4*J-2,2*d}); m1=min(m1,m);}
  int m3=99; for(int d:D3){ int m=!has(s,{2*K-1,d}) + !has(s,{4*K-2,2*d}) + !has(s,{6*K-3,3*d}); m3=min(m3,m);}
  return m1+m3;
}
int maxTargetMissingE(const vector<V>& s){
  // smallest over d-choices of the max e among missing targets
  int best1=0; { int b=1e9; for(int d:D1){int mx=0; if(!has(s,{2*J-1,d})) mx=max(mx,2*J-1); if(!has(s,{4*J-2,2*d})) mx=max(mx,4*J-2); b=min(b,mx);} best1=b; }
  int best3=0; { int b=1e9; for(int d:D3){int mx=0; if(!has(s,{2*K-1,d})) mx=max(mx,2*K-1); if(!has(s,{4*K-2,2*d})) mx=max(mx,4*K-2); if(!has(s,{6*K-3,3*d})) mx=max(mx,6*K-3); b=min(b,mx);} best3=b; }
  return max(best1,best3);
}
vector<V> candidates(const vector<V>& s){
  vector<V> c; set<V> seen(s.begin(), s.end());
  vector<V> t = s; t.push_back({0,0});
  int n=t.size();
  set<V> out;
  for(int a=0;a<n;a++) for(int b=a;b<n;b++) for(int z=0;z<n;z++){
    V v{t[a].e+t[b].e-t[z].e, t[a].d+t[b].d-t[z].d};
    if(v.e<1||v.e>MAXE||v.d<-DB||v.d>DB) continue;
    if(seen.count(v)) continue;
    out.insert(v);
  }
  return vector<V>(out.begin(), out.end());
}
void dfs(vector<V>& s, int depth, int lim, const vector<V>& parentCand, V last, bool hasLast){
  nodes++;
  int m = missing(s);
  if(m==0){ found=true; sols.push_back(vector<V>(s.begin()+nbase, s.end())); return; }
  int rem = lim-depth; if(rem<=0) return;
  int curmax=0; for(auto&x:s) curmax=max(curmax,x.e);
  int tgt=maxTargetMissingE(s); int g=0; long long cm=curmax; while(cm<tgt){cm*=2; g++;}
  if(max(m,g)>rem) return;
  vector<V> cand = candidates(s);
  set<V> pc(parentCand.begin(), parentCand.end());
  for(auto& v: cand){
    if(hasLast && pc.count(v) && !(last < v)) continue; // canonical order
    // growth prune: after adding v, remaining rem-1 steps
    s.push_back(v);
    dfs(s, depth+1, lim, cand, v, true);
    s.pop_back();
    if(sols.size()>200) return;
  }
}
int main(int argc,char**argv){
  J=atoi(argv[1]); K=atoi(argv[2]); MAXD=atoi(argv[3]);
  auto parse=[](const char* s){ vector<int> r; stringstream ss(s); string x; while(getline(ss,x,',')) r.push_back(stoi(x)); return r; };
  D1=parse(argv[4]); D3=parse(argv[5]); if(argc>6) DB=atoi(argv[6]);
  MAXE = 6*K-3; if(4*J-2>MAXE) MAXE=4*J-2;
  // base: q1, E, delta, delta^2, delta^3 (affine), q1^2, q1^3, q1^4 (stored for order-one evaluation)
  avail = {{1,-1},{1,1},{0,1},{0,2},{0,3},{2,-2},{3,-3},{4,-4}};
  nbase = avail.size();
  for(int lim=1; lim<=MAXD; lim++){
    nodes=0; sols.clear();
    vector<V> s=avail; vector<V> pc = {};
    dfs(s,0,lim,pc,{0,0},false);
    fprintf(stderr,"j=%d k=%d depth %d nodes %lld sols %zu\n",J,K,lim,nodes,sols.size());
    if(!sols.empty()){
      printf("j=%d k=%d min=%d nsols=%zu%s\n",J,K,lim,sols.size(),sols.size()>200?"+":"");
      for(size_t i=0;i<min<size_t>(sols.size(),5);i++){ for(auto&v:sols[i]) printf(" (%d,%d)",v.e,v.d); printf("\n"); }
      return 0;
    }
  }
  printf("j=%d k=%d none<=%d\n",J,K,MAXD);
}
