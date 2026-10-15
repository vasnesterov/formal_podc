// usage: mc table.txt  ; table: k S n ; then S lines state fields; then S*S lines "p q"; then init n states; bad flags per state
#include <bits/stdc++.h>
using namespace std;
typedef vector<uint16_t> Conf;
struct H{size_t operator()(const Conf&c)const{size_t h=1469598103934665603ULL;for(auto x:c){h^=x;h*=1099511628211ULL;}return h;}};
int main(int argc,char**argv){
  FILE*f=fopen(argv[1],"r"); int k,S,n; fscanf(f,"%d %d %d",&k,&S,&n);
  vector<int> P(S*S),Q(S*S); for(int i=0;i<S*S;i++) fscanf(f,"%d %d",&P[i],&Q[i]);
  Conf init(n); for(int i=0;i<n;i++){int x;fscanf(f,"%d",&x);init[i]=x;}
  vector<char> bad(S); for(int i=0;i<S;i++){int x;fscanf(f,"%d",&x);bad[i]=x;}
  sort(init.begin(),init.end());
  unordered_map<Conf,int,H> idx; vector<Conf> confs; vector<vector<int>> edges;
  idx[init]=0; confs.push_back(init); edges.push_back({});
  vector<int> st={0};
  long limit = argc>2? atol(argv[2]) : 50000000;
  while(!st.empty()){
    int v=st.back(); st.pop_back(); Conf c=confs[v]; vector<int> out;
    for(int i=0;i<n;i++){ if(i>0&&c[i]==c[i-1]) continue;
      for(int j=0;j<n;j++){ if(j==i) continue; if(j>0&&c[j]==c[j-1]&&j-1!=i) continue;
        int a=c[i],b=c[j]; int p=P[a*S+b],q=Q[a*S+b]; if(p==a&&q==b) continue;
        Conf d=c; d[i]=p; d[j]=q; sort(d.begin(),d.end()); if(d==c) continue;
        auto it=idx.find(d); int w;
        if(it==idx.end()){ w=confs.size(); idx[d]=w; confs.push_back(d); edges.push_back({}); st.push_back(w);
          if((long)confs.size()>limit){printf("LIMIT\n");return 0;} }
        else w=it->second;
        out.push_back(w);
      }}
    sort(out.begin(),out.end()); out.erase(unique(out.begin(),out.end()),out.end());
    edges[v]=out;
  }
  int N=confs.size();
  // iterative tarjan
  vector<int> index(N,-1),low(N),comp(N,-1); vector<char> onst(N,0); vector<int> S2; int cnt=0,nc=0;
  vector<vector<int>> comps;
  for(int s=0;s<N;s++){ if(index[s]!=-1) continue;
    vector<pair<int,int>> work={{s,0}}; index[s]=low[s]=cnt++; S2.push_back(s); onst[s]=1;
    while(!work.empty()){ auto &[v,pi]=work.back();
      if(pi<(int)edges[v].size()){ int w=edges[v][pi]; pi++;
        if(index[w]==-1){ index[w]=low[w]=cnt++; S2.push_back(w); onst[w]=1; work.push_back({w,0}); }
        else if(onst[w]) low[v]=min(low[v],index[w]); }
      else { int vv=v; work.pop_back(); if(!work.empty()){int u=work.back().first; low[u]=min(low[u],low[vv]);}
        if(low[vv]==index[vv]){ vector<int> mem; while(true){int w=S2.back();S2.pop_back();onst[w]=0;comp[w]=nc;mem.push_back(w); if(w==vv)break;} comps.push_back(mem); nc++; } } } }
  int nb=0, nbad=0;
  for(int cid=0;cid<nc;cid++){ bool bottom=true; for(int v:comps[cid]) for(int w:edges[v]) if(comp[w]!=cid) bottom=false;
    if(!bottom) continue; nb++;
    for(int v:comps[cid]){ bool b=false; for(auto x:confs[v]) if(bad[x]) b=true;
      if(b){ nbad++; if(nbad<=1){ printf("BADSCC size %zu :",comps[cid].size()); for(auto x:confs[v]) printf(" %d",x); printf("\n");} break; } } }
  printf("N %d bottom %d badbottom %d\n",N,nb,nbad);
}
