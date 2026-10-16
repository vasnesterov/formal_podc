// Count h_1(Delta) for Pi'_1 derived from weak 2-colouring (Section 4.6, trit description).
#include <stdio.h>
#include <stdlib.h>
static const int lab[7][2]={{0,1},{0,2},{1,0},{1,1},{1,2},{2,0},{2,1}};
int D;
int step(int st,int l){ // st bits: j*2+0: has2_j, j*2+1: has0_j
  for(int j=0;j<2;j++){ if(lab[l][j]==2) st|=1<<(2*j); if(lab[l][j]==0) st|=1<<(2*j+1);} return st;}
int good(int st){ for(int j=0;j<2;j++) if((st>>(2*j)&1) && !((st>>(2*j+1))&1)) return 1; return 0;}
int A(int*W){ unsigned reach=1; // set of states (16 bits), start state 0
  for(int i=0;i<D;i++){ unsigned nr=0; for(int s=0;s<16;s++) if(reach>>s&1) for(int l=0;l<7;l++) if(W[i]>>l&1) nr|=1u<<step(s,l); reach=nr; }
  for(int s=0;s<16;s++) if((reach>>s&1) && !good(s)) return 0; return 1; }
int W[16]; long cnt=0, cntne=0;
void rec(int i,int lo,int allowEmpty){
  if(i==D){ if(!A(W)) return;
    for(int k=0;k<D;k++) for(int l=0;l<7;l++) if(!(W[k]>>l&1)){ int o=W[k]; W[k]|=1<<l; int a=A(W); W[k]=o; if(a) return; }
    cnt++; int ne=1; for(int k=0;k<D;k++) if(!W[k]) ne=0; if(ne){cntne++; if(D<=6){printf("  ");for(int k=0;k<D;k++){printf("{");for(int l=0;l<7;l++) if(W[k]>>l&1) printf("%d%d,",lab[l][0],lab[l][1]); printf("} ");} printf("\n");}}
    return; }
  for(int m=lo;m<128;m++){ W[i]=m; rec(i+1,m,allowEmpty);} }
int main(int c,char**v){ D=atoi(v[1]); rec(0,0,1); printf("Delta=%d maximal=%ld nonempty=%ld\n",D,cnt,cntne); }
