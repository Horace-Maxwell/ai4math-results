/* venn_enum_fast.c -- same enumeration as venn_enum.c (sums of k monomials of degree <= 7 in 14
   variables, via Venn-region sizes), with a faster evaluation: g(A) = sum_{0 != R subset A} n_R by a
   zeta transform, |U_T| = used - g(~T).  Symmetry: none (every labelled configuration is visited).
   Cross-checked against venn_enum.c for k <= 4 (identical weight sets). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int K, FULL; static int n[64]; static char seen[16385]; static long long cnt=0;
static inline void eval(int used){
  int g[64]; for(int A=0;A<=FULL;A++) g[A]=n[A]; g[0]=0;
  for(int i=0;i<K;i++) for(int A=0;A<=FULL;A++) if(A&(1<<i)) g[A]+=g[A^(1<<i)];
  long long w=0;
  for(int T=1;T<=FULL;T++){ int u=used-g[FULL^T]; int t=__builtin_popcount(T);
    long long term=(1LL<<(14-u))<<(t-1); w += ((t-1)&1)? -term: term; }
  seen[w]=1; cnt++;
}
static void rec(int R,int used,int *deg){
  if(R>FULL){ eval(used); return; }
  for(int v=0; used+v<=14; v++){
    int ok=1; for(int i=0;i<K;i++) if(((R>>i)&1) && deg[i]+v>7){ ok=0; break; }
    if(!ok) break;
    n[R]=v; for(int i=0;i<K;i++) if((R>>i)&1) deg[i]+=v;
    rec(R+1,used+v,deg);
    for(int i=0;i<K;i++) if((R>>i)&1) deg[i]-=v;
  }
  n[R]=0;
}
int main(int argc,char**argv){
  K=atoi(argv[1]); FULL=(1<<K)-1; int deg[8]={0}; rec(1,0,deg);
  printf("k=%d configurations=%lld\n",K,cnt);
  int tg[]={322,326,330,334,16050,16054,16058,16062};
  for(int i=0;i<8;i++) printf("target %d: %s\n",tg[i],seen[tg[i]]?"OCCURS":"no");
  printf("weights = 2 mod 4 in [250,400]:"); for(int w=250;w<=400;w++) if(seen[w]&&(w%4==2)) printf(" %d",w); printf("\n");
  int tot=0; for(int w=0;w<=16384;w++) tot+=seen[w]; printf("distinct weights: %d\n",tot);
  return 0;
}
