/* venn_enum.c -- exhaustive enumeration of the weights of all polynomials in 14 variables over F_2
   that are sums of k monomials of degree <= 7 (k <= K), up to permutation of variables.
   A configuration is the vector of Venn-region sizes n_R (R a nonempty subset of {0..k-1}):
   n_R = number of variables lying in exactly the monomials indexed by R.  Constraints:
   sum_R n_R <= 14, deg S_i = sum_{R contains i} n_R <= 7.  Weight by inclusion-exclusion:
   wt = sum_{T nonempty} (-2)^{|T|-1} 2^{14 - |U_T|},  |U_T| = sum_{R : R meets T} n_R.
   (Coinciding monomials are allowed; they cancel and give a shorter polynomial.)
   Prints the set of weights that occur, and whether any target weight occurs. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
static int K, nreg; static int n[64]; static char seen[16385];
static long long cnt=0;
static void eval(void){
  int U[64]; long long w=0;
  for(int T=1; T<(1<<K); T++){
    int u=0; for(int R=1; R<(1<<K); R++) if(R&T) u+=n[R];
    int t=__builtin_popcount(T); long long term = 1LL<<(14-u); if((t-1)&1) term=-term; w += term * (1LL<<(t-1));
  }
  if(w<0||w>16384){ fprintf(stderr,"bad w %lld\n",w); exit(1); }
  seen[w]=1; cnt++;
}
static void rec(int R, int used, int *deg){
  if(R==(1<<K)){ eval(); return; }
  for(int v=0; used+v<=14; v++){
    int ok=1; for(int i=0;i<K;i++) if((R>>i)&1) if(deg[i]+v>7) ok=0;
    if(!ok) break;
    n[R]=v; for(int i=0;i<K;i++) if((R>>i)&1) deg[i]+=v;
    rec(R+1, used+v, deg);
    for(int i=0;i<K;i++) if((R>>i)&1) deg[i]-=v;
  }
  n[R]=0;
}
int main(int argc,char**argv){
  K=atoi(argv[1]); int deg[8]={0}; memset(seen,0,sizeof seen);
  rec(1,0,deg);
  printf("k=%d configurations=%lld\n",K,cnt);
  int tg[]={322,326,330,334,16050,16054,16058,16062};
  for(int i=0;i<8;i++) printf("target %d: %s\n",tg[i],seen[tg[i]]?"OCCURS":"no");
  printf("weights = 2 mod 4 in [250,400]:"); for(int w=250;w<=400;w++) if(seen[w]&&(w%4==2)) printf(" %d",w); printf("\n");
  printf("all weights in [0,400]:"); for(int w=0;w<=400;w++) if(seen[w]) printf(" %d",w); printf("\n");
  return 0;
}
