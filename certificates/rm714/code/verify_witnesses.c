/* Reads lines: <claimed_weight> <k> <m_1> ... <m_k>  (monomial bitmasks)
   Prints: claimed, computed weight (Moebius transform), max monomial degree, #monomials, OK/FAIL. */
#include <stdio.h>
#include <stdlib.h>
#include "rmcore.h"
int main(void){
  int claimed,k; static int mon[20000]; static uint64_t t[NW]; int bad=0,n=0;
  while(scanf("%d %d",&claimed,&k)==2){
    int maxdeg=0, dup=0;
    for(int a=0;a<k;a++){ if(scanf("%d",&mon[a])!=1) return 2; if(mon[a]<0||mon[a]>=(int)N) return 3;
      int d=__builtin_popcount(mon[a]); if(d>maxdeg) maxdeg=d; }
    /* check duplicates (a duplicated monomial would cancel) */
    for(int a=0;a<k;a++) for(int b=a+1;b<k;b++) if(mon[a]==mon[b]) dup=1;
    anf_list_to_tt(mon,k,t); int w=weight_tt(t);
    /* sanity: transform back must give the ANF again */
    moebius(t); int back_ok=1; { static uint64_t u[NW]; memset(u,0,sizeof u); for(int a=0;a<k;a++) u[mon[a]>>6]^=1ULL<<(mon[a]&63); for(int j=0;j<NW;j++) if(u[j]!=t[j]) back_ok=0; }
    int ok = (w==claimed) && (maxdeg<=7) && back_ok && !dup;
    printf("%d %d maxdeg=%d k=%d dup=%d involution=%d %s\n",claimed,w,maxdeg,k,dup,back_ok,ok?"OK":"FAIL");
    if(!ok) bad++; n++;
  }
  fprintf(stderr,"checked %d witnesses, %d failures\n",n,bad); return bad?1:0;
}
