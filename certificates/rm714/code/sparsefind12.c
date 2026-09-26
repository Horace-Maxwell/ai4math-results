/* sparsefind.c -- random sparse ANF sampler for RM(7,14): f = sum of k distinct monomials of degree 1..7
   (optionally plus a transversal pair x1..x7 + x8..x14). For every weight w in [0,16384] it keeps the
   witness with the fewest monomials. Output: lines "w k m1 ... mk" (sorted by w). */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "rmcore12.h"
static uint64_t rs; static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static unsigned bydeg[8][3432]; static int nby[8];
static int best_k[N+1]; static int best_m[N+1][16];
int main(int argc,char**argv){
  rs=strtoull(argv[1],0,10)*0x9E3779B97F4A7C15ULL+7; double secs=atof(argv[2]);
  for(unsigned s=0;s<N;s++){ int d=__builtin_popcount(s); if(d<=6) bydeg[d][nby[d]++]=s; }
  for(int w=0;w<=(int)N;w++) best_k[w]=99;
  static uint64_t t[NW]; int mon[16]; time_t t0=time(0); long it=0;
  while(difftime(time(0),t0)<secs){
    for(int rep=0;rep<2000;rep++){
      int k=1+(int)(rnd()%10); int pair=(rnd()%3==0);
      int kk=0;
      if(pair){ mon[kk++]=0x3F; mon[kk++]=0xFC0; }
      for(int i=0;i<k && kk<16;i++){
        int d; uint64_t r=rnd()%100; d = r<5?1: r<10?2: r<15?3: r<25?4: r<50?5: 6;
        unsigned s=bydeg[d][rnd()%nby[d]]; int dup=0; for(int j=0;j<kk;j++) if(mon[j]==(int)s) dup=1; if(!dup) mon[kk++]=s;
      }
      anf_list_to_tt(mon,kk,t); int w=weight_tt(t); it++;
      if(kk<best_k[w]){ best_k[w]=kk; memcpy(best_m[w],mon,sizeof(int)*kk); }
    }
  }
  int found=0; for(int w=0;w<=(int)N;w++) if(best_k[w]<99){ found++; printf("%d %d",w,best_k[w]); for(int j=0;j<best_k[w];j++) printf(" %d",best_m[w][j]); printf("\n"); }
  fprintf(stderr,"iters=%ld distinct weights found=%d\n",it,found); return 0;
}
