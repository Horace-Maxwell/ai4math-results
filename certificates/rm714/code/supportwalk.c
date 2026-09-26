/* supportwalk.c -- support-guided random walk in the low-weight region of RM(7,14).
   State: truth table f (always in RM(7,14), since we only XOR indicators of flats of dim >= 7).
   Move: pick x0 in supp f and k in {7,8} directions among differences y - x0 (y in supp f) or random
   vectors, build the flat x0 + span, XOR it in.  Such flats tend to overlap supp f heavily, so the
   walk stays among low-weight codewords.  Weight window [240, 520]; biased towards the targets.
   Start: 3-flat configurations giving 314 / 318 / 338 or the transversal pair (254). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "rmcore.h"
static uint64_t rs; static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int rndi(int n){ return (int)(rnd()%(uint64_t)n); }
static int rank_of(const unsigned *v,int k){ unsigned b[14]={0}; int r=0;
  for(int i=0;i<k;i++){ unsigned x=v[i]; for(int j=13;j>=0;j--){ if(!((x>>j)&1)) continue; if(!b[j]){ b[j]=x; r++; break;} x^=b[j]; } } return r; }
static void flat_xor(uint64_t *t,unsigned c,const unsigned *v,int k){ unsigned p=c; int n=1<<k; t[p>>6]^=1ULL<<(p&63);
  for(int g=1; g<n; g++){ int b=__builtin_ctz(g); p^=v[b]; t[p>>6]^=1ULL<<(p&63);} }
static int supp[20000];
static int list_supp(const uint64_t *t){ int n=0; for(int j=0;j<NW;j++){ uint64_t x=t[j]; while(x){ int b=__builtin_ctzll(x); supp[n++]=j*64+b; x&=x-1; } } return n; }
static void mono_flat(uint64_t *t,unsigned mask){ /* indicator of {x : x & mask == mask} */
  unsigned free_=(~mask)&(N-1); unsigned v[14]; int k=0; for(int i=0;i<14;i++) if((free_>>i)&1) v[k++]=1u<<i; flat_xor(t,mask,v,k); }
int main(int argc,char**argv){
  rs=strtoull(argv[1],0,10)*0x9E3779B97F4A7C15ULL+5; double secs=atof(argv[2]); int ntg=argc-3; int tg[16];
  for(int i=0;i<ntg;i++) tg[i]=atoi(argv[3+i]);
  static uint64_t f[NW], g[NW]; time_t t0=time(0); long it=0; int hist[1024]={0}; int hits=0;
  while(difftime(time(0),t0)<secs){
    memset(f,0,sizeof f);
    /* start: x1..x7 + x8..x14 (+ optional third monomial) */
    mono_flat(f,0x7F); mono_flat(f,0x3F80);
    if(rndi(2)){ unsigned m; do m=(unsigned)(rnd()&(N-1)); while(__builtin_popcount(m)!=7); mono_flat(f,m); }
    int w=weight_tt(f);
    for(int step=0; step<20000; step++){
      int n=list_supp(f); if(n==0) break;
      unsigned x0=supp[rndi(n)]; int k=7+(rndi(3)==0); unsigned v[14]; int tries=0;
      do { for(int j=0;j<k;j++){ v[j] = (rndi(4)==0)? (unsigned)(rnd()&(N-1)) : (unsigned)(supp[rndi(n)]^x0); } tries++; } while(rank_of(v,k)<k && tries<50);
      if(rank_of(v,k)<k) continue;
      memcpy(g,f,sizeof g); flat_xor(g,x0,v,k); int w2=weight_tt(g); it++;
      if(w2<1024 && (w2&3)==2) hist[w2]++;
      for(int q=0;q<ntg;q++) if(w2==tg[q]){ hits++; static uint64_t a[NW]; memcpy(a,g,sizeof a); moebius(a);
        int maxdeg=0; printf("HIT w=%d anf:",w2); for(unsigned s=0;s<N;s++) if((a[s>>6]>>(s&63))&1){ printf(" %u",s); int d=__builtin_popcount(s); if(d>maxdeg) maxdeg=d; } printf(" maxdeg=%d\n",maxdeg); fflush(stdout); }
      if(w2<240 || w2>520) continue;
      int d1=1<<30,d2=1<<30; for(int q=0;q<ntg;q++){ int e=abs(w-tg[q]); if(e<d1) d1=e; e=abs(w2-tg[q]); if(e<d2) d2=e; }
      if(d2<=d1 || rndi(8)==0){ memcpy(f,g,sizeof f); w=w2; }
    }
  }
  printf("DONE iters=%ld hits=%d\nHIST (2 mod 4, <1024):",it,hits); for(int w=0;w<1024;w++) if(hist[w]) printf(" %d:%d",w,hist[w]); printf("\n"); return 0;
}
