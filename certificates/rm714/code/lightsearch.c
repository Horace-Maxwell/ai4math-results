/* lightsearch.c -- targeted search in the "light side = 6-flat" family (PROOF.md Lemma F / §8):
   f = g || (g + h) on F_2^14 = F_2^13 x F_2, with g = 1_F, F = {x in F_2^13 : x7..x13 = 0} (a 6-flat,
   degree 7) and h in RM(6,13) a XOR of flats of dimension >= 7.  Then f in RM(7,14) and
   wt(f) = 128 + wt(h) - 2|F cap supp h|.  Hill climbing on the flats of h towards a target weight.
   Hits are re-verified by building f's 14-variable truth table and taking its ANF (degree <= 7). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "rmcore.h"
#define M13 13
#define N13 (1u<<M13)
#define NW13 (N13/64)
static uint64_t rs; static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int rndi(int n){ return (int)(rnd()%(uint64_t)n); }
typedef struct { int k; unsigned c; unsigned v[13]; } Flat;
static int rank_of(const unsigned *v,int k){ unsigned b[13]={0}; int r=0;
  for(int i=0;i<k;i++){ unsigned x=v[i]; for(int j=12;j>=0;j--){ if(!((x>>j)&1)) continue; if(!b[j]){ b[j]=x; r++; break;} x^=b[j]; } } return r; }
static void flat_xor(uint64_t *t,const Flat *F){ unsigned p=F->c; int n=1<<F->k; t[p>>6]^=1ULL<<(p&63);
  for(int g=1; g<n; g++){ int b=__builtin_ctz(g); p^=F->v[b]; t[p>>6]^=1ULL<<(p&63);} }
static unsigned pool[24]; static int np;
static void rand_flat(Flat *F){ int dim = 7 + (rndi(5)==0);
  for(;;){ F->k=dim; for(int j=0;j<dim;j++) F->v[j] = (rndi(3)==0)? (unsigned)(rnd()&(N13-1)) : pool[rndi(np)]; if(rank_of(F->v,dim)==dim) break; }
  F->c = (rndi(2)? 0u : (unsigned)(rnd()&(N13-1))) ^ ((rndi(2))? pool[rndi(np)] : 0u); }
static int eval(const Flat *H,int k,int *tt){ static uint64_t h[NW13]; memset(h,0,sizeof h);
  for(int i=0;i<k;i++) flat_xor(h,&H[i]); int w=0; for(int j=0;j<NW13;j++) w+=__builtin_popcountll(h[j]);
  int t=__builtin_popcountll(h[0]); *tt=t; return 128 + w - 2*t; }
static void verify_and_print(const Flat *H,int k,int wf){
  static uint64_t h[NW13]; memset(h,0,sizeof h); for(int i=0;i<k;i++) flat_xor(h,&H[i]);
  static uint64_t f[NW]; memset(f,0,sizeof f);
  /* point (x, x14): index x | (x14<<13); g = 1_F: x in [0,64) */
  for(unsigned x=0;x<N13;x++){ int gx = (x<64); int hx=(h[x>>6]>>(x&63))&1;
    if(gx) f[x>>6]|=1ULL<<(x&63); if(gx^hx){ unsigned y=x|(1u<<13); f[y>>6]|=1ULL<<(y&63);} }
  int w=weight_tt(f); static uint64_t a[NW]; memcpy(a,f,sizeof a); moebius(a);
  int maxdeg=0,cnt=0; for(unsigned s=0;s<N;s++) if((a[s>>6]>>(s&63))&1){ cnt++; int d=__builtin_popcount(s); if(d>maxdeg) maxdeg=d; }
  printf("HIT predicted=%d actual=%d maxdeg=%d nmon=%d anf:",wf,w,maxdeg,cnt);
  for(unsigned s=0;s<N;s++) if((a[s>>6]>>(s&63))&1) printf(" %u",s); printf("\n"); fflush(stdout); }
int main(int argc,char**argv){
  rs=strtoull(argv[1],0,10)*0x9E3779B97F4A7C15ULL+99; double secs=atof(argv[2]); int ntg=argc-3; int tg[16];
  for(int i=0;i<ntg;i++) tg[i]=atoi(argv[3+i]);
  time_t t0=time(0); long it=0; int hist[512]={0};
  while(difftime(time(0),t0)<secs){
    np=13; for(int i=0;i<13;i++) pool[i]=1u<<i; int extra=rndi(5); for(int i=0;i<extra;i++) pool[np++]=(unsigned)(rnd()&(N13-1))|1u<<rndi(13);
    int k=1+rndi(6); Flat H[8], G[8]; for(int i=0;i<k;i++) rand_flat(&H[i]);
    int t; int wf=eval(H,k,&t);
    int best=1<<30; for(int i=0;i<ntg;i++){ int d=abs(wf-tg[i]); if(d<best) best=d; }
    for(int step=0; step<3000; step++){
      memcpy(G,H,sizeof(Flat)*k); int i=rndi(k); int mv=rndi(5);
      if(mv==0){ int j=rndi(G[i].k); unsigned old=G[i].v[j]; G[i].v[j]=pool[rndi(np)]; if(rank_of(G[i].v,G[i].k)<G[i].k) G[i].v[j]=old; }
      else if(mv==1){ int j=rndi(G[i].k); unsigned old=G[i].v[j]; G[i].v[j]^=1u<<rndi(13); if(!G[i].v[j]||rank_of(G[i].v,G[i].k)<G[i].k) G[i].v[j]=old; }
      else if(mv==2){ G[i].c^=pool[rndi(np)]; } else if(mv==3){ G[i].c^=1u<<rndi(13); } else rand_flat(&G[i]);
      int t2; int w2=eval(G,k,&t2); it++;
      if(w2>=0 && w2<512 && (w2&3)==2) hist[w2]++;
      int d=1<<30; for(int q=0;q<ntg;q++){ int e=abs(w2-tg[q]); if(e<d) d=e; }
      if(d==0){ verify_and_print(G,k,w2); }
      if(d<=best || rndi(40)==0){ memcpy(H,G,sizeof(Flat)*k); best=d; }
    }
  }
  printf("DONE iters=%ld\nHIST f-weights (2 mod 4, <512):",it); for(int w=0;w<512;w++) if(hist[w]) printf(" %d:%d",w,hist[w]); printf("\n"); return 0;
}
