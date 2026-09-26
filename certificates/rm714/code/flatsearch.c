/* flatsearch.c -- structured search for codewords of RM(7,14) with weight in a target set,
   as XOR-sums of indicators of affine flats of dimension >= 7 (each such indicator has degree <= 7).
   Modes:
     A: random sums of k flats whose direction vectors are drawn from a small "vector pool"
        (standard basis + t random vectors), offsets random combos of pool vectors (non-distributive
        intersection patterns when t>0).
     B: local search (hill climbing with restarts) on a list of k flats, objective = distance of the
        weight to the nearest target, restricted to weights = 2 mod 4.
   Every hit is printed with its ANF (monomial list, via Moebius transform) and re-checked. */
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "rmcore.h"
static uint64_t rs;
static inline uint64_t rnd(void){ rs ^= rs<<13; rs ^= rs>>7; rs ^= rs<<17; return rs; }
static inline int rndi(int n){ return (int)(rnd()%(uint64_t)n); }
typedef struct { int k; unsigned c; unsigned v[14]; } Flat;
static int rank_of(const unsigned *v,int k){ unsigned b[14]={0}; int r=0;
  for(int i=0;i<k;i++){ unsigned x=v[i]; for(int j=13;j>=0;j--){ if(!((x>>j)&1)) continue; if(!b[j]){ b[j]=x; r++; break;} x^=b[j]; } }
  return r; }
static void flat_xor(uint64_t *t,const Flat *F){
  unsigned p=F->c; int n=1<<F->k; t[p>>6]^=1ULL<<(p&63);
  for(int g=1; g<n; g++){ int b=__builtin_ctz(g); p^=F->v[b]; t[p>>6]^=1ULL<<(p&63); }
}
static int targets[64], nt=0;
static int is_target(int w){ for(int i=0;i<nt;i++) if(targets[i]==w) return 1; return 0; }
static int dist_target(int w){ int d=1<<30; for(int i=0;i<nt;i++){ int e=abs(w-targets[i]); if(e<d) d=e; } return d; }
static void report(const uint64_t *t0, int w, const char *tag, const Flat *F, int k){
  static uint64_t a[NW]; memcpy(a,t0,sizeof a); moebius(a);
  int maxdeg=0, cnt=0; for(unsigned s=0;s<N;s++) if((a[s>>6]>>(s&63))&1){ cnt++; int d=__builtin_popcount(s); if(d>maxdeg) maxdeg=d; }
  printf("HIT w=%d tag=%s maxdeg=%d nmon=%d flats:",w,tag,maxdeg,cnt);
  for(int i=0;i<k;i++){ printf(" [c=%u",F[i].c); for(int j=0;j<F[i].k;j++) printf(",%u",F[i].v[j]); printf("]"); }
  printf(" anf:"); for(unsigned s=0;s<N;s++) if((a[s>>6]>>(s&63))&1) printf(" %u",s); printf("\n"); fflush(stdout);
}
static void random_flat_pool(Flat *F,const unsigned *pool,int np,int dim){
  for(;;){ F->k=dim; for(int j=0;j<dim;j++) F->v[j]=pool[rndi(np)]; if(rank_of(F->v,dim)==dim) break; }
  unsigned c=0; int nb=rndi(4); for(int j=0;j<nb;j++) c^=pool[rndi(np)]; F->c=c;
}
static void random_flat_any(Flat *F,int dim){
  for(;;){ F->k=dim; for(int j=0;j<dim;j++) F->v[j]=(unsigned)(rnd()&(N-1)); if(rank_of(F->v,dim)==dim) break; }
  F->c=(unsigned)(rnd()&(N-1));
}
int main(int argc,char**argv){
  char mode=argv[1][0]; rs=strtoull(argv[2],0,10)*0x9E3779B97F4A7C15ULL+12345; double secs=atof(argv[3]);
  for(int i=4;i<argc;i++) targets[nt++]=atoi(argv[i]);
  time_t t0=time(0); long iters=0; static uint64_t t[NW]; int hist[1024]={0};
  if(mode=='A'){
    unsigned pool[20]; Flat F[8];
    while(difftime(time(0),t0)<secs){
      for(int rep=0;rep<1000;rep++){
        int tpool=rndi(4); int np=14+tpool; for(int i=0;i<14;i++) pool[i]=1u<<i;
        for(int i=14;i<np;i++){ unsigned r; do r=(unsigned)(rnd()&(N-1)); while(__builtin_popcount(r)<2); pool[i]=r; }
        int k=3+rndi(4); memset(t,0,sizeof t);
        for(int i=0;i<k;i++){ int dim = (rndi(4)==0)?8:7; random_flat_pool(&F[i],pool,np,dim); flat_xor(t,&F[i]); }
        int w=weight_tt(t); iters++;
        if(w<1024 && (w&3)==2) hist[w]++;
        if(is_target(w)) report(t,w,"A",F,k);
      }
    }
  } else if(mode=='B'){
    Flat F[8], G[8]; unsigned pool[20];
    while(difftime(time(0),t0)<secs){
      int k=3+rndi(4); int tpool=rndi(4); int np=14+tpool; for(int i=0;i<14;i++) pool[i]=1u<<i;
      for(int i=14;i<np;i++){ unsigned r; do r=(unsigned)(rnd()&(N-1)); while(__builtin_popcount(r)<2); pool[i]=r; }
      for(int i=0;i<k;i++){ int dim=(rndi(4)==0)?8:7; random_flat_pool(&F[i],pool,np,dim); }
      memset(t,0,sizeof t); for(int i=0;i<k;i++) flat_xor(t,&F[i]); int w=weight_tt(t);
      int cur = ((w&3)==2)? dist_target(w) : dist_target(w)+100000;
      for(int step=0; step<4000; step++){
        memcpy(G,F,sizeof(Flat)*k); int i=rndi(k); int mv=rndi(5);
        if(mv==0){ int j=rndi(G[i].k); unsigned old=G[i].v[j]; G[i].v[j]=pool[rndi(np)]; if(rank_of(G[i].v,G[i].k)<G[i].k) G[i].v[j]=old; }
        else if(mv==1){ int j=rndi(G[i].k); unsigned old=G[i].v[j]; G[i].v[j]^= 1u<<rndi(14); if(!G[i].v[j]||rank_of(G[i].v,G[i].k)<G[i].k) G[i].v[j]=old; }
        else if(mv==2){ G[i].c ^= pool[rndi(np)]; }
        else if(mv==3){ G[i].c ^= 1u<<rndi(14); }
        else { int dim=(rndi(4)==0)?8:7; random_flat_pool(&G[i],pool,np,dim); }
        memset(t,0,sizeof t); for(int q=0;q<k;q++) flat_xor(t,&G[q]); int w2=weight_tt(t); iters++;
        if(w2<1024 && (w2&3)==2) hist[w2]++;
        if(is_target(w2)) report(t,w2,"B",G,k);
        int nv = ((w2&3)==2)? dist_target(w2) : dist_target(w2)+100000;
        if(nv<=cur || rndi(50)==0){ memcpy(F,G,sizeof(Flat)*k); cur=nv; }
      }
    }
  } else if(mode=='R'){ /* fully random affine flats (baseline) */
    Flat F[8];
    while(difftime(time(0),t0)<secs){
      for(int rep=0;rep<1000;rep++){ int k=3+rndi(3); memset(t,0,sizeof t);
        for(int i=0;i<k;i++){ random_flat_any(&F[i],7+(rndi(4)==0)); flat_xor(t,&F[i]); }
        int w=weight_tt(t); iters++; if(w<1024 && (w&3)==2) hist[w]++; if(is_target(w)) report(t,w,"R",F,k); }
    }
  }
  printf("DONE mode=%c iters=%ld\nHIST(2 mod 4, <1024):",mode,iters);
  for(int w=0;w<1024;w++) if(hist[w]) printf(" %d:%d",w,hist[w]); printf("\n");
  return 0;
}
