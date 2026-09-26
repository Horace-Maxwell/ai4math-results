/* cosetsearch.c -- search in the family f = x13*A + x14*B + x13*x14*D  (f vanishes on {x13=x14=0}),
   A, B in RM(6,12) (XOR of flats of dim >= 6 in F_2^12), D in RM(5,12) (XOR of flats of dim >= 7).
   wt(f) = wt(A) + wt(B) + wt(A+B+D).  Hill climbing towards the targets; hits are rebuilt as
   14-variable truth tables, weight recomputed and ANF degree checked. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "rmcore.h"
#define N12 4096u
#define NW12 64
static uint64_t rs; static inline uint64_t rnd(void){ rs^=rs<<13; rs^=rs>>7; rs^=rs<<17; return rs; }
static inline int rndi(int n){ return (int)(rnd()%(uint64_t)n); }
typedef struct { int k; unsigned c; unsigned v[12]; } Flat;
static int rank_of(const unsigned *v,int k){ unsigned b[12]={0}; int r=0;
  for(int i=0;i<k;i++){ unsigned x=v[i]; for(int j=11;j>=0;j--){ if(!((x>>j)&1)) continue; if(!b[j]){ b[j]=x; r++; break;} x^=b[j]; } } return r; }
static void fx(uint64_t *t,const Flat *F){ unsigned p=F->c; int n=1<<F->k; t[p>>6]^=1ULL<<(p&63);
  for(int g=1; g<n; g++){ int b=__builtin_ctz(g); p^=F->v[b]; t[p>>6]^=1ULL<<(p&63);} }
static unsigned pool[20]; static int np;
static void rflat(Flat *F,int mindim){ int dim=mindim+(rndi(4)==0);
  for(;;){ F->k=dim; for(int j=0;j<dim;j++) F->v[j]=(rndi(3)==0)?(unsigned)(rnd()&(N12-1)):pool[rndi(np)]; if(rank_of(F->v,dim)==dim) break; }
  F->c=(rndi(2)?0u:(unsigned)(rnd()&(N12-1)))^(rndi(2)?pool[rndi(np)]:0u); }
typedef struct { int ka,kb,kd; Flat a[4],b[4],d[4]; } St;
static int pc(const uint64_t *t){ int w=0; for(int j=0;j<NW12;j++) w+=__builtin_popcountll(t[j]); return w; }
static int ev(const St *s){ uint64_t A[NW12]={0},B[NW12]={0},C[NW12];
  for(int i=0;i<s->ka;i++) fx(A,&s->a[i]); for(int i=0;i<s->kb;i++) fx(B,&s->b[i]);
  for(int j=0;j<NW12;j++) C[j]=A[j]^B[j]; for(int i=0;i<s->kd;i++) fx(C,&s->d[i]);
  return pc(A)+pc(B)+pc(C); }
static void report(const St *s,int wp){ uint64_t A[NW12]={0},B[NW12]={0},D[NW12]={0};
  for(int i=0;i<s->ka;i++) fx(A,&s->a[i]); for(int i=0;i<s->kb;i++) fx(B,&s->b[i]); for(int i=0;i<s->kd;i++) fx(D,&s->d[i]);
  static uint64_t f[NW]; memset(f,0,sizeof f);
  for(unsigned x=0;x<N12;x++){ int a=(A[x>>6]>>(x&63))&1, b=(B[x>>6]>>(x&63))&1, d=(D[x>>6]>>(x&63))&1;
    /* points (x, x13, x14): index x | x13<<12 | x14<<13 */
    if(a){ unsigned y=x|(1u<<12); f[y>>6]|=1ULL<<(y&63);} if(b){ unsigned y=x|(1u<<13); f[y>>6]|=1ULL<<(y&63);}
    if(a^b^d){ unsigned y=x|(3u<<12); f[y>>6]|=1ULL<<(y&63);} }
  int w=weight_tt(f); static uint64_t an[NW]; memcpy(an,f,sizeof an); moebius(an); int md=0;
  printf("HIT predicted=%d actual=%d anf:",wp,w); for(unsigned s2=0;s2<N;s2++) if((an[s2>>6]>>(s2&63))&1){ printf(" %u",s2); int dd=__builtin_popcount(s2); if(dd>md) md=dd; }
  printf(" maxdeg=%d\n",md); fflush(stdout); }
int main(int argc,char**argv){
  rs=strtoull(argv[1],0,10)*0x9E3779B97F4A7C15ULL+17; double secs=atof(argv[2]); int ntg=argc-3; int tg[16]; for(int i=0;i<ntg;i++) tg[i]=atoi(argv[3+i]);
  time_t t0=time(0); long it=0; int hist[1024]={0};
  while(difftime(time(0),t0)<secs){
    np=12; for(int i=0;i<12;i++) pool[i]=1u<<i; int ex=rndi(4); for(int i=0;i<ex;i++) pool[np++]=(unsigned)(rnd()&(N12-1))|1u<<rndi(12);
    St s; s.ka=1+rndi(3); s.kb=1+rndi(3); s.kd=rndi(4);
    for(int i=0;i<s.ka;i++) rflat(&s.a[i],6); for(int i=0;i<s.kb;i++) rflat(&s.b[i],6); for(int i=0;i<s.kd;i++) rflat(&s.d[i],7);
    int w=ev(&s); int best=1<<30; for(int q=0;q<ntg;q++){ int e=abs(w-tg[q]); if(e<best) best=e; }
    for(int step=0;step<3000;step++){
      St t=s; int which=rndi(3); Flat *F; int k= which==0? t.ka: which==1? t.kb: t.kd; if(k==0){ which=0; k=t.ka; }
      F = which==0? &t.a[rndi(k)] : which==1? &t.b[rndi(k)] : &t.d[rndi(k)]; int mind = which==2? 7: 6;
      int mv=rndi(5);
      if(mv==0){ int j=rndi(F->k); unsigned o=F->v[j]; F->v[j]=pool[rndi(np)]; if(rank_of(F->v,F->k)<F->k) F->v[j]=o; }
      else if(mv==1){ int j=rndi(F->k); unsigned o=F->v[j]; F->v[j]^=1u<<rndi(12); if(!F->v[j]||rank_of(F->v,F->k)<F->k) F->v[j]=o; }
      else if(mv==2) F->c^=pool[rndi(np)]; else if(mv==3) F->c^=1u<<rndi(12); else rflat(F,mind);
      int w2=ev(&t); it++; if(w2<1024 && (w2&3)==2) hist[w2]++;
      int d=1<<30; for(int q=0;q<ntg;q++){ int e=abs(w2-tg[q]); if(e<d) d=e; }
      if(d==0) report(&t,w2);
      if(d<=best || rndi(40)==0){ s=t; best=d; }
    }
  }
  printf("DONE iters=%ld\nHIST (2 mod 4,<1024):",it); for(int w=0;w<1024;w++) if(hist[w]) printf(" %d:%d",w,hist[w]); printf("\n"); return 0;
}
