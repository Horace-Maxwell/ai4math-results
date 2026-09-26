/* rmcore.h -- truth tables of Boolean functions on F_2^14 packed in 256 x uint64.
   Point x in [0, 2^14): coordinate i (variable x_{i+1}) = bit i of x.
   Truth-table bit x is stored in word x>>6, bit x&63.
   A monomial is a 14-bit mask s: prod_{i in s} x_i, equal to 1 at x iff (x & s) == s.
   Written independently of the scout's numpy code (rm714_witness.py). */
#include <stdint.h>
#include <string.h>
#define M 14
#define N (1u<<M)
#define NW (N/64)
static inline int popc64(uint64_t v){ return __builtin_popcountll(v); }
static inline int weight_tt(const uint64_t *t){ int w=0; for(int j=0;j<NW;j++) w+=popc64(t[j]); return w; }
/* In-place binary Moebius transform (ANF <-> truth table; it is an involution over F_2). */
static void moebius(uint64_t *t){
  static const uint64_t mk[6]={0x5555555555555555ULL,0x3333333333333333ULL,0x0F0F0F0F0F0F0F0FULL,
                               0x00FF00FF00FF00FFULL,0x0000FFFF0000FFFFULL,0x00000000FFFFFFFFULL};
  for(int i=0;i<6;i++){ int s=1<<i; for(int j=0;j<NW;j++){ uint64_t v=t[j]; v ^= (v & mk[i]) << s; t[j]=v; } }
  for(int i=6;i<M;i++){ int s=1<<(i-6); for(int j=0;j<NW;j++) if(j & s) t[j]^=t[j^s]; }
}
static void anf_list_to_tt(const int *mon, int k, uint64_t *t){
  memset(t,0,NW*8); for(int a=0;a<k;a++){ unsigned s=(unsigned)mon[a]; t[s>>6]^=1ULL<<(s&63); } moebius(t);
}
