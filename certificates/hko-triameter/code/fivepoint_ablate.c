/*
 * Ablation for the five-point lemma S: which constraint groups are needed for infeasibility?
 * Variables in [LO, D] (LO = 0 or 1), d(x,y) = D.
 * Flags (bitmask argv[2]):
 *   1  TRI   : triangle inequalities on all 10 triples
 *   2  FPXY  : sharp BM four-point on {a,b,x,y},{a,c,x,y},{b,c,x,y}
 *   4  FPABC : sharp BM four-point on {a,b,c,x},{a,b,c,y}
 *   8  TRAB  : triameter bound for triples (u,v,x),(u,v,y)
 *   16 NPER  : non-peripherality: all distances from a,b,c are <= D-1 (else only <= D)
 *   32 DIST  : distinct points: all distances >= 1
 * Always: T = eab+eac+ebc >= 2D+1 and negated S: p_u+q_u+D <= T-1 (u = a,b,c).
 * Reports, for each D, whether a counter-model exists (and prints the first one).
 */
#include <stdio.h>
#include <stdlib.h>
static int F;
static int fp(int s1, int s2, int s3) {
  return (s1 == s2 && s3 <= s1 + 2) || (s1 == s3 && s2 <= s1 + 2) || (s2 == s3 && s1 <= s2 + 2);
}
static int tri(int ab, int ac, int bc) { return ab <= ac + bc && ac <= ab + bc && bc <= ab + ac; }
int main(int argc, char **argv) {
  int DMAX = atoi(argv[1]); F = atoi(argv[2]);
  int any = 0;
  for (int D = 1; D <= DMAX; D++) {
    int LO = (F & 32) ? 1 : 0, M = (F & 16) ? D - 1 : D, hit = 0;
    for (int eab = LO; eab <= M && !hit; eab++)
    for (int eac = LO; eac <= M && !hit; eac++)
    for (int ebc = LO; ebc <= M && !hit; ebc++) {
      int T = eab + eac + ebc;
      if (T < 2 * D + 1) continue;
      if ((F & 1) && !tri(eab, eac, ebc)) continue;
      for (int pa = LO; pa <= M && !hit; pa++) for (int qa = LO; qa <= M && !hit; qa++) {
        if ((F & 1) && !tri(D, pa, qa)) continue;
        if (pa + qa + D > T - 1) continue;
        for (int pb = LO; pb <= M && !hit; pb++) for (int qb = LO; qb <= M && !hit; qb++) {
          if ((F & 1) && !tri(D, pb, qb)) continue;
          if (pb + qb + D > T - 1) continue;
          if ((F & 1) && (!tri(eab, pa, pb) || !tri(eab, qa, qb))) continue;
          if ((F & 8) && (eab + pa + pb > T || eab + qa + qb > T)) continue;
          if ((F & 2) && !fp(D + eab, pa + qb, pb + qa)) continue;
          for (int pc = LO; pc <= M && !hit; pc++) for (int qc = LO; qc <= M && !hit; qc++) {
            if ((F & 1) && !tri(D, pc, qc)) continue;
            if (pc + qc + D > T - 1) continue;
            if ((F & 1) && (!tri(eac, pa, pc) || !tri(eac, qa, qc) || !tri(ebc, pb, pc) || !tri(ebc, qb, qc))) continue;
            if ((F & 8) && (eac + pa + pc > T || eac + qa + qc > T || ebc + pb + pc > T || ebc + qb + qc > T)) continue;
            if ((F & 2) && (!fp(D + eac, pa + qc, pc + qa) || !fp(D + ebc, pb + qc, pc + qb))) continue;
            if ((F & 4) && (!fp(eab + pc, eac + pb, ebc + pa) || !fp(eab + qc, eac + qb, ebc + qa))) continue;
            hit = 1;
            printf("  F=%d D=%d T=%d eab=%d eac=%d ebc=%d | pa=%d qa=%d pb=%d qb=%d pc=%d qc=%d\n",
                   F, D, T, eab, eac, ebc, pa, qa, pb, qb, pc, qc);
          }
        }
      }
    }
    if (hit) any = 1;
  }
  printf("F=%d (TRI=%d FPXY=%d FPABC=%d TRAB=%d NPER=%d DIST=%d) D<=%d: %s\n", F, !!(F & 1), !!(F & 2),
         !!(F & 4), !!(F & 8), !!(F & 16), !!(F & 32), DMAX, any ? "COUNTER-MODEL EXISTS" : "infeasible");
  return 0;
}
