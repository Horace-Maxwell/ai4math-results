/*
 * Five-point feasibility search for Lemma S (HKO Problem 3 route).
 *
 * Points a,b,c (a triametral triple, none peripheral) and x,y (a diametral pair), D = diam.
 * Unknowns: e_ab,e_ac,e_bc, p_u = d(u,x), q_u = d(u,y) (u in {a,b,c}), all integers.
 * Constraints (all valid in a connected DH graph under the hypotheses):
 *   - d(x,y) = D; all other distances in [1, D-1] (a,b,c non-peripheral => ecc <= D-1;
 *     the five points are distinct);
 *   - triangle inequality on all 10 triples of the 5 points;
 *   - Bandelt-Mulder sharp four-point condition on all 5 quadruples:
 *       sorted sums s1<=s2<=s3 satisfy s2==s3 or (s1==s2 and s3<=s1+2);
 *   - T = e_ab+e_ac+e_bc is the triameter: every triple of the 5 points has sum <= T;
 *     T >= 2D+1 (the case T = 2D is trivial);
 *   - NEGATED conclusion of S: p_u + q_u + D <= T - 1 for u = a,b,c.
 * Prints any feasible configuration (a counter-model) for D = 2..DMAX.
 * Mode 2 (argv[2]=2): instead of the negated S-conclusion, drop it and report configurations
 * where the triple has no peripheral vertex (to see what is forced).
 */
#include <stdio.h>
#include <stdlib.h>

static int fp(int s1, int s2, int s3) {
  int t;
  if (s1 > s2) { t = s1; s1 = s2; s2 = t; }
  if (s2 > s3) { t = s2; s2 = s3; s3 = t; }
  if (s1 > s2) { t = s1; s1 = s2; s2 = t; }
  return s2 == s3 || (s1 == s2 && s3 <= s1 + 2);
}
static int tri(int ab, int ac, int bc) {
  return ab <= ac + bc && ac <= ab + bc && bc <= ab + ac;
}

int main(int argc, char **argv) {
  int DMAX = argc > 1 ? atoi(argv[1]) : 12;
  long found_total = 0;
  for (int D = 2; D <= DMAX; D++) {
    long found = 0, cnt = 0;
    int M = D - 1;
    for (int eab = 1; eab <= M; eab++)
    for (int eac = 1; eac <= M; eac++)
    for (int ebc = 1; ebc <= M; ebc++) {
      int T = eab + eac + ebc;
      if (T < 2 * D + 1) continue;
      if (!tri(eab, eac, ebc)) continue;
      for (int pa = 1; pa <= M; pa++) for (int qa = 1; qa <= M; qa++) {
        if (!tri(D, pa, qa)) continue;                 /* x,y,a */
        if (pa + qa + D > T - 1) continue;             /* negated S for a */
        for (int pb = 1; pb <= M; pb++) for (int qb = 1; qb <= M; qb++) {
          if (!tri(D, pb, qb)) continue;
          if (pb + qb + D > T - 1) continue;
          if (!tri(eab, pa, pb) || !tri(eab, qa, qb)) continue;   /* a,b,x ; a,b,y */
          if (eab + pa + pb > T || eab + qa + qb > T) continue;   /* triameter */
          if (!fp(D + eab, pa + qb, pb + qa)) continue;           /* {a,b,x,y} */
          for (int pc = 1; pc <= M; pc++) for (int qc = 1; qc <= M; qc++) {
            if (!tri(D, pc, qc)) continue;
            if (pc + qc + D > T - 1) continue;
            if (!tri(eac, pa, pc) || !tri(eac, qa, qc)) continue;
            if (!tri(ebc, pb, pc) || !tri(ebc, qb, qc)) continue;
            if (eac + pa + pc > T || eac + qa + qc > T) continue;
            if (ebc + pb + pc > T || ebc + qb + qc > T) continue;
            if (!fp(D + eac, pa + qc, pc + qa)) continue;         /* {a,c,x,y} */
            if (!fp(D + ebc, pb + qc, pc + qb)) continue;         /* {b,c,x,y} */
            if (!fp(eab + pc, eac + pb, ebc + pa)) continue;      /* {a,b,c,x} */
            if (!fp(eab + qc, eac + qb, ebc + qa)) continue;      /* {a,b,c,y} */
            cnt++;
            if (found < 5) {
              printf("D=%d T=%d eab=%d eac=%d ebc=%d | pa=%d qa=%d pb=%d qb=%d pc=%d qc=%d\n",
                     D, T, eab, eac, ebc, pa, qa, pb, qb, pc, qc);
            }
            found++;
          }
        }
      }
    }
    printf("D=%d: feasible 5-point counter-models to S: %ld\n", D, cnt);
    found_total += cnt;
    fflush(stdout);
  }
  printf("total %ld\n", found_total);
  return 0;
}
