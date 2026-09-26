/* venn_enum_indep.c -- second, independent implementation for Proposition E
   (weights of all sums of k monomials of degree <= 7 in x1..x14, k <= 5).

   Differences from venn_enum.c / venn_enum_fast.c (written separately, shares no code):
   - Enumeration: monomial-by-monomial SPLITTING of the Venn regions.  State: r[P] for every pattern
     P (subset of the monomials processed so far, P = 0 means "in no monomial yet"), sum r[P] = 14.
     Adding monomial i splits every region P into P (not in S_i) and P|{i} (in S_i); the number moved
     is s_P with sum_P s_P = deg S_i <= 7.  Each labelled configuration of the other programs
     (n_R, R nonempty, sum <= 14, deg <= 7) is reached exactly once, so the configuration counts
     must agree (k=4: 8,568,777; k=5: 11,690,447,828).
   - Weight formula: E(Q) = #{x : every monomial in Q equals 1} = 2^{#variables in no monomial of Q}
     = 2^{zeta r (complement of Q)};  N(P) = #{x : exactly the monomials in P equal 1}
     = sum_{Q superset of P} (-1)^{|Q \ P|} E(Q)  (Moebius on the superset lattice);
     wt = sum_{|P| odd} N(P).   (The other programs use sum_T (-2)^{|T|-1} 2^{14-|U_T|}.)
   Usage: venn_enum_indep K NPROC ME OUTFILE   (work split round-robin over prefixes after 3 monomials)
   OUTFILE receives: count line, then the list of weights that occur (one per line). */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SPLITLEVEL 3
static int K, FULL, NPROC, ME;
static int r[32];
static unsigned char seen[16385];
static long long cnt = 0, prefixctr = 0;

static void evalw(void) {
  int z[32];
  for (int A = 0; A <= FULL; A++) z[A] = r[A];
  for (int i = 0; i < K; i++)
    for (int A = 0; A <= FULL; A++)
      if (A >> i & 1) z[A] += z[A ^ (1 << i)];
  long long N[32];
  for (int P = 0; P <= FULL; P++) N[P] = 1LL << z[FULL ^ P];
  for (int i = 0; i < K; i++)
    for (int P = 0; P <= FULL; P++)
      if (!(P >> i & 1)) N[P] -= N[P | (1 << i)];
  long long w = 0, tot = 0;
  for (int P = 0; P <= FULL; P++) {
    if (N[P] < 0) { fprintf(stderr, "negative N\n"); exit(2); }
    tot += N[P];
    if (__builtin_popcount(P) & 1) w += N[P];
  }
  if (tot != 16384 || w < 0 || w > 16384) { fprintf(stderr, "bad total %lld w %lld\n", tot, w); exit(3); }
  seen[w] = 1;
  cnt++;
}

static void rec(int i, int P, int deg) {
  if (P == (1 << i)) {                 /* monomial i finished */
    if (i + 1 == K) { evalw(); return; }
    if (i + 1 == SPLITLEVEL && NPROC > 1) { if ((prefixctr++ % NPROC) != ME) return; }
    rec(i + 1, 0, 0);
    return;
  }
  int avail = r[P], Q = P | (1 << i);
  for (int s = 0; s <= avail && deg + s <= 7; s++) {
    r[P] = avail - s; r[Q] = s;
    rec(i, P + 1, deg + s);
  }
  r[P] = avail; r[Q] = 0;
}

int main(int argc, char **argv) {
  if (argc < 5) { fprintf(stderr, "usage: K NPROC ME OUTFILE\n"); return 1; }
  K = atoi(argv[1]); NPROC = atoi(argv[2]); ME = atoi(argv[3]); FULL = (1 << K) - 1;
  memset(r, 0, sizeof r); r[0] = 14;
  rec(0, 0, 0);
  FILE *fo = fopen(argv[4], "w");
  fprintf(fo, "count %lld\n", cnt);
  for (int w = 0; w <= 16384; w++) if (seen[w]) fprintf(fo, "%d\n", w);
  fclose(fo);
  return 0;
}
