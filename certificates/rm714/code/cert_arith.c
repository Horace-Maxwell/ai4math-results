/* cert_arith.c -- implementation 2 (C) of the finite arithmetic certificates of PROOF.md
   (Propositions C, C', D, Lemma F).  Written separately from cert_arith.py; the two outputs are
   diffed line by line (logs/cert_arith_diff.log).  Different loop structure: triples are found by
   solving for c = w - a - b and testing membership with a lookup table; the D equations are solved
   by scanning all (a,b) pairs / all (alpha,beta) pairs; F4 uses integer square comparison. */
#include <stdio.h>
#include <string.h>

static const int U0[4] = {322, 326, 330, 334};
static const int UD[8] = {322, 326, 330, 334, 16062, 16058, 16054, 16050};   /* D is checked on all of U */
static const int L6[] = {0, 64, 96, 112, 120, 124, 126, 128, 136, 144, 148, 152, 154, 156, 158, 160, 162, 164, 166};
static int isL6[400];

static int in_p2_0to64(int s) { if (s == 0) return 1; for (int j = 0; j <= 6; j++) if (s == (1 << j)) return 1; return 0; }

int main(void) {
  int nL = (int)(sizeof L6 / sizeof L6[0]);
  memset(isL6, 0, sizeof isL6);
  for (int i = 0; i < nL; i++) isL6[L6[i]] = 1;
  /* C1 / C' */
  for (int k = 0; k < 4; k++) {
    int w = U0[k], found = 0;
    printf("C triples w=%d:", w);
    for (int i = 0; i < nL; i++) for (int j = i; j < nL; j++) {
      int a = L6[i], b = L6[j], c = w - a - b;
      if (c < b || c > a + b || c >= 400 || !isL6[c]) continue;
      printf(" (%d,%d,%d)", a, b, c); found = 1;
    }
    if (!found) printf(" none");
    printf("\n");
  }
  { int m = 0; for (int k = 0; k < 4; k++) if (U0[k] / 2 > m) m = U0[k] / 2; printf("C max needed weight: %d\n", m); }
  { int tr[5][3] = {{64,126,136},{64,126,144},{64,112,154},{64,112,158},{96,126,112}};
    for (int i = 0; i < 5; i++) printf("C' overlap wt=%d,%d sum=%d: %d\n", tr[i][0], tr[i][1], tr[i][2], (tr[i][0] + tr[i][1] - tr[i][2]) / 2); }
  { int ss[4] = {23, 25, 27, 29};
    for (int i = 0; i < 4; i++) { int ok = 0;
      for (int p = 0; p <= ss[i]; p++) if (in_p2_0to64(p) && in_p2_0to64(ss[i] - p)) ok = 1;
      printf("C' %d is sum of two of {0,1,2,...,64}: %s\n", ss[i], ok ? "True" : "False"); } }
  { int tg[2] = {11, 9};
    for (int i = 0; i < 2; i++) { int any = 0; printf("C' 1+2^j-2t=%d solutions (t,2^j): ", tg[i]);
      for (int t = 0; t <= 1; t++) { int v = tg[i] - 1 + 2 * t; if (in_p2_0to64(v)) { printf(any ? ", (%d, %d)" : "[(%d, %d)", t, v); any = 1; } }
      printf(any ? "]\n" : "none\n"); } }
  printf("C' (96,112,126) bound 3+48=%d < 55: %s\n", 51, 51 < 55 ? "True" : "False");
  /* D, case p in F3 */
  printf("D p in F3 solutions (d,w,a,b,a+b<=d):");
  { int any = 0;
    for (int d = 7; d <= 14; d++) for (int k = 0; k < 8; k++) for (int a = 1; a <= 7; a++) for (int b = a; b <= 7; b++) {
      long rhs = (1L << d) + 258 - UD[k];
      if ((1L << (a + 1)) + (1L << (b + 1)) == rhs) { printf(" (%d, %d, %d, %d, %s)", d, UD[k], a, b, a + b <= d ? "True" : "False"); any = 1; } }
    if (!any) printf(" none"); printf("\n"); }
  /* D, case p not in F3 */
  printf("D p notin F3 solutions (d,w,alpha,beta):");
  { int any = 0; int PB[8] = {0, 2, 4, 8, 16, 32, 64, 128};
    for (int d = 7; d <= 14; d++) for (int k = 0; k < 8; k++) for (int i = 0; i < 8; i++) for (int j = i; j < 8; j++) {
      long rhs = (1L << (d - 1)) + 127 - UD[k] / 2;
      if (PB[i] + PB[j] == rhs) { printf(" (%d, %d, %d, %d)", d, UD[k], PB[i], PB[j]); any = 1; } }
    if (!any) printf(" none"); printf("\n"); }
  { static int seen[40000]; memset(seen, 0, sizeof seen);
    for (int a = 7; a <= 14; a++) for (int b = 7; b <= 14; b++) {
      int lo = a + b - 14 > 0 ? a + b - 14 : 0, hi = a < b ? a : b;
      long wt0 = (1L << a) + (1L << b);
      if (wt0 % 4 == 2) seen[wt0] = 1;
      for (int j = lo; j <= hi; j++) { long wt = wt0 - 2L * (1L << j); if (wt % 4 == 2) seen[wt] = 1; } }
    printf("D two flats, weights = 2 mod 4: ["); int first = 1;
    for (int w = 0; w < 40000; w++) if (seen[w]) { printf(first ? "%d" : ", %d", w); first = 0; }
    printf("]\n"); }
  printf("D three pairwise transversal 7-flats: [%d, %d]\n", 384 - 6, 384 - 6 + 4);
  /* F3 */
  for (int k = 0; k < 4; k++) { long w = U0[k], cw = w * (w - 1) / 2;
    printf("F3 w=%ld C(w,2)=%ld > %d: %s -> wt h <= %ld\n", w, cw, 3 * 16383, cw > 3 * 16383 ? "True" : "False", w - 10); }
  /* F6 */
  for (int k = 0; k < 4; k++) { long w = U0[k], cw = w * (w - 1) / 2, bad = (cw - 16383) / 4;
    printf("F6 w=%ld C(w,2)=%ld < 5*16383=%d: %s; directions with n_a in {1,3} >= %ld; wt h in {%ld, %ld}\n", w, cw, 5 * 16383, cw < 5 * 16383 ? "True" : "False", 16383 - bad, w - 2, w - 6); }
  /* F4 */
  for (int k = 0; k < 4; k++) { long w = U0[k], num = 16384 * w - w * w, best = -1;
    for (long s = 2; s < 200; s += 4) if (s * s * 16383 >= num) { best = s; break; }
    printf("F4 w=%ld num=%ld s_min=%ld light<=%ld\n", w, num, best, (w - best) / 2); }
  /* F5 */
  { int KT[6] = {128, 192, 224, 240, 248, 252}; int wh[6], tt[6], n = 0;
    for (int i = 0; i < 6; i++) { int twot = 128 + KT[i] - 322; if (twot > 0 && (twot / 2) % 2 == 1) { wh[n] = KT[i]; tt[n] = twot / 2; n++; } }
    printf("F5 (wt h, t): [");
    for (int i = 0; i < n; i++) printf(i ? ", (%d, %d)" : "(%d, %d)", wh[i], tt[i]);
    printf("]\n");
    for (int i = 0; i < n; i++) { int any = 0;
      printf("F5 two-flat form (KT type II) wt h=%d t=%d: (s, |F cap B|) powers of two: ", wh[i], tt[i]);
      for (int s = 0; s <= 1; s++) { int v = tt[i] - 1 + 2 * s; int pw = 0; for (int j = 0; j <= 6; j++) if (v == (1 << j)) pw = 1;
        if (pw) { printf(any ? ", (%d, %d)" : "[(%d, %d)", s, v); any = 1; } }
      printf(any ? "]\n" : "none\n"); } }
  return 0;
}
