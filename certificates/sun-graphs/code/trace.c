/* debug: include sunsearch.c and trace feasibility along a given configuration */
#define main sunsearch_main
#include "sunsearch.c"
#undef main
int main(int argc, char **argv) {
    B = atoi(argv[1]); NMAX = atoi(argv[2]);
    MMAX = (int)floor(sqrt(2.0 * NMAX)); if (MMAX > 9) MMAX = 9;
    gen_spectra();
    memset(&st[0], 0, sizeof(State));
    for (int k = 0; k < B; k++) { P_[k] = atoi(argv[3 + 2 * k]); Q_[k] = atoi(argv[4 + 2 * k]); }
    for (int d = 1; d <= B; d++) {
        push(d, P_[d - 1], Q_[d - 1]);
        State *S = &st[d];
        printf("depth %d feasible=%d  nq=%d Rcnt=%d  Sp:", d, feasible(S, d), S->nq, S->R.cnt);
        for (int m = 2; m <= 9; m++) printf(" %d/%d", S->Sp[m].cnt, S->Sm[m].len - S->Sm[m].cnt);
        printf(" lb4=%lld P=%lld Q=%lld\n", S->lb4, S->P, S->Q);
    }
    printf("leaf_moments=%d\n", leaf_moments());
    for (int i = 0; i < nfeats; i++) { printf("feat %d: gt", i); for (int m = 1; m <= 9; m++) printf(" %d", feats[i].gt[m]); printf(" ge"); for (int m = 2; m <= 9; m++) printf(" %d", feats[i].ge[m]); printf(" m4=%lld s2=%lld\n", feats[i].m4, feats[i].s2); }
    printf("targets:"); for (int i = 0; i < ntarg; i++) printf(" %lld", targ[i]); printf("\n");
    return 0;
}
