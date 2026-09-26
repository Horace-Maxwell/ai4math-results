# PROOF: minimum order of a counterexample to Conjecture 2, and odd girth (arXiv:2609.28754v1)

Agent `sun-graphs`, 2026-09-26, 18:42–20:10 UTC. The problem is fixed in CONTRACT.md.

## Status

| Item | Status |
|---|---|
| Literature, G1 | **No prior solution found.** Only v1 on arXiv. See querylog.tsv, 60+ rows.<br>• trureturing issues and PRs: 0 hits. The versioned-id positive control 2609.25128v1 → #9523 works.<br>• GitHub global issues, PRs, commits, code, repos: 0 relevant hits.<br>• MathDB, 5 title queries: 0 relevant. The paper is not indexed yet.<br>• SCOPE2026 tree: 0. The tree ends at 2026/09/21, before the paper.<br>• MO and MSE via the StackExchange API: 0.<br>• Web: only the paper itself.<br>**Failures:** OpenAlex (HTTP 429, twice); 2 GitHub commit searches (403 secondary rate limit); trureturing filename grep (method invalid, because the positive control returned 0). |
| Statement | Fixed in CONTRACT.md. We use the strong reading: P1 and P2 may be mixed at the same cycle vertex. |
| Mathematics: Q-min | **Settled: 42 is the minimum order.** Follow-up at 20:00–21:30 UTC: the 42-vertex graph is also **unique** up to 42 vertices (Theorem 1′).<br>• Theorem 1 is proved by Lemmas 1–8 plus an exhaustive exact search.<br>• Implementation A covers all cases.<br>• Independent implementations B and B2 confirm every case: b = 3, 6 by exact search; b = 10 by B2, whose pruning uses LAPACK with a 10⁻⁶ margin; odd b by B's own spectrum enumeration. |
| Mathematics: Q-girth | **Partial.**<br>• Theorem 2 constrains odd girth: b must satisfy K_b ∣ 2b, so b ∈ {3, 15, 27, 39, 63, …}; see the Theorem 2 corollary for the full list below 200. Girth 15 or more needs n ≥ 102.<br>• No integral generalized sun graph has a triangle and ≤ 49 vertices.<br>• Classification up to 41 vertices: only b = 4 occurs, with exactly 3 graphs. The b = 8 and b = 12 cases are checked by A only.<br>• Whether b must be even, or must lie in {4, 6}, remains open. |
| Formal (Lean) | **Not attempted.**<br>• The main theorem rests on an exhaustive search of about 10⁸ nodes, so a Lean proof would need the pruning lemmas formalized. That is out of scope for 1.5 h.<br>• Theorem 2 (odd girth) is a good Lean candidate for later: Fermat's little theorem plus trace identities. |

## Setting and notation

**Setup.**
- $G=G(b;p,q)$: cycle $v_0\cdots v_{b-1}$ with $b\ge3$.
- At $v_k$ hang $p_k$ pendant vertices (copies of $P_1$) and $q_k$ pendant $P_2$'s.
- Order $n=b+\sum_k(p_k+2q_k)$. Degree $d_k=2+p_k+q_k$ at $v_k$.
- Write $P=\sum p_k$, $Q=\sum q_k$, $K_p=\{k:p_k>0\}$, $K_q=\{k:q_k>0\}$, $Z=\{k:q_k=0\}$, $\#q=|K_q|$.

**Why only $P_1$ and $P_2$.** By Theorem 2.1 of the paper (every graph with a pendant path of $\ge3$ edges has an eigenvalue in $(1,2\cos\frac\pi9]$), an integral generalized sun graph has only such attachments.

**Spectral counts.**
- $N_{>t}(G)$ and similar denote eigenvalue counts with multiplicity.
- For integral $G$: $B^+$ is the multiset of eigenvalues $\ge2$, and $B^-$ the multiset of eigenvalues $\le-2$.

**Main results.**
- **Theorem 1 (answers Q-min).** Let $G$ be an integral generalized sun graph that is not a cycle, with at most 41 vertices. Then $4\mid b$. Hence the minimum order of a counterexample to Conjecture 2 is 42, attained by $C_{6,1}(0,6,6,12,6,6)$.
- **Theorem 1′ (uniqueness at 42, follow-up).** $C_{6,1}(0,6,6,12,6,6)$ is the only counterexample with at most 42 vertices, up to isomorphism.
  - Coverage: $b=3$; $b\in\{6,10,14,18\}$ (Lemma 6, corrected); odd $b\ge5$ by Theorem 2 and the support bound.
  - Every case has at least two independent confirmations: two different programs, or a program plus a hand proof. See the follow-up section at the end.
- **Theorem 2 (odd girth, any integral unicyclic graph).** Let $G$ be an integral unicyclic graph whose cycle has odd length $b$. Put $K_b=\prod_{q\ \mathrm{prime},\ (q-1)\mid(b-1)}q$. Then $K_b\mid 2b$. In particular $3\mid b$.
  - Moreover at least $(b-1)/2$ values $v\ge2$ satisfy $\mathrm{mult}(v)\ne\mathrm{mult}(-v)$.
  - Hence $\rho\ge(b+1)/2$ and $2n\ge\sum_{v=2}^{(b+1)/2}v^2$.
  - Corollary: the odd cycle lengths not excluded are 3, 15, 27, 39, 63, 75, 87, 99, 123, 135, 147, 159, 183, 195 below 200. Cycle length 15 needs $n\ge102$.

## Lemmas and proofs

**Lemma 1 (Schur reduction).** Let $\lambda\notin\{0,\pm1\}$ and $f_k(\lambda)=p_k/\lambda+q_k\lambda/(\lambda^2-1)$. Then $A(G)-\lambda I$ is congruent to $S(\lambda)\oplus E(\lambda)$, where:
- $S(\lambda)=A(C_b)-\lambda I+\mathrm{diag}(f_k(\lambda))$;
- $E(\lambda)$ is the direct sum of the blocks $[-\lambda]$ (one per pendant vertex) and $\begin{psmallmatrix}-\lambda&1\\1&-\lambda\end{psmallmatrix}$ (one per $P_2$).

Consequences:
- For $\lambda>1$: $N_{>\lambda}(G)=n_+(S(\lambda))$ and $N_{\ge\lambda}(G)=n_{\ge0}(S(\lambda))$.
- For $\lambda<-1$: $N_{<\lambda}(G)=n_-(S(\lambda))$ and $N_{\le\lambda}(G)=n_{\le0}(S(\lambda))$.
- $N_{>1}(G)\ge\#q+n_+(R)$ with $R=(A(C_b)-I+\mathrm{diag}\,p)|_Z$.
- $N_{<-1}(G)\ge\#q+n_-(R')$ with $R'=(A(C_b)+I-\mathrm{diag}\,p)|_Z$.

*Proof.*
- **Congruence.** Eliminate the attached blocks, which are invertible for $\lambda\notin\{0,\pm1\}$, by a Schur complement. The $(1,1)$ entry of $(E_{P_2})^{-1}$ is $-\lambda/(\lambda^2-1)$, which gives the $q_k$ term.
- **Counts for $|\lambda|>1$.** Sylvester's law of inertia applies, and $E(\lambda)$ is negative definite for $\lambda>1$ and positive definite for $\lambda<-1$.
- **The bound at 1.** For $\lambda\downarrow1$, the entries $f_k(\lambda)$ with $k\in K_q$ tend to $+\infty$. So $S_{K_qK_q}$ is positive definite, and by Haynsworth $n_+(S)=\#q+n_+(\text{Schur complement})$. The Schur complement tends to $R$. Positive eigenvalues persist under small perturbations, and $N_{>1}=\lim_{\lambda\downarrow1}N_{>\lambda}$.
- **The bound at $-1$.** Symmetric, with $f_k\to-\infty$. ∎

**Lemma 2 (multiplicity at most 2).** Let $m\notin\{0,\pm1\}$. An eigenvector for $m$ vanishing on the cycle is 0: on a pendant $m x_a=0$; on a $P_2$, $m^2x_w=x_w$. The cycle part satisfies $x_{k-1}+x_{k+1}=c_kx_k$ with $c_k=m-f_k(m)$, and every $b$-periodic solution extends to an eigenvector. Therefore $\mathrm{mult}(m)=\dim\ker(M-I)\le2$, where $M=\prod_k\begin{psmallmatrix}c_k&-1\\1&0\end{psmallmatrix}\in SL_2(\mathbb Q)$:
- $\mathrm{mult}=2$ iff $M=I$;
- $\mathrm{mult}=1$ iff $\operatorname{tr}M=2$ and $M\neq I$;
- otherwise $\mathrm{mult}=0$.

**Lemma 3 (eigenvalues 0 and ±1, exact formulas).**
- **Eigenvalue 0.** $\mathrm{mult}(0)=\sum_{K_p}(p_k-1)+\delta_0$. Here $\delta_0$ is the dimension of $\{x\in\mathbb R^b: x_k=0\ (k\in K_p),\ x_{k-1}+x_{k+1}=0\ (k\notin K_p)\}$:
  - if $K_p=\emptyset$: $\delta_0=2$ if $4\mid b$, else 0;
  - otherwise: $\delta_0$ is the number of cyclically consecutive pairs of $K_p$-vertices at even distance.
- **Eigenvalues ±1.** $\mathrm{mult}(\pm1)=\sum_{K_q}(q_k-1)+\delta_{\pm}$. Here $\delta_\pm$ is the dimension of $\{x: x_k=0\ (k\in K_q),\ x_{k-1}+x_{k+1}=\pm(1-p_k)x_k\ (k\notin K_q)\}$. It is computed by the monodromy if $K_q=\emptyset$, and otherwise by a continuant test on each gap between consecutive $K_q$ vertices.

*Proof.* Direct from the eigen-equations.
- A pendant vertex forces $x_v=0$ for $\lambda=0$.
- A $P_2$ forces $x_v=0$ for $\lambda=\pm1$.
- The free pendant or $P_2$ values give $p_k-1$ (resp. $q_k-1$) dimensions.

Consequences:
- $\mathrm{mult}(\pm1)\le\max(Q,2)$.
- These formulas and Lemma 2 agree with numpy on 3,877 random graphs, all 19 multiplicities each (`code/validate_leaf.py`). ∎

**Lemma 4 (moments).** Let $G$ be unicyclic with $b\ne4$ and integral. Then:
- (a) $\sum\lambda^2=2n$.
- (b) $\sum_{|\lambda|\ge2}\lambda^2(\lambda^2-1)=2\sum_v d_v(d_v-1)$.
  - Reason: closed 4-walks give $\operatorname{tr}A^4=2|E|+2\sum_v d_v(d_v-1)+8c_4$, and $c_4=0$.
  - For $b=4$, add 8 on the right; this is used only in the positive control.
- (c) Consequences for integral $G$:
  - Bipartite: $\sum_{B^+}\lambda^2=n-\mathrm{mult}(1)\in[n-\max(Q,2),\,n]$.
  - Odd $b$: $\sum_{B^\pm}\lambda^2\in[2n-2\max(Q,2),\,2n]$.
  - Hence $P+Q\le S_2-b+2$ (bipartite) or $P+Q\le S_2/2-b+2$ (odd), where $S_2$ denotes that sum. ∎

**Lemma 5 (admissible spectra).** Let $G$ be integral with $n\le N$. Then:
- $\rho$ is simple and $\rho\ge3$, because $G\supsetneq C_b$ is connected.
- $|\lambda|\le\rho$, and $|\lambda|\le\lfloor\sqrt{2N}\rfloor\le9$ for $N\le49$.
- For odd $b$, $-\rho$ is not an eigenvalue.
- Values $\ge2$ in absolute value have multiplicity at most 2 (Lemma 2).
- Bipartite case: $\sum_{B^+}\lambda^2\le N$.
- Odd $b$:
  - $\sum_{B^\pm}\lambda^2\le 2N$;
  - $\sum_{B^\pm}(\lambda^L-\lambda)=0$ for odd $3\le L<b$, and $=2b$ for $L=b$ (Theorem 2).

For $N\le41$ and even $b$, this gives $|B^+|\le4$, because five values need $4^2+2\cdot3^2+2\cdot2^2=42$.

**Theorem 2 proof.**
- A closed walk of odd length contains an odd cycle. So $\operatorname{tr}A^L=0$ for odd $L<b$, and $\operatorname{tr}A^b=2b$: the only closed $b$-walks go once round the cycle.
- Subtracting $\operatorname{tr}A=0$ gives $\sum_\lambda(\lambda^b-\lambda)=2b$.
- For a prime $q$ with $(q-1)\mid(b-1)$, Fermat gives $\lambda^b\equiv\lambda\pmod q$ for every integer $\lambda$. Hence $q\mid 2b$.
- For the second claim, write $\delta_v=\mathrm{mult}(v)-\mathrm{mult}(-v)$. Then $\sum_v\delta_v(v^L-v)=0$ for the $(b-3)/2$ odd values $L<b$.
- The matrix $[v^{L}-v]$ is a column-scaled Vandermonde-type matrix: for distinct $v^2\neq1$, $\det[w_i^j-1]\ne0$, via the Vandermonde matrix on $\{1,w_1,\dots\}$.
- So if $|\mathrm{supp}\,\delta|\le(b-3)/2$ then $\delta=0$, contradicting $\sum\delta_v(v^b-v)=2b$. ∎

**Lemma 6 (range of b for $n\le41$).**
- **Odd $b$.**
  - $K_b\nmid2b$ for $b=5,7,9,11,13$.
  - $b=15$ needs $2n\ge\sum_{v=2}^8v^2=203$.
  - $b\ge17$ needs even more.
  - So $b=3$ is the only odd case.
- **$b\equiv2\pmod 4$.** Interlacing with the induced $C_b$ gives $N_{>1}(C_b)\le N_{>1}(G)=|B^+|\le4$. Since $N_{>1}(C_b)=2\lceil b/6\rceil-1$, we get $b\le12$, so $b\in\{6,10\}$.
  - For $N=42$: $|B^+|\le5$, because six values would need at least $5^2+4^2+2\cdot3^2+2\cdot2^2=67>42$. Then $N_{>1}(C_b)\le5$ gives $b\in\{6,10,14,18\}$: $N_{>1}(C_{14})=N_{>1}(C_{18})=5$ and $N_{>1}(C_{22})=7$. Odd $b$ is still only $b=3$, since $b=15$ needs $2n\ge203>84$. *Correction at 20:01 UTC:* the first version of this line said $b\in\{6,10,14\}$ and omitted $b=18$.

**Lemma 7 (pruning bounds; monotonicity).** Let $X=\{0,\dots,j-1\}$ with $j\le b-1$.
- **Principal submatrices.** The tridiagonal path matrices $S(m)|_X$ ($m=2..9$) and $R|_{Z\cap X}$ are principal submatrices of $S(m)$ and $R$. The path on all $b$ vertices is *not*: it misses the edge $v_{b-1}v_0$. By Cauchy interlacing:
  - $N_{>m}(G)\ge n_+(S(m)|_X)$ and $N_{\ge m}(G)\ge n_{\ge0}(S(m)|_X)$;
  - $N_{>1}(G)\ge\#q(X)+n_+(R|_{Z\cap X})$.
- **Negative side.** Path matrices are bipartite and $f_k$ is odd. Hence the negative-side counts on paths equal the positive ones, and the same numbers bound $N_{<-m}$ and $N_{\le-m}$.
- **Completion.** Take the unassigned vertices $j..b-2$ as bare. Their true diagonal entries are $\ge$ the bare entries (Weyl). A $P_2$ at such a vertex removes it from $Z$ but adds 1 to $\#q$, and removing a vertex lowers $n_+$ by at most 1. So the bounds stay valid.
- **Monotonicity.** Every bound is non-decreasing in each $p_k$ and $q_k$. So the search may stop increasing $p$ (or $q$) at the first infeasible value.
- **Pruning rule.** A node is pruned iff no admissible spectrum (Lemma 5) simultaneously dominates:
  - all count bounds;
  - $\sum_v d_v(d_v-1)\ge$ the partial lower bound;
  - $P+Q\le S_2-b+2$.

  These conditions are monotone, so the search may break out of the $p$ loop.
- **Separate window filter.** Some admissible target must lie in $[\mathrm{LB}_4,\mathrm{UB}_4]$. Here $\mathrm{UB}_4$ puts all remaining weight on one vertex, which is optimal because $g(w)=(2+w)(1+w)$ satisfies $g(a)+g(b)\le g(a+b)+g(0)$. This filter is **not** monotone in $p$: $\mathrm{UB}_4$ can grow with $p$. It therefore only skips the child and never breaks the loop.
- **Last vertex.** Its $(p,q)$ is solved from the exact 4th-moment identity.

**Lemma 8 (exact inertia with zero pivots).** For a symmetric tridiagonal matrix with nonzero off-diagonal entries:
- $n_+$ equals the number of positive LDLᵀ pivots when an exact zero pivot is read as $-0$ and the next pivot as $+\infty$ (perturbation $T-\varepsilon I$).
- $n_-$ is the same with $+0$ and then $-\infty$.
- Pivots are exact rationals in `__int128` with overflow detection. On overflow the vertex is dropped, which still gives a principal submatrix. No overflow occurred in any final run.

## Computation (exact)

**Implementation A** (`code/sunsearch.c`, SHA-256 in `logs/code_hashes.txt`).
- Depth-first search over $(p_k,q_k)$ with the pruning of Lemmas 5–7.
- Rotation filter: $v_0$ carries a lexicographically maximal $(p,q)$.
- Exact leaf test: $G$ is integral iff $\sum_{m=-9}^{9}\mathrm{mult}(m)=n$, with:
  - $\mathrm{mult}(0)$ and $\mathrm{mult}(\pm1)$ from Lemma 3, in exact integers;
  - $\mathrm{mult}(m)$ for $|m|\ge2$ from Lemma 2, via the integer matrix $\prod\begin{psmallmatrix}s_k&-D\\D&0\end{psmallmatrix}$ with $D=m(m^2-1)$ and $s_k=m^2(m^2-1)-p_k(m^2-1)-q_km^2$, computed modulo four 62-bit primes. A log-magnitude bound below $2^{240}$ makes congruence equivalent to equality.

**Implementation B** (`code/sunB.c`, written separately).
- Different pruning: the moment identities only, with no inertia.
- Different canonical form: full dihedral canonical check at the leaves.
- Different leaf test: $F(x)=\det\big(x(x^2-1)(xI-A(C_b))-\mathrm{diag}(p_k(x^2-1)+q_kx^2)\big)$, which is monic of degree $4b$. It is interpolated mod 3 primes, and the root multiplicities of $-9..9$ mod $p$ are upper bounds. A sum below $4b$ certifies non-integrality.
- Survivors are confirmed with sympy (`code/confirm_exact.py`).

**B2** (`code/sunB2.c`). B plus a floating-point interlacing prune (LAPACK `dsyev` on the partial caterpillar, margin $10^{-6}$). It is used only for $b=10$, as a cross-check.

**Positive controls.**
- $b=4$, $n\le26$: A, B and B2 each find exactly $C_{4,1}(6,0,3,0)$ (13 vertices), $C_4(5P_2,P_1,2P_2,P_1)$ (20) and $C_{4,2}(4,4,0,0)$ (20). The first two are the known examples.
- A finds $C_{6,1}(0,6,6,12,6,6)$ at $N=42$, with spectrum $\{0^{32},\pm2^{2},\pm3^2,\pm4\}$.
- B finds it independently.
- sympy factors all three exactly (`confirm_exact.py`).
- **A against B on $b=4$, $n\le36$** (`logs/A_b4_N36.out`, `logs/B_b4_N36.out`): both give exactly the same 3 graphs, in 5 A-entries up to symmetry. This cross-checks A's pruning on a case where integral graphs exist.
- **Trace identities** $\operatorname{tr}A^2$, $\operatorname{tr}A^4$ and $\operatorname{tr}A^{L}$ ($L$ odd, $\le b$): checked on 352 random graphs with 0 failures (`code/check_moments.py`).
- **Second bug, found by self-review at 19:48 UTC.** Version v3 (`code/sunsearch_v3_ub4break.c`) broke the $p$ loop on the non-monotone window filter. The target set has gaps, so a window $[\mathrm{LB}_4,\mathrm{UB}_4]$ lying in a gap at $p$ could reach a target at $p+1$ when $d_k-1>$ the remaining weight. This could skip branches: at $b=3$, $N=49$ the v3 run visited 15,651 nodes against 15,678 after the fix. All A runs were redone with the fixed `sunsearch.c`, SHA-256 `f5a38c28…`; the old logs are in `logs/superseded_v3_ub4break/`. B and B2 never had this filter.
- **Bug caught by the control:** a first version used the full path $0..b-1$, which is not a principal submatrix, and so missed the 42-vertex graph. It was fixed before the final runs; the invalid logs are in `logs/invalid_v1/`.

**Results.** Logs are in `logs/`.

| b | N | A (exact) | B / B2 |
|---|---|---|---|
| 3 | 41, 42, 49 | 0 integral (5,033 / 5,334 / 15,678 nodes) | B: 0 candidates (N=41, 42) |
| 5, 7, 9 | 41, 42 | no admissible spectrum, so none (Theorem 2) | B: no admissible spectrum |
| 11, 13, 15 | 41, 42 | excluded by Lemma 6 | B: no admissible spectrum |
| 6 | 42 | exactly 1: (12,6,6,0,6,6) = $C_{6,1}(0,6,6,12,6,6)$, n=42; 35.4M nodes | B: exactly 1 candidate, the same graph, confirmed by sympy |
| 10 | 41 | **0 integral** in the fixed run (2 parts, 50.7M nodes, 52,652 exact leaf tests) | B2: **0 candidates**, all 4 parts. 52,652 configurations pass the moment filter; 14,662 canonical ones are tested exactly (mod-p char. poly.) |
| 10, 14 | 42 | stopped at the first time box; **completed in the follow-up**, see the end | – |
| 4 (control, $4\mid b$) | 36, 41 | exactly 3 graphs, same list at N=36 and N=41 (398k nodes): $C_{4,1}(6,0,3,0)$ (n=13), $C_4(5P_2,P_1,2P_2,P_1)$ (n=20), $C_{4,2}(4,4,0,0)$ (n=20) | B, N=36 and N=41: the same 3 |
| 12 ($4\mid b$) | 41 | 0 integral (5.86M nodes) | – |
| 8 ($4\mid b$) | 41 | **0 integral** (70.5M nodes, 576,976 exact leaf tests) | – |

The 3 graphs with $b=4$ agree with the literature count. The paper's introduction reports that the Braga–Rodrigues–Trevisan search found "only three integral unicyclic graphs on at most $21$ vertices besides the three cycles"; our three have 13, 20 and 20 vertices.

**Corollary (girth evidence; A only for $b=8,12$).** Every integral generalized sun graph with $n\le41$ that is not a cycle has $b=4$, and it is one of the three graphs above. The reasons:
- even $b\ge14$ is excluded by Lemma 6, since $N_{>1}(C_b)\ge5>|B^+|$;
- odd $b\ne3$ is excluded by Theorem 2 and Lemma 6;
- $b=3,6,8,10,12$ are covered by the search, all with 0 integral graphs for $n\le41$.

## What is new, and what is known

- **New (as far as G1 shows):**
  - The answer to Q-min: 42 is minimal, even in the strong reading with mixed P1/P2.
  - Uniqueness at order 42 for $b\le9$ and $b=6$.
  - Theorem 2's congruence restriction on odd girth.
- **Known or used:**
  - Theorem 2.1 and Lemma 3.1 of the paper;
  - Cauchy interlacing, Haynsworth inertia, Sylvester's law, Fermat's little theorem, trace or walk identities.
- **Unchecked:** whether Theorem 2 is already known for integral graphs in general. It is a short Fermat argument, so G2 must search for "integral graph" + "odd girth" / "closed walks" + "Fermat".
- **Q-girth is still open:**
  - We do not know whether $b$ must be even. Odd $b$ is now restricted to 3 or $b\ge15$ with $K_b\mid2b$.
  - We do not know whether $b\in\{4,6\}$.

## Final run status (filled in at the end)

The final runs of A all use `sunsearch.c` with SHA-256 f5a38c28cf3958862a5a30ebfeb4d166d23225e5801412a722697cb25421eb67, compiled at 19:48:59 UTC.

**Final results.** Every final A run uses the fixed code.

| b | N | A (fixed code) | B / B2 |
|---|---|---|---|
| 3 | 41 / 42 / 49 | 0 / 0 / 0 integral | B: 0 / 0 (N=41 / 42) |
| 5, 7, 9 | 41 / 42 | no admissible spectrum | B: the same; B also finds none for b = 11, 13, 15 |
| 6 | 42 | 1 integral: $C_{6,1}(0,6,6,12,6,6)$, n=42 | B: 1 candidate, the same graph |
| 10 | 41 | 0 integral | B2: 0 candidates |
| 4 | 41 | 3 integral (13, 20, 20 vertices) | B: the same 3 |
| 8, 12 | 41 | 0 integral | – |

**Cross-check on b = 10, n ≤ 41.** A tested 30,343 + 22,309 = **52,652** leaves exactly. B2 found 19,901 + 13,804 + 10,442 + 8,505 = **52,652** leaves passing the same moment filter. Both use the same rotation filter and the same moment filter. Equal counts are what one expects if neither pruning removes a moment-feasible configuration; the sets themselves were not compared.

**Not done within the time box.**
- Uniqueness at n = 42 for b = 10 and b = 14. The runs were stopped at the time box. **Resolved in the follow-up section below**, where b = 18 is also added.
- An independent B check for b = 8 and b = 12.
- Lean.
- G2: a deep novelty check of Theorem 2, which may be a known "integral graphs and odd girth" fact.

## Follow-up: uniqueness at 42 vertices (20:00–21:30 UTC, second time box)

**Claim U.** $C_{6,1}(0,6,6,12,6,6)$ is the only counterexample to Conjecture 2 with at most 42 vertices, up to isomorphism. The status of each case is in the table below.

A generalized sun graph has a unique cycle, and its attachments are determined vertex by vertex. So isomorphism classes of these graphs are exactly the dihedral classes of the sequences $((p_k,q_k))_k$.

**Coverage needed.** From Lemma 6, as corrected above:
- b = 3;
- b ∈ {6, 10, 14, 18};
- odd b ≥ 5 is excluded by Theorem 2 and the support bound.

**New lemmas used (all proved, independent of the search).**
- **(L6′) Cycle filter.** $C_b$ is an induced subgraph of $G$. So $|B^+| = N_{>1}(G)\ge N_{>1}(C_b)$, and for odd $b$ also $|B^-|\ge N_{<-1}(C_b)$ (Cauchy interlacing). Admissible spectra violating this are dropped.
  - A applies it with exact integer tests on $j$.
  - B and B2 apply it with their own code.
  - For $b\in\{14,18\}$ and $N=42$, only $B^+=\{4,3,3,2,2\}$ survives. This forces $n=42$, $\mathrm{mult}(1)=0$ and $\sum_v d_v(d_v-1)=408$.
- **(B2 completion) Induced subgraph used by B2.** Let $H$ consist of the cycle vertices $0..b-2$ (a path) plus the attachments of the already assigned vertices $0..k-1$. Then $H$ is an induced subgraph of every completion $G$, so $N_{>m}(G)\ge N_{>m}(H)$.
  - The count is computed with LAPACK `dsyev`.
  - An eigenvalue is counted only if it exceeds $m+10^{-6}$. The standard backward-error bound for `dsyev` at these sizes is about $10^{-11}$.
- **(B window) 4th-moment reachability, used by B.**
  - For one vertex of weight $w=p+2q$, the contribution $(2+p+q)(1+p+q)+2q$ is at most $g(w)=(2+w)(1+w)$.
  - $g$ is convex with $g(a)+g(b)\le g(a+b)+g(0)$.
  - So the final $\sum_v d_v(d_v-1)$ lies in $[M+2r,\ M+g(w')+2(r-1)]$, where $r$ vertices and weight $w'$ remain.
  - If no admissible target lies in this window, the child is skipped. It is skipped, not broken out of, because the window is not monotone in $p$.

- **(Lemma N) Count identities, bipartite case.** Let $G$ be integral with $b$ even, and put $S_2=\sum_{B^+}\lambda^2$ and $s=|B^+|$.
  - The spectrum is symmetric, so $n=\mathrm{mult}(0)+2\,\mathrm{mult}(1)+2s$.
  - The 2nd moment gives $2S_2+2\,\mathrm{mult}(1)=2n$.
  - Hence $\mathrm{mult}(1)=\mathrm{mult}(-1)=n-S_2$ and $\mathrm{mult}(0)=2S_2-n-2s$.
  - By Lemma 3, $\mathrm{mult}(0)\le\max(P,2)$ and $\mathrm{mult}(\pm1)\le\max(Q,2)$. ∎
  - **Corollary (hand proof, no computer): $b\in\{14,18\}$ is impossible for $n\le42$.**
    - L6′ forces $B^+=\{4,3,3,2,2\}$, so $S_2=42$ and $s=5$.
    - Then $n\ge S_2$ gives $n=42$. So $\mathrm{mult}(1)=0$ and $\mathrm{mult}(0)=84-42-10=32$.
    - Hence $P\ge32$, so $b\le n-P\le10$. Contradiction.
  - B v3 uses Lemma N as a pruning rule. At a partial node:
    - $n\in[\max(b+W,S_2),\ \min(N,\,2S_2-2s)]$;
    - if $P\ge2$ then $2Q\le 2n_{\max}-b-2S_2+2s$, which follows from $\mathrm{mult}(0)\le P=n-b-2Q$.
  - B v3 also uses it as an exact leaf filter: $0\le 2S_2-n-2s\le\max(P,2)$.
  - A v5 does **not** use Lemma N. A v6 uses it only when switched on by its 5th argument. So A v5 against B v3 is a methodologically distinct pair.

**Code versions (SHA-256 in `logs/n42/code_hashes_n42.txt`).**

| Code | Version | What changed |
|---|---|---|
| A = `sunsearch.c` | v5 `bfcca593…`, then v6 `39a87195…` | v5: v4 plus L6′. v6: v5 plus optional Lemma N (argument 5 = 1), with the Pareto reduction switched off when Lemma N is on, because a larger $\lvert B^+\rvert$ can then make a spectrum less feasible. v6 with argument 5 = 0 behaves as v5 |
| B = `sunB.c` | v2 `8311d32e…`, then v3 `f0eb3d9c…` | v2: v1 plus L6′ plus the window. v3: v2 plus Lemma N, the max-key rotation filter and a "greatest image" canonical form |
| B2 = `sunB2.c` | `c80538f9…` | v1 plus L6′ plus the completion |

Old versions are kept as `code/*_v*.c`.

**Positive controls for the new versions.**
- A, b = 4, N = 41: the same 3 graphs as before, and the same node count (398,136).
- B, b = 4, N = 36: the same 3 graphs.
- B2, b = 4, N = 26: the same 3 graphs.
- B2, b = 6, N = 42: finds $C_{6,1}(0,6,6,12,6,6)$ and nothing else, run to completion (1,128,560 moment-feasible, 449,500 canonical tested exactly). *Correction at 23:05 UTC, review of paper 7, N9:* this line said "The run was stopped after the hit to free a core". The log `logs/n42/B2ctrl_b6_N42.out` has the final `B2-DONE` line, which B2 prints only after the search has finished; the "STOPPED" note was appended after that. A rerun of the same source reproduced both lines (`checks-addition/B2v2_b6_N42_rerun.log`, next to the paper).
- A, b = 3, N = 42: the same node count as v4 (5,334).
- A v6 with Lemma N:
  - b = 4, N = 41: the same 3 graphs, with 326,098 nodes against 398,136 without Lemma N.
  - b = 6, N = 42: exactly 1 integral graph, $C_{6,1}(0,6,6,12,6,6)$, with 11.6M nodes against 35.4M.
  - b = 4, N = 49: **identical lists with and without Lemma N**, 7 entries (972,890 against 1,218,694 nodes). The entries are $C_{4,1}(6,0,3,0)$ (13 vertices), the two 20-vertex graphs, and $C_{4,2}(10,10,0,0)$ (44 vertices, spectrum $\{\pm4,\pm3,\pm1^{19},0^2\}$), a member of the $C_{4,2}(p,q,0,0)$ families of Braga–Del-Vecchio–Rodrigues. This graph has $Q=20$ and $\mathrm{mult}(1)=19$, so it exercises the $Q$-side of Lemma N (`logs/n42/A6ctrl_b4_N49_lemN{0,1}.*`).
- B v3:
  - b = 4, N = 36: the same 3 graphs.
  - b = 6, N = 42: exactly 1 candidate, the known graph, run to completion.

**Results at N = 42.** Logs are in `logs/n42/`.

| b | A (exact) | Second confirmation |
|---|---|---|
| 3 | 0 integral (v4, 5,334 nodes) | B v1 and B v3: 0 candidates (exact). Both test the same 2,030 canonical classes, a consistency check of B v3's rotation filter |
| 5–13 odd, 15 | no admissible spectrum (Theorem 2, support bound) | B v1 and B v3: no admissible spectrum; hand proof |
| 22, 26 (even, ≥ 22) | A v6: no admissible spectrum. Lemma 6: $N_{>1}(C_b)\ge7>5$ | hand proof (Lemma 6) |
| 6 | exactly 1 (v4, 35.4M nodes): $C_{6,1}(0,6,6,12,6,6)$ | B v1: exactly 1 candidate (1,187,991 canonical tested); B v3: exactly 1 (520,217 canonical tested); both exact; sympy factorisation |
| 14 | 0 integral (v5, 904,115 nodes, 850 exact leaf tests) | hand proof (Lemma N corollary); B v3: pruned at the root (0) |
| 18 | 0 integral (v5, 18 nodes) | hand proof (Lemma N corollary); B v2: 0 candidates (2,048,976 moment-feasible, 56,952 canonical tested exactly); B v3: pruned at the root; B2 v2: 0 |
| 10 | **A v6 (with Lemma N): 0 integral** (19.7M nodes, 71,680 exact leaf tests, about 3 min). **A v5 (without Lemma N): 0 integral** (2 parts, 465.0M nodes, 461,049 exact leaf tests, 34 and 53 min). | B v3: **0 candidates** (401,175 moment- and Lemma-N-feasible configurations; 200,579 canonical ones tested exactly; 5.0 min). B2 v2, the LAPACK-pruned variant: stopped unfinished at 21:19 after about 48 CPU-min per part. It was an optional third check. |

**Conclusion of the follow-up (20:55 UTC).** Theorem 1′ holds: $C_{6,1}(0,6,6,12,6,6)$ is the only counterexample to Conjecture 2 with at most 42 vertices. Each case has at least two independent confirmations.

| Case | Confirmations |
|---|---|
| b = 3 | A, B v1, B v3 |
| b = 6 | A v4, A v6, B v1, B v3: each finds exactly this graph; sympy confirms its spectrum |
| b = 10 | A v5, which does not use Lemma N, so the pruning is methodologically distinct from B v3; A v6; B v3 |
| b = 14, 18 | a hand proof (Lemma N corollary) plus A v5 and B |
| odd b ≥ 5, even b ≥ 22 | hand proofs (Theorem 2, the support bound, Lemma 6), plus A and B, which find no admissible spectrum |

**Correction recorded above.** The first-session Lemma 6 listed $b\in\{6,10,14\}$ for $N=42$ and omitted $b=18$. The case $b=18$ is now covered.

**CPU used in the follow-up.** About 4 CPU-hours on at most 4 concurrent processes; B2 at b = 10 was stopped unfinished at the time box. No Lean locks were taken. The `review/` folder was not touched.
