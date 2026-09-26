# Referee report: Problem 15.11 of arXiv:2608.25092 (complete mappings of $\mathcal B_n$ and $\mathcal{PB}_n$)

- **Referee.** Independent referee; I did not produce this work. This is a fresh second attempt. The files of the interrupted first attempt (`review/code/`, `review/logs/`) were neither read nor used. All my code and logs are in `review/r2/`.
- **Date.** 2026-09-26, 13:37–14:13 UTC (`date -u`).
- **Material.**
  - `CONTRACT.md`, `PROOF.md`, `code/`, `certificates/`, `logs/`, `lean/`. All 38 hashes in `logs/hashes.txt` match the current files (`shasum -c`).
  - `work/research-lean/Research/BrauerCMCore.lean`, SHA-256 `a8622961…5f3c`. It is identical to `lean/BrauerCMCore.lean`.
  - `outputs/Brauer-complete-mappings/note.tex`, 914 lines.
  - Source arXiv:2608.25092v1. I downloaded the e-print again and it is byte-identical to `src/eprint.bin` (SHA-256 `0109b11b…7941`). On the abs page at 14:05 UTC, v1 is still the only version.
  - For the $\mathcal J$-class citation I also read EMRT (arXiv:1709.00142, source).

## Verdict: **MINOR REVISION** (accept after minor fixes)

The three claims are correct under the main reading:
1. $\mathcal B_n$ and $\mathcal{PB}_n$ have a CM iff $n\notin\{2,3\}$.
2. Every proper principal factor of $\mathcal B_n$ has a CM.
3. Every proper principal factor of $\mathcal{PB}_n$ has a CM except the rank-2 factor of $\mathcal{PB}_3$, which is $B(S_2,3)$ and has none.

Further:
- The proofs are complete for all $n$, not only for the computed cases.
- Every cited result of 2608.25092 exists under the stated number and has the stated hypotheses.
- Every certificate passes my own checker, which uses my own diagram product with closed loops discarded, as in EMRT §2.1.
- The non-existence claim is confirmed by my own exhaustive search.
- The Lean file states what is claimed.

**There are no BLOCKER and no MAJOR findings.**

## Findings

| # | Grade | Location | Finding | Fix |
|---|---|---|---|---|
| — | BLOCKER | — | none | — |
| — | MAJOR | — | none | — |
| m1 | MINOR | `note.tex` l.877 | The disclosure contains the placeholder `%% AUTHOR-ROLE-SENTENCE: to be completed after the author has read the paper`. | The user must write this sentence before release. |
| m2 | MINOR | `note.tex` l.582–585 | "In the notation of Section~\ref{sec:comp}" points to §8 (Computations), but §8 never defines $e_I$. It only uses $e_{I_0}$ (l.779). The definition $e_{I_0}=(I_0,1,I_0)$ is given inline here. | Define $e_\lambda=(\lambda,1,\lambda)$ once after Prop. 3.1 and drop the cross-reference. |
| m3 | MINOR | `note.tex` | Test-compiled on a scratch copy (pdflatex, 2 passes): no errors, no undefined references. There are three overfull boxes: 78 pt in the §8 bullet "The odd case" (l.773–781, the long set $\{(6,2),\dots\}$), 16 pt at l.424–426 (lifting lemma) and 9 pt in the triangle display (l.558–562). | Cosmetic line breaks. |
| m4 | MINOR | `PROOF.md` l.215 | The abbreviated hash of `cm_B7_rank3.txt` is typed `203422dd…7cfbec6`; the correct tail is `…7cbfec6`. The full hash in `logs/hashes.txt` is correct, and the file verifies. | Fix the typo. |
| m5 | MINOR | `CONTRACT.md` l.40–41 | Two paraphrases are imprecise. (i) Thm 5.2 is stated only for Rees matrix semigroups *without* zero; the $\mathcal M^0$ version is Lemma 6.3. (ii) For a *given* $G$, the "only if" of the Hall condition is Lemma 7.3, not Thm 6.2, whose item (a) quantifies over all $G$ and $P$. Neither affects the proofs: `PROOF.md` and `note.tex` (R5), (R6) cite the correct lemma and direction. | Reword the table. |
| m6 | MINOR | `note.tex` l.707, 797, 894–896 | The repository paths (`certificates/brauer-complete`, `lean/Research/BrauerCMCore.lean`), "version 1.3.0" and the Zenodo concept DOI describe a future release. | Check them when the release is made; the release is done by the user. |
| m7 | MINOR | `note.tex` l.814 | The `variable` line of the Lean listing merges the variables of the file's two sections and omits `P`. The theorem statements themselves match the `#check` output in `logs/lean_build.log` exactly. | Call the listing a summary. |
| m8 | MINOR (process) | `PROOF.md` §8–9; `note.tex` "Prior work" | The citing-works searches in OpenAlex and Semantic Scholar failed (HTTP 429), so priority is not fully checked. `note.tex` says so honestly. | Do the G2 re-check listed in PROOF.md §9 before any public claim. arXiv shows v1 only as of 14:05 UTC today. |
| m9 | MINOR (optional) | `note.tex` Prop. 3.1, last paragraph | The fact that $J_r$ is a $\mathcal J$-class is taken from EMRT. I checked it: EMRT Prop. 2.1(iii) and Rem. 2.2(v)–(vii) say this. It also follows in two lines from Prop. 3.1(a)–(c): $x=(i,gh^{-1},j)\cdot y\cdot(\mu,1,\lambda)$ for $x=(i,g,\lambda)$, $y=(j,h,\mu)$, and $\operatorname{rk}(xy)\le\min$ separates the ranks. | Optionally add the two lines, which removes the external dependency. |

## 1. Contract (task 1)

**Text.** `CONTRACT.md` §1.1 quotes the lead-in paragraph and Problem 15.11 from source lines 4649–4663 (label `p:diagram-monoids`). §1.2 quotes the definition from the abstract. I compared both by script:
- the Problem text and the definition are **character-identical** to the source after whitespace normalisation;
- the lead-in differs only by a line break inside `\cite[...]\n{EastMitchellRuskucTorpey}`, which is immaterial.

The numbering 15.11 is confirmed in two ways: by counting the `problem` environments in §15 (the counter is per section, and the Definition in §15 uses the theorem counter), and in the PDF text (`src/paper.txt`, PDF page 61). The problem opens with "Classify complete mappings for $\mathcal B_n$ and $\mathcal{PB}_n$." (arXiv:2608.25092, Problem 15.11).

The paper's definition, paraphrased: a CM of a magma $S$ is a bijection $\alpha$ such that $x\mapsto x\cdot x\alpha$ is also a bijection. Maps act on the right. This is the notion used in `PROOF.md`, in `note.tex` and in Lean (`IsCompleteMapping`).

The principal-factor convention of §4 (Thm 4.4) is $J^0=J\cup\{0\}$, with products that leave $J$ set to 0. For the minimal ideal a new zero is adjoined. `PROOF.md` and `note.tex` use the same convention.

**Does (M) answer the question?** Yes.
- The paper uses "classify" throughout in the existence sense. For example, the opening sentences of §8.1 (full linear monoids), §8.2 (partition monoid), §9 ($T_n$) and §10 (inverse semigroups) all announce a classification of *which* monoids have a CM.
- The second sentence of the problem locates the open part in the rank-2 and rank-3 proper factors.
- The third sentence adds the whole monoid.

Reading (M) decides every principal factor for every $n$, together with the whole monoid, so it answers all three sentences. (W) is contained in (M).

**Is a stronger reading intended?** A literal reading (S), "describe all CMs" as in Prop. 6.5 for Brandt semigroups, is grammatically possible but not plausible as intended: it is out of reach even for $S_r$. The paper's other diagram-monoid results (Thms 8.2, 8.5, 9.16) are existence results.

A second stronger variant is plausible. Problem 15.1 asks for *explicit* CMs of the linear monoid without the general existence theorems, and a similar request could be meant here. The work partly meets it:
- Lemmas B and C and the lift are explicit formulas.
- Lemma A still needs *some* CM of $S_r$ for $r\ge4$, supplied by Hall–Paige.

`note.tex` already restricts itself to the existence question ("Scope" paragraph; abstract: "We settle the existence question in all cases"). That wording is correct and should be kept.

## 2. Cited results (task 2)

Numbers were computed from the LaTeX counters (`theorem` counter per section, shared by prop, lemma, cor, example and definition) and cross-checked against the PDF text.

| Cited as | Source label, line | What the source says (checked) | Used for | OK? |
|---|---|---|---|---|
| Thm 1.1 | `Thm:HP`, l.210 | CM iff the Sylow 2-subgroups are trivial or non-cyclic | $S_r$: CM iff $r\notin\{2,3\}$ | ✓ |
| Prop 1.4 | `Prp:zero`, l.369 | magma with zero: $0\alpha=0\theta=0$ | CM of $J^0$ fixes 0 | ✓ |
| Cor 3.4 | `Cor:units`, l.681 | a finite monoid with a CM ⇒ its group of units has one | $n=2,3$ negative | ✓ |
| Thm 4.1 | `t:principal-factor-Rees`, l.766 | each principal factor is null or a Rees 0-matrix semigroup | context | ✓ |
| Thm 4.4 | `t:J-reduct`, l.798 | $S$ has a CM iff every $J_a^0$ has one (finite $S$) | whole monoid | ✓ |
| Thm 5.2 | `t:goingup`, l.854 | going up, for $\mathcal M$ **without** zero; explicit formula $(i,g_uh,\lambda)\mapsto(i',(h\alpha)^{p_{\lambda i'}}g_v,\lambda')$ | the formula of the Lift | ✓ (m5) |
| Lemma 6.3 | `l:factorL`, l.1304 | same for $\mathcal M^0$, with $N\trianglelefteq G$ having a CM | Lift through $A_r$ | ✓ |
| Thm 6.2 | `c:Rees0`, l.1286 | (a)–(e) equivalent; (c)⇒(a) is the Hall condition ⇒ CM for every $G$ with a CM | Lemma A existence, (R6) | ✓ (m5) |
| Prop 6.5 | `prop:brandt-latin`, l.1566 | CMs of the Brandt $B_n$ ↔ Latin squares | analogy for Lemma A | ✓ |
| Thm 7.5 / Cor 7.6 | l.1866 / l.1983 | $G$ without a CM, $\lvert I\rvert=\lvert\Lambda\rvert$ even, pattern has a one-transversal ⇒ CM | even $N$ (R7) | ✓ |
| Thm 7.7 | `t:incidence-criterion`, l.2105 | $\partial z=d$ solvable iff the product of $d$ over every component is 1 | context | ✓ |
| Def 7.13 / Thm 7.14 | l.2428 / l.2459 | residual routing, cycle-compatible mod $N$ ⇒ CM | Lemma C is a special case (checked, §3(b)) | ✓ |
| Thm 7.17 / Cor 7.18 | l.2607 / l.2722 | positive balanced weighting + anchored pair ⇒ CM; $S_3$ sign form | cited as the template | ✓ |
| Thm 7.19 | `t:converse0`, l.2762 | (a) non-trivial cyclic Sylow 2; (b) $\lvert I\rvert,\lvert\Lambda\rvert$ odd; (c) $P$ is a normalised matrix with all entries of odd order, with some entries zeroed ⇒ no CM | $B(S_2,3)$: the all-1 $3\times3$ matrix is normalised with entries of order 1; zeroing the off-diagonal gives $\Delta_3$ | ✓ |
| Thm 8.2 | `t:linear-monoid`, l.2833 | $\operatorname{End}(\mathbb F_q^d)$: CM unless $d=1$ with $q$ odd, or $(2,2)$ | background | ✓ |
| Prop 8.3, Lemma 8.4, Thm 8.5 | l.3097, 3123, 3149 | $\mathcal P_n$: CM iff $n=1$ or $n\ge4$; odd case via the triangle $I_0,I_1,I_2$ (sandwich $1,1,(12)$) and Thm 7.17 | template; the same triangle | ✓ |
| Prop 8.7 / Cor 8.8 | l.3335 / l.3354 | aperiodic regular $*$-semigroups; planar partition, Motzkin and Jones monoids | background | ✓ |
| Thm 9.16 | l.3911 | $T_n$: CM iff $n=1$ or $n\ge4$ (rank 3 via Thm 7.17) | background | ✓ |
| Thm 10.1 / Cor 10.2 | l.3939 / l.3974 | inverse semigroups: subgroup has a CM or #$\mathcal L$ even; $I_n$: iff $n\equiv0,1\pmod 4$ | second proof for $B(S_2,3)$ | ✓ |
| EMRT Prop 2.1 / Rem 2.2(v)–(vii) | arXiv:1709.00142, source l.875, 889 | $\mathcal J=\mathcal D$ = rank classes in $\mathcal{PB}_n$ and $\mathcal B_n$ (ranks $\equiv n \pmod 2$); regular; maximal subgroup $S_r$; product via the product graph, with components not meeting the outer rows discarded | Lemma 2.1 / Prop 3.1 | ✓ |

## 3. General-$n$ arguments, rechecked by hand (task 3)

**(a) Parity.**
- $N_{\mathcal B}=\binom nr(n-r-1)!!$, and $(n-r-1)!!$ is odd.
- For $r=2$ ($n$ even), $\binom n2=\frac n2(n-1)$ is odd iff $n\equiv2\pmod 4$.
- For $r=3$ ($n$ odd), $v_2\binom n3=v_2(n-1)-1$, so $\binom n3$ is odd iff $n\equiv3\pmod 4$.
- Properness forces $n\ge6$ (resp. $n\ge7$), hence $n-r\ge4$ and fibre size $m\ge3$.
- $\mathcal{PB}_n$: $a(k)=a(k-1)+(k-1)a(k-2)$ with $a(2)=2$ and $a(3)=4$, so $a(k)$ is even for $k\ge2$. For $n\ge4$ we get $n-r\ge2$, except $(4,3)$ where $N=4$. For $n\le3$ the only proper factor of rank 2 or 3 is $(3,2)$, with $N=3$. Correct.

**(b) Lemma C.**
- Bijectivity: the two image sets $\{(\lambda,1+c(\lambda),\ast)\}$ and $\{(\kappa,c(\kappa),\ast)\}$ are complementary.
- The products are $(i,1,L(i,\lambda))$ and $(i,0,L(i,\lambda\rho))$, and $c$ exists iff $(\ast)$ holds.
- It is exactly the paper's Thm 7.14 with $N=A_r$, $\Theta(i,\lambda)=(\lambda,L(i,\lambda))$ and $R(i,\lambda)=(i,\lambda\rho)$:
  - $Q_{\lambda\lambda}=1$, and $\Pi_\Theta$ is bijective by the rows of $L$;
  - $R$ is residual iff $\lambda\sim\lambda\rho$;
  - $\mu_R(i,\lambda)=(i,L(i,\lambda\rho))$ is bijective;
  - $u_a=\bar p_{\lambda\lambda}=1$ and $w_a=\bar p_{\lambda,\lambda\rho}$;
  - the cycles of $R$ are $\{i\}\times C$, and the cycle condition (eq. `general-residual-cycle-condition`) is $(\ast)$.

  The claim of `PROOF.md` §3 and `note.tex` Rem. 4.5(4) is therefore correct.

**(c) Triangle (Lemma D).** I redid the three path computations by hand:
- $\Gamma(I_0,I_1)$: $3\to1\to2$, and 4 is trivial. Identity.
- $\Gamma(I_1,I_2)$: $4\to1\to3$, and 2 is trivial. Identity.
- $\Gamma(I_2,I_0)$: $2\to1\to4$, and 3 is trivial. This gives $(1\,2)$.
- $R_0$ gives double edges. For $r=3$ the point 5 is the largest free point of all three half-diagrams, so it does not change the order.
- This is independent of $n$, and $3+1\equiv0$.
- The parity is intrinsic: $e_{I_0}e_{I_1}e_{I_2}e_{I_0}=(I_0,p_{01}p_{12}p_{20},I_0)$, and reversing the cycle does not change it because $s(p_{ab})=s(p_{ba})$.

**(d) Lemma E.** One can choose the $z$'s iff $n-r-k\ge k$. The leftover $n-r-2k$ points are even in number since $n\equiv r\pmod 2$. The paths are $x_t,z_t,y_t$. Correct.

**(e) Lemma F.**
- $\binom nr-3$ is even.
- The pairing condition $r+2k\le n$ holds for any pairing when $r=2$ ($k\le2$, $n\ge6$) or when $r=3$ and $n\ge9$ ($k\le3$).
- For $(7,3)$ it means the two sets intersect:
  - Dirac's theorem applies: 32 vertices with minimum degree $\ge 30-3=27\ge16$.
  - `note.tex` also gives an explicit list, which I verified: it covers exactly the 32 other 3-sets, and every pair intersects.
- Each fibre loses exactly one element, either to the triangle or to a cross edge. The $m-1$ remaining elements are an even number and form a clique (Lemma 2.1(d)).
- So $G-X$ has a perfect matching. $\rho$ has no fixed points, $\lambda\sim\lambda\rho$ for all $\lambda$, and the transpositions satisfy $(\ast)$. Correct.

**(f) Lift through $A_r$.**
- $A_2=1$ and $A_3\cong C_3$; in both, $h\mapsto h^2$ is bijective.
- With $p=P_{\lambda j}\ne0$ (guaranteed because $\bar f$ has non-zero products), $x\cdot xf=(i,g_uh^2pg_v,\mu)$. For fixed $(i,u,\lambda)$ this runs over the $A_r$-coset of sign $u+s(p)+v$.
- This is the paper's formula with $\alpha=\mathrm{id}$ and $x^g=g^{-1}xg$. Correct for $S_2$ and $S_3$.

**(g) Whole monoids, and $B(S_2,3)$.**
- Units $=J_n\cong S_n$. Cor 3.4, Hall–Paige and Thm 4.4 then give (c).
- The hypotheses of Thm 7.19 hold for $B(S_2,3)$; see §2.
- The Rees data of $\mathcal{PB}_3$ at rank 2 are the identity pattern. A free point of $\lambda$ that is not free in $i$ is a singleton of $i$, hence an isolated vertex.

## 4. Independent computations (task 4)

My own code shares nothing with `code/` or `review/code/`. `rd2.py` has:
- its own parser;
- its own product: a component search on $3n$ vertices, keeping only components that meet the outer rows, so closed loops and middle paths are discarded;
- its own enumeration of $\mathcal B_n$ and $\mathcal{PB}_n$;
- its own Rees coordinates and a path-walk for $p_{\lambda i}$.

It is single-threaded. Results:

1. **`struct2.py`: product sanity, Green's classes and Lemma 2.1.**
   - Hand-computed products pass, including loop discarding and a dead end at a singleton.
   - $|\mathcal B_n|=(2n-1)!!$ for $n\le6$ and $|\mathcal{PB}_n|=a(2n)$ for $n\le5$. The identity is correct, and 3000 random triples per monoid are associative.
   - From full Cayley tables: $\mathcal D$-classes = rank classes for $\mathcal B_2$–$\mathcal B_5$ and $\mathcal{PB}_2$–$\mathcal{PB}_4$.
   - Lemma 2.1 (a)–(d) and the product rule hold on **all** pairs of every $J_r$ of $\mathcal B_3$–$\mathcal B_5$ and $\mathcal{PB}_2$–$\mathcal{PB}_4$, and of $J_0(\mathcal B_6)$.
   - On random pairs they hold for 300k pairs in $\mathcal B_6$ rank 2, 100k in $\mathcal B_6$ rank 4, 100k in $\mathcal B_7$ rank 3, and 150k in each of $\mathcal{PB}_5$ ranks 2 and 3.
   - Support degree: 35 for $\mathcal B_6$ rank 2 (matches PROOF.md) and 63 for $\mathcal B_7$ rank 3. **PASS.**
2. **`cert2.py`: checks at the level of the definition.**
   - For a factor, the key set equals the independently enumerated $J_r$, $\alpha$ is a permutation of it, and all $x\cdot x\alpha$ have rank $r$ and are distinct.
   - For a whole monoid, the keys are the monoid, and both $\alpha$ and $x\mapsto x\cdot x\alpha$ are permutations of it.
   - As a negative control, 20 out of 20 corrupted copies were rejected.
   - **All 12 certificates pass:** `cm_B6_rank2` (4050, `246e42f7…04d9d0`), `cm_B7_rank3` (66150, `203422dd…7cbfec6`), `alt/cm_B6_rank2`, `alt/cm_B7_rank3`, and the whole monoids `cm_B1`, `B4`, `B5`, **`B6`** (10395), `PB1`, **`PB4`** (764), `PB5` (9496) and `PB6` (140152).
3. **`nonex2.py` + `tcount.c`: exhaustive count of all transversals.**
   - The search runs over all bijections and does **not** assume $0\alpha=0$.
   - The counter is validated on known counts: $\mathbb Z_3$ 3, $\mathbb Z_4$ 0, $\mathbb Z_5$ 15, $\mathbb Z_7$ 133, $S_2$ 0, $S_3$ 0, and the Brandt semigroups $B_2$ 2, $B_3$ 12, $B_4$ 576 (= number of Latin squares, Prop 6.5). Brute force over all permutations agrees for $B_2$, $S_3$ and $\mathbb Z_5$.
   - Positive controls, each with a CM found: $S_4$, $B(S_2,2)$, $B(S_2,4)$, $J_1^0(\mathcal{PB}_2)$, $J_0^0(\mathcal{PB}_3)$, $J_1^0(\mathcal{PB}_3)$ and $J_0^0(\mathcal B_4)$.
   - **Target: $J_2^0(\mathcal{PB}_3)$, 19 elements built from my own product, has 0 CMs** (3,342,878 DFS nodes).
   - An explicit isomorphism with $B(S_2,3)$ was checked on all 361 products, and abstract $B(S_2,3)$ also has 0 CMs.
   - The units of $\mathcal B_2$, $\mathcal B_3$, $\mathcal{PB}_2$ and $\mathcal{PB}_3$ are exactly the rank-$n$ diagrams. **PASS.**
4. **`construct2.py`: CMs rebuilt from the written proof.**
   - I used my own random indexing of $H$ and a *different* Latin square, $L(i,\lambda)=\lambda-i$.
   - Lemma C with Lemmas D, E and F and the lift gives CMs of **$\mathcal B_6$ rank 2 and $\mathcal B_7$ rank 3 (the $S_3$ lift)**. Both were verified on diagrams.
   - Lemma B with the lift gives CMs of $\mathcal B_4$ r2, $\mathcal B_5$ r3 ($S_3$ lift), $\mathcal{PB}_4$ r2, $\mathcal{PB}_4$ r3 and $\mathcal{PB}_5$ r2. All were verified on diagrams.
   - The triangle sandwich values $1,1,(1\,2)$ hold for all $4\le n\le60$.
   - $e_{I_0}e_{I_1}e_{I_2}e_{I_0}$ is odd at the diagram level for $6\le n\le20$.
   - The Lemma E edges of the fibre pairing are compatible for $(n,r)=(10,2)$, $(11,3)$, $(14,2)$, $(15,3)$, $(18,2)$, $(19,3)$, $(22,2)$ and $(23,3)$.
   - The full $\rho$ satisfies the hypotheses of Lemma C at $N=4725$ and $N=17325$. **PASS.**
5. **`mutate2.py`: mutation tests.** A positive 3-cycle violates $(\ast)$. Flipping one value of $c$ makes the rebuilt map fail. **PASS.**
6. **`parity2.py`.** The parity table of `note.tex` Table 1 holds for all $n\le400$, and the $N$ formulas agree with enumeration for $n\le8$. **PASS.**

## 5. Lean, read only (task 5)

I did not run `lake`. Reading `BrauerCMCore.lean` (324 lines):

**Model.**
- `mul` is exactly the product of $\mathcal M^0(\mathbb Z_2,H,H,P)$. Row index $l$ is the $\mathcal L$-class, column $j$ is the $\mathcal R$-class, and `none` is 0. This matches the paper's $(A,a,\alpha)(B,b,\beta)=(A,ap_{\alpha B}b,\beta)$.
- `IsCompleteMapping` is the paper's definition for a magma.

**The two theorems.**
- `fC` is Lemma C's map: the `else` branch is the case $a=1+c(l)$. `fB` is Lemma B's map.
- The hypotheses of `lemmaC`:
  - `hdiag` is the identity diagonal;
  - `hρ` gives $\lambda\sim\lambda\rho$ together with its sign;
  - `hc` is the recursion for $c$;
  - `hrow` and `hcol` make $L$ a Latin square;
  - `[Finite H]`.
- `lemmaB` requires only $t(\delta\mu)=t(\mu)+1$. This is stronger than PROOF.md, which asks for an involution, and it forces $\lvert H\rvert$ even.
- No hypothesis is vacuous or too strong. The conclusions are exactly "CM of $\bar{\mathcal M}$".

**Hygiene.**
- 10 × `decide`, each on a closed $\mathbb Z_2$ statement with at most 3 variables.
- No `sorry`, `axiom`, `native_decide`, `unsafe` or `extern`.
- `#check` in `logs/lean_build.log` agrees with the source.

**Scope.** The Lean file certifies only the two $\mathbb Z_2$-level constructions. Not covered:
- the existence of $c$ from $(\ast)$;
- the lift;
- Lemma 2.1;
- Lemmas D–F;
- the paper's theorems.

`PROOF.md` §9 and `note.tex` §9 state this accurately. Toolchain: v4.33.1, Mathlib `0df444a3` (`lake-manifest.json`), as stated.

## 6. The paper draft `note.tex` (task 6)

**Statements.** The statements agree with `PROOF.md`. Thm 1.1(a)–(c) is PROOF Thms 1–3, and Prop. 3.1 is Lemma 2.1. Lemmas 4.1–4.4 are A, lift, B and C; Lemmas 5.1–5.4 are parity, D, E and F; Lemma 6.1 and Prop. 6.2 are §5.

**Differences from PROOF.md.** They are improvements:
- Lemma B is stated for any $\delta$, matching Lean.
- The triangle lemma assumes only $n-r\ge2$.
- An explicit $(7,3)$ pairing replaces Dirac's theorem.

**Faithfulness to the source.**
- (R1)–(R8) state the cited results with their hypotheses. (R5) correctly says that Lemma 6.3 extends Thm 5.2 to $\mathcal M^0$.
- The problem is paraphrased accurately.
- The $\mathcal P_n$ triangle is credited to Thm 8.5, and the novelty claim is modest and accurate ("direct extension of the methods").

**Numerical claims.** Every numerical claim in §8 matches the logs: sizes 4050 and 66150; $N$ values; 67,911,890 nodes; the $S_6$ exact-cover time of about 409 s ≈ 7 min; 400k samples; the run times 07:42–07:44.

**Remaining issues.** Only m1–m3, m6, m7 and m9 above.

## 7. Recomputation log

The logs are in `review/r2/logs/`, and `review/r2/code/run_r2.sh` reruns everything, single core, in about 1 min.

| Script | Result line | CPU (1 core) |
|---|---|---|
| `struct2.py` | `STRUCT2 PASSED` | 13.4 s |
| `cert2.py` | `CERT2 PASSED` (12/12) | 2.9 s |
| `nonex2.py` (+ `tcount.c`, `cc -O2`) | `NONEX2 PASSED`: target 0 CMs | 28.8 s |
| `construct2.py` | `CONSTRUCT2 PASSED` | 1.5 s |
| `mutate2.py` | `MUTATE2 PASSED` | 1.6 s |
| `parity2.py` | `PARITY2 PASSED` | <0.1 s |
| scratch `pdflatex` of `note.tex` (2 passes) | exit 0 | ≈2 s |
| **aborted run**: first version of `nonex2.py` (pure-Python exact cover, counting all CMs of $S_4$ etc.); stopped at the 600 s tool timeout, no result used | — | ≈600 s |
| **Total** | | **≈11 min on one core**, within the limit of 4 cores and 20 min |

**Hashes.** The SHA-256 of every referee script and log is in `review/r2/SHA256SUMS`. For example, `rd2.py` is `261c7981…920c` and `nonex2.py` is `e32006ee…7b41`.

**Nothing was published or pushed, and no project file was modified.** New files: `review/REVIEW.md` and `review/r2/`. `note.tex` was compiled only as a scratch copy outside the project.
