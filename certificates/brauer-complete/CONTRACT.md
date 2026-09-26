# CONTRACT: Problem 15.11 of Araújo–Bentz–Cameron–Hendrey–Kinyon (Brauer and partial Brauer monoids)

Written 2026-09-26 (UTC) by the round-6 research agent `brauer-complete`. Revised 2026-09-26 14:27 UTC after the referee report (`review/REVIEW.md`, item m5): the rows for Thm 5.2 / Lemma 6.3 and Thm 6.2 / Lemma 7.3 in §2 now state the results precisely.

## 1. Source

- **Paper.** J. Araújo, W. Bentz, P. J. Cameron, K. Hendrey, M. Kinyon, *Complete Mappings of Semigroups*, arXiv:2608.25092.
- **Versions.** Only v1 exists: Tue 25 Aug 2026 19:40:50 UTC, 65 KB, submitted by M. Kinyon. Checked at 06:49 UTC on the abs page and again through the arXiv API. There is no v2.
- **Files and hashes.**
  - LaTeX source: `https://arxiv.org/e-print/2608.25092`, fetched 06:38 UTC. SHA-256 `0109b11b959d8156d9eb57f72303484c51196f1810eed22c65f34326b3f67941`; the archive contains `Complete_Mappings_arXiv.tex`, 4924 lines.
  - PDF: `https://arxiv.org/pdf/2608.25092v1`. SHA-256 `456f20d06aac29a4ebffdcb5fed49cd1f9027b8da052159ccde3271b46ceb0c2`.
  - Copies are in `src/`.
- **Location of the problem.** Section 15 ("Problems"), **Problem 15.11**. Its LaTeX label is `p:diagram-monoids` (source lines 4648–4663). It is on PDF page 61.

### 1.1 Verbatim text, with the lead-in paragraph (LaTeX source)

> We assume the reader to be familiar with the Brauer monoid $\mathcal B_n$ and the partial Brauer monoid $\mathcal{PB}_n$; their definitions are given in \cite[Section~2.2]{EastMitchellRuskucTorpey}. In \cite[Proposition~2.1 and Remark~2.2(v)--(vii)]{EastMitchellRuskucTorpey} it is proved that their $\mathcal J$-classes are the rank classes and that a maximal subgroup in rank $r$ is isomorphic to $S_r$.
>
> **Problem 15.11.** Classify complete mappings for $\mathcal B_n$ and $\mathcal{PB}_n$. In view of the Hall--Paige theorem, the unresolved proper factors are those of ranks $2$ and $3$ which occur in the corresponding monoid. Determine also for which values of $n$ the whole monoid has a complete mapping.

`[EastMitchellRuskucTorpey]` is J. East, J. D. Mitchell, N. Ruškuc, M. Torpey, *Congruence lattices of finite diagram monoids*, Adv. Math. 333 (2018) 931–1003.

### 1.2 Definition used by the paper (verbatim, abstract and §1)

> A complete mapping of a semigroup $S$ is a bijection $\alpha\colon S\to S$ such that the map $\theta\colon S\to S$ defined by $x\theta=x\cdot x\alpha$ is also a bijection.

Maps act on the right. For a finite magma this is the same as a transversal of the Cayley table (§1).

## 2. The reduction results the paper provides

Theorem numbers are those of the compiled PDF. LaTeX labels are given in brackets.

| # | Statement (paraphrased; exact text in `src/`) | Used here for |
|---|---|---|
| Thm 1.1 [Thm:HP] | Hall–Paige: a finite group has a complete mapping (CM) iff its Sylow 2-subgroups are trivial or non-cyclic. So $S_r$ has a CM iff $r\notin\{2,3\}$. | groups $S_r$ |
| Prop 1.4 [Prp:zero] | A CM of a magma with zero fixes 0 (so does its orthomorphism). | factors $J^0$ |
| Cor 3.4 [Cor:units] | If a finite monoid has a CM, so does its group of units. | non-existence for $n=2,3$ |
| Thm 4.1 [t:principal-factor-Rees] | Each principal factor is null or a Rees 0-matrix semigroup. | Rees form |
| **Thm 4.4** [t:J-reduct] | **Principal-factor reduction**: $S$ has a CM iff every principal factor $J^0$ has one (convention: $J^0=J\cup\{0\}$, products leaving $J$ become $0$). | whole monoid |
| Thm 5.2 [t:goingup] | Going up, **zero-free version only**: for a Rees matrix semigroup $\mathcal M(G,I,\Lambda,P)$ without zero, if $N\trianglelefteq G$ has a CM and $\mathcal M(G/N,I,\Lambda,\bar P)$ has one, then $\mathcal M(G,I,\Lambda,P)$ has one. Its proof gives the explicit lifting formula. | the formula of the lift (not the statement) |
| Lemma 6.3 [l:factorL] | Going up for Rees **0**-matrix semigroups: if $N\trianglelefteq G$ has a CM and $\mathcal M^0(G/N,I,\Lambda,\bar P)$ has one, then $\mathcal M^0(G,I,\Lambda,P)$ has one. The proof uses the construction of Thm 5.2 on the non-zero elements and fixes $0$. | lift $S_3\to C_2$ through $A_3$ |
| Thm 6.2 [c:Rees0] | For a zero-one matrix $Q$, five conditions are equivalent, among them: (a) for **every** group $G$ with a CM and **every** $P$ over $G\cup\{0\}$ with pattern $Q$, $\mathcal M^0(G,I,\Lambda,P)$ has a CM; (c), (d) the Hall inequalities for rows and for columns; (e) $Q$ has a **balanced support weighting** (non-negative, row sums $\lvert I\rvert$, column sums $\lvert\Lambda\rvert$, supported on $Q$). For a given $G$ with a CM, this yields only "Hall ⇒ CM", via (c)⇒(a). | cross-check only |
| Lemma 7.3 [l:Rees0-support-necessary] | For a **given** finite $\mathcal M^0(G,I,\Lambda,P)$, with any $G$: if it has a CM, then its pattern $Q$ satisfies (c) and (d) of Thm 6.2. This lemma, not Thm 6.2, is the "only if" of the Hall condition for a given $G$. | cross-check only |
| Thm 7.5 [t:Rees0-noncomp-even], Cor 7.6 | **Even case**: if $G$ has no CM and $\lvert I\rvert$ or $\lvert\Lambda\rvert$ is even, a CM exists iff the Hall/balance condition holds. Cor 7.6: if $\lvert I\rvert=\lvert\Lambda\rvert$ is even and $Q$ has a one-transversal, a CM exists. | even $N$ (alternative route) |
| Thm 7.7 [t:incidence-criterion] | **Incidence criterion**: $\partial_\Gamma z=d$ is solvable over an abelian group iff $\prod_{v\in W}d_v=1$ on every component $W$. | cycle equations |
| Thms 7.11, 7.14, 7.17; Cor 7.18 | Sufficient conditions in the **odd-by-odd case**: defect-compatible routings (7.11), cycle-compatible residual permutation (7.14), and positive balanced weighting plus anchored pair (7.17), with the $S_3$ sign form (7.18). | odd $N$ (our Lemma C is a special case of 7.14) |
| Thm 7.19 [t:converse0] | **Non-existence**: if $G$ has a non-trivial cyclic Sylow 2-subgroup, $\lvert I\rvert,\lvert\Lambda\rvert$ are odd, and $P$ arises from a normalised matrix with all entries of odd order by zeroing entries, then there is no CM. | $PB_3$, rank 2 |
| Thm 8.2 [t:linear-monoid] | $\operatorname{End}(\mathbb F_q^d)$ has a CM iff $\mathrm{GL}_d(q)$ does, i.e. unless $d=1$ with $q$ odd, or $(d,q)=(2,2)$. Every proper factor has a CM. | analogue |
| Thm 8.5 [t:partition-monoid] | $\mathcal P_n$ has a CM iff $n=1$ or $n\ge4$. Every proper factor has one. The odd rank-2 and rank-3 cases use Thm 7.17 with a negative 3-cycle $I_0,I_1,I_2$ and the pairing Lemma 8.4. | template |
| Thm 9.16 [Thm:full-transformation-semigroup] | $T_n$ has a CM iff $n=1$ or $n\ge4$. The rank-3 factor for $n\equiv3\pmod 4$ uses Thm 7.17. | analogue |
| Thm 10.1, Cor 10.2 | Inverse semigroups: a CM exists iff each $J$-class has a maximal subgroup with a CM or an even number of $\mathcal L$-classes. $I_n$ has a CM iff $n\equiv0,1\pmod4$. | analogue |

What the paper settles:
- $T_n$, $\mathcal P_n$: a CM exists iff $n=1$ or $n\ge4$.
- Full linear monoids: exactly as in Thm 8.2.
- $I_n$: iff $n\equiv 0,1\pmod 4$.
- Planar partition, Motzkin and Jones monoids: always (Prop 8.7, Cor 8.8).
- For $\mathcal B_n$ and $\mathcal{PB}_n$ the paper proves nothing; they are left as Problem 15.11.

## 3. Fixed reading and normalisations

- **Objects.** $\mathcal B_n$ is the set of perfect matchings of $[n]\cup[n]'$. $\mathcal{PB}_n$ is the set of partial matchings, i.e. partitions into blocks of size 1 or 2.
- **Product.** $xy$: draw $x$ above $y$, identify $x$'s bottom row with $y$'s top row, and keep the connectivity of the outer points. Closed loops and middle-only components are discarded (monoid, not algebra).
- **Rank.** The number of blocks meeting both rows. $n\ge1$; $n=0$ gives the trivial monoid.
- **Principal factor.** For the rank-$r$ $\mathcal J$-class $J_r$ (EMRT Prop 2.1: $\mathcal J$-classes are the rank classes), $J_r^0=J_r\cup\{0\}$, as in the paper's §4.
- **Proper factor.** A principal factor other than that of the group of units ($r=n$).
- **Complete mapping** of $J_r^0$: a bijection of $J_r^0$ whose product map is a bijection. By Prop 1.4 it fixes 0, so equivalently: a bijection $\alpha$ of $J_r$ with $x\cdot x\alpha\in J_r$ for all $x$ and $x\mapsto x\cdot x\alpha$ bijective on $J_r$.

### Readings

- **(W) Weak reading.** Decide, for every $n\ge1$, whether $\mathcal B_n$ and $\mathcal{PB}_n$ have a CM. This is the last sentence of the problem.
- **(M) Main reading**, which we adopt. Also decide, for every $n$ and every rank $r$ that occurs, whether the principal factor $J_r^0$ has a CM. This is "classify complete mappings" as the second sentence explains it: "the unresolved proper factors are those of ranks 2 and 3".
- **(S) Strong reading.** Describe or enumerate *all* complete mappings, as Prop 6.5 does for Brandt semigroups via Latin squares. **Not attempted and not claimed.** No such description is known even for the groups $S_r$.

The deliverable is a complete answer under (M), which includes (W). Any claim beyond (M) is flagged separately in PROOF.md.
