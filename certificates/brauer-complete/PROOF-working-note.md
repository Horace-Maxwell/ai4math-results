# PROOF: complete mappings of the Brauer and partial Brauer monoids (Problem 15.11 of arXiv:2608.25092)

Round-6 agent `brauer-complete`, 2026-09-26 (UTC). The contract, verbatim statement and readings are in `CONTRACT.md`. The literature search is in `querylog.tsv`.

## 0. Status

| Track | Status |
|---|---|
| Literature (G1) | **No prior solution, claim or announcement found** (details in §8 and `querylog.tsv`). The only earlier AI work on the paper is trureturing #9377/#9405, on Problem 15.5 only; their note explicitly makes no claim on the other problems. **Failed, not zero:** OpenAlex (429) and Semantic Scholar (429). Citing works are therefore unchecked; they must be re-checked at G2. |
| Statement | Main reading (M) of CONTRACT §3: every principal factor of $\mathcal B_n$ and $\mathcal{PB}_n$, and every whole monoid, for all $n\ge1$. |
| Mathematics | **Settled completely under (M).** Proofs are below. They rely on these results of the paper: Thm 1.1 (Hall–Paige), Prop 1.4, Cor 3.4, Thm 4.4 (principal-factor reduction), Lemma 6.3 (going up), Thm 7.19 (non-existence); and on EMRT Prop 2.1 ($\mathcal J$-classes are the rank classes). Everything else is proved here. |
| Computation | Explicit complete mappings (CMs) of the two smallest critical factors: $\mathcal B_6$ rank 2 (4050 elements) and $\mathcal B_7$ rank 3 (66150 elements). **CMs of the whole monoids $\mathcal B_6$ (10395 elements; the first $\mathcal B_n$ with an odd-index critical factor) and $\mathcal{PB}_6$ (140152 elements)**, and of $\mathcal B_1,\mathcal B_4,\mathcal B_5,\mathcal{PB}_1,\mathcal{PB}_4,\mathcal{PB}_5$. Every certificate is re-verified by an independent second implementation. Exhaustive non-existence checks. |
| Formal (Lean) | **Partial.** Lemmas B and C (§3) are formalised for an arbitrary finite index type: `Research/BrauerCMCore.lean` (`lemmaC`, `lemmaB`). `lake build Research.BrauerCMCore` exits 0; `#print axioms` gives ⊆ {propext, Classical.choice, Quot.sound}; `decide` is used only on closed `ZMod 2` facts. The Brauer-specific Lemmas 2.1, D, E, F and the $S_3$ lift are **not** formalised; they are covered by paper proofs and the computations. See §9. |

**Answer.**
- Every proper principal factor of $\mathcal B_n$ has a CM.
- Every proper principal factor of $\mathcal{PB}_n$ has a CM, except the rank-2 factor of $\mathcal{PB}_3$, which has none.
- $\mathcal B_n$ and $\mathcal{PB}_n$ have a CM iff $n\notin\{2,3\}$, i.e. iff $S_n$ does, i.e. iff $n=1$ or $n\ge4$. This matches $T_n$ and $\mathcal P_n$.

Under reading (M), 100% of Problem 15.11 is settled. The strong reading (S), a description of all CMs, is not addressed.

## 1. Main results

Write $H_r=H_r(\mathcal B_n)$ or $H_r(\mathcal{PB}_n)$ for the set of rank-$r$ half-diagrams (§2), and $N=|H_r|$. Then
$$N_{\mathcal B}(n,r)=\binom nr (n-r-1)!!\quad(n\equiv r \bmod 2),\qquad N_{\mathcal{PB}}(n,r)=\binom nr\,a(n-r),$$
where $a(k)$ is the number of involutions of a $k$-set: $1,1,2,4,10,26,76,\dots$

**Theorem 1 ($\mathcal B_n$).** For every $n\ge1$ and every rank $r<n$ with $r\equiv n\pmod2$, the principal factor $J_r^0$ of $\mathcal B_n$ has a complete mapping. The factors not covered by the paper's general results are:
- rank 2 when $n\equiv2\pmod4$, $n\ge6$, where $N=\binom n2(n-3)!!$ is odd; the first case is $\mathcal B_6$ with $N=45$;
- rank 3 when $n\equiv3\pmod4$, $n\ge7$, where $N=\binom n3(n-4)!!$ is odd; the first case is $\mathcal B_7$ with $N=105$.

**Theorem 2 ($\mathcal{PB}_n$).**
- For $n\ge4$, every proper principal factor of $\mathcal{PB}_n$ has a CM. The factors of ranks 2 and 3 have $N$ even.
- For $n\le3$, every proper principal factor has a CM **except the rank-2 factor of $\mathcal{PB}_3$**. That factor is the Brandt semigroup $B(S_2,3)$ and has no CM.

**Theorem 3 (whole monoids).** For $n\ge1$ the following are equivalent:
- (a) $\mathcal B_n$ has a CM;
- (b) $\mathcal{PB}_n$ has a CM;
- (c) $S_n$ has a CM;
- (d) $n=1$ or $n\ge4$.

## 2. Rees coordinates of the rank-$r$ $\mathcal J$-class

Let $D\in\{\mathcal B_n,\mathcal{PB}_n\}$. Points $1,\dots,n$ form the top row and $1',\dots,n'$ the bottom row. $xy$ means $x$ drawn above $y$ (CONTRACT §3).

A **half-diagram of rank $r$** is a pair $h=(F,M)$:
- $F\subseteq[n]$ with $|F|=r$ (the *free points*);
- $M$ a matching of $[n]\setminus F$: perfect for $\mathcal B_n$, partial for $\mathcal{PB}_n$ (unmatched points are *singletons*).

For $x$ of rank $r$:
- $U(x)$ is its top half: $F$ is the set of top points of through-blocks, $M$ the set of top arcs.
- $L(x)$ is its bottom half, with primes removed.
- $g(x)\in S_r$ is defined as follows. Let $a_1<\dots<a_r$ be the top through points and $b_1<\dots<b_r$ the bottom ones. Then $x$ contains the blocks $\{a_k,b'_{k\,g(x)}\}$. Permutations act on the right; products are read left to right.

For $\lambda,i\in H_r$, let $\Gamma(\lambda,i)$ be the multigraph on $[n]$ whose edges are the arcs of $\lambda$ and the arcs of $i$. Its maximum degree is 2, so its components are paths and cycles.
- $\lambda\sim i$ (**compatible**) means: every component containing a point of $F(\lambda)$ is a path with one end in $F(\lambda)$ and the other in $F(i)$. A point of $F(\lambda)\cap F(i)$ is a path of length 0.
- Then $p_{\lambda,i}\in S_r$ is defined by: the $k$-th smallest point of $F(\lambda)$ is joined to the $(k\,p_{\lambda,i})$-th smallest point of $F(i)$.

**Lemma 2.1.**

(a) $x\mapsto(U(x),g(x),L(x))$ is a bijection $J_r\to H_r\times S_r\times H_r$.

(b) For $x,y\in J_r$: $\operatorname{rank}(xy)=r$ iff $L(x)\sim U(y)$. In that case
$$U(xy)=U(x),\qquad L(xy)=L(y),\qquad g(xy)=g(x)\,p_{L(x),U(y)}\,g(y).$$
Hence, with EMRT Prop 2.1 ($J_r$ is a $\mathcal J$-class),
$$J_r^0\cong\mathcal M^0(S_r,H_r,H_r,P),\qquad P_{\lambda,i}=p_{\lambda,i}\ \text{ if }\lambda\sim i,\quad P_{\lambda,i}=0\ \text{ otherwise}.$$
Rows of $P$ correspond to $\mathcal L$-classes and columns to $\mathcal R$-classes. The product is $(i,a,\lambda)(j,b,\mu)=(i,a P_{\lambda j} b,\mu)$ if $P_{\lambda j}\neq0$, and $0$ otherwise.

(c) $\lambda\sim\lambda$ and $p_{\lambda,\lambda}=1$. Also $\lambda\sim i\iff i\sim\lambda$, and $p_{i,\lambda}=p_{\lambda,i}^{-1}$.

(d) If $F(\lambda)=F(i)$, then $\lambda\sim i$ and $p_{\lambda,i}=1$.

*Proof.*

(a) A diagram of rank $r$ is determined by its top arcs and singletons, its bottom arcs and singletons, and the pairing of the top and bottom through points. Every triple occurs.

(b) Consider $xy$. Top arcs and top singletons of $x$ are blocks of $xy$. The top through point $a_k$ of $x$ goes down to the middle point $b_{k g(x)}\in F(L(x))$ and then follows its component in $\Gamma(L(x),U(y))$.
- If that component is a path ending in $F(U(y))$, the walk continues through $y$ to the bottom row.
- Otherwise the path ends at another point of $F(L(x))$. Then two top points are joined, so $xy$ has a top arc.
- Or ($\mathcal{PB}_n$ only) the path ends at a singleton, and $a_k$ becomes a singleton.

In the last two cases the rank drops. So $\operatorname{rank}(xy)=r$ iff all $r$ paths starting in $F(L(x))$ end in $F(U(y))$, which is compatibility. In that case the paths pair $F(L(x))$ bijectively with $F(U(y))$. The top half of $xy$ is then $U(x)$, the bottom half is $L(y)$ by symmetry, and following $a_k$ gives the formula for $g$. Since $\operatorname{rank}(xy)\le r$ always, the rank-$r$ products are exactly the non-zero products of $J_r^0$.

(c) In $\Gamma(\lambda,\lambda)$ every arc is doubled, giving 2-cycles, and every free point is an isolated vertex. $\Gamma(i,\lambda)$ is the same graph as $\Gamma(\lambda,i)$, with the same paths traversed in the opposite direction.

(d) Each free point lies on no arc of $\lambda$ or of $i$, so it is a trivial path. $\square$

**Computer check** (`code/check_structure.py`, log `logs/check_structure.log`):
- Green's $\mathcal D=\mathcal J$-classes equal the rank classes, for $\mathcal B_n$ with $n\le5$ and $\mathcal{PB}_n$ with $n\le4$.
- (a)–(c) hold, and the product rule (b) holds for all pairs in $J_r$ for $\mathcal B_n$, $n\le5$, and $\mathcal{PB}_n$, $n\le4$. For $\mathcal B_6$ it holds for all pairs of rank 0 and rank 6 and for 400 000 random pairs of ranks 2 and 4. For $\mathcal{PB}_5$ it holds for all pairs where $|J_r|^2\le4\cdot10^6$, and for 400 000 random pairs otherwise.
- The values of $N$ and the support degrees match the formulas. For example, $\mathcal B_6$ rank 2 has $N=45$ and every row has degree 35. $\mathcal{PB}_3$ rank 2 has $N=3$ and degree 1, so its support is the identity pattern.

## 3. Three explicit constructions for $\mathcal M^0(S_r,H,H,P)$ with identity diagonal

Throughout, $H$ is a finite set with $|H|=N$, and $P$ is a $H\times H$ matrix over $S_r\cup\{0\}$ with $P_{\lambda\lambda}=1$. By Lemma 2.1(c) this is our situation. Fix a Latin square $L$ on $H$: $L(i,\cdot)$ and $L(\cdot,\lambda)$ are bijections. In the code, $L(i,\lambda)=i+\lambda \bmod N$ after indexing $H$ by $\mathbb Z/N$. Every map $f$ below fixes $0$.

**Lemma A** ($S_r$ has a CM $\varphi$, i.e. $r\notin\{2,3\}$). Put
$$(i,g,\lambda)f=(\lambda,\;g\varphi,\;L(i,\lambda)).$$
This is a CM of $\mathcal M^0(S_r,H,H,P)$.

*Proof.*
- $f$ is bijective: $(i,\lambda)\mapsto(\lambda,L(i,\lambda))$ is a bijection of $H^2$, and $\varphi$ is bijective.
- The product is $x\cdot xf=(i,\,g\,P_{\lambda\lambda}\,g\varphi,\,L(i,\lambda))=(i,\,g\cdot g\varphi,\,L(i,\lambda))$. It is non-zero, and bijective because $g\mapsto g\cdot g\varphi$ and $\lambda\mapsto L(i,\lambda)$ are. $\square$

Lemma A only uses the diagonal (Brandt-type) products, as in the paper's Prop 6.5. For $r=0,1$ take $\varphi=\mathrm{id}$.

For $r\in\{2,3\}$ let $s:S_r\to\mathbb Z/2$ be the sign bit, with kernel $A_r$. Let $\bar{\mathcal M}=\mathcal M^0(\mathbb Z/2,H,H,\bar P)$ with $\bar P=s(P)$, written additively. Then $\bar P_{\lambda\lambda}=0$.

**Lift (paper, Lemma 6.3 / Thm 5.2).** $A_r$ has a CM: $A_2=1$, and on $A_3\cong C_3$ the map $h\mapsto h^2$ is bijective. So a CM $\bar f$ of $\bar{\mathcal M}$ lifts to a CM $f$ of $\mathcal M^0(S_r,H,H,P)$. Explicitly (as implemented), fix $g_0=1$, $g_1=(1\,2)$ and write $g=g_u h$ with $u=s(g)$ and $h\in A_r$. If $(i,u,\lambda)\bar f=(j,v,\mu)$, put
$$(i,g,\lambda)f=(j,\;p^{-1}hp\,g_v,\;\mu),\qquad p=P_{\lambda j}.$$
Then $x\cdot xf=(i,g_uh^2pg_v,\mu)$. For fixed $(i,u,\lambda)$ this runs bijectively over one $A_r$-coset, namely the one given by $\bar f$'s product.

**Lemma B** ($r\in\{2,3\}$, $N$ even). Let $\delta$ be a fixed-point-free involution of $H$, and $t:H\to\mathbb Z/2$ with $t(\delta\mu)=1+t(\mu)$. Writing $\mu=L(i,\lambda)$, define on $\bar{\mathcal M}$
$$(i,\,1+t(\mu),\,\lambda)\bar f=(\lambda,1,\mu),\qquad (i,\,t(\mu),\,\lambda)\bar f=(\lambda,0,\delta\mu).$$
This is a CM of $\bar{\mathcal M}$, hence (Lift) of $\mathcal M^0(S_r,H,H,P)$.

*Proof.*
- Bijectivity: $(\lambda,1,\mu)$ is hit once, from $i$ with $L(i,\lambda)=\mu$. $(\lambda,0,\nu)$ is hit once, from $i$ with $L(i,\lambda)=\delta\nu$.
- Products: $(i,\,t(\mu),\,\mu)$ and $(i,\,t(\mu),\,\delta\mu)$. For fixed $i$ and target class $(i,\nu)$, the two contributions are $t(\nu)$ (from $\lambda$ with $L(i,\lambda)=\nu$) and $t(\delta\nu)=1+t(\nu)$ (from $\lambda'$ with $L(i,\lambda')=\delta\nu$). So they are distinct, and all products are non-zero. $\square$

This only needs $N$ even and a diagonal one-transversal. It is an explicit form of the paper's Cor 7.6.

**Lemma C** ($r\in\{2,3\}$, any $N$). Suppose $\rho\in\operatorname{Sym}(H)$ satisfies $\lambda\sim\lambda\rho$ for all $\lambda$, and on every cycle $(\lambda_0,\dots,\lambda_{m-1})$ of $\rho$
$$m+\#\{t:\ \bar P_{\lambda_t,\lambda_{t+1}}=1\}\equiv0\pmod 2.\tag{$\ast$}$$
Then there is $c:H\to\mathbb Z/2$ with $c(\lambda\rho)=c(\lambda)+1+\bar P_{\lambda,\lambda\rho}$. Define
$$(i,\,c(\lambda),\,\lambda)\bar f=(\lambda,\;1+c(\lambda),\;L(i,\lambda)),\qquad (i,\,1+c(\lambda),\,\lambda)\bar f=(\lambda\rho,\;c(\lambda\rho),\;L(i,\lambda\rho)).$$
This is a CM of $\bar{\mathcal M}$, hence (Lift) of $\mathcal M^0(S_r,H,H,P)$.

*Proof.*
- $c$ exists: propagate it around each cycle; $(\ast)$ is exactly the consistency condition.
- Bijectivity: the first rule has image $\{(\lambda,1+c(\lambda),\mu)\}$, the second $\{(\kappa,c(\kappa),\mu)\}$ with $\kappa=\lambda\rho$. Here $\mu$ ranges over $H$ as $i$ does. These are complementary.
- Products:
  - First rule: $(i,\,c(\lambda)+0+1+c(\lambda),\,L(i,\lambda))=(i,1,L(i,\lambda))$. It is non-zero since $\lambda\sim\lambda$.
  - Second rule: $(i,\,1+c(\lambda)+\bar P_{\lambda,\lambda\rho}+c(\lambda\rho),\,L(i,\lambda\rho))=(i,0,L(i,\lambda\rho))$. It is non-zero since $\lambda\sim\lambda\rho$.
  - For fixed $i$ these fill $\{i\}\times\{1\}\times H$ and $\{i\}\times\{0\}\times H$ bijectively. $\square$

*Remarks.*
- $\rho$ has no fixed points: a 1-cycle violates $(\ast)$ because $\bar P_{\lambda\lambda}=0$.
- A transposition $(a\ b)$ with $a\sim b$ always satisfies $(\ast)$, since $\bar P_{ab}=\bar P_{ba}$ by Lemma 2.1(c).
- A 3-cycle $a\to b\to c\to a$ satisfies $(\ast)$ iff an odd number of $\bar P_{ab},\bar P_{bc},\bar P_{ca}$ equal 1 (a *negative triangle*).
- Lemma C is the special case of the paper's **Thm 7.14** (residual routing) with routing $\Theta(i,\lambda)=(\lambda,L(i,\lambda))$ and residual permutation $R(i,\lambda)=(i,\lambda\rho)$. $(\ast)$ is the paper's cycle condition (eq. `general-residual-cycle-condition`). We give the direct four-line proof because it yields an explicit formula and avoids the flow/König steps of Thm 7.17.

## 4. The Brauer monoid: odd index sets

Assume $r\in\{2,3\}$, $n\equiv r\pmod 2$ and $n-r\ge4$. Write points as $1,\dots,n$, and let $G$ be the compatibility graph on $H=H_r(\mathcal B_n)$: $\lambda\ne\mu$ are adjacent iff $\lambda\sim\mu$.

**Lemma D (negative triangle).** Let $E$ be $\emptyset$ for $r=2$ and $\{5\}$ for $r=3$. Let $R_0$ be the matching $\{6,7\},\{8,9\},\dots$ for $r=3$, and $\{5,6\},\{7,8\},\dots$ for $r=2$. Define
$$I_0=(\{3,4\}\cup E,\ \{1,2\}\cup R_0),\quad I_1=(\{2,4\}\cup E,\ \{1,3\}\cup R_0),\quad I_2=(\{2,3\}\cup E,\ \{1,4\}\cup R_0).$$
They are pairwise compatible, with $p_{I_0,I_1}=p_{I_1,I_2}=1$ and $p_{I_2,I_0}=(1\,2)$. So $\rho_0=(I_0\,I_1\,I_2)$ satisfies $(\ast)$.

*Proof.* The arcs of $R_0$ and the point 5 (if $r=3$) are common to all three, so only the points 1–4 matter.
- $\Gamma(I_0,I_1)$: $3\to1\to2$ (via $\{1,3\}$ then $\{1,2\}$), and $4$ is a trivial path. So $3\mapsto2$ and $4\mapsto4$; order preserved.
- $\Gamma(I_1,I_2)$: $2$ is trivial, and $4\to1\to3$. Order preserved.
- $\Gamma(I_2,I_0)$: $2\to1\to4$, and $3$ is trivial. So the smaller free point 2 goes to the larger point 4: a transposition. The extra free point 5 is fixed and is the largest in both sets.

These are the same three half-diagrams the paper uses for $\mathcal P_n$ in Thm 8.5, completed to perfect matchings. $\square$

**Lemma E (joining two fibres).** For an $r$-set $F$ let the *fibre* be $H_F=\{h\in H:F(h)=F\}$. It has size $m=(n-r-1)!!$, which is odd and at least 3. By Lemma 2.1(d) each fibre is a clique of $G$.

Let $F\neq F'$ with $F\setminus F'=\{x_1<\dots<x_k\}$, $F'\setminus F=\{y_1<\dots<y_k\}$, and suppose $r+2k\le n$. Choose distinct $z_1,\dots,z_k\notin F\cup F'$ and a perfect matching $R$ of the remaining $n-r-2k$ points (an even number). Then
$$v=(F,\ \{z_t,y_t\}_t\cup R)\in H_F\quad\text{and}\quad w=(F',\ \{x_t,z_t\}_t\cup R)\in H_{F'}$$
are compatible: the paths are $x_t\to z_t\to y_t$, the points of $F\cap F'$ are trivial paths, and $R$ gives 2-cycles.

**Lemma F (perfect matching of $G-X$).** Let $X=\{I_0,I_1,I_2\}$ and suppose $N$ is odd. Then $G-X$ has a perfect matching.

*Proof.*
- $X$ meets exactly the three fibres over $\{3,4\}\cup E$, $\{2,4\}\cup E$, $\{2,3\}\cup E$, one element each.
- Since $m$ is odd, $N=\binom nr m$ odd means $\binom nr$ is odd, so the number $\binom nr-3$ of other fibres is even.
- Pair the other fibres into pairs $(F,F')$ satisfying Lemma E's condition $r+2|F\setminus F'|\le n$:
  - If $r=2$ ($k\le2$, $n\ge6$) or $r=3$ with $n\ge9$ ($k\le3$), every pair qualifies, so any pairing works.
  - If $(n,r)=(7,3)$, the condition is $F\cap F'\neq\emptyset$. The intersection graph of the 32 remaining 3-subsets of $[7]$ has minimum degree at least $30-3=27\ge16$. By Dirac's theorem it is Hamiltonian, so it has a perfect matching. An explicit one is in the certificate.
- For each fibre pair take the edge $(v,w)$ of Lemma E.
- Every fibre now has $m-1$ unused elements, an even number. Pair them inside the fibre (a clique). $\square$

**Proof of Theorem 1.**
- *Parities.* $(n-r-1)!!$ is odd, so $N$ is odd iff $\binom nr$ is odd. For $r=2$ ($n$ even) this happens iff $n\equiv2\pmod4$. For $r=3$ ($n$ odd) it happens iff $n\equiv3\pmod4$ (Lucas). Proper factors need $n>r$, so $n\ge6$, resp. $n\ge7$, and then $n-r\ge4$.
- *Odd $N$.* $\rho=\rho_0\cdot\prod_{\{a,b\}\in\mathcal M}(a\ b)$, with $\mathcal M$ from Lemma F, satisfies Lemma C's hypotheses. So the factor has a CM.
- *Even $N$, $r\in\{2,3\}$.* Lemma B.
- *$r\notin\{2,3\}$.* Lemma A, with Hall–Paige (Thm 1.1) for $r\ge4$.

These cover every proper factor. $\square$

## 5. The partial Brauer monoid

*Parity.* $a(k)=a(k-1)+(k-1)a(k-2)$ with $a(2)=2$ and $a(3)=4$. By induction $a(k)$ is even for $k\ge2$. For $n\ge4$ and $r\in\{2,3\}$, either $n-r\ge2$, so $a(n-r)$ is even, or $(n,r)=(4,3)$ with $N=4$. So **$N$ is even** in all these cases, and Lemma B applies. Ranks $r\notin\{2,3\}$ are covered by Lemma A. This proves Theorem 2 for $n\ge4$.

For $n\le3$ the proper factors of ranks other than 2 are covered by Lemma A. The only rank-2 proper factor is that of $\mathcal{PB}_3$.

**$\mathcal{PB}_3$, rank 2.**
- A half-diagram is $(F,\varnothing)$ with $|F|=2$; the third point is a singleton.
- If $F\ne F'$, a point of $F\setminus F'$ is a dead end in $\Gamma$. So the support is the identity pattern with $p_{hh}=1$, and $J_2^0\cong\mathcal M^0(S_2,3,3,\mathrm{diag}(1,1,1))=B(S_2,3)$.
- By the paper's Thm 7.19 (all entries of odd order; $|I|=|\Lambda|=3$ odd; $S_2$ has a non-trivial cyclic Sylow 2-subgroup) it has **no** CM. Equivalently, by Thm 10.1: an inverse semigroup whose $J$-class has 3 $\mathcal L$-classes and maximal subgroup $S_2$.
- Independently, an exhaustive depth-first search over all bijections of the 19-element factor finds none (67 911 890 nodes; `code/nonexistence.py`, `logs/nonexistence.log`). $\square$

## 6. Whole monoids (Theorem 3)

- (a) or (b) $\Rightarrow$ (c): by Cor 3.4, since the group of units of $\mathcal B_n$ and of $\mathcal{PB}_n$ is $S_n$ (the rank-$n$ class). This is also checked exhaustively for $n=2,3$.
- (c) $\Leftrightarrow$ (d): Hall–Paige (Thm 1.1).
- (c) $\Rightarrow$ (a), (b): the top factor $S_n^0$ has a CM, and every proper factor has one (Theorems 1 and 2; for $\mathcal{PB}_n$ with $n\ge4$ there is no exceptional factor). Then use Thm 4.4. $\square$

## 7. Checks and certificates

Two implementations:
- **Implementation 1** (`code/diagrams.py`, `check_structure.py`, `construct.py`, `check_proof_rho.py`): products by union-find; Rees coordinates; the constructions of §3–4 exactly as written.
- **Implementation 2** (`code/verify_cm.py`, `nonexistence.py`): a separate parser and a separate product (walking alternating paths, no union-find). It enumerates elements itself, via involutions of `itertools.permutations`, and computes the size of $J_r$ from the closed formula. It never uses the Rees coordinates.

A certificate file lists `x<TAB>alpha(x)` for every element of the factor or monoid. The checker verifies:
- the keys are exactly $J_r$ (valid diagrams of rank $r$, all distinct, count $=N^2r!$);
- the values are distinct and of rank $r$;
- $x\cdot x\alpha$ has rank $r$ (non-zero in $J_r^0$) for all $x$, and these products are distinct.

| Certificate (`certificates/`) | Content | Entries | SHA-256 | Independent check |
|---|---|---|---|---|
| `cm_B6_rank2.txt` | CM of $J_2^0(\mathcal B_6)$, $N=45$ odd (Lemmas C, D, F) | 4050 | `246e42f7…04d9d0` | VERIFIED |
| `cm_B7_rank3.txt` | CM of $J_3^0(\mathcal B_7)$, $N=105$ odd | 66150 | `203422dd…7cbfec6` | VERIFIED |
| `cm_B4_all.txt`, `cm_B5_all.txt`, `cm_B1_all.txt` | CMs of the whole monoids | 105 / 945 / 1 | `4cb7b2dd…326`, `026dc8b4…709`, `4b30fc60…7be` | VERIFIED |
| `cm_PB4_all.txt`, `cm_PB5_all.txt`, `cm_PB1_all.txt` | CMs of the whole monoids | 764 / 9496 / 2 | `8fb17908…a32`, `e5a5f6d0…d23`, `fc98246d…4ec` | VERIFIED |
| **`cm_B6_all.txt`** | **CM of the whole monoid $\mathcal B_6$**: ranks 0, 2 (Lemma C), 4, 6 | 10395 | `fc542082…d2dc55` | VERIFIED |
| **`cm_PB6_all.txt`** | **CM of the whole monoid $\mathcal{PB}_6$**: ranks 2, 3 by Lemma B | 140152 | `b8c9c943…7625e7` | VERIFIED |
| `cm_S4.json`, `cm_S5.json`, `cm_S6.json` | CMs of $S_4,S_5$ (CaDiCaL) and $S_6$ (exact cover, `group_cm_dlx.py`, 409 s; CaDiCaL timed out at 1195 s). Used for the top and rank $\ge4$ factors | 24 / 120 / 720 | `58d5f257…a269`, `d964f32c…9f70`, see `logs/hashes.txt` | checked in-script and through the whole-monoid certificates |
| `rho_B6_rank2.txt`, `rho_B7_rank3.txt` | human-readable $\rho$ (triangle plus pairs), sign bits and $c$ used by Lemma C | 45 / 105 rows | see `logs/hashes.txt` | (input data of the two factor certificates) |
| `alt/cm_B6_rank2.txt`, `alt/cm_B7_rank3.txt` | a second pair of CMs, built from a *searched* negative triangle (sign bits 0,1,0) and a networkx maximum matching instead of the proof's choices | 4050 / 66150 | `603ec41c…e96b`, `0f836e59…f28b` | VERIFIED |

Full hashes are in `logs/hashes.txt`. The whole pipeline is reproduced by `code/run_all.sh`, log `logs/run_all.log`; every certificate hash was identical on re-generation. Further checks:
- `check_proof_rho.py` (`logs/check_proof_rho.log`) confirms the triangle sign bits $(0,0,1)$ and a perfect matching of $G-X$ by compatible pairs for $(n,r)=(6,2),(7,3),(10,2),(11,3),(14,2)$, i.e. $N=45$, $105$, $4725$, $17325$, $945945$.
- `check_triangle_indep.py` (implementation 2, coordinate-free) confirms $e_{I_0}e_{I_1}e_{I_2}e_{I_0}$ is the diagram swapping the two through strings (an odd element of the group $\mathcal H$-class of $e_{I_0}$), for $n=6,7,10,11$.
- `check_parities.py` confirms the parity pattern of $N(n,r)$, $r\in\{2,3\}$, for all $n\le200$ in both families. In particular $\mathcal{PB}_n$ has odd $N$ only at $(n,r)=(2,2),(3,2),(3,3)$.
- `nonexistence.py`: $S_2,S_3$ have no CM; the units of $\mathcal B_2,\mathcal B_3,\mathcal{PB}_2,\mathcal{PB}_3$ are exactly the permutation diagrams; $\mathcal{PB}_3$ rank 2 has no CM (exhaustive); three positive controls pass.

## 8. What is new, what is known (G1 summary)

**Known (arXiv:2608.25092 itself):**
- the reduction to principal factors (Thm 4.4);
- the Rees 0-matrix criteria: Thms 6.2, 7.5, 7.14, 7.17 and 7.19;
- the same pattern for $\mathcal P_n$, $T_n$ and $\operatorname{End}(V)$;
- the triangle $I_0,I_1,I_2$ (Thm 8.5, for $\mathcal P_n$).

Our Lemmas A, B and C are explicit special cases of the paper's Prop 6.5/Thm 6.2, Cor 7.6 and Thm 7.14.

**New:**
1. The Rees data of $\mathcal B_n$ and $\mathcal{PB}_n$ (Lemma 2.1), with reflexive, symmetric support and identity diagonal.
2. The parity analysis: for $\mathcal{PB}_n$ with $n\ge4$ every rank-2 and rank-3 factor has an even index set, so Problem 15.11 for $\mathcal{PB}_n$ is immediate from Cor 7.6. The single exceptional proper factor is $\mathcal{PB}_3$ rank 2, which has **no** CM; this is the only negative proper factor in the family.
3. For $\mathcal B_n$: the odd cases ($n\equiv2,3\pmod 4$) are settled by the negative triangle (Lemma D) and a perfect matching of the compatibility graph minus the triangle (Lemmas E, F). This gives a CM by an explicit formula; no flows or edge colourings are needed.
4. The complete answer to Problem 15.11 under reading (M), and to the whole-monoid question: iff $n\notin\{2,3\}$.
5. Machine-checkable certificates:
   - for the first two critical factors ($\mathcal B_6$ rank 2, $\mathcal B_7$ rank 3);
   - for the whole monoids $\mathcal B_4,\mathcal B_5,\mathcal B_6$ ($\mathcal B_6$ is the first with an odd-index critical factor) and $\mathcal{PB}_4,\mathcal{PB}_5,\mathcal{PB}_6$;
   - a Lean 4 proof of the two abstract constructions (Lemmas B and C).

**Assessment.** This is a routine but complete extension of the paper's own methods; the novelty is modest. The main risk to priority is the authors' own v2 (the $\mathcal P_n$ template transfers directly).

**G1 coverage:**
- arXiv versions: v1 only.
- arXiv API: 8 phrasings; the first 4 failed on an http→https redirect and were redone.
- trureturing:
  - issues and PRs updated since 05:00Z;
  - a regex grep over the titles and bodies of all #1–#10138 (the scout's 05:58Z dump): only #9377/#9405 are relevant;
  - #9377 and #9405 read with their comments;
  - full tree at `f64143db`, except `Meta/`, which is truncated;
  - the literature note `araujo2026completemappings.md` read in full;
  - code search with a positive control.
- MathDB: 9 title phrasings, 450 items; no entry for this paper.
- SCOPE2026 at `796426b8`: tree and content grep, with a positive control; the hits are about group orthomorphisms only.
- AI-Has-Taste at `f3ae144b` and formal-conjectures at `2424bb48`: tree grep, 0 hits.
- astrafala: OEIS-only, 0 hits.
- gh search commits (6), code (4) and repos (3); web search (6).
- MathOverflow and Math.SE (StackExchange API, 3 phrasings each): nothing relevant.
- Author pages: Cameron's blog post of 2026-08-27 has 0 comments; no later post; his publication list and arXiv feed show no follow-up. Kinyon's AGTA 2025 slides: no diagram monoids.
- Crossref: nothing.
- **OpenAlex and Semantic Scholar: HTTP 429, counted as FAILED.**

## 9. Lean and open items

**Lean: partial formalisation (optional part of the task).**
- File: `Research/BrauerCMCore.lean` in `work/research-lean`, with a copy at `lean/BrauerCMCore.lean` (SHA-256 `a8622961…5f3c`, identical).
- Build: `lake build Research.BrauerCMCore` under lock B, 07:38:24–07:38:32 UTC. Exit 0; peak RSS 5.9 GB. Log: `logs/lean_build.log`.
- Axioms: `lemmaC` and `lemmaB` depend only on `[propext, Classical.choice, Quot.sound]`.
- Forbidden-word grep (`sorry|admit|axiom|native_decide|bv_decide|implemented_by|extern|unsafe|partial def|debug.skipKernelTC`): no hits apart from the two `#print axioms` lines.
- The 10 uses of `decide` are closed statements about `ZMod 2`: at most 3 variables, 8 cases.
- Kernel replay: `lake env leanchecker Research.BrauerCMCore`, 07:43:12–07:43:20 UTC, **exit 0** (`logs/leanchecker.log`). It replays the module's own declarations and trusts the imported Mathlib. It uses Lean's own kernel, so it is not an independent kernel.
- The module is not added to `Research.lean`, so that other agents' default-target builds are unaffected. Build it with `lake build Research.BrauerCMCore`.

Statement table:

| Lean | Plain meaning | PROOF.md | Difference |
|---|---|---|---|
| `mul P` on `Option (H × ZMod 2 × H)` | the Rees 0-matrix product of $\mathcal M^0(\mathbb Z/2,H,H,\bar P)$; `none` is 0; `P l j = none` is a zero entry | §3, $\bar{\mathcal M}$ | none |
| `IsCompleteMapping op α` | α bijective and x ↦ op x (α x) bijective | paper's definition | stated for any magma; associativity is not needed |
| `lemmaC` | hypotheses: $\bar P_{ll}=0$; $\bar P_{l,\rho l}=s_l$ (a support edge); $c(\rho l)=c(l)+1+s_l$; $L$ a Latin square (rows and columns injective); $H$ finite. Conclusion: `fC` is a CM | Lemma C | Lean assumes the solution $c$ exists; PROOF.md derives $c$ from $(\ast)$ by propagating around cycles (elementary, not formalised). No parity assumption on $N$ is needed in either. |
| `lemmaB` | hypotheses: $\bar P_{ll}=0$; δ a permutation with $t(\delta\mu)=t(\mu)+1$; $L$ a Latin square. Conclusion: `fB` is a CM | Lemma B | Lean is slightly **stronger**: δ need not be an involution |

**Not formalised:**
- Lemma 2.1 (Rees coordinates of the diagram monoids; EMRT Prop 2.1);
- the lift through $A_3$ (paper Lemma 6.3);
- Lemmas D, E, F (triangle and matching);
- Theorem 4.4 of the paper.

These are covered by the written proofs, and for $n\le7$ (Lemma 2.1) or $n\le14$ (Lemmas D–F) by the independent computations of §7. A full formalisation would need diagram monoids in Lean, which Mathlib lacks.

**Other open items:**
- **Whole-monoid certificates.**
  - $\mathcal B_6$ and $\mathcal{PB}_6$: done. The CM of $S_6$ was found by exact cover (`logs/group_cm_S6_dlx.log`); CaDiCaL had timed out (`logs/group_cm_S6.log`).
  - $\mathcal B_7$ as a whole: not done. It needs a CM of $S_7$ (5040 elements), too large for the Python exact cover.
  - None of these is needed for the theorems: $S_n$ has a CM for $n\ge4$ by Hall–Paige, and the critical $\mathcal B_7$ rank-3 factor is certified separately.
- **G2 to-do before any publication:**
  - retry OpenAlex and Semantic Scholar citing-works for 2608.25092; both returned 429 today;
  - re-check arXiv for a v2 of 2608.25092;
  - re-check trureturing issues and PRs, MathDB and the Cameron blog within 24 h of release.

---
*Release note (v1.4.0 packaging).* Some files referenced above are not redistributed in the public repository: the query log and raw search dumps (`querylog.tsv`, `g1/`), the copy of the source paper (`src/`), and the referee's own scripts (`review/r2/`). Reproducing the certificates needs only `code/` and `certificates/`, via `code/run_all.sh`. `logs/hashes-release.txt` lists the SHA-256 of the shipped files.
