# CONTRACT — switching conjecture for main eigenvalues (trees and regular graphs)

Agent: round6/switching. Written 2026-09-26 ~19:30 UTC (`date -u`). Sources are cited by file and line. The LaTeX of the primary source was read in full.

## 1. Primary source and exact statements

**Source.** arXiv:2609.27046**v1**: S. Akbari, H. Kumar, B. Mohar, S. Pragada, "The switching conjecture for main eigenvalues is asymptotically true".
- Submitted 2026-09-22 20:40 UTC. Only v1 exists; `/abs/2609.27046v2` returns 404 (G1 agent, 19:0x UTC).
- LaTeX: `work/round6/scouting/fresh-0926/src/2609.27046/Switching_v1.tex`; a copy is in `lit/2609.27046/`.

**Problem** (`Switching_v1.tex` lines 201–203, verbatim):
> Show that the switching conjecture for main eigenvalues holds for trees and connected regular graphs of order $n\ge 3$.

**Conjecture 1.1** (lines 129–131, verbatim; attributed to Akbari–França–Ghasemian–Javarsineh–de Lima):
> For any unsigned connected graph $G \notin\{ K_2, K_4 - e\}$, there is a switching $\s$ such that all (distinct) eigenvalues of $G^{\s}$ are main.

**Definitions** (lines 95–116):
- A switching is a vector $\s\in\{\pm1\}^n$.
- $G^{\s}$ is the signed graph with $\sigma(ij)=s_is_j$ on the edges of $G$, so $A(G^{\s})=D_{\s}A(G)D_{\s}$.
- An eigenvalue $\lambda$ is *main* if $E_\lambda\not\subseteq \1^\perp$.

**Correction to the task description.** The conjecture was published in **Linear Algebra Appl. 614 (2021) 270–280**, doi 10.1016/j.laa.2020.04.029, not in Appl. Math. Comput. 2022.
- Appl. Math. Comput. 423 (2022) 127014 is Shao–Yuan, "Some signed graphs whose eigenvalues are main" (= arXiv:2106.07878).
- MathDB #350999 cites the conjecture through 2106.07878.
- Per its zbMATH abstract, the 2021 paper states the conjecture for "every graph $G\ne K_2,K_4-e$" without "connected". 2609.27046 adds "connected" and shows this is necessary (lines 161).
- We follow the 2609.27046 wording.

## 2. Fixed reading and normalisations

Let $A=A(G)$ with distinct eigenvalues $\theta_1,\dots,\theta_d$ and orthogonal projections $P_\theta$ onto $E_\theta$.

(N1) Since $P_\theta(G^{\s})=D_{\s}P_\theta D_{\s}$, we have $\1^\top P_\theta(G^{\s})\1=\s^\top P_\theta\s=\|P_\theta\s\|^2$. So all eigenvalues of $G^{\s}$ are main **iff $P_\theta\s\ne0$ for every $\theta\in\operatorname{spec}(A)$**. We call such an $\s$ *good*.

(N2) **Krylov criterion** (standard):
- $\operatorname{rank}[\s,A\s,\dots,A^{n-1}\s]=\#\{\theta: P_\theta\s\ne0\}$, because $A^j\s=\sum_\theta\theta^jP_\theta\s$ and the vectors $P_\theta\s$ are orthogonal.
- Hence $\s$ is good iff this rank equals $d=\deg\mu_A=n-\deg\gcd(\varphi,\varphi')$.
- Equivalently: every polynomial $f$ with $f(A)\s=0$ has $f(A)=0$ (the annihilator form used in Lean).

(N3) **Galois closure.** For $\s$ rational, $P_\theta\s=0$ iff $P_{\sigma\theta}\s=0$ for every conjugate $\sigma\theta$. So only one condition per irreducible factor of $\mu_A$ over $\mathbb Q$ is needed. This is folklore, as in "the main part of the spectrum is Galois-closed".

(N4) **Bipartite symmetry.** Let $\b$ be the bipartition sign vector. Then $P_{-\theta}=D_{\b}P_\theta D_{\b}$, so the set of good $\s$ is invariant under $\s\mapsto -\s$ and $\s\mapsto \b\circ\s$. Switching $U$ is the same as switching $V\setminus U$.

(N5) For **connected $k$-regular** $G$ and $\s=\1-2\cdot\1_U$:
- $\theta\neq k$ is main in $G^{\s}$ iff $P_\theta\1_U\ne0$;
- $k$ is main iff $2|U|\ne n$.
- This is Stanić 2020, Cor. 4.6 (Czech. Math. J. 70, 1091–1102; read in full; `lit/stanic2020_cmj.txt` l. 456).

## 3. Strong and weak readings

- **Strong (the Problem as posed):** (T) every tree with $n\ge3$ has a good switching, **and** (R) every connected regular graph with $n\ge3$ has one. Both remain OPEN after this session.
- **Weak readings we address:**
  - (R′) a sufficient condition for regular graphs that contains all walk-regular graphs, including those with $\le4$ distinct eigenvalues;
  - (T≤N) all trees with $3\le n\le N$, by exhaustive exact computation;
  - (T3) the stronger quantitative form "a good switching with $\min(|U|,n-|U|)\le3$ exists", for $n\le N$.
- No reading is changed. The exceptions $K_2$ ($n=2$) and $K_4-e$ (not a tree, not regular) are outside both classes when $n\ge3$.

## 4. What is already known (G1 + literature, see PROOF.md §5)

- **2021 paper** (abstract only; full text blocked, 403): Cayley graphs, distance-regular, vertex-transitive and edge-transitive graphs, double stars, paths, stars, and all connected graphs with $n\le9$.
- **Shao–Yuan 2022** (arXiv v3 read in full): harmonic trees $T_a$, complete multipartite graphs, $S_{n,r}$.
- **Stanić 2020:** net-regular criteria (Thm 4.5, Cor 4.6, 4.7).
- **Xiang–Zhang 2023:** Wenger graphs, by switching one vertex.
- **2609.27046:** asymptotic versions, with $n-O(n/(\log n)^{1/4})$ main eigenvalues counted with multiplicity, and $d-O(d/(\log d)^{1/4})$ distinct.
- **Walk-regular graphs:** no source states this. It is an immediate consequence of Stanić Cor 4.6 together with $(P_\theta)_{vv}=m_\theta/n$ (Godsil–McKay 1980). We treat it as **known-in-effect**, not as new.

## 5. Contract for our results

**Theorem R (formal; Lean `Research/SwitchingWalkProfile.lean`).**
- Hypotheses:
  - $A$ is a real symmetric matrix on a finite index set with $|V|\ne2$;
  - $A\1=k\1$;
  - $v\in V$, and weights $w_u>0$ satisfy $(A^j)_{vv}=\sum_u w_u(A^j)_{uu}$ for all $j\ge0$.
- Conclusion: every eigenvalue of $D_{\s_v}AD_{\s_v}$ is main, where $\s_v=\1-2e_v$.
- Lean statements, all over `ℝ`:
  - `annihilator`: $f(A)\s_v=0\Rightarrow f(A)=0$;
  - `eigen_nonorth`: every eigenvalue $\theta$ of $A$ has an eigenvector $y$ with $\s_v\cdot y\ne0$;
  - `main_after_switching`: every eigenvalue $\theta$ of $B=D AD$ has an eigenvector $z$ with $\1\cdot z\ne0$;
  - `walkRegular_main_after_switching`: the special case of constant diagonals of all powers.
- For a graph, "eigenvalue" means real $\theta$ with a nonzero real eigenvector, which is the paper's notion.
- The informal equivalent is that the local spectral vector $((P_\theta)_{vv})_\theta$ lies in the relative interior of the convex hull of all local spectral vectors. That the Lean hypothesis is equivalent to this, and to the truncated profile $j=3..d-2$, is argued on paper only.

**Theorem C (computational, exact certificates).**
- (C1) Every tree with $3\le n\le 24$ has a good switching. That is 63,242,254 trees.
- (C2) For $3\le n\le 23$, some $U\subseteq V$ with $\min(|U|,n-|U|)\le3$ gives a good $\s=\1-2\cdot\1_U$. At $n=24$ this fails for exactly 39 trees. Each of them needs, and has, a good switching with 4 switched vertices (exact; PROOF §3.7).
- The certificate is $\operatorname{rank}_{\mathbb F_p}[\s,\dots,A^{d-1}\s]=d$, with $d$ computed exactly. This is valid because $\operatorname{rank}_{\mathbb F_p}\le\operatorname{rank}_{\mathbb Q}\le d$.
- A second implementation (exact $\mathbb Q$-rank) confirms every $n\le22$.
  - For $n\le21$ it uses its own canonical-augmentation generator.
  - For $n=22$ it uses networkx's WROM code.
  - $n=23,24$ rest on one implementation only (PROOF §3.5).

**Sequence (exact).**
- Let τ(T) = min over good U of min(|U|, n − |U|), and a(n) = max over trees on n vertices of τ(T).
- Then a(3..24) = 1,1,2,2,2,2,2,2,2,2,3,2,3,3,3,3,3,3,3,3,3,4.
- Lower bounds come from exact witnesses, checked by two independent criteria.
- Upper bounds come from the certified exhaustive runs: both implementations for n ≤ 20; implementation B only for 21 ≤ n ≤ 24, plus the exact check of the 39 trees at n = 24 (PROOF §3.7).
- The 13-vertex example below is the witness for a(13) = 3.

**Sharpness (exact).** The 13-vertex tree with edges 0-5, 0-9, 0-12, 0-1, 1-2, 2-3, 3-4, 5-6, 5-8, 6-7, 9-10, 9-11 has no good switching with $\min(|U|,n-|U|)\le2$. It has 28 good 3-sets. See `logs/three_flips_needed.log`.

## 6. Session 2 contract: trees of diameter ≤ 4 (2026-09-26 21:35 UTC)

**Goal (from the coordinator).** Prove that every tree of diameter ≤ 4 other than K₂ has a switching s such that all distinct eigenvalues of T^s are main.

**Reading.**
- Trees of diameter ≤ 4 with n ≥ 3 are exactly the rooted trees T(a) of height ≤ 2 with n ≥ 3:
  - a centre c with children v₁..v_k;
  - v_i has a_i ≥ 0 leaf children.
- Diameter 3 trees (double stars) and diameter 2 trees (stars) are included. Every such tree equals T(a) for a centre c.
- "Main" and "good switching" are as in §2 (N1, N2).

**Definitions used in the statements.**
- **Secular polynomial:** R(t) = ∏_{b∈B}(t − b)·(1 − Σ_b k_b/(t − b)), with B the set of distinct a_i and k_b their multiplicities.
- **Non-even pair:** a pair of irreducible factors g(x), g(−x) ≠ ±g(x) of R(x²) over ℚ.

**Proved (PROOF.md §9).**
- (M) The conclusion holds for every T(a) with n ≥ 3 whose R(x²) has at most one non-even pair.
- It holds with any number of pairs for:
  - stars;
  - T(1,0^k);
  - T(1^{k₁},0^{k₀}) with k₀, k₁ ≥ 2;
  - T(2^m,0^{m+1}) with m ≥ 2;
  - D(2,2);
  - the classes D1, D1+, D2, D3.

**Computed.** All T(a) with 3 ≤ n ≤ 44, with exact certificates.

**Open.** T(a) with ≥ 2 non-even pairs outside the above. For n ≤ 30 these are exactly 5 trees, all certified by computation.

**Lean (session 2).** `SwitchingDiam4.no_eigenvalue_root_cubic` (A rational with Aᵀ = A; θ a real root of the mapped charpoly ⇒ θ³ − θ + 2 ≠ 0). This is exactly the algebraic step used in class D1 and nothing more.

### 6.1 Session 3 update (2026-09-26 22:37 UTC →)

**Proved (PROOF.md §9.0, §9.15, §9.16).**
- (D) The conclusion holds for every tree T(a), n ≥ 3, satisfying any one of:
  - N ≤ 1;
  - all a_i ≤ 1;
  - some a_i ≥ 2 and Row criterion (a) or (b).
- The two criteria:
  - (a) some branch size β ≥ 1 has |𝓛_β| ≥ 2N + 1, where |𝓛_β| = k_ββ − 1 − [β = k_β = 2] for β ≥ 2, and |𝓛₁| = k₁ − 1 (k₁ ≥ 2) or 2 (k₁ = 1);
  - (b) 2(k₀ + 1) > 4N + N_ei, with N_ei the number of secular roots that are even non-square integers.
  - The good switching is one of the explicit candidates s_{ε,Λ} or s_{ε,m}.
- (D′) Every tree with N ≤ 4 satisfies the conclusion. The proof uses a finite exact search of the exceptional region: 799 trees for N = 2, 12,841 for N = 3 and 212,231 for N = 4. The only exceptions, D(2,2) and T(3,1⁴,0³), have explicit switchings.

**Computed.** Census of N for all 376,324 trees with n ≤ 44 gives N ≤ 3. Hence every tree with n ≤ 44 is covered by (D) and (D′).

**Open.** Trees with N ≥ 5 that fail (a) and (b). None is known; any such tree has n ≥ 45. The N = 5 region search was started but not completed (PROOF §9.19).

**Known (with sources)** — none of these covers general diameter-4 trees:

| Class | Source |
|---|---|
| Stars | Akbari et al., LAA 614 (2021), Thm 4.1 (complete bipartite) |
| Double stars (all diameter-3 trees) | Akbari et al., LAA 614 (2021) |
| Paths | Akbari et al., LAA 614 (2021) |
| Harmonic trees | Shao–Yuan, AMC 423 (2022) 127014, Prop. 2.1 |
| All graphs with n ≤ 9 | Akbari et al., LAA 614 (2021) |

**Lean (session 3).** `SwitchingRow.card_bad_le_two` and `card_bad_le_one_of_ne` formalize the counting step "an injective affine map ℤ → K hits {θ, −θ} at most twice", and at most once if 2θ ∉ wℤ. The rest of Theorem D is on paper.

### 6.2 Session 3 final: the complete statement for diameter ≤ 4

**Proved (PROOF.md §9.22, Theorem 9.22).** Every tree of diameter ≤ 4 other than K₂ has a switching s such that every distinct eigenvalue of T^s is main. This is the goal of §6.

**Structure of the proof.** Let b* = max a_i.
- **b* ≥ 13.** Theorem 9.22.2, a hand proof. Criterion (a′) holds at β = b*, so one of the 2(k_{b*}b* − 1) explicit switchings s_{ε,Λ} is good.
- **2 ≤ b* ≤ 12.** Criteria (a′) |𝓛_β| ≥ 2N_I + N_II + 1 or (b′) 2(k₀ + 1) > 4N_I + 2N_II + N_ei (Lemma 9.22.1), where:
  - N_I is the number of perfect-square secular roots;
  - N_II is the number of irrational non-even pairs.
  - The trees failing both form a finite set of 13,376 trees (Lemma 9.22.3). Its exact search (two independent implementations) leaves T(2,2), D(2,2) and K₁,₄, each with an explicit switching.
- **b* ≤ 1.** §9.7 families, class D1, or the Main Theorem.

**Status of each ingredient.**
- **Hand-checkable:** Lemma S, Lemma M, Lemmas 9.15.1–9.15.3, Lemma 9.22.1, Theorem 9.22.2, Lemma 9.22.3, and the family arguments of §9.7.
- **Computer-assisted:**
  - the finite search of Lemma 9.22.3, with two implementations;
  - the resultant check that closes family A (§9.7, finite range [2, 400)²);
  - the exact checks of the explicit switchings.
- **Lean:**
  - `SwitchingThmH.row_budget`: the inequality of Theorem 9.22.2;
  - `sol_subsingleton` and `indep_of_irrational`: the refined count;
  - `SwitchingRow.card_bad_le_two`;
  - `SwitchingDiam4.no_eigenvalue_root_cubic` (class D1).
  - Not formalized: the spectrum lemma, the reduced form and the searches.

**Known before (unchanged; see the §6.1 table):** stars, double stars (diameter 3), paths, harmonic trees, and all graphs with n ≤ 9.

**New:** the theorem for all trees of diameter ≤ 4, the method (reduced form, even/non-even split, Row Lemmas with the refined count, square counting), and the exhaustive checks (n ≤ 44 direct certificates).

**Still open:** Problem (T) for all trees and Problem (R) for all connected regular graphs.

**Superseded:** the "Open" paragraph of §6.1 (N ≥ 5) is closed by Theorem 9.22.
