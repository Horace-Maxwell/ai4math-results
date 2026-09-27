# PROOF — switching conjecture for main eigenvalues: trees and regular graphs

Agent: round6/switching. Session 1: 2026-09-26 18:42–20:47 UTC. Session 2 (trees of diameter ≤ 4): 21:35–22:35 UTC, see §9. Session 3 (trees of diameter ≤ 4, all remaining cases): 22:37 UTC–00:19 UTC (27 Sep), see §9.0 and §9.15–9.23. The statement contract is in `CONTRACT.md` (§6 for session 2).

## 0. Status table

| Item | Literature / novelty | Statement | Mathematics | Formal (Lean) |
|---|---|---|---|---|
| Problem (T): all trees | open (2609.27046 l.199; G1: no claim anywhere) | fixed (CONTRACT §1) | **not proved** | — |
| Problem (R): all connected regular graphs | open | fixed | **not proved** | — |
| Thm R: walk-profile criterion (contains walk-regular) | walk-regular case is known in effect (Stanić 2020 Cor 4.6 + Godsil–McKay); the convex-hull form was not found anywhere | fixed | proved (§1) | **built; axioms clean; clean-directory replay OK** (`Research/SwitchingWalkProfile.lean`) |
| Cor R1: regular graphs with ≤ 4 distinct eigenvalues | follows from van Dam 1995 (walk-regular) + Thm R; no explicit statement found | fixed | proved | covered by `walkRegular_main_after_switching` once walk-regularity is given (the van Dam step is not formalized) |
| Thm C: all 63,242,254 trees with 3 ≤ n ≤ 24; for n ≤ 23 with ≤ 3 switched vertices | new computation (previous: all graphs n ≤ 9 [2021]; our scout: trees n ≤ 19, floating point) | fixed | exact certificates; two independent implementations for n ≤ 22; n = 23, 24 by one implementation only | not formalized (too large for the kernel) |
| a(n) = worst-case minimum number of switched vertices (§3.7): exact for 3 ≤ n ≤ 24, namely 1,1,2,…,2,3,2,3,…,3,**4** | new (not in OEIS) | fixed | exact lower-bound witnesses (two criteria); upper bounds from B (A for n ≤ 20), plus an exact check of the 39 exceptional trees at n = 24 | — |
| Lemma G (bipartite Galois pairing) | new observation, elementary | fixed | proved (§4.3) + numerical sanity check | — |
| **Session 2 — Main Theorem:** every tree of diameter ≤ 4 (n ≥ 3) with at most one non-even secular pair (§9.0) | new; G1 (§9.12): no prior claim. Known before: stars, double stars, paths, harmonic trees | fixed (CONTRACT §6) | proved (§9.2–9.8), with explicit switchings; families A and B; classes D1–D3 | key algebraic step of class D1 formalized: `Research/SwitchingDiam4Cubic.lean`, built, axioms clean, clean replay OK. The spectrum lemma and the rest are not formalized |
| Session 2 — all trees of diameter ≤ 4 with n ≤ 44 (376,324 rooted trees of height ≤ 2) | new computation | fixed | exact certificates, 0 failures; d-formula cross-checked by sympy for n ≤ 30; the proved constructions re-checked exactly for n ≤ 30 | — |
| Session 2 — trees of diameter ≤ 4 with ≥ 2 non-even secular pairs outside the families and classes | — | fixed | superseded by session 3 (next rows) | — |
| **Session 3 — Theorem D** (§9.0, §9.15): Row Lemmas, valid for any number N of non-even pairs | new | fixed (CONTRACT §6) | proved (hand-checkable) | — |
| Session 3 — Corollary D′: every tree of diameter ≤ 4 with N ≤ 4 (intermediate; superseded by Theorem 9.22) | new | fixed | proved, with a finite computer-assisted region search (799 + 12,841 + 212,231 trees; §9.16), re-run by a second implementation (§9.21) | — |
| Session 3 — all trees of diameter ≤ 4 with n ≤ 44 covered by Theorem D (census: N ≤ 3, §9.17) | new | fixed | proof + exact census | — |
| **Session 3 — Theorem 9.22: every tree of diameter ≤ 4 other than K₂ has a switching making all eigenvalues main** | new; G1 recheck at 23:00 UTC (§9.19): no prior claim | fixed (CONTRACT §6.2) | **proved** (§9.22): hand proof when the largest branch has ≥ 13 leaves; otherwise a finite search of 13,376 trees (two independent implementations) leaves 3 trees on ≤ 7 vertices with explicit switchings | the inequality of Thm 9.22.2 and the refined count are formalized (`Research/SwitchingThmH.lean`, built, axioms clean, clean replay OK); spectrum lemma, reduced form and finite search not formalized |

**Verdict.** The Problem is not solved; no complete proof for all trees or all regular graphs was found. **Session 3 proved it for every tree of diameter ≤ 4 (Theorem 9.22, §9.22).**

Session 2 proved the conjecture for **all trees of diameter ≤ 4 with at most one non-even secular pair**. That is 9,284 of the 9,294 trees with n ≤ 26, and together with the explicit families and classes, all but 5 trees with n ≤ 30. It also verified every tree of diameter ≤ 4 with n ≤ 44. A thin arithmetic residue (≥ 2 non-even pairs) remains unproved (§9.0, §9.11).

What session 1 established:
- a clean, Lean-verified sufficient condition for regular graphs, whose main content (walk-regular) is known in effect;
- an exhaustive exact verification for all trees up to 24 vertices;
- a new integer sequence a(n), the worst-case minimum number of switched vertices:
  - exact for n ≤ 24; not monotone (a(13) = 3, a(14) = 2);
  - a(24) = 4: exactly 39 trees on 24 vertices need 4 switched vertices;
- structural lemmas that explain where the difficulty in trees sits.

## 1. Theorem R (regular graphs; Lean-verified)

**Theorem R.** Let A be a real symmetric matrix on a finite set V with |V| ≠ 2 and constant row sums, A**1** = k**1**. Let v ∈ V. Suppose there are weights w_u > 0 (u ∈ V) with

  (A^j)_{vv} = Σ_u w_u (A^j)_{uu}  for every j ≥ 0. (★)

Let s_v = **1** − 2e_v. Then:
- every polynomial f with f(A)s_v = 0 satisfies f(A) = 0;
- equivalently, every eigenvalue of D_{s_v} A D_{s_v} is main.

When A is the adjacency matrix of a connected k-regular graph G with n ≥ 3, **switching G at the single vertex v makes all eigenvalues of G^{s_v} main.**

**Proof.**
1. Let M = f(A). M is symmetric, M**1** = f(k)**1**, and f(A)s_v = 0 gives f(k)**1** = 2Me_v.
2. Sum the coordinates. Using symmetry, **1**ᵀMe_v = (M**1**)_v = f(k). So n f(k) = 2 f(k), hence f(k) = 0 because n ≠ 2. Therefore Me_v = 0.
3. Put g = f². Then g(A) = M², and (M²)_{uu} = ‖Me_u‖² ≥ 0 for every u, with (M²)_{vv} = 0.
4. By linearity, (★) holds for every polynomial in A in place of A^j. Hence 0 = (M²)_{vv} = Σ_u w_u ‖Me_u‖².
5. Since every w_u > 0, Me_u = 0 for all u, so M = 0.
6. Eigenvalue form: let θ be an eigenvalue and μ = minpoly(A) = (x − θ)q. Then q(A) ≠ 0, so y := q(A)s_v ≠ 0 by the annihilator form, and (A − θ)y = 0.
7. If s_v·y = 0, then ‖y‖² = s_vᵀq(A)²s_v = q(θ)·(s_v·y) = 0, a contradiction. So s_v·y ≠ 0.
8. Passing to B = DAD with D = diag(s_v), D² = I, gives an eigenvector z = Dy of B with **1**·z = s_v·y ≠ 0. ∎

**Remarks.**
- (a) (★) says that the local spectral vector ((P_θ)_{vv})_θ of v lies in the relative interior of the convex hull of all vertices' local spectral vectors. Indeed (A^j)_{vv} = Σ_θ θ^j (P_θ)_{vv}, and a Vandermonde matrix is invertible.
- (b) For a connected k-regular graph with d distinct eigenvalues, it suffices to check (★) for 3 ≤ j ≤ d − 2, together with Σ_u w_u = 1.
  - The cases j = 0, 1, 2 are then automatic: (A^j)_{uu} = 1, 0, k.
  - The cases j ≥ d − 1 follow because the Hoffman polynomial gives A^j = p_j(A) + c_jJ with deg p_j ≤ d − 2.
- (c) Walk-regular graphs are the case w_u = 1/n. This covers distance-regular, vertex-transitive and Cayley graphs (known), and all walk-regular graphs.
- (d) For d = 5 distinct eigenvalues, (★) holds iff v lies in a number of triangles strictly between the minimum and the maximum over all vertices, or all counts are equal.
- (e) The walk-regular case also follows in two lines from Stanić 2020, Cor 4.6 (see CONTRACT §2, N5), because (P_θ)_{vv} = m_θ/n > 0 there. We therefore do **not** claim the walk-regular case as new. What is new is:
  - the convex-hull form (★);
  - the self-contained polynomial proof;
  - the Lean formalization.
- (f) **Cor R1.** A connected regular graph with at most four distinct eigenvalues is walk-regular (van Dam 1995: A³ has constant diagonal by the Hoffman polynomial). So every such graph with n ≥ 3 satisfies the conjecture by switching any single vertex.
- (g) **Complement remark (trivial).** If G is k-regular and both G and its complement are connected, then G and its complement have the same eigenspaces. Hence their sets of good switchings coincide.

**Lean.** Files: `work/research-lean/Research/SwitchingWalkProfile.lean` and `.../SwitchingWalkProfileAudit.lean`; copies in `lean/`, sha256 in `lean/SHA256SUMS`.
- Declarations: `annihilator`, `eigen_nonorth`, `main_after_switching`, `walkRegular_main_after_switching`.
- Build: `lake build Research.SwitchingWalkProfile Research.SwitchingWalkProfileAudit` exited 0 at 19:20:24 UTC. Log: `logs/lake_build_SwitchingWalkProfile.log`.
- Toolchain: Lean 4.33.1, Mathlib `0df444a3…`.
- Axiom audit: 8 `#print axioms` lines for 4 distinct declarations (each printed twice). Every set is ⊆ {propext, Classical.choice, Quot.sound}.
- Forbidden-token grep (sorry, admit, native_decide, bv_decide, implemented_by, extern, axiom, debug.): empty.
- Lock B was held 19:18:51–19:20:35 UTC and released.
- `Research.lean` was **not** edited, to avoid conflicts with other agents. The main agent should add `import Research.SwitchingWalkProfile` if wanted.
- The audit file checks the semantics of `switchVec` and of `D A D` on K₃ switched at vertex 0: entry (0,1) = −1 and entry (1,2) = +1.
- **Not formalized:**
  - the passage "graph ⇒ matrix" (it is literally A = adjacency matrix);
  - the convex-hull reformulation of (★);
  - van Dam's walk-regularity for d ≤ 4.
- **Clean-directory replay** (playbook 3.5, step 4), 20:12:07–20:12:44 UTC, under lock B:
  - fresh directory `lean/replay-20260926T201207Z/` containing only lakefile, manifest, toolchain and the two sources; `.lake/packages` symlinked to the shared cache, no project oleans;
  - `lake build` exit 0; 8 axiom lines, all ⊆ {propext, Classical.choice, Quot.sound};
  - `shasum -c` of the published copies: OK; package revisions recorded in `replay.log` (Mathlib `0df444a3…`);
  - the build log's sha256 is also recorded in `replay.log`.

**Statement table (for the author; template 7.4).** A third-party statement review is still to do (playbook 3.3 item 10).

| Lean | 中文白话 | Paper / contract | Differences |
|---|---|---|---|
| `main_after_switching A hA k hk hn v w hw hprof θ x hx0 hx : ∃ z, (D*A*D) *ᵥ z = θ • z ∧ 1 ⬝ᵥ z ≠ 0`, with `D = diagonal (switchVec v)` | 设 A 是实对称矩阵，每行和都等于 k，顶点数不等于 2。假设顶点 v 的各长度闭途径数，都能写成全体顶点闭途径数的严格正加权平均（同一组权重对所有长度成立）。那么只切换 v 一个点之后，每个特征值都有一个特征向量，它和全 1 向量不正交，也就是说每个特征值都是 main。 | CONTRACT §5, Thm R. With A = A(G) for a connected k-regular G and n ≥ 3, this is exactly "all eigenvalues of G^{s_v} are main". | Lean is stated for any real symmetric matrix with constant row sums (stronger), and it needs no connectivity. "Eigenvalue" means a real θ with a nonzero real eigenvector, the right notion for symmetric A. |
| `walkRegular_main_after_switching … (hwr : ∀ j u u', (A^j) u u = (A^j) u' u') …` | 如果所有 A 的幂的对角线都是常数（walk-regular），那么切换任意一个点都行。 | Remark (c) | Special case w ≡ 1/n. |
| `annihilator … : aeval A f = 0` | 任何把 s_v 消成 0 的多项式都把整个 A 消成 0。 | Krylov form (N2) | Equivalent by §2 (K); the equivalence is proved in Lean through `eigen_nonorth`. |

## 2. Structural facts used everywhere (standard)

- (K) **Krylov criterion.** rank[s, As, …, A^{d−1}s] = #{θ : P_θ s ≠ 0}. So s is good iff the rank is d = n − deg gcd(φ, φ′), because a symmetric matrix has a squarefree minimal polynomial.
- (Gal) **Galois closure.** If s is rational, P_θ s = 0 ⇔ P_{σθ} s = 0. The conditions are one per irreducible factor of μ_A over ℚ.
- (Bip) **Bipartite symmetry.** P_{−θ} = D_b P_θ D_b. The good set is invariant under s ↦ −s and s ↦ b∘s.

## 3. Theorem C — exhaustive exact verification for trees

**Claim C1.** Every tree T with 3 ≤ n ≤ 24 vertices has a good switching. This covers 63,242,254 trees.

**Claim C2.** For 3 ≤ n ≤ 23, some U ⊆ V with min(|U|, n − |U|) ≤ 3 makes s = **1** − 2·**1**_U good. At n = 24 this fails for exactly 39 trees. They need 4 switched vertices, and 4 suffice; both facts are exact (§3.7).

### 3.1 Certificate
- d is computed exactly.
- The certificate is rank_{𝔽_p}[s, As, …, A^{d−1}s] = d. This suffices because rank_{𝔽_p} ≤ rank_ℚ ≤ d always.
- A failure of the modular test never produces a false positive; it only leads to trying another s.

### 3.2 Implementation B (`code/swtrees.c`, C)
- **Generation:** Wright–Richmond–Odlyzko–McKay level sequences (port of networkx 3.4 `nonisomorphic_trees`).
- **Characteristic polynomial:** exact int64 via the matching-number DP.
- **d:**
  - take the monic gcd of φ and φ′ mod a 61-bit prime and lift it symmetrically;
  - accept it only if it divides both φ and φ′ exactly over ℤ (`__int128`, with overflow guards);
  - then deg gcd_ℚ = deg of the lift, so d is exact. `gcdfail` was 0 for every n.
- **Search order:** s = 1, single flips, double, triple, then random and exhaustive.
- **Rank:** Krylov rank mod 2³¹ − 1.
- **Run:** `code/run_swtrees.sh`, 3 shards, logs `logs/swtrees_B_*.out`.

### 3.3 Implementation A (`code/swtrees_A.py`, Python) — independent in every component
- **Generation:** canonical augmentation (add a leaf everywhere, deduplicate by the AHU string at the centre or central edge).
- **φ:** rooted recursion in x.
- **d:** `sympy.gcd` over ℤ.
- **Certificate:** EXACT rank over ℚ by Bareiss fraction-free elimination on the integer Krylov matrix. A floating-point pre-screen only proposes candidates.
- **Logs:** `logs/swtrees_A.log` (n ≤ 20), `logs/swtrees_A_n21.log`, `logs/swtrees_A_n22_s*.log`.

### 3.4 Results

The tree counts equal OEIS A000055 for every n (checked by both generators where both ran).

| n | trees | B certified | s = 1 | 1 flip | 2 flips | 3 flips | B > 3 | A (exact over ℚ) |
|---|---|---|---|---|---|---|---|---|
| 3–12 | 1, 2, 3, 6, 11, 23, 47, 106, 235, 551 | all | | | | 0 | 0 | all certified |
| 13 | 1301 | 1301 | 429 | 712 | 159 | 1 | 0 | 1301 |
| 14 | 3159 | 3159 | 1171 | 1700 | 288 | 0 | 0 | 3159 |
| 15 | 7741 | 7741 | 2828 | 3993 | 917 | 3 | 0 | 7741 |
| 16 | 19320 | 19320 | 7470 | 9995 | 1846 | 9 | 0 | 19320 |
| 17 | 48629 | 48629 | 18996 | 24022 | 5570 | 41 | 0 | 48629 |
| 18 | 123867 | 123867 | 50191 | 61651 | 11943 | 82 | 0 | 123867 |
| 19 | 317955 | 317955 | 128894 | 154200 | 34548 | 313 | 0 | 317955 |
| 20 | 823065 | 823065 | 340200 | 403262 | 78908 | 695 | 0 | 823065 |
| 21 | 2144505 | 2144505 | 890865 | 1028544 | 222612 | 2484 | 0 | 2144505 |
| 22 | 5623756 | 5623756 | 2367395 | 2716575 | 534487 | 5299 | 0 | 5623756 (A′) |
| 23 | 14828074 | 14828074 | 6250904 | 7069902 | 1488515 | 18753 | 0 | — |
| 24 | 39299897 | 39299897 | 16708839 | 18850631 | 3697856 | 42532 | **39** | — |

How to read the columns:
- "k flips" is the first category in B's search order that produced a certificate. So "3 flips" counts trees for which B certified no s with ≤ 2 flips.
- That count is an upper bound on the trees that truly need 3, since the modular test is one-sided.
- The exact example of §3.6 shows that 3 is really needed.

### 3.5 Status of the second implementation
- A at n = 21 finished: all 2,144,505 trees certified by exact ℚ-rank (1305 s; `logs/swtrees_A_n21.log`).
- A′ at n = 22 finished: all 5,623,756 trees certified by exact ℚ-rank.
  - A′ uses the exact checker of A on trees from networkx's own WROM code, which is independent of the C port.
  - Enumeration count 5,623,756 = A000055(22).
  - 3 shards, about 1000 s each; `logs/swtrees_Anx_n22_s*.log`.
- n = 23 and 24 are covered by implementation B only.

Final numbers are appended in §7.

### 3.6 Sharpness, exact
- The tree has edges 0-1, 1-2, 2-3, 3-4, 0-5, 5-6, 6-7, 5-8, 0-9, 9-10, 9-11, 0-12 (n = 13).
- φ = x(x−1)(x+1)(x²−x−1)(x²+x−1)(x⁶−8x⁴+14x²−2), so d = 13.
- No U with |U| ≤ 2 (hence none with min(|U|, 13 − |U|) ≤ 2) is good.
- 28 sets U with |U| = 3 are good.
- Exact ℚ-rank; script `code/three_flips_needed.py`, log `logs/three_flips_needed.log`.

### 3.7 The minimum number of switched vertices: a new sequence
**Definition.**
- For a tree T on n ≥ 3 vertices, let τ(T) = min{ min(|U|, n − |U|) : U ⊆ V and s = **1** − 2·**1**_U is good }.
- Let a(n) = max over trees T with n vertices of τ(T).

**Result.**

| n | 3 | 4 | 5–12 | 13 | 14 | 15–23 | 24 |
|---|---|---|---|---|---|---|---|
| a(n) | 1 | 1 | 2 | **3** | **2** | 3 | **4** |

In full, n = 3..24: 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 3, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4.

**Proof of the values.**
- **Upper bounds.** B's exhaustive certified run: the largest category at each n is 1 flip (n ≤ 4), 2 flips (5 ≤ n ≤ 12 and n = 14), 3 flips (n = 13 and 15 ≤ n ≤ 23); see §3.4. A second, tier-recording run of implementation A for n ≤ 20 is in §7.
- **Lower bounds.** For each n = 3..23, the first tree in WROM order whose certified category is ≥ a(n) was re-checked **exactly**:
  - d by sympy gcd;
  - Bareiss ℚ-rank for every U with |U| < a(n): none is good;
  - an exact good U with |U| = a(n) is exhibited.
  - Script `code/lower_bounds.py`; witnesses (level sequences and edges) in `logs/lower_bounds.log`. Every line reads "PROVED".
  - **Second, independent criterion:** s is good ⇔ (μ/p)(A)s ≠ 0 for every irreducible factor p of μ. This uses sympy charpoly and factor, and integer Horner evaluation on the matrix; it shares no code with the Krylov/Bareiss path.
  - That criterion confirms every lower-bound witness n = 3..23 and all 13 exact n = 24 witnesses (`code/crosscheck_galois.py`, `logs/crosscheck_galois_all.log`).
  - It also reproduces the 13-vertex result: no good |U| ≤ 2, and 28 good 3-sets.
- **n = 24.**
  - B found 39 trees without a certified switching of ≤ 3 flips.
  - All 39 were printed by `code/swtrees_print.c` (3 shards; statistics identical to the original run) and checked exactly with `code/verify_hard24.py` (logs `logs/verify_hard24_*.log`).
  - Result: **none of the 39 has a good switching with min(|U|, n − |U|) ≤ 3, and each has a good 4-set.**
  - The independent Galois-factor criterion confirms "none with ≤ 3" for all 39 (`logs/crosscheck_galois_all.log`).
  - Every other tree on 24 vertices has a certified switching with ≤ 3 flips. Hence **a(24) = 4**, with the upper bound resting on implementation B.
  - All 39 have characteristic polynomial x²(x−1)(x+1)(x²−x−1)(x²+x−1)(x²−2)·q(x²) with an irreducible even factor q(x²) of degree 14. That means four "rigid" non-even orbits (x ± 1, x² ± x − 1), as Lemma G predicts.
- **OEIS.** The sequence 1,1,2,2,2,2,2,2,2,2,3,2,3,3,3 is not in the OEIS: a JSON search returned null, while a positive control returned results.

**Question (new).** Is a(n) bounded?
- The data show a(n) is not monotone (a(14) = 2 < a(13) = 3) and a(24) = 4.
- Heuristic: each independent rigid local structure forces its own switched vertex. Examples: pendant P₂ pairs (θ = ±1) and P₄-type branches (θ = ±φ^{±1}).
- This suggests a(n) → ∞ slowly. That is not proved.
- If true, it would not contradict the conjecture, but it would rule out every "switch at most c vertices" proof strategy for trees. Already proved: no strategy with c = 3 works.

## 4. Mathematics toward the tree case: what works, what fails

### 4.1 Failed route 1: naive leaf induction
**Leaf-addition lemma** (standard rank-one/pendant analysis; proof by Schur complement). Let T = T′ + leaf ℓ at u, s = (s′, t), h(x) = s′ᵀ(xI − A′)⁻¹e_u, g(x) = e_uᵀ(xI − A′)⁻¹e_u.

The key identity is R_T(x) = R_{T′}(x) + (t + h(x))²/(x − g(x)), where R(x) = sᵀ(xI − A)⁻¹s.

- (a) Let θ ∉ spec T′ be an eigenvalue of T. Then θ is simple, and it is s-main ⇔ t ≠ −h(θ).
- (b) Let θ ∈ spec T′ with (P′_θ)_{uu} = 0. If θ is s′-main in T′, it is s-main in T, for either t.
- (c) Let θ ∈ spec T′ with (P′_θ)_{uu} > 0. Then m_T(θ) = m_{T′}(θ) − 1, and θ is s-main ⇔ P′_θ s′ ∉ span(P′_θ e_u). This holds for every t, and it can fail even when s′ is good.

**Test** (`code/explore2.py`, floating point, diagnostic):
- For each tree we asked whether some leaf ℓ exists such that *every* good switching of T − ℓ extends.
- Trees with such a leaf: n = 6: 5/6; n = 9: 40/47; n = 11: 209/235; n = 12: 528/551.
- So a strengthened induction hypothesis is required; plain "good ⇒ good" fails.

### 4.2 Failed route 2: Combinatorial Nullstellensatz, top-degree coefficient
- The scout found this criterion fails on 21 of the 106 trees with n = 10.
- One mechanism behind the cancellation: for an eigenvector x_θ = (u, w) with θ ≠ 0 we have ‖u‖ = ‖w‖. Hence the ±θ factor (s·x_θ)(s·x_{−θ}) = (s_X·u)² − (s_Y·w)² has zero constant term after multilinear reduction (s_i² = 1).
- A Galois-grouped variant (one factor per irreducible factor) was not tested.
- Lemma G below separates the orbits where the ±θ conditions merge (even minimal polynomial) from those where they stay independent.

### 4.3 Lemma G (bipartite Galois pairing) — proved
**Lemma G.**
- Setting: G is bipartite with parts X, Y and A = [[0, B], [Bᵀ, 0]]. Let θ ≠ 0 be an eigenvalue whose minimal polynomial over ℚ is **even**, i.e. −θ is a Galois conjugate of θ. Put t = θ², U_t = ker(BBᵀ − t) ⊆ ℝ^X and W_t = ker(BᵀB − t) = BᵀU_t.
- Claim: for every rational s = (s_X, s_Y),

  P_θ s = 0 ⇔ P_{−θ} s = 0 ⇔ (s_X ⊥ U_t and s_Y ⊥ W_t).

**Proof.**
1. E_θ = {(u, Bᵀu/θ) : u ∈ U_t}, and U_t has a basis in ℚ(t)^X.
2. For such u, s·(u, Bᵀu/θ) = a + θb, where a = s_X·u ∈ ℚ(t) and b = s_Y·Bᵀu/t ∈ ℚ(t).
3. The minimal polynomial is even, so it equals g(x²) with g irreducible. Hence [ℚ(θ) : ℚ(t)] = 2 and θ ∉ ℚ(t).
4. Therefore a + θb = 0 ⇔ a = b = 0. The same computation with −θ gives the same condition. ∎

**Consequence.**
- For "even" orbits, the two conditions for ±θ merge into the single weak condition s ⊥̸ E_θ ⊕ E_{−θ}, which is the t-eigenspace of A².
- All the rigidity comes from **non-even** pairs, i.e. θ ∈ ℚ(θ²). Examples: integer eigenvalues, and pairs like x² ± x − 1 (golden ratio, from P₄).
- The sharp 13-vertex example has exactly such factors: x ± 1 and x² ± x − 1.
- **Sanity check** (float, diagnostic): all trees 4 ≤ n ≤ 12 with 30 random s each gave 121,980 tests, with 0 violations on even factors. On non-even factors, P_θ s = 0 without P_{−θ} s = 0 happened 4,027 times, so the hypothesis is needed. Script `code/check_lemmaG.py`, log `logs/check_lemmaG.log`.

### 4.4 Failed route 3: union bound over Galois orbits
- The bound Σ_p 2^{−dim W_p} < 1 fails whenever there are ≥ 2 rational simple eigenvalues.
- A Littlewood–Offord refinement fails on small-support eigenvectors, such as pendant P₂ pairs with θ = ±1, which have support 4.

### 4.5 Where a proof might come from (not carried out)
- Reduce with Lemma G, so that only non-even pairs are rigid.
- Prove a strengthened leaf/pendant-path induction hypothesis that controls the rational-function values h(θ) at the non-even eigenvalues.
- Families where this looks feasible with explicit spectra, not done in the time box: trees of diameter ≤ 4 (they generalize stars, double stars and harmonic trees; §4.6 has partial notes) and spiders.

### 4.6 Partial notes on trees of diameter ≤ 4 (no claim)
Set-up: center c; v_i has a_i leaves; t = θ².
- Secular eigenvalues: t solves Σ_i 1/(t − a_i) = 1; they are simple.
- Leaf-group eigenvalues: θ = ±√b with multiplicity (#{i : a_i = b}) − 1.
- The eigenvalue 0 has an explicit kernel.
- With s_{v_i} = 1 for all i, a secular θ is good unless P(t)² = t, where P(t) = s_c + Σ_i λ_i/(t − a_i) and λ_i is the sum of the leaf signs at v_i.
- By Lemma G this can only fail when √t ∈ ℚ(t). Example: a = (1, 1, 1), t = 4, θ = ±2 with all signs +1.
- A full case analysis was not completed.

### 4.7 A trivial but clean special case
**Single-orbit remark.** Suppose φ_T(x) = x^m g(x²) and g(x²) is irreducible over ℚ. Then T satisfies the conjecture.

Proof.
1. All nonzero eigenvalues form one Galois orbit. By (Gal), P_θ s ≠ 0 for one of them iff P_{range A} s ≠ 0, i.e. iff As ≠ 0.
2. As ≠ 0 holds for **every** s ∈ {±1}^n, because a leaf ℓ with neighbour u gives (As)_ℓ = s_u = ±1.
3. If m ≥ 1, choose s = sign(z) for some 0 ≠ z ∈ ker A. Then s·z = ‖z‖₁ > 0, so P_0 s ≠ 0. ∎

The same leaf argument shows that, for any tree, the nonzero spectrum can never be non-main *as a whole*.

## 5. Regular graphs: evidence (exact certificates, `code/swgraph.py`, `code/regfamilies.py`)

355 connected regular graphs were tested:
- 142 generalized Petersen graphs GP(n, k), 5 ≤ n ≤ 25;
- 14 rings of diamonds (cubic, not walk-regular), m = 2..15, i.e. n ≤ 60;
- truncations of 7 cubic graphs;
- 192 random regular graphs (degrees 3–5, n ≤ 40).

All have a certified good switching: 350 with s = 1 or a single flip, 4 with two flips, 1 with three (a random 5-regular graph on 10 vertices). Logs: `logs/reg_families.log`, `logs/reg_diamond.log`.

Some small non-walk-regular graphs with d = 6 have **no good single flip**, verified exactly (sympy gcd for d, Bareiss ℚ-rank):
- a cubic graph on 8 vertices, where the 2-set {0, 4} works;
- a 4-regular graph on 12 vertices, where the 2-set {0, 1} works.

Edges and characteristic polynomials are in `logs/regular_no_single_flip.log`. So Thm R's single-vertex method cannot settle (R) by itself.

## 6. What is new, what is known

**Known** (see CONTRACT §4):
- the conjecture for Cayley, distance-regular, vertex- and edge-transitive graphs, paths, stars, double stars, harmonic trees, complete multipartite graphs, S_{n,r}, Wenger graphs, and all connected graphs with n ≤ 9;
- the net-regular criterion (Stanić Cor 4.6);
- the asymptotic results of 2609.27046.

**New here:**
1. Thm R in convex-hull form (★), with a Lean proof. Its walk-regular special case is known in effect.
2. Cor R1 (≤ 4 distinct eigenvalues) as an explicit statement.
3. Thm C: all trees with n ≤ 24, exact.
4. The sequence a(n) (§3.7): exact for n ≤ 24, with a(24) = 4. It rules out any proof for trees that switches at most 3 vertices; whether a(n) is bounded is open.
5. Lemma G and the diagnosis of which eigenvalue pairs are rigid.
6. Regular-graph evidence on families that are not walk-regular, including exactly verified graphs where no single flip works.

Items 1–2 are minor. Items 3–4 are solid computational contributions. Item 5 is a useful structural remark. **The Problem itself is not solved.**

## 6b. Suggested minimal cross-model review (for the main agent to decide)
1. Lemma G (§4.3): the step θ ∉ ℚ(θ²) ⇔ the minimal polynomial is even.
2. `swtrees.c`: certified gcd lift (divisibility check over ℤ ⇒ exact d), and the one-sided rank certificate.
3. Lean statement faithfulness (statement table in §1).

## 7. Final numbers (appended at the end of the session)

**Implementation B (C)** covers n ≤ 24:
- all 63,242,254 trees certified, 0 failures, `gcdfail` = 0;
- the enumeration counts equal A000055;
- per-n table in §3.4, logs `logs/swtrees_B*.out`.

**Second implementation** (A, A′):
- n ≤ 20: `logs/swtrees_A.log`.
- n = 21: `logs/swtrees_A_n21.log`, 2,144,505 trees certified exactly.
- n = 22: A′, `logs/swtrees_Anx_n22_s*.log`, 5,623,756 trees certified exactly.
- In total every tree with n ≤ 22 is confirmed by exact ℚ-rank, with a generator independent of B's C port.

**Tier-recording A** (`code/swtrees_A_tiers.py`, fast mode = certified upper bounds; `logs/swtrees_A_tiers_fast.log`):
- For every n ≤ 20, every tree has an exactly certified switching with ≤ 3 flips.
- The largest tier per n agrees with B: 1 (n ≤ 4); 2 (5 ≤ n ≤ 12 and n = 14); 3 (n = 13 and 15 ≤ n ≤ 20).
- The number of trees needing 3 flips agrees with B for every n ≤ 20: 1, 0, 3, 9, 41, 82, 313, 695.

**a(n).**
- Exact for 3 ≤ n ≤ 20: lower bounds double-checked (Bareiss and the Galois-factor criterion); upper bounds double-checked (B and A).
- Exact for 21 ≤ n ≤ 23: lower bounds double-checked; upper bounds from B only.
- n = 24: a(24) = 4. All 39 exceptional trees were checked exactly: no switching with ≤ 3 flips (two criteria), and a 4-set works (Bareiss). The other 39,299,858 trees have certified ≤ 3-flip switchings (B only).

**Regular graphs.**
- 355 family graphs, all certified.
- 2 exactly verified graphs where single flips fail and 2 flips work.

**Lean.**
- Build and clean replay OK (§1).

## 8. Recommendation (session 1; superseded for trees of diameter ≤ 4 by §9.13)

1. **Not a solution.** The Problem (trees; connected regular graphs) is not solved, so there is nothing to claim as "the switching conjecture holds for trees/regular graphs".
2. **What could be published now, with modest value:** a short computational note.
   - (a) Exhaustive exact verification for all 63,242,254 trees with n ≤ 24. Two independent implementations for n ≤ 22.
   - (b) The new sequence a(n) (§3.7), exact for 3 ≤ n ≤ 24: 1,1,2,2,2,2,2,2,2,2,3,2,3,3,3,3,3,3,3,3,3,4. It shows that small switchings do not suffice. It is also a natural **OEIS candidate**, but that is an external action for the user to decide.
   - (c) Lemma G, the structural reason why the rigid eigenvalues are the rational and golden-ratio-type pairs.
   - (d) Theorem R with its Lean proof, stating clearly that the walk-regular case follows from Stanić 2020 Cor. 4.6.
3. **Better use of one more session:** try to prove the Problem for **trees of diameter ≤ 4**, using Lemma G and the explicit secular equation (§4.6).
   - This class contains all known tree cases (stars, double stars, harmonic trees) except paths.
   - A proof there, plus the data above, would make a solid short paper.
   - Estimated chance of success in one day: about 0.3.
4. **Regular graphs:** no realistic route to the general case was found. Theorem R covers only graphs with a "central" vertex, and some 8- and 12-vertex regular graphs need two switched vertices.

## 9. Session 2 (2026-09-26 21:35–22:35 UTC): trees of diameter ≤ 4

Files: `diam4/code/`, `diam4/logs/`, `diam4/g1/`. Queries are appended to `querylog.tsv`.

### 9.0 Result in one paragraph (updated in session 3, 2026-09-26 22:37–00:19 UTC (27 Sep))

**Final result (session 3, §9.22).** **Theorem 9.22.** Every tree of diameter ≤ 4 other than K₂ has a switching s such that every distinct eigenvalue of T^s is main.
- If the largest branch has b* ≥ 13 leaves, the leaf-row family of that branch (2b* − 2 or more explicit switchings) contains a good one. This is a short hand proof (Theorem 9.22.2).
- If 2 ≤ b* ≤ 12, the refined Row criteria (a′), (b′) apply, except on an explicit finite set of 13,376 trees. An exact search of that set, done by two independent implementations, leaves only T(2,2), D(2,2) and K₁,₄, each with an explicit switching.
- If every branch has at most one leaf, the families of §9.7 and the Main Theorem apply.
- The key new facts are:
  - an irrational non-even pair spoils at most 2 members of a row, not 4;
  - integer non-even pairs come from perfect squares below b*, so there are at most ⌊√(b* − 1)⌋ + 1 of them.

The intermediate results of session 3 (Theorem D and Corollary D′, below) remain true, but the final theorem no longer needs them.

**Intermediate results (session 3, before §9.22).**

Let T be a tree of diameter ≤ 4 with n ≥ 3 vertices. Let N be its number of **non-even secular pairs** (§9.3).

**Theorem D (proved; explicit switchings).** T has a switching making every distinct eigenvalue main in each of these cases:
- (i) N ≤ 1 (Main Theorem, §9.8);
- (ii) every branch has at most one leaf (families of §9.7, any N);
- (iii) T has a branch with ≥ 2 leaves and satisfies Row criterion (a) or (b) of §9.15 (any N).

**Corollary D′ (every tree with N ≤ 4).** Every tree of diameter ≤ 4 with at most four non-even secular pairs has a good switching.
- If (i)–(iii) all fail, then N ≥ 2 and the tree lies in an explicit finite region (§9.16).
- The region was searched exactly for N = 2, 3, 4.
  - N = 2 (799 trees): only D(2,2) = T(2,0,0) and T(3,1,1,1,1,0,0,0). Both have explicit good switchings, each verified by two independent exact criteria.
  - N = 3 (12,841 trees) and N = 4 (212,231 trees, n ≤ 105): nothing.
- This finite search is a computer-assisted step: finite and reproducible, not a hand proof.

**Census.** Every one of the 376,324 trees with n ≤ 44 has N ≤ 3. The distribution is {0: 373,837; 1: 2,442; 2: 44; 3: 1}, and the only tree with N = 3 is T(12,12,8,0⁶), which is covered by (a). So **every tree of diameter ≤ 4 with n ≤ 44 is covered by Theorem D / Corollary D′**, independently of the direct certificates of §9.10.

**Not proved by Theorem D / D′ alone.** Trees with N ≥ 5 that fail both crude Row criteria. This gap is closed by §9.22, so no tree of diameter ≤ 4 is uncovered.

### 9.1 Setting

Trees of diameter ≤ 4 with n ≥ 3 are exactly the trees of radius ≤ 2, i.e. the rooted trees T(a) of height ≤ 2 (take c = a centre):
- a centre c with children v₁, …, v_k (k ≥ 1);
- v_i has a_i ≥ 0 leaf children (the set L_i);
- the distinct values of the a_i form the set B, and value b occurs k_b times (index set I_b);
- "bare" branches are those with a_i = 0.

n = 1 + k + Σa_i. For a switching s write:
- s_c = s(c), σ_i = s(v_i);
- λ_i = Σ_{ℓ∈L_i} s(ℓ), the leaf sum of branch i.

### 9.2 Lemma S (spectrum of T(a); standard, proof by solving Ax = θx)

Let F(t) = Σ_{b∈B} k_b/(t − b) and R(t) = ∏_{b∈B}(t − b)·(1 − F(t)). Then R ∈ ℤ[t] is monic of degree r = |B|, and R(b) = −k_b∏_{b'≠b}(b − b') ≠ 0.

- **(i) Secular eigenvalues.** R has r simple real roots t₁ < … < t_r with b_j < t_j < b_{j+1} and t_r > b_r (so all t_j > 0).
  - Each gives two simple eigenvalues θ = ±√t_j.
  - Eigenvector: x_c = 1, x_{v_i} = θ/(t − a_i), x_ℓ = 1/(t − a_i) for ℓ ∈ L_i.
- **(ii) Leaf-group eigenvalues.** For b ∈ B with b ≥ 1 and k_b ≥ 2: θ = ±√b with multiplicity k_b − 1.
  - Eigenspace: {x_c = 0, x_{v_i} = α_i (i ∈ I_b), x_ℓ = α_i/θ (ℓ ∈ L_i), Σα_i = 0, zero elsewhere}.
- **(iii) θ = 0.**
  - If k₀ ≥ 1: the kernel is ⊕_{a_i≥1}{vectors on L_i with sum 0} ⊕ {vectors on the bare v_i with sum 0}.
  - If k₀ = 0: the kernel is {x_c = γ, x_v = 0, Σ_{L_i}x = −γ}.
- **Completeness.** The dimensions add up to n.
- **Consequence.** The number of distinct eigenvalues is d = 2r + 2·#{b ≥ 1 : k_b ≥ 2} + [kernel ≠ 0]. This formula was cross-checked against sympy (d = n − deg gcd(φ, φ′)) for all 23,023 trees with n ≤ 30: 0 mismatches (`diam4/logs/verify_diam4_*`).

Proof sketch:
1. For θ ≠ 0, the leaf equations give x_ℓ = x_{v_i}/θ, and then x_{v_i}(θ² − a_i) = θx_c.
2. If x_c ≠ 0, the centre equation becomes F(θ²) = 1: case (i).
3. If x_c = 0, then x_{v_i} = 0 unless a_i = θ², and Σx_{v_i} = 0: case (ii).
4. θ = 0 is direct.
5. Secular roots are never poles, so (i) and (ii) do not overlap. ∎

### 9.3 Lemma M (when is each eigenvalue main) and the reduced form

- **(S)** A secular θ is main iff G(θ) := s_c + Σ_i (σ_iθ + λ_i)/(t − a_i) ≠ 0, with t = θ².
  - Since F(t) = 1 at a secular root, **G(θ) = Σ_{b∈B}(A_b + S_bθ)/(t − b)**, where A_b = Σ_{i∈I_b}(s_c + λ_i) and S_b = Σ_{i∈I_b}σ_i.
- **(L)** θ = ±√b (k_b ≥ 2) is main iff the vector (σ_i + λ_i/θ)_{i∈I_b} is not constant.
- **(Z)** 0 is main iff:
  - when k₀ ≥ 1: some branch with a_i ≥ 2 has non-constant leaf signs, or σ is not constant on the bare branches;
  - when k₀ = 0: some leaf group is non-constant, or s_c ≠ Σ_i ε_i, where ε_i is the common sign of L_i.

**Lemma C (Galois).**
- The secular θ are exactly the roots of R(x²) ∈ ℤ[x]. So their set is stable under Galois conjugation, and all conjugates are real secular eigenvalues.
- A **non-even pair** is a pair of irreducible factors g(x), g(−x) ≠ ±g(x) of R(x²). Equivalently, θ ∈ ℚ(θ²).

**Corollary (Lemma G, §4.3).** If σ_i = +1 for every i, then S_b = k_b, so Σ_b S_b/(t − b) = 1. Hence G(θ) = θ + P(t) with P(t) = Σ_b A_b/(t − b) ∈ ℚ(t).
- If θ has an even minimal polynomial, θ ∉ ℚ(t), so G(θ) ≠ 0. **Every even secular orbit is automatically main.**
- For a non-even orbit, G vanishes on θ or on −θ iff **P(t)² = t**.

### 9.4 The base switchings s⁺ and s⁻

- s_c = ±1, and σ_i = +1 for every branch, bare ones included.
- Leaf sums λ (branch i has (a_i − λ_i)/2 leaves of sign −1):
  - odd b ≥ 3: λ = −1 on every branch, except that for k_b ≥ 2 the first two branches get +1 and −3;
  - b = 1: λ = −1, except that for k₁ ≥ 2 the first branch gets +1;
  - even b ≥ 2: λ = 0, −2, 0, −2, … alternately.
- For s⁺ this gives:
  - A₀ = k₀;
  - A₁ = 2 if k₁ ≥ 2, else 0;
  - A_b = 0 for odd b ≥ 3;
  - A_b = 1 or 0 for even b ≥ 2, according as k_b is odd or even.
- At every secular root, **P⁻ = P⁺ − 2**, because A_b changes by −2k_b and F = 1.
- (L) holds: every group of size ≥ 2 has non-constant λ.
- (Z) holds for s⁺ and s⁻ whenever some a_i ≥ 2 (a non-constant leaf branch exists), or k₀ = 1 and all a_i ≤ 1 (the kernel is 0).
- The remaining shapes are:
  - k₀ ≥ 2 with all a_i ≤ 1 (§9.7);
  - the spiders T(1^{k₁}), where s⁺ satisfies (Z) and s⁻ may not. These are in class D1 (§9.9), where s⁺ is proved good.

### 9.5 Theorem E (no non-even pair)

If R(x²) has no non-even factor, then s⁺ is good (outside §9.7). This is immediate from the Corollary: every secular orbit is even, and (L), (Z) hold. ∎

### 9.6 Theorems F and F2 (exactly one non-even pair)

**Theorem F.** Suppose there is exactly one non-even pair and it is not {x − 1, x + 1}. Then s⁺ or s⁻ is good (outside §9.7).

Proof.
1. Even orbits, (L) and (Z) are fine for both switchings.
2. Suppose both switchings fail on the pair. By Galois equivariance, the failures can be read at one and the same t.
3. So P⁺(t) ∈ {θ, −θ} and P⁺(t) − 2 ∈ {θ, −θ}. Since θ ≠ 0, this forces θ = ±1. ∎

**Theorem F2.** Suppose the unique non-even pair is {x ± 1}, so t = 1 is secular and hence k₁ = 0, and suppose some a_i ≥ 3. Then a good switching exists.

Proof.
1. At θ = ±1, s⁺ fails iff P⁺(1) ∈ {±1}, and s⁻ fails iff P⁺(1) ∈ {1, 3}. So both fail only when P⁺(1) = 1.
2. In that case, raise the leaf sum of one branch of the largest group b* ≥ 3 by 2. For odd b*, change −1 to +1 (or −3 to −1); for even b*, change 0 to 2.
3. (L) still holds. The changed branch has |λ| < b*, so it is non-constant and (Z) still holds.
4. P⁺(1) becomes 1 − 2/(b* − 1), which is not in {±1, 3} because b* ≥ 3. So the adjusted s⁺ is good. ∎

If instead all a_i ≤ 2 and the pair {x ± 1} occurs, then B ⊆ {0, 2} and F(1) = 1 forces k₀ = k₂ + 1. That is family B(m) of §9.7, or D(2,2) when m = 1.

### 9.7 Explicit families (any number of non-even pairs)

Every case below is proved exactly.

- **Stars T(0^{k₀}), k₀ ≥ 2.**
  - Switching: s_c = +1; one bare leaf −1; for k₀ = 4, two bare leaves −1.
  - The only secular t is k₀, and G(θ) = 1 + E/θ with E the sum of the bare-leaf signs.
  - G = 0 would need E² = k₀; with E = k₀ − 2 this happens only for k₀ ∈ {1, 4}, and for k₀ = 4 we use E = 0.
- **T(1, 0^{k₀}), k₀ ≥ 2.**
  - Switching: s_c = +1, one bare leaf −1, σ = +1, far leaf −1.
  - The failure resultant is Res = −k₀²(k₀ − 1)² ≠ 0 (`diam4/logs/family_small.log`).
- **Family A: T(1^{k₁}, 0^{k₀}), k₀, k₁ ≥ 2** (centre with k₀ pendant vertices and k₁ pendant P₂'s).
  - Switching: s_c = +1, one bare leaf −1, σ ≡ +1, one far leaf −1.
  - With the secular equation t² − (1 + k₀ + k₁)t + k₀ = 0 this gives G = P + θQ, where P = (t + k₁ − 3)/(t − 1) and Q = (t − 2)/t.
  - A secular failure means t(t + k₁ − 3)² = (t − 2)²(t − 1)². The roots satisfy t₁ ∈ (0, 1) and t₂ ∈ (k₀ + k₁, k₀ + k₁ + 1).
  - At t₂ there is no failure once k₀ + k₁ ≥ 9 (elementary inequality; §9.7 notes in `familyA.py`).
  - At t₁ there is never a failure for k₁ = 2. For k₁ ≥ 10 there is none, since √t₁(k₁ − 3) > 2 > (2 − t₁)(1 − t₁). There is none for 4 ≤ k₁ ≤ 9 with k₀ ≥ 40, and none for k₁ = 3 with k₀ ≥ 46.
  - The finite remainder lies in [2, 400)², where the exact resultant Res_t(failure, secular) ∈ ℤ[k₀, k₁] has no integer zero (`diam4/code/familyA.py`, `logs/familyA.log`).
  - (Z) holds because the bare-leaf signs are non-constant. (L₁) holds because the far-leaf signs are non-constant.
- **Family B(m): T(2^m, 0^{m+1}), m ≥ 2.**
  - Switching: s_c = +1, all bare leaves +1, σ ≡ +1; the first 2-branch has leaves (−,−), all other 2-branches have leaves (+,−).
  - The secular roots are t = 1 and t = 2m + 2.
  - G(±1) ∈ {2, 4}.
  - At t = 2m + 2, G = (1 − 1/m) + θ ≠ 0, because θ is an algebraic integer and (m − 1)/m is not.
  - (Z) holds via the (+,−) branches. (L₂) holds because λ = (−2, 0, …).
- **D(2,2) = T(2,0,0).** Switching (c; two bare leaves; v; its two leaves) = (+; +,+; −; +,−). Certified exactly (`diam4`, exhaustive search at n = 6).

### 9.8 Proof of the Main Theorem

1. If k₀ ≥ 2 and all a_i ≤ 1, T is a star, a T(1,0^{k₀}) or in family A: §9.7.
2. Otherwise (L) and (Z) hold for s⁺. They hold for s⁻ too, except on spiders, which are D1 and handled by s⁺.
3. With 0 non-even pairs, use Theorem E. With 1 pair other than ±1, use F.
4. With the pair ±1: use F2 if some a_i ≥ 3; otherwise T is family B or D(2,2) (§9.7). ∎

### 9.9 Structural classes (proved; they also contain some trees with several non-even pairs)

Each uses the reduced form and the fact that every conjugate of a secular θ is real and secular (Lemma C).

- **D1.** No bare leaves, and every even value b ≥ 2 occurs an even number of times.
  - s⁺ gives G = θ, or θ + 2/(t − 1) when k₁ ≥ 2.
  - A failure forces θ³ − θ + 2 = 0. That cubic is irreducible with only one real root, so it cannot contain a secular orbit.
- **D1+.** No bare leaves, exactly one even value b* with odd multiplicity, and k₁ ≤ 1.
  - G = θ + 1/(t − b*), and a failure forces θ³ − b*θ + 1 = 0.
  - For b* ≥ 4 this cubic is irreducible with a root in (0, 1). For b* = 2 it equals (x − 1)(x² + x − 1).
  - Either way the orbit contains an element with |θ| ≤ 1, but without bare leaves every secular t > 1.
- **D2.** Every odd value occurs an even number of times, t = 1 is not secular, T ≠ K₁,₄, and T is not T(2,2,1^{2j},0^{k₀}) with k₀ ≥ 1.
  - The "Target II" switching (leaf-sum average 0 in every group) gives G = θ + 1.
- **D3.** Bare leaves with k₀ not a perfect cube (or k₀ = m³ with m² not secular), no even value of odd multiplicity, k₁ ≤ 1, and some a_i ≥ 2.
  - G = θ + k₀/θ², and a failure forces θ³ = −k₀. For non-cube k₀ that cubic is irreducible and not totally real.
- Exact consistency check: 0 construction failures on their classes for n ≤ 28 (`diam4/code/theorems_check.py`).

### 9.10 Computation

**Exhaustive verification.** `diam4/code/verify_diam4.py`, logs `diam4/logs/verify_diam4_*.log`.
- Scope: all multisets a with 3 ≤ n ≤ 44, i.e. 376,324 rooted trees of height ≤ 2, which contain every tree of diameter ≤ 4 with n ≤ 44.
- Certificate: rank_{𝔽_p}[s, As, …, A^{d−1}s] = d with p = 2⁶¹ − 1 and d from Lemma S. Since rank_{𝔽_p} ≤ rank_ℚ ≤ d, this is a sound certificate. d was cross-checked by sympy for n ≤ 30.
- Result: 0 failures.
- An **empirical rule** (`rules.py`, rule R_A: the s⁺ above, with one bare-leaf sign flipped when all a_i ≤ 1 and k₀ ≥ 2), or the same rule with the centre flipped, works for every tree with n ≤ 44 except K₁,₄ and D(2,2). For n = 17..44 the counts are 375,544 by R_A and 98 by the centre-flipped R_A.

**Independent checks.**
- d-formula against sympy: 0 mismatches for n ≤ 30.
- Main-Theorem constructions (§9.4–9.8), tested exactly with the Bareiss ℚ-rank for n ≤ 30: 0 failures; 16 trees with ≥ 2 pairs not claimed (`main_theorem_check_3-30.log`).
- Classes D1–D3 for n ≤ 28 (`theorems_check.py`).
- Family resultants: `familyA.log`, `family_small.log`.

**How common are non-even pairs** (`count_noneven.py`, n ≤ 26): 9,028 trees have none, 256 have exactly one, and 10 have two. Non-even factors occur in degrees 1–4.

**Residue not covered by any proof, n ≤ 30** (`coverage2_3-30.log`): T(3,1,1,1,1,0,0,0), T(6,3,2,0⁹), T(8,8,1,1,1,0,0), T(8,5,2,2,0⁵), T(6,4,3,2,1,1,1,1). Each has exactly two non-even pairs, and each is certified by the computation.

### 9.11 What would finish the last case (session-2 sketch; superseded by §9.15–9.18)

Consider the options s^± and s^±_b, where s^±_b means "raise one branch of an adjustable group b by 2". A non-even pair (θ, −θ) with θ ≠ ±1:
- kills at most one option of each sign pair;
- kills options in two different classes only if t − b ∈ {±1, ±1/θ, ±1/(1 ± θ)}.

With two adjustable groups b ≠ b′ this forces b′ − b to be a difference of two such numbers. That confines θ to a short explicit list: small integers, and roots of x² ± x − 1, x² ± 3x + 1 and x² ± 2x − 1.

So two non-even pairs can kill all options only in finitely many arithmetic configurations. Checking them, and handling trees with at most one adjustable group, would complete the proof. This is the natural next step (estimate 2–4 hours).

### 9.12 G1 for this subclass (2026-09-26 21:35–22:01 UTC; details in `querylog.tsv` and `diam4/g1/`)

- **Nobody** has proved or claimed the conjecture for trees of diameter ≤ 4, or for any class containing them.
- Previously settled tree cases: stars, double stars (= diameter 3) and paths (2021 paper, abstract); harmonic trees (Shao–Yuan 2022, Prop. 2.1); every graph with n ≤ 9.
- A web-search false positive ("proved for all trees of diameter 4") traces to a Laplacian-energy thesis, arXiv:2107.09161.
- Related unsigned work: França–Brondani–Jaume, DAM 2026, on diameter-4 trees with exactly 3 main eigenvalues (abstract only). It may be the right reference for the equitable-partition viewpoint of Lemma S.
- trureturing, MathDB #350999 (still open, 0 solutions), GitHub and SCOPE2026: no hits.
- The 2021 full text is still inaccessible (bot checks; not bypassed).

### 9.13 New vs known, and recommendation

**New:**
- the Main Theorem (≤ 1 non-even pair), the explicit families A and B, and the classes D1–D3;
- the method: the reduced form, Lemma G for even orbits, and the total-reality and cubic arguments for non-even orbits;
- the exhaustive verification to n = 44;
- the empirical two-option rule.

**Known:** stars, double stars, paths and harmonic trees; the method of Lemma S (standard equitable-partition spectrum).

**Recommendation (session 2; superseded by §9.20).** A short note, "The switching conjecture for main eigenvalues holds for trees of diameter at most 4 (with one arithmetic exception class)", is realistic *after* one more session to close §9.11. Then it would be a complete theorem: every tree of diameter ≤ 4 except K₂. Publishing now is premature:
- the residue is small but real;
- only one algebraic step is formalized in Lean (§9.14): no eigenvalue of a real symmetric rational matrix is a root of X³ − X + 2. The spectrum lemma and the case analysis are not.

### 9.14 Lean (session 2)

Files: `work/research-lean/Research/SwitchingDiam4Cubic.lean` and `SwitchingDiam4CubicAudit.lean`; copies in `lean/`, sha256 in `lean/SHA256SUMS`.

**Main statement.** `SwitchingDiam4.no_eigenvalue_root_cubic`: for A : Matrix n n ℚ with Aᵀ = A and θ : ℝ with `((A.map (algebraMap ℚ ℝ)).charpoly).eval θ = 0`, we have θ³ − θ + 2 ≠ 0.

**Proof in Lean:**
1. X³ − X + 2 has no rational root, by the integral root theorem and an integer check. Hence it is irreducible over ℚ.
2. It is therefore the minimal polynomial of θ, so it divides charpoly(A).
3. The mapped charpoly splits over ℝ (Hermitian). So the cubic would have 3 real roots.
4. It has at most one real root, so all three roots equal θ. The sum of the roots is 0, so θ = 0, a contradiction.

**Checks:**
- `lake build Research.SwitchingDiam4Cubic Research.SwitchingDiam4CubicAudit` exited 0 at 22:31 UTC (`diam4/logs/lake_build_SwitchingDiam4Cubic.log`).
- 6 `#print axioms` lines, all ⊆ {propext, Classical.choice, Quot.sound}.
- Forbidden-token grep empty.
- Clean-directory replay 22:31:54–22:32:09 UTC, exit 0 (`lean/replay-cubic-*/replay.log`).
- Lock B was taken only for each short build and released.
- `Research.lean` was not edited.

**Scope.** This formalizes only the algebraic step behind class D1 (the case with k₁ ≥ 2). Not formalized: the spectrum lemma, the reduced form, the case split, and the families.

### 9.15 Session 3: the Row Lemmas (proved; any number of non-even pairs)

Notation as in §9.1–9.4. The **base switching** is the leaf pattern of s⁺ (§9.4; code `construction_I`).
- For every group b ≥ 1 with k_b ≥ 2 the leaf sums λ_i are not all equal.
- Whenever some a_i ≥ 2, some branch of size ≥ 2 has non-constant leaf signs: an odd b ≥ 3 group has a branch with λ = ±1, and an even b ≥ 2 group has a branch with λ = 0.

Let U_β(t) = Σ_{b ≥ 1, b ≠ β} Λ_b/(t − b) and U(t) = Σ_{b ≥ 1} Λ_b/(t − b), where Λ_b are the base leaf-sum totals. These are fixed rational functions.

**Lemma 9.15.1 (realizability).** Let β ≥ 2, k ≥ 1, and Λ ≡ kβ (mod 2) with |Λ| ≤ kβ − 2 and (β, k, Λ) ≠ (2, 2, 0). Then there are leaf sums λ₁..λ_k ∈ {−β, −β+2, …, β} with:
- Σλ_i = Λ;
- the λ_i not all equal when k ≥ 2;
- some |λ_i| < β (a branch with non-constant leaf signs).

The same holds for β = 1 with λ_i ∈ {±1} and |Λ| ≤ k − 2 when k ≥ 2 (then the λ_i are automatically not all equal), and with Λ = ±1 when k = 1. The set of such Λ is written 𝓛_β:
- |𝓛_β| = kβ − 1 − [β = k = 2] for β ≥ 2;
- |𝓛_1| = k₁ − 1 if k₁ ≥ 2, and 2 if k₁ = 1.

*Proof.* Put M = (kβ − Λ)/2, the number of leaves of sign −1; then 1 ≤ M ≤ kβ − 1. For k = 1 take λ₁ = Λ, which has |Λ| ≤ β − 2.

For k ≥ 2, distribute M as evenly as possible (m_i ∈ {⌊M/k⌋, ⌈M/k⌉}, λ_i = β − 2m_i). If k ∤ M, the λ_i are not all equal.
- If M = kq, then 1 ≤ q ≤ β − 1; use (q + 1, q − 1, q, …, q) instead.
- A value m_i with 0 < m_i < β exists in every case except k = 2, M = 2, β = 2, i.e. (β, k, Λ) = (2, 2, 0). ∎ (Code check: `row_lemmas.realize` asserts both properties.)

**Lemma 9.15.2 (leaf-row lemma).** Assume some a_i ≥ 2. Fix β ∈ B with β ≥ 1. For ε ∈ {±1} and Λ ∈ 𝓛_β let s_{ε,Λ} be defined by:
- s_c = ε;
- σ_i = +1 for every branch, bare ones included;
- base leaf signs in every group b ≠ β;
- in group β, leaf sums from Lemma 9.15.1 with total Λ.

Then:
- (i) (L) and (Z) hold;
- (ii) every even secular orbit is main;
- (iii) every non-even pair makes at most 4 of the 2|𝓛_β| switchings bad, and at most 2 unless θ(θ² − β) ∈ ℤ.

**Row criterion (a):** if |𝓛_β| ≥ 2N + 1, some s_{ε,Λ} is good.

*Proof.*
- (i) (L) holds by the base pattern in the groups b ≠ β and by Lemma 9.15.1 in group β. For (Z): if β ≥ 2, group β contains a branch with non-constant leaf signs; if β = 1, a group b ≥ 2 of the base pattern does. By Lemma M(Z) the eigenvalue 0, if present, is main.
- (ii) Since σ ≡ 1, S_b = k_b and Σ_b S_b/(t − b) = F(t) = 1. Also A_b = εk_b + Λ_b.
  - Hence at every secular root **G(θ) = θ + ε + U_β(t) + Λ/(t − β)**.
  - For an even orbit θ ∉ ℚ(t), so G(θ) ≠ 0 (Lemma C).
- (iii) For a non-even pair (θ, −θ), the switching s_{ε,Λ} is bad iff ε + U_β(t) + Λ/(t − β) ∈ {θ, −θ}.
  - For fixed ε the left side is injective in Λ (t ≠ β). So at most two Λ are bad for each ε, four in total.
  - Two bad Λ, Λ′ for the same ε satisfy (Λ − Λ′)/(t − β) = ±2θ. Since Λ − Λ′ ∈ 2ℤ, this means θ(t − β) ∈ ℤ.
  - With N pairs at most 4N < 2|𝓛_β| switchings are bad. ∎

**Lemma 9.15.3 (bare-row lemma).** Assume some a_i ≥ 2 and k₀ ≥ 1. For ε ∈ {±1} and 0 ≤ m ≤ k₀ let s_{ε,m} be defined by:
- s_c = ε;
- base leaf signs everywhere;
- σ_i = +1 on non-bare branches;
- exactly m bare branches with σ = −1.

Then:
- (i) (L) and (Z) hold;
- (ii) an even secular orbit makes at most one s_{ε,m} bad, and only if its t is an even integer (t = 2m, a non-square);
- (iii) a non-even pair makes at most 4 bad, and at most 2 unless θ is an integer.

**Row criterion (b):** if 2(k₀ + 1) > 4N + N_ei, where N_ei is the number of secular roots that are even non-square integers, some s_{ε,m} is good.

*Proof.*
- (i) Bare branches carry no leaves. (Z) follows from a branch of size ≥ 2 with non-constant leaf signs in the base pattern.
- Now S₀ = k₀ − 2m and S_b = k_b for b ≥ 1, so Σ S_b/(t − b) = 1 − 2m/t. Also A_b = εk_b + Λ_b with Λ₀ = 0.
  - Hence **G(θ) = ε + U(t) + θ(1 − 2m/t)**.
- (ii) For an even orbit, 1 and θ are linearly independent over ℚ(t). So G = 0 iff ε + U(t) = 0 and t = 2m.
  - This forces t ∈ 2ℤ.
  - Also ε + U(t) = 0 holds for at most one ε.
- (iii) For a non-even pair, the switching is bad iff ε + U(t) = ±θ(1 − 2m/t). For fixed ε and sign, the map m ↦ θ(1 − 2m/t) is injective.
  - Two bad m for the same ε force 1 − (m + m′)/t = 0, so t ∈ ℤ. Then θ ∈ ℚ(t) = ℚ, i.e. θ is an integer. ∎

**Consistency check** (not needed for the proof): `diam4/code/test_row_lemmas.py`. For every tree with n ≤ 24 satisfying (a), resp. (b), the family contains a good switching, and the number of bad members is ≤ 4N, resp. ≤ 4N + N_ei. Exact ℚ-rank; 4,992 (a)-cases and 3,910 (b)-cases; 0 violations (`s3/test_row_lemmas_17-24.log`).

### 9.16 Session 3: the exceptional region and Corollary D′

**Lemma 9.16.1 (region bounds).** Suppose some a_i ≥ 2, the tree has N non-even pairs, and it fails both (a) and (b). Then:
- every β ≥ 2 in B has |𝓛_β| ≤ 2N, i.e. k_ββ ≤ 2N + 1, or (β, k_β) = (2, 2);
- in particular β ≤ 2N + 1;
- k₁ ≤ 2N + 1;
- k₀ = 0, or 2(k₀ + 1) ≤ 4N + N_ei ≤ 4N + r.

Hence, for fixed N, the tree lies in an explicit finite set.

`diam4/code/region_search.py NT` enumerates this set for N = NT. For each tree it computes the exact N (sympy factorization of R(x²) over ℚ) and N_ei, and reports every tree with N ≥ NT that fails (a) and (b) for its actual N.

| NT | trees in region | exceptional trees found | log |
|---|---|---|---|
| 2 | 799 | T(2,0,0) = D(2,2) and T(3,1,1,1,1,0,0,0), both N = 2 | `s3/region_NT2.log` |
| 3 | 12,841 | none | `s3/region_NT3_s*.log` |
| 4 | 212,231 (n ≤ 105) | none | `s3/region_NT4_s*.log` |

**Explicit switchings for the two exceptional trees.** Each is checked by the Bareiss ℚ-rank and by the independent Galois-factor criterion.
- D(2,2): (c; bare, bare; v; its two leaves) = (+; +, +; −; +, −) (§9.7).
- T(3,1,1,1,1,0,0,0) (n = 16):
  - s_c = +, all σ = +;
  - the four P₂-branches have far leaves (+, +, +, −);
  - the 3-branch has leaves (−, +, +).
  - Vertex-order string `++++++++++++--++`; see `s3/five_residual.log`.

**Proof of Corollary D′.**
1. If all a_i ≤ 1, apply §9.7. If N ≤ 1, apply §9.8.
2. If N ∈ {2, 3, 4} and (a) or (b) holds, apply Lemma 9.15.2 or 9.15.3.
3. Otherwise T is in the region of Lemma 9.16.1 with NT = N. The exhaustive region search lists only the two trees above, which are handled explicitly. ∎

**The 5 trees left uncovered after session 2** (`s3/five_residual.log`):
- T(6,3,2,0⁹), T(8,8,1,1,1,0,0), T(8,5,2,2,0⁵) and T(6,4,3,2,1⁴) satisfy (a), with β = 6, 8, 8, 6 and |𝓛_β| = 5, 15, 7, 5. Their row families have 1, 0, 2 and 0 bad members, all ≤ 4N = 8. A good member of each is re-checked by the Galois-factor criterion.
- T(3,1,1,1,1,0,0,0) is exceptional and handled explicitly as above.

### 9.17 Session 3: census of non-even pairs (n ≤ 44)

`diam4/code/noneven_census.py`, logs `s3/census_*_s*.log`.
- Scope: all 376,324 rooted trees of height ≤ 2 with 3 ≤ n ≤ 44.
- Distribution of N: {0: 373,837; 1: 2,442; 2: 44; 3: 1}.
- Every tree with N ≥ 2 satisfies (a), except D(2,2) and T(3,1⁴,0³) (`row_criterion.py` output in this section's logs).
- The unique N = 3 tree is T(12,12,8,0⁶), with the three integer pairs x ∓ 2, x ∓ 3, x ∓ 4; it satisfies (a) with β = 12, |𝓛| = 23.

### 9.18 Session 3: status of N ≥ 4, and what is known vs new

**N = 4.** The region search NT = 4 checked 212,231 trees (n ≤ 105) and found no exceptional tree, so Corollary D′ holds for N ≤ 4. **N = 5:** the region has 2,267,005 trees (n ≤ 144); its search was stopped unfinished (§9.19).

**Why N ≥ 5 is not closed.** The Row criteria need a group, or the bare leaves, with more than about 2N options. For fixed N the exceptional region is finite (Lemma 9.16.1), but N is not bounded a priori.
- A general bound on the number of *integer* secular roots t = q² relative to the largest group would close the proof.
- The crude bound N_int ≤ √t_r ≤ √(b_max + k) is too weak.

**A possible route to all N (not carried out): integrality.**
- Failure of s_{ε,Λ} at a non-even pair needs ε + U_β(t) + Λ/(t − β) = ±θ, and θ is an algebraic integer. So a failure needs U_β(t) + Λ/(t − β) ∈ O_K.
- Hence the failing Λ lie in a single residue class modulo d, the positive generator of ℤ ∩ (t − β)O_K. Note that d divides N(t − β) = ±h(β).
- This gives extra leverage whenever t − β is not a unit.
- The exceptional tree T(3,1⁴,0³) shows why this is not enough. Its golden orbit t = φ² makes t − 0 = φ², t − 1 = φ and t − 3 = −φ^{−2} all units, so no integrality obstruction exists there.

**Known before this work** (sources in the G1 logs of §4 and §9.12):

| Tree class | Source |
|---|---|
| Stars K₁,ₙ₋₁ | Akbari–França–Ghasemian–Javarsineh–de Lima, LAA 614 (2021) 270–280, doi 10.1016/j.laa.2020.04.029, Thm 4.1 (complete bipartite); as cited in Shao–Yuan arXiv:2106.07878v3, main.tex l.59 |
| Double stars (= all trees of diameter 3) | same 2021 paper (abstract via zbMATH Zbl 1459.05155) |
| Paths | same 2021 paper (abstract) |
| Harmonic trees T_a | Shao–Yuan, Appl. Math. Comput. 423 (2022) 127014, Prop. 2.1 (= arXiv:2106.07878v3, l.73) |
| All connected graphs with n ≤ 9 | 2021 paper, as stated in arXiv:2609.27046 l.159 |

**New here:**
- Theorem D (Main Theorem + Row Lemmas + families);
- Corollary D′ (every tree of diameter ≤ 4 with N ≤ 4), with a finite computer-assisted region search;
- **Theorem 9.22 (§9.22): all trees of diameter ≤ 4;**
- coverage of all trees with n ≤ 44 by proof plus census;
- the exhaustive certificate check to n = 44.

### 9.19 Session 3: region searches (N = 2, 3, 4, 5) and G3-style recheck

| Target N | trees in the region | max n | exceptional trees (N ≥ target, failing (a) and (b)) | logs |
|---|---|---|---|---|
| 2 | 799 | 38 | D(2,2), T(3,1,1,1,1,0,0,0) (both N = 2; explicit switchings, §9.16) | `diam4/s3/region_NT2.log` |
| 3 | 12,841 | 67 | none | `diam4/s3/region_NT3_s*.log` |
| 4 | 212,231 | 105 | none | `diam4/s3/region_NT4_s*.log` |
| 5 | 2,267,005 | 144 | **not completed**: started 22:59 UTC, stopped 23:27 UTC after about 28 of about 120 CPU-minutes per shard, to free cores for the independent re-check. No exceptional tree was printed before stopping; this is **not** a claim. | `diam4/s3/region_NT5_STOPPED.txt` |

- Each tree's N is exact: sympy factorization of R(x²) over ℚ.
- The criteria are the crude (a) and (b) of §9.15 (`row_lemmas.criteria`).
- Enumeration bounds are those of Lemma 9.16.1 (`region_search.py`).

**Recheck of prior work at 23:00 UTC** (`querylog.tsv`, `diam4/g1/*_s3.*`):
- MathDB "Akbari et al.'s switching conjecture…": status open, 0 solutions;
- trureturing issue and PR search "switching conjecture": 0 hits;
- arXiv, newest by date for "main eigenvalues" AND switching: still only 2609.27046v1, 2106.07878v3 and 1908.02001v3.

### 9.20 Recommendation (session 3, before §9.22; superseded by §9.23)

**What can be claimed now:**
- (1) Theorem D, the hand-checkable Row Lemmas, together with the Main Theorem and families;
- (2) Corollary D′: every tree of diameter ≤ 4 with at most four non-even secular pairs switches to all-main;
- (3) every tree of diameter ≤ 4 with n ≤ 44, both by proof plus census and by direct certificates.

Before (2) and (3) can be stated, the reader must accept the finite computer searches (region enumeration and census) as part of the proof.

**Not yet a complete theorem.** Trees with many non-even pairs are not excluded by an argument. None is known, and N ≤ 3 holds for every tree with n ≤ 44.

**Next step.** A short note is reasonable after:
- an independent re-run of the region searches, with a second implementation of the non-even-pair count, e.g. a C modular screen plus exact confirmation;
- a Codex review of Lemma 9.15.1–9.15.3.

The honest title is "…for all trees of diameter at most 4 with at most four non-even secular pairs (in particular all with at most 44 vertices)". A complete theorem needs a bound on the number of integer secular roots t = q² relative to the largest group (§9.18). That is a genuinely new idea that has not been found.

### 9.21 Session 3: independent re-check of the region searches, and Lean

**Second implementation** (`diam4/code/region_indep.py`). It shares only the enumeration bounds with `region_search.py` and computes the number of non-even pairs differently:
- it factors R(t) over ℚ, which has lower degree than R(x²), instead of factoring R(x²);
- it certifies an orbit as even by showing h(x²) irreducible modulo a prime p ∤ lc·disc, using its own Rabin irreducibility test over 𝔽_p;
- orbits that cannot be certified are counted, so this gives an upper bound N_up ≥ N. Linear factors t − v with v a perfect square are counted exactly;
- it computes N_ei by exact evaluation of F at even non-square integers;
- a tree is cleared if N_up < NT, or if criterion (a) or (b) holds with N_up. Both criteria are monotone in N, so this is sound.

Results:
- NT = 2: 799 trees; not cleared are exactly D(2,2) and T(3,1⁴,0³), the same two trees as §9.16 (`s3/indep_NT2.log`).
- NT = 3: 12,841 trees, none not cleared (`s3/indep_NT3.log`).
- NT = 4: 212,231 trees in 4 shards, none not cleared (`s3/indep_NT4_s*.log`; run 23:27:47–23:45:26 UTC).
- Both agree with §9.16. So Corollary D′ is confirmed by two implementations.

**Lean (session 3).** `work/research-lean/Research/SwitchingRowCount.lean` plus its audit file; copies and sha256 in `lean/`.
- `SwitchingRow.card_bad_le_two`: over any field of characteristic 0, with w ≠ 0, the set {Λ ∈ ℤ : u + Λw ∈ {θ, −θ}} has at most 2 elements. This is the counting step of Lemmas 9.15.2 and 9.15.3.
- `SwitchingRow.card_bad_le_one_of_ne`: at most 1 element if 2θ ∉ wℤ.
- Checks:
  - `lake build` exit 0;
  - axioms ⊆ {propext, Classical.choice, Quot.sound};
  - forbidden-token grep empty;
  - clean-directory replay OK (`lean/replay-rowcount-*/replay.log`, 23:28:46–23:29:01 UTC);
  - lock B was held only during each short build; `Research.lean` untouched.
- Not formalized: the spectrum lemma, the reduced form, realizability, and the region searches.

### 9.22 Session 3 (continued): the complete theorem for diameter ≤ 4

Files:
- code: `diam4/code/final_region.py` (implementation 1), `final_region_indep.py` (implementation 2), `final_region_witness.py`, `test_refined_rows.py`, `five_refined.py`;
- logs: `diam4/s3/final_region*.log`, `test_refined_rows_*.log`, `five_refined.log`.

Notation as in §9.1–9.4 and §9.15. Write b* = max a_i.
- N_I is the number of secular roots t that are perfect squares. These are the non-even pairs with θ ∈ ℤ; each is a linear factor t − q² of R.
- N_II is the number of non-even pairs with deg t ≥ 2 ("irrational pairs").
- So N = N_I + N_II. N_ei is as in §9.15.

**Theorem 9.22.** Every tree of diameter ≤ 4 other than K₂ has a switching s such that every distinct eigenvalue of T^s is main.

**Lemma 9.22.1 (refined Row Lemmas).** Assume some a_i ≥ 2.
- (i) In the leaf-row family of any β ∈ B, β ≥ 1 (Lemma 9.15.2), bad members are counted as follows: an integer non-even pair makes at most 4 bad, an irrational non-even pair at most 2, and an even orbit none.
- (ii) In the bare-row family (Lemma 9.15.3, k₀ ≥ 1), an integer pair makes at most 4 bad, an irrational pair at most 2, and an even orbit at most 1 (only when t = 2m is an even integer).

Hence T has a good switching if
- **(a′)** |𝓛_β| ≥ 2N_I + N_II + 1 for some β ∈ B with β ≥ 1, or
- **(b′)** k₀ ≥ 1 and 2(k₀ + 1) > 4N_I + 2N_II + N_ei.

*Proof.* Everything except the count for irrational pairs is Lemmas 9.15.2 and 9.15.3. Let (θ, −θ) be a non-even pair with t = θ² ∉ ℚ; then θ ∉ ℚ.
- **Leaf row.** s_{ε,Λ} is bad iff ε + Λw = −θ − U_β(t) or ε + Λw = θ − U_β(t), where w = 1/(t − β).
  - Since w ∉ ℚ, 1 and w are linearly independent over ℚ.
  - So each of the two equations has at most one solution (ε, Λ) ∈ ℤ².
- **Bare row.** Use θ/t = 1/θ. Then s_{ε,m} is bad iff ε − 2m/θ = −θ − U(t) (that is, G(θ) = 0) or ε + 2m/θ = θ − U(t) (that is, G(−θ) = 0).
  - Since 1/θ ∉ ℚ, 1 and 1/θ are linearly independent over ℚ.
  - So there is at most one (ε, m) for each equation. ∎

Lean: `SwitchingThmH.sol_subsingleton` and `SwitchingThmH.indep_of_irrational`.

**Theorem 9.22.2 (large branches).** If b* ≥ 13, criterion (a′) holds at β = b*. So one of the explicit switchings s_{ε,Λ} of the leaf-row family of b* (Lemma 9.15.2) is good.

*Proof.*
1. |𝓛_{b*}| = k_{b*}b* − 1 ≥ b* − 1 (Lemma 9.15.1).
2. B ⊆ {0, 1, …, b*}. Let g be the number of values in {0, …, b*} that are not in B. Then r = |B| = b* + 1 − g.
3. Bound N_I.
   - By interlacing (Lemma S), every secular root except the largest lies in (0, b*).
   - An integer secular root is never a pole, so it is not in B.
   - Hence N_I ≤ sq + 1, where sq = #{q ≥ 1 : q² ≤ b* − 1, q² ∉ B}.
   - Clearly sq ≤ ⌊√(b* − 1)⌋ and sq ≤ g.
4. Bound N_I + 2N_II. An integer pair uses one root and an irrational pair at least two. So N_I + 2N_II ≤ r = b* + 1 − g.
5. Combine. From steps 3 and 4:
   - 2(2N_I + N_II) ≤ 3N_I + b* + 1 − g;
   - ≤ 3sq + b* + 4 − g;
   - ≤ 2sq + b* + 4;
   - ≤ 2⌊√(b* − 1)⌋ + b* + 4.
6. Conclude.
   - For b* ≥ 13 we have 2⌊√(b* − 1)⌋ + 7 ≤ b*. For b* ≤ 16, ⌊√(b* − 1)⌋ = 3. For b* ≥ 17, write q = ⌊√(b* − 1)⌋ ≥ 4; then q² + 1 ≤ b*, and q² + 1 ≥ 2q + 7.
   - Hence 2(2N_I + N_II) ≤ 2b* − 3, so 2N_I + N_II ≤ b* − 2 < |𝓛_{b*}|. ∎

Lean: `SwitchingThmH.row_budget` (steps 4–6 as a statement about natural numbers) and `two_sqrt_add_seven_le`.

The bound 13 is where this crude count stops working: for b* = 12 it only gives 2N_I + N_II ≤ 11 = b* − 1.

**Lemma 9.22.3 (the finite remainder).** Let 2 ≤ b* ≤ 12, and suppose T fails (a′) for every β and fails (b′). With sq, r as above, put NI_max = min(sq + 1, r) and M = 2·NI_max + ⌊(r − NI_max)/2⌋. Then:
- |𝓛_β| ≤ 2N_I + N_II ≤ M for every β ∈ B with β ≥ 1. In particular b* − 1 ≤ M.
- If k₀ ≥ 1, then 2(k₀ + 1) ≤ 4N_I + 2N_II + N_ei ≤ 3N_I + r ≤ 3·NI_max + r. This uses N_I + 2N_II + N_ei ≤ r: the three kinds of roots are distinct.

So these trees form an explicit finite set. It has **13,376 trees** (n ≤ 124).

**The finite search (the computer-assisted step).**
- **Implementation 1** (`final_region.py`, 0.5 s, `s3/final_region.log`).
  - It enumerates the 13,376 trees, pruning by each group set B.
  - It computes N_I, N_ei and the number N_rat of integer secular roots with exact integer arithmetic, and uses N_II ≤ ⌊(r − N_rat)/2⌋.
  - 10 trees fail this cheap test. For these it factors R(x²) over ℚ to get the exact N_II.
  - Exactly 3 trees still fail (a′) and (b′): **T(2,2), T(2,0,0) = D(2,2) and T(3) = K₁,₄**.
- **Implementation 2** (`final_region_indep.py`, `s3/final_region_indep.log`).
  - It enumerates a cruder superset of **7,892,382 trees**, using only the per-b* bounds from the proof of Theorem 9.22.2 and no per-B pruning.
  - It finds integer roots by a floating-point screen of F(t) − 1 at every integer t, and confirms each hit exactly with rational arithmetic. A true root cannot be missed by the screen.
  - It bounds N_II by `region_indep.N_upper`: it factors R(t) and certifies even orbits by a Rabin irreducibility test of h(x²) mod p; uncertified orbits count as non-even.
  - It gives the same 10 survivors of the cheap test and the same 3 final trees.

**The three leftover trees.** Each switching is verified by the Bareiss ℚ-rank and by the independent Galois-factor criterion (`s3/five_refined.log`). Vertex order: centre, branch vertices in nondecreasing size, then leaves branch by branch.
- T(2,2), n = 7, N = 1: s = `+++++--` (centre and both branch vertices +; leaves (+,+) and (−,−)). It is also covered by Theorem F.
- T(2,0,0) = D(2,2), n = 6, N = 2: s = `+++-+-`, as in §9.7.
- T(3) = K₁,₄, n = 5, N = 1: s = `+++--`. It is a star (known), and also covered by Theorem F.

**Proof of Theorem 9.22.**
1. For n ≤ 2 the only trees are K₁, which is trivial, and K₂, the exception.
2. **Case all a_i ≤ 1.**
   - If k₀ ≥ 2: §9.7 (stars, T(1, 0^{k₀}), family A).
   - If k₀ = 0: T is a spider T(1^{k₁}), class D1 (§9.9).
   - If k₀ = 1: R(t) = t² − (k₁ + 2)t + 1 is irreducible, because its discriminant k₁(k₁ + 4) lies strictly between (k₁ + 1)² and (k₁ + 2)². So N ≤ 1 and the Main Theorem (§9.8) applies.
3. **Case b* ≥ 13:** Theorem 9.22.2 and Lemma 9.15.2.
4. **Case 2 ≤ b* ≤ 12.**
   - If (a′) or (b′) holds, Lemma 9.22.1 applies.
   - Otherwise T lies in the finite set of Lemma 9.22.3. By the search, T is one of the three trees above, which have explicit switchings. ∎

**Checks** (not needed for the proof).
- **Refined counts, all rows.** `test_refined_rows.py` covers all 11,535 trees with 5 ≤ n ≤ 27 and b* ≥ 2.
  - It tests every leaf row at every β (31,925 rows, 282,968 switchings) and every bare row (9,114 rows, 97,552 switchings).
  - The number of bad members never exceeds 4N_I + 2N_II (+ N_ei for bare rows): 0 violations.
  - Goodness is certified by F_p-rank = d, and uncertified members are re-checked exactly over ℚ (`s3/test_refined_rows_*.log`).
- **End to end on the finite set.** `final_region_witness.py` covers all 13,373 covered trees of Lemma 9.22.3 (n ≤ 124).
  - The designated family always contains a certified good member.
  - It never has more bad members than predicted: 0 violations (`s3/final_region_witness_s*.log`).
- **The 5 trees of session 2** (`s3/five_refined.log`). A good member of each is also confirmed by the Galois criterion.

  | Tree | Criterion | Check | Bad members |
  |---|---|---|---|
  | T(3,1⁴,0³) | (b′) | 8 > 6 | 1 of 8 |
  | T(6,3,2,0⁹) | (a′) at β = 6 | 5 ≥ 3 | 1 of 10 |
  | T(8,8,1³,0²) | (a′) at β = 8 | 15 ≥ 4 | 0 of 30 |
  | T(8,5,2,2,0⁵) | (a′) at β = 8 | 7 ≥ 4 | 2 of 14 |
  | T(6,4,3,2,1⁴) | (a′) at β = 6 | 5 ≥ 3 | 0 of 10 |

- **The counting bounds, exactly, for n ≤ 44.** `test_bounds.py` covers all 375,820 trees with 4 ≤ n ≤ 44 and b* ≥ 2, using exact N_I and N_II (`s3/test_bounds_*_s*.log`, 0 violations). It checks:
  - N_I ≤ sq + 1;
  - N_I + 2N_II + N_ei ≤ r;
  - (a′) at β = b* for all 105,970 trees with b* ≥ 13;
  - that every tree is covered by b* ≥ 13, (a′), (b′) or the list of three. Only those three trees fail (a′) and (b′).
  - The N distribution it finds (45 trees with N ≥ 2, one with N = 3) matches the census of §9.17.
  - The remaining 504 trees with n ≤ 44 have all a_i ≤ 1 (step 2 of the proof).
- **Direct certificates.** The direct certificates for all 376,324 trees with n ≤ 44 (§9.10) remain an independent cross-check of the statement.

**Internal review (same model; not the cross-model review of §9.23).** An adversarial Claude subagent (00:02–00:19 UTC) re-derived Lemma 9.22.1, Theorem 9.22.2 and Lemma 9.22.3. Its own checks:
- it re-ran the finite set with exact N_I, N_II and N_ei for all 13,376 trees;
- it brute-forced (a′)/(b′) on all 136,878 trees with 2 ≤ b* ≤ 12 and n ≤ 40, which again leaves only the three trees;
- it checked the full b*-row of all 524 trees with b* ≥ 13, N ≥ 1 and n ≤ 44 by exact Krylov rank;
- it checked the §9.7 families for k₀, k₁ ≤ 30.

It found no mathematical error, only a sign typo in the bare-row equation of Lemma 9.22.1, which does not change the count and is now fixed. Its scripts are in the session scratchpad (not part of the record).

**Lean (session 3, second file).** `work/research-lean/Research/SwitchingThmH.lean` plus `SwitchingThmHAudit.lean`; copies and sha256 in `lean/`.
- Statements:
  - `row_budget`: b ≥ 13, sq ≤ √(b − 1), sq ≤ g, NI ≤ sq + 1 and NI + 2NII + g ≤ b + 1 imply 2NI + NII + 1 ≤ b − 1;
  - `two_sqrt_add_seven_le`;
  - `sol_subsingleton`: if 1 and w are ℚ-independent, then ε + Λw = u has at most one solution (ε, Λ) ∈ ℤ²;
  - `indep_of_irrational`.
- Checks:
  - `lake build` exit 0 (`s3/lake_build_SwitchingThmH.log`);
  - 6 axiom lines, all ⊆ {propext, Classical.choice, Quot.sound};
  - forbidden-token grep empty;
  - clean-directory replay 23:53:19–23:53:31 UTC, exit 0 (`lean/replay-thmH-20260926T235319Z/replay.log`).
- Lock B was held 23:52–23:53:35 UTC only; `Research.lean` was not edited.
- Not formalized: Lemma S, Lemma M, realizability and the finite search.

**What is proved, known and new (diameter ≤ 4).**
- **Proved here:** Theorem 9.22 (all trees of diameter ≤ 4). It rests on hand proofs (§9.2–9.9, §9.15, §9.22) plus one small finite search (13,376 trees, two implementations).
- **Known before** (§9.18 table):
  - stars (Akbari et al. 2021, Thm 4.1);
  - double stars, i.e. all diameter-3 trees, and paths (Akbari et al. 2021);
  - harmonic trees (Shao–Yuan 2022, Prop. 2.1);
  - all graphs with n ≤ 9 (Akbari et al. 2021).
  - G1 (§9.12, recheck §9.19) found no claim for diameter 4.
- **New:**
  - the theorem itself;
  - the reduced form G(θ) = Σ_b(A_b + S_bθ)/(t − b) with the even/non-even split (Lemma G);
  - the Row Lemmas with the refined count;
  - the square-counting bound on integer pairs;
  - the exhaustive checks.

### 9.23 Recommendation (session 3, final)

The conjecture is now **proved for all trees of diameter ≤ 4** (Theorem 9.22). The proof has three parts:
- a hand proof when the largest branch has ≥ 13 leaves;
- the hand-checkable Lemma 9.22.1 plus a finite search of 13,376 trees, run in two independent implementations;
- three small trees with explicit switchings.

A short note, "The switching conjecture for main eigenvalues holds for trees of diameter at most 4", is realistic after:
1. a minimal Codex cross-model review of Lemma 9.22.1, Theorem 9.22.2 and Lemma 9.22.3, with one run of `final_region.py`. This is short: the script runs in under a second.
2. a fresh G1 check on the day of release (arXiv, MathDB, trureturing, GitHub), because 2609.27046v1 is new and others may be working on it.

The full Problem (T) for all trees remains open. Only the diameter-≤-4 subclass is settled.
