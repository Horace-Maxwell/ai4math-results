> **Note added for release v1.4.0.** This working note was written before Paper 1 version 1.4, and its status entries (for example on G3 and on the reviews) are as of writing. Its references to Paper 1 use older numbering: Conjecture 12 and Proposition 13 are Conjecture 14 and Proposition 15 of version 1.4, and Lemmas 4, 5, 6 and 7 are the path identity, the potential, the cell function and the local lemma (Lemmas 7, 8, 10 and 11 of version 1.4). Theorems B, B′ and C are Theorems 4, 25 and 5 of version 1.4. The runs for a = 5–8 (min(a, b) ≤ 8) have not been reviewed, and these cases are not claimed.

# Theorem B: maximal energy of ICG(p²q^b) for even b (equal parity, a = 2)

Round 6 working note, 2026-09-26. Builds on Paper 1 (`outputs/ICG-q3-general/note.tex`: T_k, path identity Lemma 4,
potential Lemma 5, cell Lemma 6, the functional G(Y) of eq. (G), Conjecture 12, Theorem 3, Proposition 13) and on
`work/round4/icg-equal-parity/PROOF.md` (Lemma P = Lean `L1_potential`, Lemma M = Lean `nu_sub_L` …).

## Status table

| Item | Literature | Statement | Mathematics | Formal (Lean) |
|---|---|---|---|---|
| **Theorem B**: n = p²q^b, b ≥ 2 even, p, q any distinct odd primes | no prior work found beyond n = pq (deep check 2026-09-26, round 4 `literature.md`); **G1 incremental refresh by the main session 05:53–05:58 UTC passed** (`novelty/G1-refresh.md`: arXiv, OpenAlex, MathDB, GitHub incl. trureturing; no prior proof, concurrent work or registration); G3 (Jiang–Yang new versions, new arXiv) still required before release. Conjecture 12 is our own. | exact E_max and exactly two maximisers (Conjecture 12 with a = 2) | **complete proof** (§1–§5). All steps are human-readable; the finitely many b-independent elementary inequalities in Lemmas FD1/FD2 (bivariate rational functions of p, q) are certified by an exact symbolic computation (137 vertex checks → 325 polynomials with nonnegative coefficients, `prove_fd.py`, `logs/certificates.txt`); hand proofs are given for the tight ones. **Independent review: ACCEPT WITH MINOR REVISIONS, no blocker/major (§6.4); minor findings fixed.** | **formalised** by a separate Lean subagent of the main session (`lean/STATUS.md`): `ICGEqualParityB.theoremB`, `corollaryB`, `theoremB_swap`, `thmB'` in `work/research-lean/Research/ICGEqualParityB{Col,FD,Main,Graph}.lean` (+ 325 certificate lemmas `Cert1..6`); `lake build` OK, axioms propext/Classical.choice/Quot.sound, leanchecker OK (as reported; read-only spot check by this agent: files present, no sorry/admit/axiom, statement matches Theorem B). Not re-run here (lock A held by the main session). |
| Corollary: n = p^b q² (swap of the primes) | same | same | immediate | — |
| Theorem B′ (sign-matrix form, real parameters p ≥ 5, q ≥ 3 or p = 3, q ≥ 5) | — | §0 | proved (same proof) | — |
| Lemma S (one-step bound, column path, F-side T₂(p), incl. q = 3) | — | §2 | proved by hand | — |
| **Theorem C**: shapes (3, b), b odd, and (4, b), b even (all b), hence Conjecture 12 whenever min(a,b) ≤ 4 | as above | §10 (Theorem B′_a) | **computer-assisted proof**: the same argument with the per-a case list generated and certified symbolically by two independent implementations (ours: a = 3: 14 196, a = 4: 70 416 bivariate polynomial certificates; referee 2's direct-cell certifier), 0 failures; **independent review (`review2/REVIEW_GENERIC.md`): ACCEPT WITH MINOR REVISIONS for a = 3 and a = 4, no blocker/major; fixes F1–F9 incorporated** | — |
| Extension a = 5, 6, 7, 8 (→ min(a,b) ≤ 8) | as above | §10 | certified by both implementations, 0 failures (a = 8: ≈ 58 million certificates in ours); **not reviewed as a claim** | — |

Relation to earlier results: Theorem B contains Proposition 13 for (2,2), (2,4), (2,6), (2,8) and their transposes, now for all
even b, by a b-uniform argument (no enumeration over sign matrices).

## 0. Statement and notation

**Theorem B.** Let p, q be distinct odd primes, b ≥ 2 even, n = p²q^b. The maximal energy of an integral circulant graph of
order n is

  E_max(n) = ½[n + d₂(p) d_b(q)] − δ₂(p) δ_b(q) = ½[n + (5p² − 8p + 4) d_b(q)] − (p² − 2p + 2) δ_b(q),

attained exactly by D⁻ = {p^i q^j : i + j odd} and D⁺∖{n} = {p^i q^j : i + j even}∖{n}. Exchanging the names of the primes,
for n = p^b q² the maximal energy is ½[n + d_b(p) d₂(q)] − δ_b(p) δ₂(q), attained exactly by the two sets with the same description.

Notation (Paper 1). P = p − 1, Q = q − 1, M = T₂(p) = [[0, −pP, pP], [−pP, P², P], [pP, P, 1]], N = T_b(q).
For w ∈ ℝ^{b+1}: path z_{b−1} = w_b, z_{j−1} = (z_j + Q w_j)/q, and ν(w) := ‖Nw‖₁/q^b; (Nw)_b = q^b z_{−1}(w).
Potential (x = q): μ_{−1} = 1, μ_j = (Q − μ_{j−1})/q; ĉ_j = Q(1 + μ_{j−1})/q (0 ≤ j < b), ĉ_b = ρ := μ_{b−1};
D̂ := Σ_{j≤b} ĉ_j = d_b(q)/q^b, ρ = δ_b(q)/q^b. Lemma M: with L = Q/(q+1), μ_j − L = (−1/q)^{j+1}(1 − L); for even j ≥ 0,
μ₀ ≤ μ_j < L (increasing), for odd j, L < μ_j ≤ μ₁ (decreasing); μ₀ = (Q−1)/q, μ₁ = (Q²+1)/q².
Cell function h_μ(A,B) = Q|A−B| + μ|B+QA| − (Q−μ)|B| − Q(1+μ)|A| (Paper 1 Lemma 6 with P ← Q). Exact values for A ≥ 0
(general case by h(−A,−B) = h(A,B)): 0 ≤ B ≤ A: −2(Q−μ)B; B > A: 2(μB − QA); −QA ≤ B < 0: 0; B < −QA: 2μ(|B| − QA).
Hence h ≤ 2μ·max(0, |B| − Q|A|), h(0,B) = 2μ|B|, and for A ≠ 0 and |B| < Q|A| (0 ≤ μ ≤ 1): h(A,B) = 0 ⇔ B·sgn A ≤ 0,
and h(A,B) < 0 otherwise. (Without the hypothesis |B| < Q|A| the zero set is larger: for A > 0, μ > 0 it is [−QA, 0] ∪ {QA/μ};
referee finding 3.)
**Lemma P** (round 4; Lean `L1_potential`): ν(w) = Σ_{j≤b} ĉ_j|w_j| + (1/q) Σ_{j<b} h_{μ_{j−1}}(w_j, z_j(w)) for every real w.
D_p := d₂(p) = 5P² + 2P + 1, δ_p := δ₂(p) = P² + 1, Θ := d₂(p)d_b(q) − 2δ₂(p)δ_b(q).
For Y ∈ {±1}^{3×(b+1)}: Z = MYNᵀ, G(Y) = Σ_{(i,j)≠(2,b)} |Z_ij| + Z_{2b} (= 2E − n when Y = 2X − J is the sign matrix of D).

**Theorem B′.** Let (P ≥ 4, Q ≥ 2) or (P = 2, Q ≥ 4) be real, b ≥ 2 even. Every Y ∈ {±1}^{3×(b+1)} with Y_{2b} = −1 satisfies
G(Y) ≤ Θ, with equality exactly for Y⁻ = −s₂s_bᵀ and Y⁺ = s₂s_bᵀ − 2e₂e_bᵀ.

*Theorem B′ ⇒ Theorem B.* As in Paper 1 §7/§9: by Jiang–Yang Prop. 2.2 and M𝟏 = p²e₂, N𝟏 = q^b e_b, 2E(ICG_n(D)) − n = G(Y)
for the sign matrix Y of D (Y_{2b} = −1 as n ∉ D). Y⁻ and Y⁺ are the sign matrices of D⁻ and D⁺∖{n}, which are nonempty sets of
proper divisors (p ∈ D⁻, 1 ∈ D⁺∖{n}, n ∉ D⁻ as 2 + b is even). Distinct odd primes give P ≥ 4, Q ≥ 2 (p ≥ 5) or P = 2, Q ≥ 4
(p = 3). The case p^b q² follows because E is invariant under transposing X (exchange of the primes). ∎

## 1. Column types and the column-path identity

Columns c_j = (Y_{0j}, Y_{1j}, Y_{2j})ᵀ ∈ {±1}³; s₂ = (1,−1,1)ᵀ. Up to sign there are four types (normalised by the top entry):

| type t | α(t) := M t | F_p(t) = ‖α(t)‖₁ | Δ(t) = D_p − F_p(t) |
|---|---|---|---|
| A = (1,−1,1) = s₂ | (2pP, −2P², P²+1) | D_p | 0 |
| B = (1,1,−1) | (−2pP, −2P, p²−2) | 3p² − 4 | 2(P−1)² |
| C = (1,−1,−1) | (0, −2pP, P²−1) | 3p² − 4p | 2(P²+1) = 2δ_p |
| E = (1,1,1) | (0, 0, p²) | p² | 4P² |

Over all c ∈ {±1}³: max|(Mc)₀| = 2pP, max|(Mc)₁| = 2pP, max|(Mc)₂| = p²; the same bounds hold for Mζ, ζ ∈ [−1,1]³ = conv{±1}³.

Rows r_i := (MY)_{i·} ∈ ℝ^{b+1}, so r_{ij} = (Mc_j)_i. Column-path states: ζ_{b−1} := c_b, ζ_{j−1} := (ζ_j + Qc_j)/q. Each ζ_j is a
convex combination of c_{j+1}, …, c_b (so ζ_j ∈ [−1,1]³), and by linearity z_j(r_i) = (Mζ_j)_i. Define, for 0 ≤ j < b,

  s_j := ĉ_j Δ(c_j) − (1/q) Σ_{i=0}^{2} h_{μ_{j−1}}((Mc_j)_i, (Mζ_j)_i),   κ := 2(z_{−1}(r₂))^−.

**Proposition 1.** (Θ − G(Y))/q^b = Σ_{j<b} s_j + ρΔ(c_b) + κ − 2δ_pρ.

*Proof.* Row i of Z is N r_i, so ‖row_i Z‖₁ = q^b ν(r_i), and Z_{2b} = (N r₂)_b = q^b z_{−1}(r₂). Hence G/q^b = Σ_i ν(r_i) − κ.
Lemma P for each r_i and Σ_i |r_{ij}| = F_p(c_j) = D_p − Δ(c_j) give G/q^b = D_pD̂ − Σ_{j≤b} ĉ_jΔ(c_j) + (1/q)Σ_{j<b}Σ_i h(…) − κ,
while Θ/q^b = D_pD̂ − 2δ_pρ. ∎  (Checked against the matrix model for every Y of the shapes (2,2) and (2,4) at the parameter
pairs listed in §6: `colsurplus.py`, `verify_proof.py`.)

## 2. Lemma S (one-step bound; includes q = 3)

**Lemma S.** In the parameter range of Theorem B′, for 0 ≤ μ ≤ 1, c ∈ {±1}³ and ζ ∈ [−1,1]³, the quantity
s(c,ζ) := Q(1+μ)/q · Δ(c) − (1/q) Σ_i h_μ((Mc)_i, (Mζ)_i) is ≥ 0, and > 0 unless c = ±s₂. More precisely (A = Mc, B = Mζ):
* type A: |B₀| ≤ 2pP = |A₀|; |B₁| ≤ 2pP ≤ 2QP² = Q|A₁| (QP ≥ 2P ≥ p); |B₂| ≤ p² ≤ Q(P²+1) (2(P²+1) − (P+1)² = (P−1)²). All three
  cells are ≤ 0, so s ≥ 0.
* type B: h₀ ≤ 0 (|B₀| ≤ |A₀|), h₂ ≤ 0 (|B₂| ≤ p² ≤ Q(p²−2)), h₁ ≤ 2μ(2pP − 2PQ)^+. So s ≥ (2/q)[Q(1+μ)(P−1)² − 2μP(p−Q)^+] > 0:
  if Q ≥ p (always when P = 2) the bracket is Q(1+μ)(P−1)² > 0; otherwise P ≥ 4, the bracket is affine in μ, equals Q(P−1)² > 0 at
  μ = 0, and at μ = 1 equals 2Q(P−1)² − 2P(P+1−Q) ≥ 4(P−1)² − 2P(P−1) = 2(P−1)(P−2) > 0 (it increases with Q).
* type C: h₀ = 2μ|B₀| ≤ 4μpP; h₁ ≤ 0 (|B₁| ≤ |A₁|); h₂ ≤ 0 as |B₂| ≤ p² ≤ Q(P²−1) [(P−3)(P+1) > 0 for P ≥ 4; 12 > 9 for
  P = 2, Q ≥ 4]. So s ≥ (2/q)[Q(1+μ)(P²+1) − 2μpP] ≥ (4/q)[P² + 1 − μ(P−1)] ≥ (4/q)(P² − P + 2) > 0.
* type E: h₀, h₁ ≤ 4μpP each, h₂ ≤ 0 (|B₂| ≤ |A₂|). So s ≥ (4/q)[Q(1+μ)P² − 2μpP] ≥ (8P/q)(P − μ) > 0. ∎

By Lemma S (μ = μ_{j−1} ∈ [0,1]), s_j ≥ 0 for every j < b and every Y; s_j > 0 if c_j ≠ ±s₂, and if c_j = ±s₂ then s_j = 0 iff all
three cells at j vanish. (Lemma S is the column-orientation analogue of Paper 1 Lemma 7 for F-side T₂(p). In Lemma 7 the cell
parameter is the path-side P = p − 1 ≥ 4; here the path side is q and the cell parameter is Q = q − 1, which equals 2 at q = 3,
a value not covered by the hypotheses of Lemma 7.) Random exact test: `lemmaS_check.py` (24 000 cases, both parameter regions).

## 3. First deviation from the anti-checkerboard (Lemma FD1)

Y⁻ has columns c_j = (−1)^{j+1}s₂. For Y ≠ Y⁻ with Y_{2b} = −1 let **J := max{j : c_j ≠ (−1)^{j+1}s₂}**. If J < b, the columns
J+1, …, b agree with Y⁻, and induction (ζ_{b−1} = −s₂; if ζ_j = σμ_{b−2−j}s₂ and c_j = −σs₂ then ζ_{j−1} = −σ((Q−μ_{b−2−j})/q)s₂
= −σμ_{b−1−j}s₂) gives the **exact state**

  ζ_J = ε m s₂,   ε := (−1)^J,   m := μ_{b−2−J},   so Mζ_J = ε m α(A).

**Lemma FD1.** In the range of Theorem B′, for 0 ≤ J < b and every c ∈ {±1}³∖{−εs₂}: s_J(c, ζ_J) > 2δ_pρ.

*Closed forms.* Put μ := μ_{J−1}, ĉ := Q(1+μ)/q, μ_J = (Q−μ)/q, and write "same"/"opp" for c = +εt / −εt. The sign pattern of
α(t)·α(A) (entrywise) is (+,+,+) for A, (−,+,+) for B, (0,+,+) for C, (0,0,+) for E; with |B_i| = m|α(A)_i| and the exact cell
values of §0 one gets (each line is a direct evaluation, verified symbolically against the definition in `formulas.py`,
112 000 exact random checks):

| deviation | s_J |
|---|---|
| A same | 2μ_J m D_p |
| B same | 2(P−1)²ĉ + 2μ_J(P²+1)m + (4P/q)·min{(Q−μ)Pm, Q − μPm} |
| B opp | 2(P−1)²ĉ + 4μ_J pP m − (4μP/q)·(Pm − Q)^+ |
| C same | 2(P²+1)ĉ − (4μ/q)pPm + 4μ_J P²m + (2/q)·min{(Q−μ)(P²+1)m, Q(P²−1) − μ(P²+1)m} |
| C opp | 2(P²+1)ĉ − (4μ/q)pPm |
| E same | 4P²ĉ − (4μ/q)(pP + P²)m + 2μ_J(P²+1)m |
| E opp | 4P²ĉ − (4μ/q)(pP + P²)m |

(The seven are all of {±1}³∖{−εs₂}.)

*Parameter regimes* (b even): (R0) J = 0: μ = 1, m = μ_{b−2} ∈ [μ₀, L), ρ = (Q − m)/q. (R1) J = b−1: m = 1, μ = μ_{b−2} ∈ [μ₀, L),
ρ = (Q − μ)/q. (R2) 1 ≤ J ≤ b−2: μ = μ_{J−1}, m = μ_{b−2−J}; the indices J−1, b−2−J are ≥ 0 with odd sum b−3, so one is even
(value in [μ₀, L)) and the other odd (value in (L, μ₁]); since odd-indexed μ's decrease and b−1 is odd and larger,
ρ = μ_{b−1} < (the odd one). So (R2a) μ ∈ [L, μ₁], m ∈ [μ₀, L], ρ < μ, or (R2b) μ ∈ [μ₀, L], m ∈ [L, μ₁], ρ < m.

*Proof of the inequality.* In each regime, s_J − 2δ_pρ (with ρ replaced by its exact value or upper bound) is, in each of
μ and m separately, affine or a minimum of affine functions (the (·)^+ term enters as min{0, −(4μP/q)(Pm − Q)} with μ ≥ 0), hence
concave in each variable separately. So its minimum over the closed parameter box (a relaxation of the half-open true ranges) is
attained at a vertex: for fixed m the minimum over μ is at an endpoint μ_lo or μ_hi, and g(m) = min{f(μ_lo,m), f(μ_hi,m)} is
concave, so its minimum is at an endpoint. At a vertex, base + Σ min{X_i, Y_i} > 0 ⇔ every choice of one argument per min is > 0.
Each vertex value is an explicit rational function of (P,Q). Substituting P = 4 + s, Q = 2 + t (resp. P = 2, Q = 4 + t), every
numerator is a polynomial with nonnegative coefficients and positive constant term over a denominator that is a product of
factors with nonnegative coefficients and positive constant term (`prove_fd.py`: 84 vertex checks for FD1, all certified;
polynomials listed in `logs/certificates.txt`). Hand proofs of representative cases:
* **A same** (the tight case). R1: s = 2ρD_p > 2(P²+1)ρ. R0 and R2 with J, b−2−J even: μ_J, m ≥ μ₀ and ρ ≤ μ₁, so it suffices
  that μ₀²D_p > μ₁δ_p, i.e. (Q−1)²(5P²+2P+1) > (Q²+1)(P²+1). Indeed D_p − 5(P²+1) = 2(P−2) ≥ 0 and
  5(Q−1)² − (Q²+1) = 2(2Q−1)(Q−2) ≥ 0, so (Q−1)²D_p ≥ 5(Q−1)²(P²+1) ≥ (Q²+1)(P²+1), with equality in both only at P = Q = 2
  (p = q = 3, excluded). R0 uses the exact ρ = (Q−m)/q and monotonicity in m: at m = μ₀ the inequality is exactly this one. R2 with J,
  b−2−J odd: μ_J > L ≥ ½ and m > ρ, so s > ρD_p > 2δ_pρ. This is Lemma R / Remark T of round 4: at b = 2, J = 0, q = 3 the margin
  is (target − G)(Y) = 4(p−3) for Y = s₂(1,1,−1)ᵀ.
* **C opp.** s − 2δ_pρ = (2/q)[(P²+1)(Q(1+μ) − qρ) − 2μpPm]. R0: = (2/q)[(P²+1)Q − m(P²+2P−1)] > 0 (m < 1, Q ≥ 2). R1:
  = (2μ/q)[(P²+1)q − 2pP] ≥ (2μ/q)(P² − 2P + 3) > 0. R2: qρ ≤ qμ₁ = Q − μ₀, m ≤ μ₁, and (P²+1)Q ≥ (18/5)μ₁(P²+1) > 2μ₁(P²+P).
* **E opp.** s ≥ (4P/q)[PQ(1+μ) − μ(2P+1)] ≥ (4P/q)(PQ − 1) (m ≤ 1), and 4P(PQ−1)(Q+1) − 2(P²+1)(Q²+1) = PQ(PQ−4) + Q²(P²−2) +
  (4P²Q − 2P² − 4P − 2) > 0, while 2δ_pρ ≤ 2(P²+1)(Q²+1)/q².
Direct exact evaluation at the true μ-values for p, q ∈ {3,5,7,11,13,17,101} and b ≤ 20 (all J, all seven deviations):
`first_dev.py`, minimum ratio s_J/(2δ_pρ) = 1.0039 (p = 101, q = 3, b = 2, A same; it tends to 1 as p → ∞ at q = 3, b = 2). ∎

## 4. Last column B (Lemma FD2)

**Lemma FD2.** In the range of Theorem B′, if c_b = B = (1,1,−1) then Σ_{j<b} s_j + κ > 4Pρ (= 2δ_pρ − ρΔ(B)).

*Proof.* The state ζ_{b−1} = B is exact; μ := μ_{b−2} ∈ [μ₀, L), ρ = (Q − μ)/q. For the state ε′mα(B) (here ε′ = 1, m = 1) the
surplus of the eight possible next columns is (γ := α(B); "same"/"opp" relative to ε′; the continuation −ε′B is the "B-chain"):

| column | s |
|---|---|
| −ε′B (chain) | 2(P−1)²ĉ (all three cells vanish: opposite signs, |B_i| ≤ Q|A_i|) |
| A same | 4μ_J Pm + (2/q)·min{(Q−μ)(p²−2)m, Q(P²+1) − μ(p²−2)m} |
| A opp | 4μ_J pPm |
| B same | 2(P−1)²ĉ + 2μ_J m(3p² − 4) |
| C same | 2(P²+1)ĉ − (4μ/q)pPm + 4μ_J Pm + (2/q)·min{(Q−μ)(p²−2)m, Q(P²−1) − μ(p²−2)m} |
| C opp | 2(P²+1)ĉ − (4μ/q)pPm |
| E same | 4P²ĉ − (4μ/q)(pP + P)m + 2μ_J(p²−2)m |
| E opp | 4P²ĉ − (4μ/q)(pP + P)m |

(a) If c_{b−1} is not the chain column, s_{b−1} > 4Pρ (m = 1; vertex certificates, both parameter regions; e.g. A same:
s ≥ 4μ_J P = 4Pρ plus a positive term; A opp: 4pPρ > 4Pρ). If P ≥ 4, also the chain column pays: 2(P−1)²ĉ_{b−1} − 4Pρ
= (2/q)[(P−1)²Q(1+μ) − 2P(Q−μ)] is increasing in μ and at μ = μ₀ equals (4/q²)[(P−1)²Q² − P(Q²+1)] ≥ (4/q²)(4P² − 13P + 4) > 0
(using (P−1)²Q² − P(Q²+1) = Q²(P² − 3P + 1) − P ≥ 4(P² − 3P + 1) − P).
So for p ≥ 5 the lemma follows from Lemma S.
(b) P = 2 (p = 3, Q ≥ 4) and c_{b−1} = −B. Let J′ := max{j < b : c_j ≠ (−1)^j B} (J′ ≤ b−2; J′ = −1 if none) and k := b−1−J′.
On the chain, ζ_j = (−1)^{j+1}μ_{b−2−j}B and s_j = ĉ_jΔ(B) = 2ĉ_j.
* J′ = −1: Σ s_j = 2(D̂ − ρ) and κ = 0 (ζ_{−1} = ρB, so (Mζ_{−1})₂ = ρ(p²−2) > 0); 2(D̂ − ρ) > 8ρ ⇔ D̂ > 5ρ, and
  D̂ − 5ρ = D̂_{b−1} − 3ρ ≥ (3q−4)/q − 3μ₁ = (2q−6)/q² > 0
  (d_b = q d_{b−1} + 2δ_b, D̂_{b−1} ≥ D̂₁ = d₁(q)/q). This is the vertical rank-one competitor Y = (1,1,−1)ᵀ s_bᵀ; its margin tends to 0
  as q → ∞ at b = 2.
* k ≥ 3: the chain alone pays: with x = μ_{b−2}, 2(ĉ_{b−1} + ĉ_{b−2} + ĉ_{b−3}) − 8ρ ≥ (1/q)[2Q(3 + x + L + μ₀) − 8(Q − x)],
  which is increasing in x and at x = μ₀ equals (1/q)[(4Q+8)μ₀ − 2Q + 2QL] > 0 (μ_{b−3} > L, μ_{b−4} ≥ μ₀; for Q ≥ 4,
  μ₀ ≥ 3/5 and L ≥ 2/3 give (26/15)Q + 24/5 > 0). (An earlier version displayed this bound with a spurious factor 2;
  referee finding 1. `prove_fd.py` certifies the correct expression.)
* k = 1 (m = μ₀, μ = μ_{b−3} ∈ (L, μ₁] or μ = 1 if b = 2, x := μ_{b−2} = (Q−μ)/q, ρ = (Q−x)/q) and k = 2 (m = μ₁, μ = μ_{b−4} ∈ [μ₀, L),
  μ_{b−3} = (Q−μ)/q, μ_{b−2} = (Q−μ_{b−3})/q): chain cost + s_{J′} − 8ρ is concave in μ; vertex certificates for all seven
  deviations (`prove_fd.py`, region P = 2, Q = 4 + t).
Other terms are ≥ 0 by Lemma S and κ ≥ 0. ∎  (Exact replay: `fd2.py`, min ratio 1.0005 at p = 3, q = 1009, b = 2, full chain;
≥ 1.9 for b ≥ 4.)

## 5. Equality and the proof of Theorem B′

**Lemma EQ.** If c_b = C = (1,−1,−1), s_j = 0 for all j < b, then Y = Y⁺; conversely G(Y⁺) = G(Y⁻) = Θ.
*Proof.* By Lemma S every c_j (j < b) is ±s₂ with all cells zero, i.e. (Mζ_j)_i ∈ [−Q|(Mc_j)_i|, 0]·sgn(Mc_j)_i. Mζ_{b−1} = α(C) =
(0, −2pP, P²−1) forces c_{b−1} = −s₂ (coordinates 1 and 2). If Mζ_j = σ(x₀, −x₁, x₂) with x_i > 0 (bounded by 2pP, 2pP, p²),
then a zero cell at coordinate 0 needs B₀·sgn A₀ ≤ 0 with B₀ = σx₀ ≠ 0 and A₀ = ±2pP, which forces c_j = −σs₂ (for type-A
columns max|B_i| < Q|A_i|, so the zero-set statement of §0 applies). Then Mζ_{j−1} = −σ(2QpP − x₀, −(2QP² − x₁), Q(P²+1) − x₂)/q
has the strict pattern −σ(+,−,+) (2QP² > 2pP, Q(P²+1) > p²); this holds for Mζ_{b−2} directly. So c_j = (−1)^j s₂ for all
j < b: Y = Y⁺. For Y⁺ (and Y⁻) the same computation
shows all cells vanish; κ(Y⁺) = 0 (sign of (Mζ_{−1})₂ is +) and κ(Y⁻) = 2ρδ_p (ζ_{−1} = −ρ s₂), so Proposition 1 gives Θ − G = 0. ∎

*Proof of Theorem B′.* Let Y_{2b} = −1. If Y = Y⁻, G = Θ. Otherwise J exists.
(i) J < b: c_b = −s₂, Δ(c_b) = 0; by Proposition 1, Lemma S and κ ≥ 0, (Θ − G)/q^b ≥ s_J − 2δ_pρ > 0 (Lemma FD1).
(ii) J = b: c_b ∈ {C, −E, B}. C: ρΔ(C) = 2δ_pρ, so (Θ − G)/q^b = Σ s_j + κ ≥ 0, with equality iff Y = Y⁺ (Lemma EQ).
−E: ρΔ(E) = 4P²ρ > 2(P²+1)ρ. B: (Θ − G)/q^b = Σ_{j<b} s_j + κ − 4Pρ > 0 (Lemma FD2). ∎

## 6. Checks (all exact rational arithmetic; logs in `logs/`)

1. `colsurplus.py`: Proposition 1 against the matrix model and s_j ≥ 0, every Y, (2,2) and (2,4), several (p,q).
2. `formulas.py`: the 7 + 7 closed forms of §3–§4 and the chain/anti-checkerboard continuations against the cell definition,
   112 000 random exact points (P ≥ 4 real, Q ≥ 2 real; P = 2, Q ≥ 4; μ, m ∈ [0,1]).
3. `prove_fd.py` (+ `prove_fd_hardening.py`: strict re-certification with denominator factors having positive constant terms,
   `logs/prove_fd_hardening.log`): 137 vertex checks, 325 certified polynomials (listed in `logs/certificates.txt`), 0 failures;
   42 000 random interior points of the FD1 boxes, all positive.
4. `first_dev.py`, `fd2.py`: FD1/FD2 at the true μ-values, p, q up to 1009, b ≤ 30.
5. `lemmaS_check.py`: Lemma S and its explicit bounds, 24 000 random exact cases (arbitrary states in the cube).
6. `verify_proof.py`: replays the whole proof (identity, Lemma S, the state at J, FD1, case J = b, FD2, equality set) on every
   sign matrix for (2,2) and (2,4), 15 parameter pairs incl. non-integer (11/2, 7/2), (3, 9/2), (101,3), (3,101).
7. `direct26.py`: exhaustive integer check of Theorem B for (2,6) (9 prime pairs) and (2,8) (2 pairs): max G = Θ, exactly two
   maximisers. `h1_test.py`: Conjecture 12 exhaustively for 11 shapes × 9 prime pairs (including the negative control that the
   odd-parity shapes (2,3), (1,2), (2,1) do *not* satisfy it).

### 6.4 Independent review
`review/REVIEW_B.md` (fresh referee subagent, own code written from note.tex only, exact arithmetic): **ACCEPT WITH MINOR
REVISIONS; no blocker, no major issue; no finding affects the truth of Theorem B′/B.** The referee re-derived Proposition 1,
Lemma S (exact minimisation over the whole cube via arrangement vertices, 90 parameter pairs), the exact states, all 15 closed
forms (100 200 exact checks), the regimes, the vertex reduction (dense grid, 103 600 points) and re-certified all 137 checks /
325 polynomials with its own code (plus negative controls); replayed the proof on 232 960 sign matrices; brute-forced max G for
(2,2), (2,4), (2,6), (2,8) at 69 prime/real pairs; and computed exact graph energies from Ramanujan-sum spectra for all divisor sets
of 21 orders p²q^b (b = 2, 4, 6; up to 3²·7⁶ = 1 058 841), all agreeing with Theorem B. Findings 1–9 (a factor-2 slip in a displayed
bound of FD2(b), a missing 1/q in FD2(a), the zero set of h stated too broadly, clarity/wording points, a missing script) are
fixed in this version; finding 10 (re-run the prior-work scan before any public claim) is open; finding 11 (trust boundary: the
325 polynomial certificates) is recorded in the status table.

## 7. Remarks

* **Why the round-4 obstruction disappears.** Round 4 observed that a single non-alternating column need not pay the corner cost
  2δ_aρ (per-column ratio down to 0.38). Here only the *first* deviation (scanning from the corner column) has to pay, and at that
  column the state is known exactly (ζ_J = ±μ_{b−2−J}s₂); all other columns only need Lemma S. The bad per-column ratios come from
  columns whose state is already far from the anti-checkerboard.
* **Tightness.** Two families are asymptotically tight: the horizontal rank-one Y = s₂(1,1,−1)ᵀ (A-same deviation at J = 0,
  b = 2, q = 3, p → ∞; Θ − G = 4(p−3)) and the vertical rank-one Y = (1,1,−1)ᵀ s_bᵀ (p = 3: Θ − G = 2(d_b(q) − 5δ_b(q)),
  which is 4(q−3) at b = 2). Both margins are o(Θ); any proof must be exact on both.
* **Split by the corner sign (found on the way, not needed above).** Since sgn Z_{ab} = Y₀₀, Conjecture 12 is equivalent to
  (H1) ‖Z‖₁ − 2|Z_{ab}| ≤ Θ for Y₀₀ = Y_{ab} and (H2) ‖Z‖₁ ≤ Θ for Y₀₀ ≠ Y_{ab}. Numerically (H1) even holds for *all* Y and all
  shapes tested, including odd parity (`h1_test.py`), and so does the stronger convex form
  ‖Z‖₁ − |Z_{a,b−1}| − |Z_{ab}| + |Z_{a,b−1} + Z_{ab}| ≤ Θ (`h1_reduced.py`). A naive |corner| potential for (H1) fails
  (`h1_potential.py`).

## 8. Lean status and feasibility

**Theorem B is formalised** (separate Lean subagent launched by the main session; `lean/STATUS.md`, lock A held 06:23–07:16 UTC
and released): `ICGEqualParityB.theoremB` (energy bound with equality iff D ∈ {D⁻, D⁺∖{n}}, d_b(q) = `L1 q b sgnv`,
δ_b(q) = `Tv q b sgnv b` as in `corollaryA`), `corollaryB`, `theoremB_swap`, and the real-parameter `thmB'`. It follows §1, §2, §5
(Proposition 1, Lemma S, first deviation, cases, Lemma EQ) but replaces the regime-by-regime FD1/FD2 vertex certificates by cruder
boxes (μ, m ∈ [μ₀, 1], ρ ≤ μ₁, plus the exact ρ in the regimes J = 0, J = b−1) and FD2(b) by a two-column argument; all 325 vertex
certificates of `prove_fd.py` are additionally proved as a cross-check. Reused: `ICGBridge*`, `ICGGeneral*` (general-shape
energy identity, `L1`, `Tv`, `Zp`, `nu`), `ICGEqualParityLemmas` (Lemma P = `L1_potential`, Lemma M). This agent did not run Lean
(lock A is currently held by the main session for a release replay); it only checked the files read-only.

**Theorem C (a ≥ 3)** is not formalised. Feasible route: formalise Theorem B′_a once for general a (Proposition 1 for a+1 rows,
the uniform surplus formula, the case logic, Appendix A of `review2/REVIEW_GENERIC.md`) and check the certificate lists with a
verified checker (the lists have 10⁴–10⁷ items, too many for hand-written lemmas).

## 9. Open

* Conjecture 12 for min(a,b) ≥ 5 as a *reviewed* result; see §10 for the certified-but-unreviewed runs a = 5, 6, … . Smallest
  shapes not covered by any certificate: see the status line of §10. A structural (a-uniform) proof of FD1_a and CH_a would settle
  Conjecture 12 in full; the numerics (`general_a.py`, `general_chain.py`, `general_a56.py`) show uniform margins (FD1 ratio ≥ 1.12,
  chain ratio ≥ 1.26 for a ≤ 6).
* Formalisation of Theorem C (Theorem B is formalised, §8): a general-a Lean statement of Theorem B′_a plus a verified
  certificate checker.
* Before release: prior-work gate G3 (G1 refresh passed, `novelty/G1-refresh.md`).
* Review of the a = 5–8 certificate runs as a claim (min(a,b) ≤ 8); a structural a-uniform argument.

## 10. Extension to fixed a ≥ 3: Theorem C (computer-assisted, per a)

(Referee report `review2/REVIEW_GENERIC.md` calls this section "§11"; its fixes F1–F9 are incorporated below.)

**Theorem B′_a.** Fix a ≥ 1 and a region ℛ ∈ {(P ≥ 4, Q ≥ 2), (P = 2, Q ≥ 4)} (P = p − 1, Q = q − 1 real). Put M = T_a(p),
α = M s_a, D_a = ‖α‖₁ = d_a(p), δ_a = α_a = δ_a(p), g_t = (−1)^b s_a − 2e_a (the last column of Y⁺). Suppose the following
finite list of statements holds on ℛ (each is b-independent):
1. **(S_a)** for every c ∈ {±1}^{a+1}: q·s ≥ Q(1+μ)Δ(c) − 2μ Σ_i (‖row_i M‖₁ − Q|(Mc)_i|)^+ is > 0 for c ≠ ±s_a, and for c = ±s_a
   every term (‖row_i M‖₁ − Q|α_i|)^+ vanishes (so every cell of an alternating column is ≤ 0 on the whole cube of states).
   The bound is valid for every state ζ ∈ [−1,1]^{a+1} (|(Mζ)_i| ≤ ‖row_i M‖₁ and Paper 1 Lemma 6), nondecreasing in Q and affine
   in μ, equal to QΔ(c) ≥ 0 at μ = 0; so it is certified at Q = Q_min and μ = 1. For q ≥ 5 it is also Paper 1 Lemma 7 with the
   roles of the primes exchanged (path prime q, cell parameter Q = q − 1 ≥ 4, μ ∈ [(q−2)/q, 1] ⊂ [3/5, 1], F-side T_a(p)).
2. **(FD1_a)** s_J > 2δ_aρ for all 2^{a+1} − 1 deviations at the exact anti-checkerboard state, in the regimes

   | b | J | μ = μ_{J−1} | m = μ_{b−2−J} | ρ used |
   |---|---|---|---|---|
   | even | 0 | 1 | [μ₀, L] | exact (Q−m)/q |
   | even | b−1 | [μ₀, L] | 1 | exact (Q−μ)/q |
   | even | 1…b−2, J even | [L, μ₁] | [μ₀, L] | upper bound μ |
   | even | 1…b−2, J odd | [μ₀, L] | [L, μ₁] | upper bound m |
   | 1 | 0 | 1 | 1 | exact μ₀ |
   | odd ≥ 3 | 0 | 1 | [L, μ₁] | exact (Q−m)/q |
   | odd ≥ 3 | b−1 | [L, μ₁] | 1 | exact (Q−μ)/q |
   | odd ≥ 3 | 1…b−2 | both in [L, μ₁] or both in [μ₀, L] | | upper bound L (b−1 even ⇒ ρ < L) |
3. **(CH_a)** for every last column g ≠ g_t with g_a = −1, g ≠ −(−1)^b s_a, whose sign of 2δ_a − Δ(g) is not certified ≤ 0: the
   g-chain c_j = (−1)^{b−j}g has vanishing cells and s_j = ĉ_jΔ(g); after k = 0,…,4 chain steps the state is (−1)^kμ_{k−1}g exactly;
   with y = μ_{b−2−k} (in its parity range, or y = 1 when b = k+1) all of ĉ, ρ and the chain cost are affine in y; every deviation
   satisfies chain cost + s > (2δ_a − Δ(g))ρ; for k ≥ 5 the first five chain steps alone pay; the full chain pays via
   D̂_b/ρ_b ≥ D̂₁/μ₁ + 2 (b even), = D̂₁/μ₀ (b = 1), ≥ D̂₂/L + 2 (b odd ≥ 3) (κ ≥ 0 dropped).
4. **(EQ_a)** Δ(g_t) = 2δ_a identically, and s((−1)^b s_a) > 0 at the state g_t (m = 1) for every μ in the range of μ_{b−2}
   (a direct certificate: referee 2, finding F1; the earlier code only tested a sign pattern, which is not enough when b = 1).
Then for every b ≡ a (mod 2) and every Y ∈ {±1}^{(a+1)×(b+1)} with Y_ab = −1: G(Y) ≤ Θ, with equality exactly for Y⁻ and Y⁺.

*Proof.* Proposition 1 holds verbatim for a + 1 rows (Lemma P on each row of MY): (Θ − G)/q^b = Σ_{j<b}s_j + ρΔ(c_b) + κ − 2δ_aρ,
κ = 2((Mζ_{−1})_a)^−. The surplus at a state εm·v (v = Mg) is given by the **uniform formula** s = Q(1+μ)Δ(c)/q + (1/q)Σ_i T_i with
A = M(εc): T_i = −2μm|v_i| if A_i = 0; T_i = 0 if v_i = 0 ≠ A_i (h(A,0) = 0); T_i = 2 min{(Q−μ)m|v_i|, Q|A_i| − μm|v_i|} if
A_i v_i > 0; T_i = −2μ(m|v_i| − Q|A_i|)^+ if A_i v_i < 0 — the signs of A_i and v_i must be certified on ℛ (the provers abort
otherwise). It is concave in μ and in m separately, so vertex checks with min/max branch splitting are exact. If Y = Y⁻, G = Θ.
Otherwise let J = max{j : c_j ≠ (−1)^{j+1}s_a}. (i) J < b: the state is ζ_J = (−1)^Jμ_{b−2−J}s_a, and FD1_a with S_a and κ ≥ 0
gives Θ > G. (ii) J = b: c_b = g falls into exactly one class: Δ(g) > 2δ_a (certified strict) ⇒ Θ > G; g = g_t ⇒ Θ − G =
q^b(Σs_j + κ) ≥ 0; otherwise CH_a ⇒ Θ > G. Equality case (proof of referee 2, Appendix A, facts A1–A6 certified for a ≤ 8 in
`review2/t10_eq_symbolic.py`): along Y⁺ the path is ζ_j = (−1)^{j+1}μ_{b−2−j}s_a − 2q^{−(b−1−j)}e_a, all cells vanish and
κ(Y⁺) = 0, so G(Y⁺) = Θ; conversely, if c_b = g_t and G = Θ then all s_j = 0 and κ = 0, so every c_j = ±s_a (S_a strict part)
with all cells zero (S_a cellwise part); c_{b−1} = (−1)^{b−1}s_a by EQ_a; and inductively (Mζ_j)_a has the sign of c_{j+1}'s last
entry with |(Mζ_j)_a| ≥ (Qδ_a − p^a)/q > 0 (A5: Qδ_a > p^a), which makes the cell at coordinate a nonzero for the same-sign
choice, so c_j = (−1)^j s_a: Y = Y⁺. ∎

**Cheap last columns** (g_a = −1, Δ(g) < 2δ_a; all classifications have certified strict signs): a = 2: (1,1,−1).
a = 3: (−1,1,1,−1), (−1,−1,1,−1), plus (1,1,1,−1) when p = 3. a = 4: (1,1,−1,1,−1), (1,−1,1,1,−1), (1,−1,−1,1,−1), plus
(−1,−1,1,1,−1) when p = 3. For a = 5, 6, 7, 8: 4/7, 5/12, 6/15, 7/19 cheap columns (p ≥ 5 / p = 3).

**Implementations.** (I) ours, uniform formula: `generic_prover.py` + `generic_prover_fast.py` (sympy; a ≤ 4) and the independent
integer port `generic_fast2.py` (own polynomial arithmetic over the fixed denominators q^K(q+1)^L; identical check counts for
a = 2, 3, 4; includes the EQ_a direct certificate). (II) referee 2's `review2/c3_certify.py` (own integer arithmetic, surplus
expanded directly from the cell definition, end-to-end validation of every item at a random exact point).

**Results** (all 0 failures; logs `logs/generic_fast_a*.log`, `logs/generic_fast2_a*.log`, `review2/logs/c3_certify_a*.log`,
`crosscheck/`):

| a | (I) FD1 / CH / S / other checks | (II) | exhaustive / branch-and-bound confirmations (referee 2) | status |
|---|---|---|---|---|
| 2 | 864 / 864 / 16 / 32 | ✓ | (2,2)–(2,8) exhaustive; (2,20) B&B | Theorem B (human proof, reviewed) |
| 3 | 4 056 / 10 140 / 32 / 85 | ✓ | (3,7) exhaustive at 3 prime pairs (2^31 each); B&B up to (3,41) | **reviewed: ACCEPT w/ minor** |
| 4 | 15 648 / 54 768 / 64 / 118 | ✓ | (4,6) exhaustive at 2 prime pairs (2^34 each); B&B up to (4,40) | **reviewed: ACCEPT w/ minor** |
| 5 | 69 368 / 381 524 / 128 / 299 | ✓ | B&B (5, b ≤ 25) | certified by (I) and (II); not reviewed as a claim |
| 6 | 259 104 / 2 202 384 / 256 / 430 | ✓ | B&B (6, b ≤ 20) | certified by (I) and (II); not reviewed as a claim |
| 7 | 1 129 336 / 11 858 028 / 512 / 1 101 | ✓ (`review2/logs/c3_certify_a7.log`) | — | certified by (I) and (II); not reviewed as a claim |
| 8 | 4 182 048 / 54 366 624 / 1 024 / 1 604 | ✓ (`review2/logs/c3_certify_a8.log`, `crosscheck/logs/c3_certify_a8.log`) | B&B spot checks (referee 2) | certified by (I) and (II); not reviewed as a claim |

**Theorem C (reviewed, computer-assisted).** Conjecture 12 holds for every exponent pair (a, b) with a + b even and
min(a, b) ≤ 4, for all pairs of distinct odd primes (min = 1: Paper 1 Theorem 3; min = 2: Theorem B; min = 3, 4: Theorem B′_a
with the certified lists; transposed shapes by exchanging the primes — the two regions cover every ordered pair of distinct odd
primes with p on the a-side). **Beyond (certified, not yet reviewed as a claim):** by the same Theorem B′_a with lists certified by two independent
implementations, the same holds for min(a, b) ≤ 8; the smallest shapes not covered are then (9,9), (9,11), (10,10).

The case logic was also replayed on every sign matrix of (3,1), (1,3), (3,3), (4,2), (2,2), (2,4) (`replay_general.py`).

## 11. Files

`core.py` (copied from round 4), `fastenum.py`, `colsurplus.py`, `formulas.py`, `prove_fd.py`, `prove_fd_hardening.py`,
`first_dev.py`, `fd2.py`, `lemmaS_check.py`, `verify_proof.py`, `direct26.py` (Theorem B); `generic_prover.py`,
`generic_prover_fast.py`, `generic_fast2.py`, `replay_general.py` (Theorem C); exploration: `h1_test.py`, `h1_reduced.py`,
`h1_potential.py`, `near_extremal.py`, `case_scan.py`, `payer_scan.py`, `general_a.py`, `general_chain.py`, `general_a56.py`,
`crude_S.py`. Logs in `logs/`; referee material in `review/` (Theorem B) and `review2/` (Theorem C); `crosscheck/` = referee 2's
certifier re-run by us for a = 5–8.
