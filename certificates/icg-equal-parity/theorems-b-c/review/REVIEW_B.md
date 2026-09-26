# Referee report: Theorem B (equal parity, a = 2), `work/round6/equal-parity-a2/PROOF.md`

Reviewed file: `PROOF.md`, 246 lines, mtime 2026-09-26 01:36:51, MD5 `c3f4b90acbfb31ba8c03ac62ae616335`.
Referee: independent Claude Code referee agent, 2026-09-26. All code in this folder (`review/`) was written from the
definitions in `outputs/ICG-q3-general/note.tex`. Nothing is imported from the authors' scripts. All arithmetic is exact
(Python `Fraction`, SymPy, or int64 with asserted overflow bounds). Lean was not run.

## Overall verdict: ACCEPT WITH MINOR REVISIONS

The proof of Theorem B′ (and hence Theorem B, i.e. Conjecture 12 for n = p²q^b, b ≥ 2 even, p, q distinct odd primes) is
**correct**. I found no blocker and no major issue. Each of these parts was re-derived by hand and re-checked by my own code:

* the reduction to sign matrices;
* the column-path identity (Proposition 1);
* the one-step bound (Lemma S);
* the exact states along the anti-checkerboard and along the B-chain;
* the 7 + 8 closed forms;
* the parameter regimes;
* the vertex reduction and all 137 vertex inequalities (325 polynomials);
* the hand proofs;
* Lemma FD2(b);
* Lemma EQ and the final case split.

Independent evidence of other kinds agrees:

* exhaustive maximisation of G for the shapes (2,2), (2,4), (2,6) and (2,8), at prime and non-integer parameters;
* a graph-level check from Ramanujan-sum spectra that does not use the sign-matrix model;
* adversarial searches for larger b.

The findings are:

* one displayed inequality that is false as written (off by a factor 2; the conclusion still holds);
* one wrong constant (a typo);
* an incorrect general statement about the zero set of the cell function (harmless where it is used);
* several presentation and reproducibility points.

The computer-assisted part (FD1/FD2 vertex certificates) is a genuine trust boundary. It is routine, and my independent
re-implementation reproduces it exactly: 137 checks and 325 polynomials, all certified by the plain coefficient test,
with negative controls that fail as they should.

## Findings

| # | Severity | Location | Finding |
|---|---|---|---|
| 1 | minor (false display, conclusion OK) | §4 FD2(b), bullet "k ≥ 3" | The displayed bound 2(ĉ_{b−1}+ĉ_{b−2}+ĉ_{b−3}) − 8ρ ≥ (2/q)[(4Q+8)μ₀ − 2Q + 2QL] overstates the right-hand side by a factor 2. The correct bound, the infimum at x = μ₀, y = L, w = μ₀, is (2/q)[(2Q+4)μ₀ + QL − Q] = (1/q)[(4Q+8)μ₀ − 2Q + 2QL]. As written, the inequality fails at the true parameters in all 95 (q,b) cases tested, e.g. q = 5, b = 4: LHS 2.573 < RHS 4.693. The corrected bound is still > 0 for Q ≥ 4 (coefficient certificate), so the conclusion "the chain alone pays" stands. The authors' `prove_fd.py` certifies the correct expression. (`rv_fd_cert.py`, `rv_fd_true.py`) |
| 2 | typo | §4 FD2(a), chain column for P ≥ 4 | The value at μ = μ₀ is (4/q²)[(P−1)²Q² − P(Q²+1)], not (4/q)[…]. The sign argument is unaffected: (P−1)²Q² − P(Q²+1) ≥ 4P² − 13P + 4 > 0, with equality in the first step at P=4, Q=2. (`rv_hand.py`, `rv_fd_cert.py`) |
| 3 | minor (incorrect lemma statement, harmless use) | §0, line 36 | "For A ≠ 0: h(A,B) = 0 ⇔ −Q\|A\| ≤ B·sgn A ≤ 0" is false in general. For μ > 0, h also vanishes at B·sgn A = Q\|A\|/μ, e.g. μ = 1, A = 1, B = Q gives h = 0. For μ = 0, h vanishes on the whole ray B·sgn A < −Q\|A\|. The correct zero set for A > 0, μ > 0 is B ∈ [−QA, 0] ∪ {QA/μ}. The statement is used only in Lemma EQ, for type-A columns (the only columns with s_j = 0). There, max over the cube of \|B_i\| < Q\|A_i\| for i = 0, 1, 2 (2pP < 2QpP, 2pP < 2QP², p² < Q(P²+1)), so the extra zero is unreachable and μ ≥ μ₀ > 0. Fix the statement, or add the hypothesis \|B\| < Q\|A\|. (`rv_eq_cases.py` (c)) |
| 4 | minor (clarity) | §5 Lemma EQ | The induction says "if Mζ_j = σ(x₀,−x₁,x₂) … and c_j = −σs₂, then …". It should also say why c_j must be −σs₂: coordinate 0 alone forces it, since a zero cell needs B₀·sgn A₀ ≤ 0 with B₀ = σx₀ ≠ 0. The b−1 step does this explicitly; the general step does not. (Verified exactly: along Y⁺, for every even b ≤ 40 and every j < b, exactly one of the 8 columns has s_j = 0, and it is Y⁺'s column. `rv_eq_cases.py` (b)) |
| 5 | typo | §4 FD2(b), bullet J′ = −1 | "κ = 0 (u₀ = 1)": u₀ is Paper-1/round-4 notation and is undefined here. It should read (Mζ_{−1})₂ = ρ(p²−2) > 0. |
| 6 | minor (reproducibility) | §6 item 3 | `logs/prove_fd_hardening.log` ("strict re-certification … 42 000 random interior points") has no generating script in the folder. No `.py` file mentions it, so presumably it was run inline. Add the script, or drop the citation. (My `rv_fd_cert.py` and the dense grid in `rv_fd_true.py` (D) cover the same ground.) |
| 7 | minor (wording) | §1, end of proof of Prop. 1 | "Checked against the matrix model for every Y" should say "for every Y of shapes (2,2), (2,4) at the listed parameters". |
| 8 | minor (wording) | §2, remark after Lemma S | "it covers q = 3, which Lemma 7 does not": Lemma 7 of note.tex is stated for q ≥ 3. The point is that in Lemma 7 the cell parameter is p − 1 ≥ 4, while here it is Q = q − 1 = 2 at q = 3. Rephrase. |
| 9 | minor (presentation) | §3 "Proof of the inequality" | Add the one-line reason why separate concavity gives a vertex minimum. For fixed m the minimum over μ is at an endpoint. Then g(m) = min(f(μ_lo,m), f(μ_hi,m)) is concave, so its minimum is at an endpoint. Also say that the closed boxes [L, μ₁] × [μ₀, L] are relaxations of the half-open true ranges. Both points are correct as used (dense-grid confirmation in `rv_fd_true.py` (D)). |
| 10 | process (non-mathematical) | status table | PROOF.md itself says the prior-work check for p²q^b was not repeated in this session. Per project practice (competitor repos: trureturing, astrafala, OEIS-Settled, Park, Schreib …), re-run the literature/repository scan before any public claim. The referee did not do a literature search. |
| 11 | info (trust boundary) | §3–§4 | Most FD1/FD2 vertex cases rest on computer algebra: 325 polynomials with non-negative coefficients after P = 4+s, Q = 2+t or P = 2, Q = 4+t. This is routine and reproduced independently here. For publication, include the certificate listing (`logs/certificates.txt`) or give hand proofs of the remaining deviation types. |

No finding affects the truth of Theorem B′, Theorem B or the corollary for p^b q².

## Item-by-item verification

### 1. Reduction Theorem B′ ⇒ Theorem B: correct

* 2E − n = G(Y). This follows from X = (Y+J)/2, MJNᵀ = n e₂e_bᵀ (row sums of T_k(x) are x^k e_k) and |Z_{2b}| ≤ n (last rows of M, N are non-negative with sums p², q^b).
* Admissibility:
  * Y⁻ = −s₂s_bᵀ has corner −(−1)^{2+b} = −1 for b even, so n ∉ D⁻; p ∈ D⁻.
  * Y⁺ = s₂s_bᵀ − 2e₂e_bᵀ; 1 ∈ D⁺∖{n}.
  * Both sets are nonempty sets of proper divisors.
* Parameter ranges: distinct odd primes give either p ≥ 5, q ≥ 3 (P ≥ 4, Q ≥ 2) or p = 3, q ≥ 5 (P = 2, Q ≥ 4). The first region has no order constraint between p and q.
* Swap p^b q²: this is a relabelling of the primes. The graph check confirms the formula read in both labellings.
* Independent of Jiang–Yang Prop. 2.2 and of T_k, I computed exact graph energies from Ramanujan-sum spectra, E(D) = Σ_{g\|n} φ(n/g) \|Σ_{d∈D} c_{n/d}(g)\| with the von Sterneck formula (cross-checked against the divisor-sum definition). This covered every divisor set of 21 orders n = p²q^b:
  * b = 2: 8 orders;
  * b = 4: 9 orders, incl. 3²·5⁴, 5²·3⁴, 3²·11⁴;
  * b = 6: 4 orders, incl. 3²·5⁶ = 140625 and 3²·7⁶ = 1058841, each with 2²⁰ − 1 sets.

  In every case max E equals the Theorem B formula, and the maximisers are exactly D⁻ and D⁺∖{n}. For n ≤ 6000 the exact energies also agree with FFT spectra of the actual circulant adjacency matrices for all sets (max \|diff\| ≤ 1.5e−11). (`rv_graph.py`, `logs/rv_graph.log`)

### 2. Proposition 1 (column-path identity): correct

I re-derived it from Lemma P:

* Row i of Z is N r_i with r_i = (MY)_{i·}, so ‖row_i Z‖₁ = q^b ν(r_i) and Z_{2b} = q^b z_{−1}(r₂).
* By linearity of the path, z_j(r_i) = (Mζ_j)_i, with ζ_{b−1} = c_b and ζ_{j−1} = (ζ_j + Qc_j)/q.
* Σ_i \|r_ij\| = F_p(c_j) = D_p − Δ(c_j).
* Θ/q^b = D_p D̂ − 2δ_pρ.

Tests (`rv_prop1.py`, `logs/rv_prop1.log`):

* T_k(x) built from the note.tex definition equals the Ramanujan-sum formula φ(x^{k−i}) c_{x^{k−j}}(x^i) for k ≤ 6, x ∈ {3,5,7}.
* d_k and δ_k (definitions) equal their closed forms for k ≤ 11. The formula for T₂(p) and the type table (α(t), F_p, Δ, max\|(Mc)_i\| = (2pP, 2pP, p²)) are confirmed.
* Lemma P holds on 3,000 random real vectors.
* Proposition 1 holds exactly for **every** Y in shapes (2,2) and (2,4) at 13 parameter pairs, 216,320 matrices in total. The pairs include (11/2, 7/2), (3, 9/2), (101,3), (3,101), and two pairs outside the range, where the identity must also hold. It also holds for 1,200 random Y with b = 6, 8, 10, 12.
* z_j(r_i) = (Mζ_j)_i and ζ_j ∈ [−1,1]³ at every step.

### 3. Lemma S: correct, on the whole cube, including q = 3

Line-by-line check of each case (symbolically, `rv_lemmaS.py`):

* **A:** 2pP ≤ 2QP² (QP ≥ 2P ≥ p) and p² ≤ Q(P²+1) (2(P²+1) − (P+1)² = (P−1)²).
* **B:** p² ≤ Q(p²−2), and h₁ ≤ 4μP(p−Q)^+. The bracket is affine in μ and positive at both ends: at μ = 1 it equals 2(P−1)(P−2) at Q = 2, and its derivative in Q is 2(P−1)² + 2P > 0. If Q ≥ p, which always holds when P = 2, the bracket is Q(1+μ)(P−1)².
* **C:** p² ≤ Q(P²−1): (P−3)(P+1) > 0 for P ≥ 4, and 12 > 9 for P = 2. The chain of lower bounds ending at (4/q)(P²−P+2) is correct.
* **E:** the lower bound (8P/q)(P−μ) is correct.

All used inequalities pass the coefficient test on both regions.

**Exact adversarial minimisation** (not sampling):

* For fixed (P, Q, c), ζ ↦ s is continuous and piecewise affine. Its pieces are cut by the planes (Mζ)_i ∈ {A_i, 0, −QA_i} and the cube facets. So the exact minimum over [−1,1]³ is attained at an arrangement vertex, since every cell vertex lies on 3 independent planes. I enumerated all triples of planes (at most C(15,3) = 455 per column; fewer for C and E, where some A_i = 0) and solved them exactly. M is nonsingular: det M = −p⁴P².
* s is affine in μ and the vertex set does not depend on μ, so μ ∈ {0, 1} suffices.
* This was run for 90 parameter pairs: 81 with P ∈ {4, 4.001, 4.5, 5, 6, 10, 37/3, 50, 1000} and Q ∈ {2, 2.001, 2.5, 3, 4, 6, 10, 100, 1000}, plus 9 with P = 2 and Q ∈ {4, 4.001, …, 1000}.

Results:

* **0 violations.**
* The exact minimum for type A is exactly 0.
* The smallest q·min s for B, C, E (at P = 2, Q = 4) is 8, 40 and 64.
* The exact minimum is ≥ the hand lower bound in every case.
* Several minimisers are non-vertex points of the cube, e.g. ζ = (0, −1/2, 1) for type E, so a search over cube corners only would not have been enough.

Informative, outside the range: type B reaches min s = 0 at P = Q = 2 and is negative at (P,Q) = (3/2, 2) and (4, 3/2). So the hypotheses are used.

Lemma S is needed for arbitrary states: for j < J the state depends on arbitrary columns J..b. It holds on the whole cube, so there is no gap.

### 4. Exact states: correct

* Anti-checkerboard: ζ_J = (−1)^J μ_{b−2−J} s₂ for every J < b, b even ≤ 40, 8 values of q including non-integer ones (3,360 cases).
* The induction does not depend on the parity of b; it also holds for odd b. Evenness is used only to make the anti-checkerboard corner equal −1, i.e. c_b = −s₂ admissible.
* B-chain: ζ_j = (−1)^{j+1} μ_{b−2−j} B, all chain cells are 0, s_j = ĉ_jΔ(B), and for the full chain ζ_{−1} = ρB with κ = 0 (5,760 exact steps).
* Lemma M facts were confirmed. (`rv_states.py`, `logs/rv_states.log`)

### 5. Lemma FD1: correct

**Closed forms, re-derived by me from the case values of h.** By h(−A,−B) = h(A,B), take ε = +1. The state vector is mβ with β = α(A) = (2pP, −2P², P²+1). Cell values (h₀ | h₁ | h₂):

| deviation | h₀ | h₁ | h₂ |
|---|---|---|---|
| A same | −4(Q−μ)pPm | −4(Q−μ)P²m | −2(Q−μ)(P²+1)m |
| B same | 0 | Pm ≤ 1: −4(Q−μ)P²m; else 4P(μPm − Q) | −2(Q−μ)(P²+1)m |
| B opp | −4(Q−μ)pPm | Pm ≤ Q: 0; else 4μP(Pm − Q) | 0 |
| C same | 4μpPm | −4(Q−μ)P²m | m(P²+1) ≤ P²−1: −2(Q−μ)(P²+1)m; else 2(μm(P²+1) − Q(P²−1)) |
| C opp | 4μpPm | 0 | 0 |
| E same | 4μpPm | 4μP²m | −2(Q−μ)(P²+1)m |
| E opp | 4μpPm | 4μP²m | 0 |

with s = ĉΔ(t) − (h₀+h₁+h₂)/q. Each case split equals the min{…} of the table: the difference of the two min-arguments is Q·(switching quantity), e.g. Q(Pm−1). The side conditions of the unsplit cells hold for all m ∈ [0,1] on both regions (12 coefficient checks).

This derivation equals the raw cell definition in 100,200 exact checks, for ε = ±1 and at 3,340 parameter points, including every switching point ±10⁻⁶ and m, μ ∈ {0, 1}. The PROOF.md table, transcribed verbatim, equals it in 50,100 checks with 0 mismatches. The seven deviations plus the anti column are exactly {±1}³. (`rv_fd_forms.py`)

**Regimes:** R0, R1, R2a and R2b were checked at the true μ-values for every J < b, b even ≤ 40, 8 values of q (3,360 cases). In particular:

* J−1 and b−2−J have odd sum b−3;
* ρ = μ_{b−1} < the odd-indexed one of μ_{J−1}, μ_{b−2−J}, because odd-indexed μ's decrease strictly and both indices are ≤ b−3 < b−1.

(`rv_states.py` (d))

**Vertex reduction:** valid.

* Every form is affine or a min of affine functions in μ for fixed m, and likewise in m for fixed μ. The (·)^+ term enters as min{0, −(4μP/q)(Pm−Q)} with μ ≥ 0.
* The ρ-term is exact and affine (R0, R1) or an affine upper bound (R2).
* Separate concavity gives a minimum at a vertex (finding 9).
* At a vertex, base + Σ min(groups) > 0 iff every choice is > 0.
* A dense exact grid of 103,600 points over all relaxed boxes, at 11 (P,Q) pairs including the corners, is positive everywhere, and grid min ≥ vertex min. (`rv_fd_true.py` (D))

**Vertex inequalities, certified by my own code** (`rv_fd_cert.py`, built from my forms, not the authors'):

* The procedure substitutes P = 4+s, Q = 2+t or P = 2, Q = 4+t, factors the denominator (every factor has non-negative coefficients and a positive constant term), and requires a numerator with non-negative coefficients and a positive constant term.
* Results: 84 FD1 vertex checks, i.e. 240 polynomials, all certified by the coefficient test with no fallback needed. Each vertex expression was also evaluated exactly at random rational points.
* Negative controls are rejected, as they should be:
  * A-same at R0 with need × 1.05;
  * the same vertex on the enlarged region P, Q ≥ 2, which is 0 at p = q = 3;
  * the P = 2 chain column alone.

**Hand proofs** (`rv_hand.py`):

* **A same:** D_p − 5(P²+1) = 2(P−2) and 5(Q−1)² − (Q²+1) = 2(2Q−1)(Q−2). Equality occurs only at P = Q = 2, which is excluded. R0 is monotone in m, with the value 2(μ₀²D_p − μ₁δ_p) at μ₀. In R2 with J odd, L ≥ ½ and D_p > 2δ_p.
* **C opp:** the R0 and R1 identities hold. R2 uses 5Q(Q+1)² − 18(Q²+1) = 33t + 22t² + 5t³ ≥ 0 at Q = 2+t, and 8P² − 10P + 18 > 0.
* **E opp:** the decomposition identity holds and all terms are ≥ 0.

All three are correct.

**True values, direct from the definitions (no closed forms):**

* 58,800 cases: every J < b, b ≤ 40, 7 deviations, 20 parameter pairs.
* s_J > 2δ_pρ always.
* The minimum ratio is 1.000396 (A same, p = 1009, q = 3, b = 2, J = 0). It tends to 1, matching the authors' remark (1.0039 at p = 101). (`rv_fd_true.py` (A))

### 6. Lemma FD2: correct, with findings 1, 2 and 5

**Closed forms.** The 8-column B-chain table was re-derived (state mγ, γ = (−2pP, −2P, p²−2)). Its checks are included in the 100,200 and 50,100 counts above. The chain column has all three cells zero.

**(a) c_{b−1} not the chain column:**

* 14 vertex checks on both regions (36 polynomials) are certified.
* Chain column for P ≥ 4: 2 checks, certified, and the hand argument is correct apart from the constant in finding 2.
* True values: 3,060 cases, minimum ratio 1.80.

**(b) P = 2:**

* **J′ = −1:** D̂_b − 5ρ = D̂_{b−1} − 3ρ ≥ (3q−4)/q − 3μ₁ = (2q−6)/q² > 0. Checked exactly for b ≤ 30 and 5 values of q.
* **k ≥ 3:** correct up to finding 1.
* **k = 1:** 21 vertex checks, certified.
* **k = 2:** 14 vertex checks, certified.
* Concavity in μ was confirmed on dense grids.
* **Parity and range claims:** μ_{b−2} ∈ [μ₀, L), ρ = (Q−μ_{b−2})/q, μ_{b−3} ∈ (L, μ₁] and μ_{b−4} ∈ [μ₀, L), checked for b ≤ 40.
* **Case split:** J′ ≤ b−2 with k = b−1−J′ ≥ 1. k = 2 with J′ ≥ 0 needs b ≥ 4. For b = 2, k = 2 is exactly J′ = −1. The split is exhaustive.
* **True values:** 19,740 cases (all J′, all 7 deviations, full chain including κ). The minimum ratio is 1.000495 (full chain, p = 3, q = 1009, b = 2), matching the authors' 1.0005. For the chain alone over three columns (k ≥ 3), the minimum ratio is 1.48.

(`rv_fd_cert.py`, `rv_fd_true.py` (B), (C), `rv_hand.py`)

Total over FD1 and FD2: 137 vertex checks and 325 polynomials, which matches the authors' count exactly.

### 7. Lemma EQ and the final case analysis: correct, with findings 3 and 4

**Full replay** on every sign matrix of (2,2) and (2,4) at 14 parameter pairs, 232,960 matrices in total, including the boundary corners and (51/10, 31/10). The replay checks:

* Proposition 1;
* s_j ≥ 0 and κ ≥ 0;
* c_b ∈ {−s₂, C, −E, B};
* case (i): the state formula and s_J > 2δ_pρ, hence gap ≥ q^b(s_J − 2δ_pρ) > 0;
* case (ii): for C, gap = q^b(Σs_j + κ), and gap = 0 only at Y⁺; for −E, gap ≥ q^b(4P² − 2δ_p)ρ > 0; for B, Σs_j + κ > 4Pρ;
* the equality set is exactly {Y⁻, Y⁺}.

**Lemma EQ for general b:** for b even ≤ 40 and 8 parameter pairs:

* along Y⁺, at every j < b exactly one of the 8 columns has s_j = 0, and it is Y⁺'s column (so s_j = 0 for all j forces Y = Y⁺);
* the sign patterns are strict as claimed;
* κ(Y⁺) = 0;
* all cells of Y⁻ vanish and κ(Y⁻) = 2ρδ_p.

(`rv_eq_cases.py`, `logs/rv_eq_cases.log`)

### 8. Independent brute-force confirmation: confirmed

**Exhaustive maximum of G** over all Y with Y_{2b} = −1, in exact integer arithmetic (rational parameters scaled to integers, overflow bound asserted): 69 runs.

* (2,2): 24 pairs.
* (2,4): 24 pairs. The pairs for (2,2) and (2,4) are:
  * primes (3,5), (5,3), (3,7), (7,3), (5,7), (7,5), (3,11), (11,3), (3,101), (101,3), (11,13), (13,11), (3,1009), (1009,3);
  * real pairs (11/2, 7/2), (5, 10/3), (51/10, 31/10), (41/4, 3), (3, 11/2), (3, 51/10), (3, 41/4), (21/4, 21/4), plus the corners (5,3) and (3,5).
* (2,6): 15 pairs, including (3,101), (101,3), (1009,3), (11/2, 7/2), (3, 11/2), (51/10, 31/10), (3, 41/4).
* (2,8): 6 pairs, including (11/2, 7/2) and (3, 11/2).

In every run max G = Θ, and the maximisers are exactly {Y⁻, Y⁺}. The next value below the maximum at b = 2 reproduces the two tight families: 4(p−3) at q = 3 (gaps 8, 16, 32, 392, 4024) and 4(q−3) at p = 3. (`rv_brute.py`, `logs/rv_brute.log`)

**Graph level:** see item 1 (`rv_graph.py`).

**Larger b** (b = 10, 12, 16, 20; not exhaustive):

* all Y within Hamming distance ≤ 2 of Y⁻ or Y⁺ have G < Θ;
* the whole rank-one family g yᵀ was checked exhaustively for b ≤ 16;
* 300 greedy-ascent restarts per case never exceed Θ, and every Θ-hit is Y⁻ or Y⁺.

(`rv_search.py`, `logs/rv_search.log`)

**Tightness families (§7):**

* Θ − G(s₂(1,1,−1)ᵀ) = 4(p−3) at (2,2), q = 3.
* Θ − G((1,1,−1)ᵀs_bᵀ) = 2(d_b(q) − 5δ_b(q)) at p = 3 for b = 2, 4, 6, 8, which is 4(q−3) at b = 2.

(`rv_hand.py`)

### 9. Other checks: no hidden gap found

**Where b even is used:**

* the corner of Y⁻ is −1 (admissibility, n ∉ D⁻), and the last column of Y⁺ is C;
* the parity of the indices b−2 (even), b−1 (odd), b−3 (odd) and b−4 (even), and J−1 + b−2−J = b−3 (odd);
* the B-chain orientation c_{b−1} = −B.

Negative control: for odd b ∈ {1, 3, 5} the checkerboard s₂s_bᵀ is admissible and has G = d₂d_b > Θ, so Theorem B′ is false for odd b and evenness is essential (`rv_hand.py`).

**Off-by-one μ_{J−1} vs μ_J:** the cell at column j uses μ_{j−1}, and ĉ_j = Q(1+μ_{j−1})/q. This matches Lemma P, which I checked numerically with this indexing. All true-value checks compute from the definitions with this indexing.

**Same/opp sign conventions:** checked with ε = ±1 in every closed-form test.

**Lemma S on all states:** it is needed (states for j < J are arbitrary), and it holds on the full cube.

**Strictness at the boundaries P = 4, Q = 2 and P = 2, Q = 4:**

* all certificates have strictly positive constant terms;
* the hand-proof equality cases (P = Q = 2) are excluded;
* exact brute force at (5,3) and (3,5) gives exactly two maximisers.

**Hypotheses genuinely needed:**

* Lemma S fails at P = 3/2 or Q = 3/2 (informative run).
* The A-same certificate fails on P, Q ≥ 2: the gap is 0 at p = q = 3.

**Non-mathematical remarks.** The folder now contains new scripts for a ≥ 3 (`general_a*.py`, `generic_prover*.py`, `replay_general.py`, created after PROOF.md). They are outside the scope of this review and were not examined. The §7 remarks on (H1)/(H2) are explicitly "not needed" and were not reviewed.

## Suggested fixes

1. §4 FD2(b), k ≥ 3: replace the displayed bound by (2/q)[(2Q+4)μ₀ + QL − Q] (or (1/q)[(4Q+8)μ₀ − 2Q + 2QL]).
2. §4 FD2(a): replace (4/q)[(P−1)²Q² − P(Q²+1)] with (4/q²)[…].
3. §0: state the zero set of h correctly (A > 0, μ > 0: B ∈ [−QA, 0] ∪ {QA/μ}), or restrict the "⇔" to \|B\| < Q\|A\|/μ. Note in Lemma EQ that type-A columns satisfy max\|B_i\| < Q\|A_i\|.
4. §5 Lemma EQ: say explicitly that coordinate 0 forces c_j = −σs₂ at each step.
5. §4 FD2(b), J′ = −1: replace "(u₀ = 1)" with "((Mζ_{−1})₂ = ρ(p²−2) > 0)".
6. §3: add the one-line separate-concavity ⇒ vertex argument, and note that the closed boxes relax the half-open true ranges.
7. §1 and §2: fix the wording of findings 7 and 8.
8. Add the script that produced `logs/prove_fd_hardening.log`, or remove the citation. For publication, include the 325-polynomial certificate listing.
9. Before any public claim, re-run the prior-work scan for p²q^b (finding 10).

## Files (all in `review/`)

| script | what it checks | log |
|---|---|---|
| `rv_common.py` | own exact helpers: T_k from the definition and from Ramanujan sums, path, potential, h, G, Θ | — |
| `rv_prop1.py` | basic facts, type table, Lemma P, Proposition 1 (all Y of (2,2), (2,4); random up to b = 12) | `logs/rv_prop1.log` |
| `rv_lemmaS.py` | Lemma S: exact cube minimisation by arrangement vertices; hand-proof inequalities; out-of-range behaviour | `logs/rv_lemmaS.log` |
| `rv_states.py` | exact states (anti-checkerboard, B-chain), Lemma M, FD1/FD2 regimes at true μ-values | `logs/rv_states.log` |
| `rv_fd_forms.py` | own cell-by-cell derivation vs definition vs PROOF.md tables; min-structure; completeness | `logs/rv_fd_forms.log` |
| `rv_fd_cert.py` | own certification of all 137 vertex checks (325 polynomials) + negative controls + findings 1, 2 | `logs/rv_fd_cert.log` |
| `rv_fd_true.py` | FD1/FD2 at true parameters from definitions (b ≤ 40); dense-grid check of vertex reduction; finding 1 | `logs/rv_fd_true.log` |
| `rv_hand.py` | hand proofs (A same, C opp, E opp, FD2 J′=−1, FD2(a) chain), tightness families, odd-b control | `logs/rv_hand.log` |
| `rv_eq_cases.py` | full proof replay on all Y of (2,2), (2,4); Lemma EQ for b ≤ 40; finding 3 | `logs/rv_eq_cases.log` |
| `rv_brute.py` | exhaustive max G for (2,2), (2,4), (2,6), (2,8), primes and reals | `logs/rv_brute.log` |
| `rv_graph.py` | graph energies from Ramanujan spectra (+ FFT), 21 orders, all divisor sets | `logs/rv_graph.log` |
| `rv_search.py` | b = 10–20: Hamming-2 neighbourhoods, rank-one family, greedy ascent | `logs/rv_search.log` |
| `run_all.sh` | reruns everything (~5 min CPU) | — |

Final end-to-end rerun with `run_all.sh` on 2026-09-26: exit code 0, 314 s CPU (15 min wall-clock on a machine shared with
the authors' concurrent jobs). Every log ends in `DONE`/`ALL OK`, and every number quoted above is taken from these logs.
