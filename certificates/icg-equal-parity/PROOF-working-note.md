# Equal-parity exponents: maximal energy of ICG(p^a q^b), a + b even

Round 4 working note (2026-09-26). Builds on `work/round3/icg-q3/q3-proof.md` (Lemmas 1–3, notation) and
`outputs/ICG-q3-general/note.tex` (Conjecture "Exponents of equal parity").
Revised 2026-09-26T03:0xZ after the independent referee report `review/REVIEW_A.md` (no blocker, no mathematical
error; minor findings 1–7 addressed below).

## Status table

| Item | Literature | Statement | Mathematics | Formal (Lean 4.33.1) |
|---|---|---|---|---|
| Conjecture, all a + b even | not found (`literature.md`) | as in note.tex | **open** in general | — |
| n = pq (a = b = 1) | implicitly known (Ilić 2009 + Ilić–Bašić 2011 formulas; no explicit statement found) | E_max = 4(p−1)(q−1), maximisers {1}, {p,q} | special case m = 1 of Theorem A | covered by `corollaryA` (m = 1) |
| **Theorem A / Corollary A**: n = p q^m and n = p^m q, m odd, all distinct odd primes | not found | exact E_max and exactly two maximisers | **complete human proof** (§1–§2); independent referee: no error; exact step checks | **fully formalised**: `ICGEqualParity.corollaryA` (admissibility of both sets, value, both attain, maximality, uniqueness) for n = p·q^m; n = p^m·q is the same theorem with the primes exchanged. Axioms: propext, Classical.choice, Quot.sound; clean-directory rebuild passed |
| **Part B**: shapes (2,2), (2,4), (4,2), (2,6), (6,2), (2,8), (8,2), (3,3), (3,5), (5,3), (4,4), all distinct odd primes | not found | exact E_max and exactly two maximisers | **computer-assisted exact proof** (polynomial certificates, §3) | not formalised |
| Rank-one reduction, tightness (general a, b) | — | Lemma R, Remark T | proved / computed | — |

## 0. Notation and the reduction to sign matrices

For real x > 2, P = x − 1 and w ∈ R^{m+1}, the path is z_{m−1} = w_m, z_{k−1} = (z_k + P w_k)/x (k = m−1, …, 0).
By Lemma 1 of q3-proof.md, ‖T_m(x) w‖₁ = x^m N_x(w) with

  N_x(w) := |z_{−1}| + Σ_{k=0}^{m−1} |z_{k−1} − z_k|,   and (T_m(x) w)_m = x^m z_{−1}(w).

Potential: μ_{−1} = 1, μ_k = (P − μ_{k−1})/x; c_k = P(1 + μ_{k−1})/x (0 ≤ k < m); ĉ_k = c_k (k < m), ĉ_m = μ_{m−1} =: ρ = ρ_m(x);
D̂ = D̂_m(x) := Σ_{k=0}^{m} ĉ_k = d_m(x)/x^m, and x^m ρ_m(x) = δ_m(x) = (x^m(x−1) + 2(−1)^m)/(x+1).
Cell function (Lemma 3 of q3-proof.md): h_μ(A,B) = P|A−B| + μ|B+PA| − (P−μ)|B| − P(1+μ)|A|, and h_μ(A,B) ≤ 2μ·max(0, |B| − P|A|)
for 0 ≤ μ ≤ 1 ≤ P (valid also at P = 2). We use h_μ(0,B) = 2μ|B| and, for 0 ≤ B ≤ A, h_μ(A,B) = −2(P−μ)B.

Graph ↔ sign matrices. For n = p^a q^b, X the 0/1 divisor matrix (x_ab = 0), Y = 2X − J and Z = T_a(p) Y T_b(q)ᵀ,
Jiang–Yang Prop. 2.2 and T_a(p)1 = p^a e_a give 2E(ICG_n(D)) = ‖n e_a e_bᵀ + Z‖₁ and, since |Z_ab| ≤ n,

  G(Y) := 2E − n = Σ_{(i,j)≠(a,b)} |Z_ij| + Z_ab = ‖Z‖₁ − 2 (Z_ab)^−.

The Conjecture (a + b even) is equivalent to: max{G(Y) : Y ∈ {±1}^{(a+1)×(b+1)}, Y_ab = −1} = d_a(p)d_b(q) − 2δ_a(p)δ_b(q), attained exactly
at the anti-checkerboard Y = −s_a s_bᵀ and the truncated checkerboard Y = s_a s_bᵀ − 2 e_a e_bᵀ (both correspond to nonempty D).

(Notation warning, referee finding 7: in §2 the letters 𝒜 and 𝒟 denote index sets of positions where the two rows agree / differ;
they are unrelated to divisor sets D and energies E.)

## 1. One-dimensional lemmas

**Lemma P (potential identity for real vectors).** For every w ∈ R^{m+1},
  N_x(w) = Σ_{k=0}^{m} ĉ_k |w_k| + (1/x) Σ_{k=0}^{m−1} h_{μ_{k−1}}(w_k, z_k(w)).

*Proof.* z_{k−1} − z_k = (P/x)(w_k − z_k), |z_{k−1}| = |z_k + P w_k|/x and x μ_k = P − μ_{k−1} give, for each k < m,
|z_{k−1} − z_k| + μ_{k−1}|z_{k−1}| − μ_k|z_k| = (1/x)[h_{μ_{k−1}}(w_k, z_k) + P(1+μ_{k−1})|w_k|]. Summing, the potential terms
telescope to μ_{−1}|z_{−1}| − μ_{m−1}|z_{m−1}| = |z_{−1}| − ρ|w_m|. ∎  (Lean: `L1_potential`.)

Lemma 2 of q3-proof.md (sign vectors y, x > 2): sgn z_j(y) = y_{j+1}, |z_j(y)| ∈ [(x−2)/x, 1], and
N_x(y) = D̂ − 2σ(y), σ(y) := Σ_{j ∈ NA(y)} μ_j |z_j(y)|, NA(y) = {0 ≤ j < m : y_j = y_{j+1}}.

**Lemma M.** With L = P/(x+1): μ_k − L = (−1/x)^{k+1}(1 − L). Hence μ_k > L for odd k ≥ −1, μ_k < L for even k ≥ 0,
μ_k ≥ μ_0 = (x−2)/x for all k ≥ 0, and (since |μ_k − L| decreases) μ_k ≤ μ_1 for all k ≥ 0.

*Proof.* μ_k − L = −(μ_{k−1} − L)/x because L = (P − L)/x, and μ_{−1} − L = 1 − L > 0. ∎  (Lean: `nu_sub_L`, `nu_even_gt`,
`nu_odd_lt`, `nu_even_le_two`; Lean's `nu x k` is μ_{k−1}.)

**Lemma C′ (the non-corner part).** For x > 2 and every sign vector y ∈ {±1}^{m+1},
  N_x(y) − |z_{−1}(y)| = Σ_{k=0}^{m−1} |z_{k−1}(y) − z_k(y)| ≤ D̂ − ρ,
with equality iff y = ±s_m.

*Proof.* Run the proof of Lemma 2 with the potential μ′_{−1} = 0, μ′_k = (P − μ′_{k−1})/x (so μ′_k ∈ (0, P/x] for k ≥ 0).
The computation of Lemma 2 only uses x μ′_k = P − μ′_{k−1} and the sign facts, hence for each k:
|z_{k−1} − z_k| + μ′_{k−1}|z_{k−1}| − μ′_k|z_k| = c′_k − [k ∈ NA(y)]·2μ′_k|z_k|, c′_k = P(1+μ′_{k−1})/x.
Telescoping (μ′_{−1} = 0, |z_{m−1}| = 1): Σ_k|z_{k−1} − z_k| = Σ_k c′_k + μ′_{m−1} − 2Σ_{NA} μ′_k |z_k|.
The right side is maximal exactly when NA(y) = ∅, i.e. y = ±s_m, and there the left side equals N_x(s) − |z_{−1}(s)| = D̂ − ρ. ∎
(Lean: `noncorner_le`, `noncorner_sgnv`.)

**Lemma B (a parity defect costs enough).** Let x ≥ 3, R ≥ 1, m ≥ 1 odd and y a sign vector with y_0 = y_m. Then (3R − 1) σ(y) > (R − 1) ρ.

*Proof.* Since m is odd and y_0 = y_m, y is not alternating; let J = max NA(y). On J+1..m the vector alternates, so the recursion
|z_{k−1}| = (P − |z_k|)/x from |z_{m−1}| = 1 gives |z_J(y)| = μ_{m−2−J}, and σ(y) ≥ μ_J μ_{m−2−J}.
If J = m−1 this is ρ·1 and (3R−1)ρ > (R−1)ρ. If J ≤ m−2, the indices J and m−2−J are ≥ 0 and have opposite parity (their sum
m−2 is odd), so by Lemma M one factor exceeds L and the other is ≥ μ_0: σ(y) > μ_0 L. Also ρ = μ_{m−1} < L (m−1 even).
Finally (3R−1)μ_0 ≥ R−1, i.e. (3R−1)(x−2) ≥ (R−1)x ⟺ 2R(x−3) + 2 ≥ 0. So (3R−1)σ(y) > (3R−1)μ_0 L ≥ (R−1)L ≥ (R−1)ρ. ∎
(Lean: `lemmaB`.)

## 2. Theorem A (one exponent equal to 1)

**Theorem A (sign-matrix form).** Let m ≥ 1 be odd and let x, R be real with either (x ≥ 5, R ≥ 2) or (x = 3, R ≥ 4).
Put r = R + 1, M = T_1(r), N = T_m(x). For every Y ∈ {±1}^{2×(m+1)} with Y_{1,m} = −1,

  G(Y) = Σ_{(i,j)≠(1,m)} |(M Y Nᵀ)_ij| + (M Y Nᵀ)_{1m} ≤ d_1(r) d_m(x) − 2 δ_1(r) δ_m(x),

with equality iff Y = −s_1 s_mᵀ (anti-checkerboard) or Y = s_1 s_mᵀ − 2 e_1 e_mᵀ (truncated checkerboard).
(d_1(r) = 3r − 4 = 3R − 1, δ_1(r) = r − 2 = R − 1.) The ranges are sufficient, not sharp (referee: the statement also holds e.g. at
x = 3, R ∈ [5/2, 39/10] and for some x ∈ (3,5); it fails at x = 3, R ≤ 3/2 and at x ≥ 5, R ≤ 5/4).

**Corollary A (graphs).** Let p, q be distinct odd primes and m ≥ 1 odd.
* For n = p q^m: E_max(n) = ½[n + (3p − 4) d_m(q)] − (p − 2) δ_m(q).
* For n = p^m q: E_max(n) = ½[n + (3q − 4) d_m(p)] − (q − 2) δ_m(p).
In both cases the maximum is attained exactly by D = {p^i q^j : i + j odd} and D = {p^i q^j : i + j even} \ {n}.
(m = 1 gives E_max(pq) = 4(p−1)(q−1), cf. `literature.md`.)

*Proof of the corollary.* For n = p q^m apply Theorem A with r = p (row side, exponent 1) and x = q (exponent m): if q ≥ 5 then
R = p − 1 ≥ 2; if q = 3 then p ≥ 5 and R ≥ 4. Every admissible D gives Y with Y_{1m} = −1 and G(Y) = 2E − n; the two extremal Y
correspond to nonempty D. For n = p^m q exchange the names of the primes (E(ICG_n(D)) is invariant under X ↦ Xᵀ). ∎

### Proof of Theorem A

Write u = (Y_{0,j})_j, v = (Y_{1,j})_j, so v_m = −1. Since T_1(r) = [[−R, R], [R, 1]], the rows of Z = M Y Nᵀ are
−R·N(u − v) and N(Ru + v). With w1 := u − v ∈ {0, ±2}^{m+1} and w2 := Ru + v and N_x = ‖N·‖₁/x^m:

  G(Y)/x^m = Φ(u,v) := R·N_x(w1) + N_x(w2) − 2 (z_{−1}(w2))^−.        (1)

Let 𝒜 = {k : u_k = v_k} and 𝒟 = {k : u_k ≠ v_k}. Then w1_k = 0, |w2_k| = R+1 on 𝒜 and |w1_k| = 2, |w2_k| = R−1 on 𝒟, so
R|w1_k| + |w2_k| = 3R−1 on 𝒟 and R+1 on 𝒜. Lemma P applied to w1 and w2 gives the exact identity

  Φ(u,v) = (3R−1)D̂ − 2(R−1)Σ_{k∈𝒜} ĉ_k + H − 2(z_{−1}(w2))^−,
  H := (1/x) Σ_{k<m} [ R·h_{μ_{k−1}}(w1_k, z_k(w1)) + h_{μ_{k−1}}(w2_k, z_k(w2)) ].

The target divided by x^m is (3R−1)D̂ − 2(R−1)ρ with ρ = ĉ_m. So Theorem A is equivalent to

  H − 2(z_{−1}(w2))^− ≤ 2(R−1)[Σ_{k∈𝒜} ĉ_k − ĉ_m].        (†)

Signs of the cells (all by Lemma 3):
* (S1) w2-cells: |w2_k| ≥ R−1 and |z_k(w2)| ≤ R+1 ≤ P(R−1) (this is R ≥ x/(x−2); true in both parameter ranges), so h ≤ 0.
* (S2) w1-cells with k ∈ 𝒟: |w1_k| = 2 ≥ |z_k(w1)|, so |z_k(w1)| ≤ P|w1_k| and h ≤ 0.
* (S3) w1-cells with k ∈ 𝒜: h(0, B) = 2μ|B|, so the cell contributes (2R/x) μ_{k−1} |z_k(w1)| ≤ (4R/x) μ_{k−1}.
For k ∈ 𝒜, k < m define the surplus s_k := 2(R−1)c_k − (2R/x) μ_{k−1}|z_k(w1)| ≥ (2/x)[(R−1)P(1+μ) − 2Rμ]_{μ=μ_{k−1}}.
The bracket is linear in μ ∈ [μ_0, 1] and positive at both ends in our ranges (at μ = 1 it is 2[R(P−1) − P] > 0), so **s_k > 0**.
Hence (†) follows once we show

  Σ_{k∈𝒜, k<m} s_k + [−(R/x) Σ_{k∈𝒟,k<m} h(w1_k, ·)] + [−(1/x)Σ_k h(w2_k, ·)] + 2(z_{−1}(w2))^− ≥ 2(R−1)(ĉ_m − [m∈𝒜] ĉ_m),   (2)

where all four groups on the left are ≥ 0.

**Case I: m ∈ 𝒜** (u_m = v_m = −1). The right side of (2) is 0; done. Equality requires 𝒜 = {m} (each s_k > 0), every cell
and the corner term zero. The corner term vanishes iff z_{−1}(w2) ≥ 0 iff u_0 = +1 (the sign of z_{−1}(w2) is that of w2_0 because
P(R−1) > R+1). For k ≤ m−2 the state z_k(w1) (a weighted average of 2u_{k+1}, …, 2u_{m−1}, 0 with weight P/x > ½ on 2u_{k+1}) is nonzero
with sign u_{k+1}; if u_k = u_{k+1} the 𝒟-cell equals −2(P−μ)|z_k(w1)| < 0. So equality forces u to alternate on 0..m−1 with u_0 = 1,
u_m = −1 and v = −u except v_m = −1: the truncated checkerboard. Conversely, for the truncated checkerboard 𝒜 = {m} and u alternates,
so every w1 𝒟-cell has A, B of opposite signs or B = 0 (h = 0); every w2-cell has opposite signs with |B| ≤ P|A| (h = 0), because
P(R−1) > R+1 makes z_k(w2) carry the sign u_{k+1}; and the corner term vanishes because u_0 = 1. Hence Φ equals the target.

**Case II: m ∈ 𝒟 and 𝒜 ≠ ∅** (so u_m = +1 and 𝒜 ⊆ {0,…,m−1}). It suffices that s_{k0} ≥ 2(R−1)ρ, strictly, for some k0 ∈ 𝒜.
Using ρ = μ_{m−1} < L = P/(P+2) (Lemma M, m−1 even) and |z_{k0}(w1)| ≤ 2, it suffices that, with μ = μ_{k0−1},

  (R−1)P[1 + μ(P+2)] − 2Rμ(P+2) = (R−1)P + μ(P+2)[R(P−2) − P] ≥ 0.

* x ≥ 5 (P ≥ 4), R ≥ 2: R(P−2) ≥ 2(P−2) ≥ P, so the expression is ≥ (R−1)P > 0 (for every k0 ∈ 𝒜).
* x = 3 (P = 2): the expression is 2(R−1) − 8μ. If some k0 ∈ 𝒜 has k0 ≥ 1 then μ = μ_{k0−1} ≤ μ_1 = 5/9 (Lemma M) and
  2(R−1) − 40/9 > 0 for R ≥ 4. Otherwise 𝒜 = {0}. If m = 1: z_0(w1) = w1_1 = 2u_1, s_0 = (2/3)(2R − 4) and 2(R−1)ρ = 2(R−1)/3 < s_0
  for R > 3. If m ≥ 3: s_0 = (2/3)[4(R−1) − 2R|z_0(u)|] (here w1 = 2u on 1..m). If |z_0(u)| ≤ 5(R−1)/(4R) then s_0 ≥ R−1 > 2(R−1)ρ
  (ρ < 1/2). Otherwise |z_0(u)| > 15/16 > 5/9 forces u_1 = u_2 (an alternation at 1 gives |z_0(u)| ≤ (2 − 1/3)/3 = 5/9), and
  position 1 ∈ 𝒟: its w1-cell is h(2u_1, 2z_1(u)) with equal signs and |2z_1(u)| ≤ 2, i.e. −2(P − μ_0)·2|z_1(u)| = −(20/3)|z_1(u)|.
  So the 𝒟-group contributes ≥ (R/3)(20/3)(1/3) = 20R/27, and s_0 + 20R/27 ≥ (2/3)(2R − 4) + 20R/27 = (56R − 72)/27 > R − 1.
  (Referee: this refinement is genuinely needed at R = 4; the guaranteed margin (R−1)(1 − 2ρ) = (R−1)3^{−m} is positive but tends to 0.)
All inequalities are strict, so Case II never attains equality.

**Case III: 𝒜 = ∅** (v = −u, u_m = +1). Then w1 = 2u, w2 = (R−1)u and (1) reads Φ = (3R−1) N_x(u) − 2(R−1)(z_{−1}(u))^−.
* IIIa, u_0 = +1: Φ = (3R−1)(D̂ − 2σ(u)). Here u_0 = u_m with m odd, so Lemma B gives (3R−1)σ(u) > (R−1)ρ, i.e. Φ < target/x^m.
* IIIb, u_0 = −1: Φ = (R+1)N_x(u) + 2(R−1)[N_x(u) − |z_{−1}(u)|] ≤ (R+1)D̂ + 2(R−1)(D̂ − ρ) = target/x^m by Lemma 2 and Lemma C′,
  with equality iff u = ±s_m, i.e. u = −s_m (u_0 = −1): the anti-checkerboard Y = −s_1 s_mᵀ. ∎

**Verification of §1–§2.**
* `verify_1m.py` (authors): exact, every (u, v), m ∈ {1,3,5,7}, 18 parameter pairs (incl. non-integers): reduction (1) vs the matrix
  model, Lemma P, (S1)–(S3), the decomposition, Case I/III claims, the equality set; for Case II it checks that *some* surplus reaches
  2(R−1)ρ (non-strictly) and otherwise the combined x = 3 bound; for IIIb it checks an older "deviation formula" argument instead of
  Lemma C′ as written (referee finding 3). Log `logs/verify_1m.log`.
* `review/steps_check.py`, `review/lemmas_check.py`, `review/random_check.py`, `review/fragile_check.py` (independent referee, own
  Ramanujan-sum model): **every intermediate claim exactly as written**, incl. Lemma C′ via μ′, Case II for every k0, and each sub-claim of
  the x = 3 refinement (68 + 78 runs, 0 failures); Theorem A exhaustively for m ≤ 11; Corollary A against graph spectra for 35 values of
  n up to 234375 (`review/REVIEW_A.md`, `review/logs/`).
* `fft_check_A.py`: Corollary A against FFT spectra of the actual circulants and dense `eigvalsh` for n ≤ 700 (10 values of n,
  all nonempty divisor sets). Log `logs/fft_check_A.log`.
* Lean: §4.

## 3. Part B: finite shapes by exact polynomial certificates

For a fixed shape (a, b) substitute p = 5 + s, q = 3 + t (s, t ≥ 0 real). Every entry Z_ij(Y) of Z = T_a(p) Y T_b(q)ᵀ is a polynomial
in (s, t) with integer coefficients, and G(Y) = max over sign patterns S with S_ab = +1 of Σ S_ij Z_ij. **Certificate:** for every Y
with Y_ab = −1, entries whose coefficients are all ≥ 0 (resp. ≤ 0) get S_ij = +1 (resp. −1) (they have that sign on the whole
region); every remaining entry is bounded coefficientwise by the absolute values of its coefficients; the resulting polynomial
target − (bound) is shown to have all coefficients ≥ 0 and a positive constant term. Hence target − G(Y) > 0 on the whole region for
every Y except the two conjectured maximisers, for which target − G(Y) ≡ 0 (the fallback branch treats these two exactly).
This proves G(Y) ≤ target with exactly two maximisers for **all real p ≥ 5, q ≥ 3**. Since E is invariant under transposition
(exchange of the primes), the shape (a, b) with p ≥ 5, q ≥ 3 together with the shape (b, a) with p ≥ 5, q ≥ 3 covers all pairs of distinct
odd primes (p = 3 forces q ≥ 5).

**Result (computer-assisted, exact integer arithmetic).** The Conjecture holds, with exactly the two stated maximisers, for all distinct
odd primes and the shapes (2,2), (2,4), (4,2), (2,6), (6,2), (2,8), (8,2), (3,3), (3,5), (5,3), (4,4)
(all passed, `logs/cert_small.log`, `logs/cert_fast_small.log`, `logs/cert_fast_large.log`). Together with Theorem A this covers every
equal-parity shape with (a+1)(b+1) ≤ 27, and all shapes (1, m), (m, 1).

Checks: `cert22.py` (pure-Python dict polynomials, one branch per undetermined sign) and `cert_fast.py` (vectorised numpy, coefficientwise
bound, overflow guard asserted) agree on (1,1), (1,3), (2,2), (2,4), (4,2), (3,3); `cert_sanity.py` checks the polynomial T-matrices
against the exact model at sample points and the rank-one gap 4(p−3); a negative control (target − 1) is correctly rejected;
`cert_sympy_check.py` is an independent sympy re-implementation (T from the Ramanujan-sum definition, target recomputed and compared with
the closed form) and confirms (1,3), (2,2), (3,3), (2,4) [and (4,2), see `logs/cert_sympy_more.log`].
Logs: `logs/cert_small.log`, `logs/cert_fast_small.log`, `logs/cert_fast_large.log`, `logs/cert_sympy_22.log`, `logs/cert_sympy_13.log`,
`logs/cert_sympy_more.log`.

Trust boundary: Part B is a finite machine computation (Python), not formalised; its correctness rests on the two agreeing implementations
plus the independent sympy check.

## 4. Lean formalisation (Theorem A and Corollary A)

Files (new, in `work/research-lean/Research/`, building on `ICGGeneral*` without modifying them; 2251 lines):
* `ICGEqualParityLemmas.lean` (400 lines): Lemma P (`L1_potential`), Lemma M (`nu_sub_L`, `nu_even_gt`, `nu_odd_lt`, `nu_even_le_two`),
  alternating tails (`Zp_alt_tail`, `Zp_sgnv_zero`), Lemma C′ (`noncorner_le`, `noncorner_sgnv`, via the potential `nuc x 0`), Lemma B
  (`lemmaB`).
* `ICGEqualParityA.lean` (581 lines): `thmA_le` — for real x, R with (x ≥ 5 ∧ R ≥ 2) ∨ (x = 3 ∧ R ≥ 4), odd m, sign vectors u, v with
  v_m = −1: R‖T_m(x)(u−v)‖₁ + ‖T_m(x)(Ru+v)‖₁ − 2x^m max(0, −z_{−1}(Ru+v)) ≤ (3R−1)‖T_m(x)s‖₁ − 2(R−1)(T_m(x)s)_m.
  All cases I, II (incl. the x = 3 refinement `refine_x3`), III.
* `ICGEqualParityGraph.lean` (292 lines): the two-row energy identity `two_L1mat_rows`; `energy_anti` (value of D⁻);
  `energy_le_anti` (maximality); `DantiPQ_subset` (D⁻ admissible).
* `ICGEqualParityUnique.lean` (978 lines): `thmA_lt` (strict inequality unless (u,v) is the anti- or the truncated checkerboard);
  `trunc_value`, `energy_trunc` (D⁺ \ {n} attains the same energy); `energy_lt_anti` (every other admissible D is strictly worse);
  `DtruncPQ_subset`; and the combined statement

  `corollaryA (p q m) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp3 : 3 ≤ p) (hq3 : 3 ≤ q) (hm : Odd m)`:
  D⁻ ⊆ properDivisors(p q^m) ∧ D⁺∖{n} ⊆ properDivisors(p q^m) ∧
  2·E(ICG(p q^m, D⁻)) = p q^m + (3p−4)·‖T_m(q)s‖₁ − 2(p−2)·(T_m(q)s)_m ∧ E(ICG(p q^m, D⁺∖{n})) = E(ICG(p q^m, D⁻)) ∧
  ∀ D ⊆ properDivisors(p q^m), E(D) ≤ E(D⁻) ∧ (E(D) = E(D⁻) → D = D⁻ ∨ D = D⁺∖{n}).

  Here E is the genuine graph energy (`ICGBridge.energy`: sum of absolute values of the Hermitian eigenvalues of the adjacency matrix
  `ICGBridge.icgAdj n D`, entry 1 iff gcd((j−i) mod n, n) ∈ D), as in round 3; d_m(q) and δ_m(q) appear as ‖T_m(q)s‖₁ and
  (T_m(q)s)_m (their closed forms are JY (1.4), (3.4) / note.tex Remark `rem:closed`, not re-formalised here). The case n = p^m q is
  `corollaryA q p m …`, since q·p^m is the same natural number and D⁻, D⁺∖{n} are the same sets.
* Audit: `#print axioms` for `thmA_le`, `thmA_lt`, `energy_le_anti`, `energy_lt_anti`, `energy_anti`, `energy_trunc`, `trunc_value`,
  `corollaryA`, `lemmaB`, `noncorner_le`, `L1_potential`: propext, Classical.choice, Quot.sound only. No `sorry`, no `native_decide`.
* Builds: `lake build Research.ICGEqualParityLemmas Research.ICGEqualParityA Research.ICGEqualParityGraph Research.ICGEqualParityUnique`
  in `work/research-lean` (exit 0, `lean-logs/build.log`); clean-directory replay (fresh copies of the 12 source files of the import
  closure, Mathlib `0df444a3` packages linked, all research modules rebuilt from source; exit 0, `lean-logs/clean-replay-build.log`).
  SHA-256 of the four new files: `lean-logs/sha256.txt`. Note: a single-file `lake env lean` does not apply the package option
  `autoImplicit = false`; only `lake build` results are claimed.
* Not formalised: Part B (finite certificates) and the closed forms of d_m, δ_m.

## 5. What remains open, and why (general a, b)

**Lemma R (rank one).** If every column of Y is ±s_a, i.e. Y = s_a yᵀ, then Z = (T_a s_a)(T_b y)ᵀ, Z_ab = δ_a q^b z_{−1}(y) and
G(Y) = d_a q^b N_q(y) − 2δ_a q^b (z_{−1}(y))^−. The Conjecture restricted to such Y is a 1D statement; for y_0 = +1 it reduces (last NA J)
to D̂_a(p)·μ^q_J μ^q_{b−2−J} ≥ ρ_a(p) ρ_b(q).

**Remark T (asymptotic tightness).** For (a,b) = (2,2), q = 3 the rank-one matrix Y = s_2 (1,1,−1)ᵀ has target − G(Y) = 4(p − 3) exactly
(checked for p = 5, 7, 11, 40, 1000, 13/2; `logs/top_configs.log`, `cert_sanity.py`), while the target grows like 25p². Equivalently
D̂_2(p) (μ^3_0)² − ρ_2(p) ρ_2(3) = (2/9)(p−3)/p². So any proof must be exact on the rank-one family.

**Why the Part-A method does not extend directly** (exact data, `qpath_decomp.py`, `percol_probe.py`, logs):
* In the column-path accounting (path over the q side, F-side T_a(p)) the per-column slack s_k is ≥ 0 for every column k < b in all
  tested shapes ((2,2),(2,4),(4,2),(3,3),(1,3),(3,1) with p, q ∈ {3,5,7,40}); but a single non-alternating column k < b does *not* always
  pay the full corner cost 2δ_aρ_b/q^b (ratio down to 0.38 at p = 5 or q = 5 small; ≥ 1.1 at p = 40). For a = 1 the non-alternating
  inputs of T_1 have deficit exactly 2δ_1, which is what makes Case I and II of Theorem A work; for a ≥ 2 a non-alternating column of
  T_a(p) can have deficit 2p^a μ_0 μ_{a−2}-type < 2δ_a.
* A single "signed potential" μ_k F(ζ) − 2λ_k(ε_k ξ_{−1}(ζ))^− fails (`potential1d_test.py`): it over-deducts at states whose two coordinates
  have the same sign; the correct value function has a min-structure (continue the anti pattern vs. pay a cheap parity switch).
* With the path over the side x = 3 and F-side prime ≥ 5, the one-step bound of Theorem 5 held in all tested small shapes
  (`step_path3.py`) — suggestive for a general proof, not proved.

## 6. Files

* `core.py` — exact model helpers (T_k(x), μ, δ, d, G, target).
* `scan_real.py`, `top_configs.py`, `case_split.py` — scans and near-extremal configurations.
* `oned_two_vector.py`, `verify_1m.py`, `fft_check_A.py` — Theorem A reduction, step checks, spectral check.
* `cert22.py`, `cert_fast.py`, `cert_sanity.py`, `cert_sympy_check.py` — Part B certificates and cross-checks.
* `potential1d_test.py`, `qpath_decomp.py`, `step_path3.py`, `percol_probe.py` — exploration for general shapes.
* `review/` — independent referee report and code; `lean-logs/` — Lean build log and hashes; `literature.md` — prior-work receipts.
