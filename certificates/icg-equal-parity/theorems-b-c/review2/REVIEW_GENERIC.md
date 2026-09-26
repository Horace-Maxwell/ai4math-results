# Referee report 2: PROOF.md §11 (Conjecture 12 for fixed a = 3 and a = 4, all b ≡ a mod 2)

Independent referee (Claude agent, folder `review2/`), 2026-09-26, 06:19–07:25 UTC.

**Scope.** `work/round6/equal-parity-a2/PROOF.md` §0–§5 (the a = 2 template) and §11; `generic_prover.py`,
`generic_prover_fast.py`, `replay_general.py`; logs `logs/generic_fast_a{2,3,4}.log` and `logs/replay_general.log`. Background:
Paper 1 (`outputs/ICG-q3-general/note.tex`: Lemmas 4–7, eq. (G), Conjecture 12, Theorem 3, Proposition 13) and round 4
(`work/round4/icg-equal-parity/PROOF.md`: Lemma P, Lemma M).

**Ground rules kept.** I ran no Lean and published or posted nothing. I did not open or touch `review/`, which belongs to the other
referee. No file outside `review2/` was modified, and the authors' code was only imported read-only. At most 6 worker processes ran at
a time. All arithmetic is exact (Python int, Fraction and sympy Rational). Scripts are in `review2/`, logs in `review2/logs/`.

---

## 0. Verdict

| case | verdict | blocker | major | minor | typo / remark |
|---|---|---|---|---|---|
| **a = 3** (all odd b ≥ 1) | **ACCEPT WITH MINOR REVISIONS** | 0 | 0 | 7 (F1–F7) | F8–F9 typo; F10–F12 remarks |
| **a = 4** (all even b ≥ 2) | **ACCEPT WITH MINOR REVISIONS** | 0 | 0 | same (F7 is the a = 4 status line) | same |
| a = 2 (consistency case) | consistent with §3–§5 | – | – | – | – |

I found no mathematical error, and none of the checks listed below failed.

- **The reduction holds for every a.** The case logic of Theorem B′ works with Proposition 1 for a + 1 rows, Lemma S_a, FD1_a,
  CH_a and EQ_a (item 1).
- **The certified list is complete and correct.** The code checks exactly the inequalities the argument needs. In two places it
  checks slightly less than the text claims, but in neither is there a real gap for a = 3 or 4 (F1, F3). The certification
  primitive is sound (item 7).
- **Re-certified independently.** I rebuilt the whole list for a = 2, 3 and 4 with my own code (`c3_certify.py`). It does not use
  the authors' uniform formula or sympy, and it validates every certified item end-to-end at an exact random point. Result: 0
  failures, and the negative controls fail where they should.
- **The authors' own runs reproduce.**
  - a = 3: the full task list regenerates identically (FD1 = 4 056, chains = 10 140). Re-running all 14 196 tasks with the
    authors' own code certifies every one (0 failures), and every task expression is positive at 4 exact points
    (`logs/t8_rerun_authors_a3_full.log`).
  - a = 4: their run finished during this review (`certified 70416 tasks, failures 0 … total time 2949s`). A sample of 1 040 of
    their a = 4 tasks re-certifies with 0 failures.
- **The statement itself is confirmed by exhaustive checks from the matrix model.**
  - Brute force over every sign matrix: (3,7) at (p,q) = (5,3), (3,5), (7,3), 2^31 matrices each; (4,6) at (5,3) and (3,5),
    2^34 each; plus spot checks of (3,5), (5,3), (4,4).
  - An exact branch and bound, validated against brute force, covers (3,b) for b ∈ {1, 3, …, 21, 25, 31, 41} and (4,b) for
    b ∈ {2, 4, …, 16, 20, 30, 40}, among 966 runs at integer and rational parameter points of both regions.

**Consequence.** Subject to the minor revisions, I agree that Conjecture 12 holds for every (a,b) with a + b even and
min(a,b) ≤ 4:

- min = 1: Theorem 3 of Paper 1.
- min = 2: Theorem B. This case is also re-derived by the generic a = 2 run and by my a = 2 certificate, so it does not rest on the
  §3–§5 hand proofs alone.
- min = 3 and min = 4: the generic a = 3 and a = 4 results.
- The transposed shapes follow from the prime swap. The regions (P ≥ 4, Q ≥ 2) and (P = 2, Q ≥ 4) cover every ordered pair of
  distinct odd primes with p on the a-side, so the swap is needed only to pass from shape (a,b) to shape (b,a).

The result is computer-assisted and not formalised (F10).

---

## 1. The argument as audited (restatement for general a)

Notation.

- Matrices and vectors: M = T_a(p), α = M s_a, D_a = ‖α‖₁ = d_a(p), δ_a = α_a = δ_a(p), u = M e_a (the last column of M).
- Sign matrix: Y has columns c_0, …, c_b ∈ {±1}^{a+1} and Y_ab = −1.
- Column path: ζ_{b−1} = c_b and ζ_{j−1} = (ζ_j + Q c_j)/q.
- Potentials and surplus: μ_j is the potential of x = q, ĉ_j = Q(1+μ_{j−1})/q, ρ = μ_{b−1}, and
  s_j = ĉ_j Δ(c_j) − (1/q) Σ_i h_{μ_{j−1}}((Mc_j)_i, (Mζ_j)_i).
- κ = 2((Mζ_{−1})_a)^−.
- Special columns: Y⁻ = −s_a s_bᵀ, Y⁺ = s_a s_bᵀ − 2e_ae_bᵀ, and g_t = (−1)^b s_a − 2e_a is the last column of Y⁺.

**Proposition 1** (valid verbatim for a + 1 rows):

  (Θ − G)/q^b = Σ_{j<b} s_j + ρΔ(c_b) + κ − 2δ_aρ.

**Case logic (Theorem B′_a).** If Y = Y⁻, then G = Θ. Otherwise let J = max{j : c_j ≠ (−1)^{j+1}s_a}.

1. **J < b.** Then Δ(c_b) = 0 and the state is exactly ζ_J = (−1)^J μ_{b−2−J} s_a. By S_a every s_j ≥ 0, and κ ≥ 0. FD1_a gives
   s_J > 2δ_aρ, hence Θ > G.
2. **J = b.** Then c_b = g with g_a = −1 and g not the anti-checkerboard column. On each region every such g falls into exactly
   one class:
   - Δ(g) > 2δ_a: strict inequality directly;
   - g = g_t: Δ = 2δ_a identically, so Θ ≥ G, with equality only for Y = Y⁺ (EQ_a);
   - "cheap": CH_a gives Σ s_j + κ > (2δ_a − Δ(g))ρ, hence Θ > G.

The a = 2 text of §5 uses a = 2 only through the explicit list {C, −E, B}, through FD2, through the coordinate 1/2 pattern argument
of Lemma EQ, and through the per-type bounds of Lemma S. §11 replaces these by, respectively, the machine classification of the
2^a − 1 last columns, CH_a, the last-coordinate forcing, and the crude S_a. I found no other a = 2-specific ingredient.

The one implicit ingredient is the following. For c_j = ±s_a we need "s_j = 0 if and only if every cell at j vanishes", and this
needs every cell to be ≤ 0 for alternating columns. It is supplied by the alternating-column branch of the S_a check (F3).

---

## 2. Findings

**F1 [minor]. The EQ_a forcing check in the code is weaker than the text.**

- *What the code checks.* `generic_prover.eq_forcing` checks only that the wrong alternating column (−1)^b s_a and the state
  v = M g_t have the same sign in at least one coordinate i.
- *Why that is not enough by itself.* In that case h = −2(Q−μ)|v_i| < 0 if |v_i| ≤ |A_i|. Otherwise h = 2(μ|v_i| − Q|A_i|), which is
  strictly negative only if μ|v_i| < Q|A_i|.
- *When it is enough.* The alternating-column part of S_a gives |v_i| ≤ ‖row_i M‖₁ ≤ Q_min|A_i|. So strictness is automatic when
  μ = μ_{b−2} < 1, that is, when b ≥ 2.
- *When it is not.* For b = 1 (a odd, μ = 1) the pattern check alone does not give strictness.
- *No actual gap for a = 3.* The coordinate i = a gives h = 2(2 − (Q−1)δ_a) < 0. My direct certificate that s(wrong) > 0 at
  column b − 1 passes for a = 2 to 6. It is affine in μ and is checked at μ ∈ {1, L, μ₁} for odd a and at {μ₀, L} for even a
  (`c3_certify.py`, "EQ wrong choice").
- *Fix.* Certify s(wrong) > 0, or one strictly negative cell, directly on the μ-range of column b − 1.

**F2 [minor]. The rest of EQ_a is neither written out nor machine-checked.**

- The claims "afterwards alternation is forced by the last coordinate" and "all cells of Y⁺ vanish, so G(Y⁺) = Θ" are asserted in
  §11 but not proved there, and the code checks only column b − 1.
- Both claims are true. A complete proof is in Appendix A.
- The facts it uses (A1–A6 of Appendix A, labelled F1–F6 in `t10_eq_symbolic.py`) are certified for a = 2 to 8 on both
  regions.
- The conclusions (all cells of Y⁺ vanish, κ(Y⁺) = 0, Δ(g_t) = 2δ_a, G(Y⁺) = G(Y⁻) = Θ) are checked exactly for a ≤ 6, b ≤ 13
  (`t1_prop1.py`).
- *Fix.* Insert Appendix A into §11.

**F3 [minor]. Lemma S_a: two points are implicit.**

- (i) §11 says "certified at Q = Q_min, μ ∈ {0,1}", but the code checks only μ = 1, as its own comment says. The μ = 0 endpoint
  (value QΔ(c) > 0) follows from the μ = 1 inequality, which forces Δ(c) > 0, or from Paper 1 Lemma 5.
- (ii) Cellwise nonpositivity for c = ±s_a comes from the alternating-column branch of the check, which requires every
  (‖row_i M‖₁ − Q_min|α_i|)^+ to vanish. EQ_a needs it.
- Both are correct as coded. *Fix:* state them as part of S_a.

**F4 [minor]. The uniform-formula text misses one case.**

- The case v_i = 0 ≠ A_i gives T_i = 0 (because h(A,0) = 0). The code handles it; the §11 text does not list it.
- The text should also say that the formula presupposes certified signs of A_i and v_i, and that the prover aborts otherwise (it
  does, with a RuntimeError).

**F5 [minor]. "Cheap" is defined differently in the text and in the code.**

- The text says a cheap column has Δ(g) < 2δ_a, and that every other admissible last column has Δ(g) ≠ 2δ_a on the region.
- The code sends every column other than g_t whose sign of 2δ_a − Δ(g) is not certified ≤ 0 to CH_a, including a column whose
  sign is undetermined. This is harmless, because CH_a proves the needed strict inequality whatever that sign is. But the code
  does not certify the "≠" statement as written.
- In fact all classifications have certified strict signs for a ≤ 6 (my certifier):

| a | cheap columns (p ≥ 5) | extra cheap column for p = 3 | columns with Δ > 2δ_a |
|---|---|---|---|
| 3 | (−1,1,1,−1), (−1,−1,1,−1) | (1,1,1,−1) | 4 (p ≥ 5) / 3 (p = 3) |
| 4 | (1,1,−1,1,−1), (1,−1,1,1,−1), (1,−1,−1,1,−1) | (−1,−1,1,1,−1) | 11 (p ≥ 5) / 10 (p = 3) |

- *Fix.* Record these tables in §11.

**F6 [minor]. "The case logic is then identical" is correct but not verbatim.**

- Step (ii) must range over the 2^a − 1 non-anti last columns with the three-way classification above.
- FD2 is replaced by CH_a.
- Lemma EQ's two-coordinate pattern argument is replaced by the last-coordinate argument.
- *Fix.* For the paper, state Theorem B′_a and write out its proof (Appendix B).

**F7 [minor]. The a = 4 status line is out of date.**

- When I started, `logs/generic_fast_a4.log` held only the generation line. The run then finished:
  `a=4: certified 70416 tasks, failures 0; direct-check failures 0; total time 2949s`.
- PROOF.md §11 still says "a = 4: see log". *Fix:* update the status line and record the counts (FD1 15 648, chains 54 768,
  S 64, cheap {big 3, p3 4}).
- Independently of that log, the a = 4 list is fully certified by `c3_certify.py`. The sample re-run (1 040 tasks) and the
  exhaustive (4,4) and (4,6) runs also pass.

**F8 [typo]. Section order and cross-references in PROOF.md.**

- §11 stands before "## 10. Files".
- §9 says "See §10 for the status of a = 3, 4"; it should be §11.
- The status table at the top does not yet mention the general-a result or its trust boundary.

**F9 [typo/wording]. The remark "(For q ≥ 5 this is also Paper 1 Lemma 7.)" needs the roles of the primes stated.**

- The remark holds only with the roles exchanged. Lemma 7 applies with F-side T_a(p) (F-side prime ≥ 3), path prime q, P ← Q = q − 1 ≥ 4,
  and μ ∈ [3/5, 1]; indeed μ₀ = (q−2)/q ≥ 3/5 exactly when q ≥ 5.
- With these roles, Λ ≤ Q(1+μ)D is exactly s ≥ 0. Say so.

**F10 [remark]. Trust boundary.**

- The a = 3 and a = 4 results are computer-assisted and not formalised.
- There are now two independent implementations of the certificate list:
  - the authors': sympy, uniform formula, coefficient test;
  - mine: own integer polynomial arithmetic and direct expansion of the cell definition.
- Brute force and branch and bound confirm the statement at sample parameters.
- The paper should state this, as Paper 1 does for Proposition 13.

**F11 [remark, outside the claim]. The method appears to reach further.**

- My certifier also certifies the complete list, with the forcing and full-chain checks included, for a = 5, 6, 7 and 8 with 0
  failures. For a = 8 this is 1 024 S checks, 45 753 FD1 and 514 111 CH branch expressions, in 228 s; the logs are
  `logs/c3_certify_a{5,6,7,8}.log`.
- Branch and bound confirms (5, b ≤ 25), (6, b ≤ 20), (7,3), (7,5), (7,9), (8,2), (8,4), (8,6) at sample points
  (`logs/t11_bnb_a78.log`).
- So min(a,b) ≤ 8 looks within reach. I have not reviewed this as a claim: each new a needs its own run, record and review.

**F12 [remark]. Efficiency.**

- The sympy pipeline took 939 s (a = 3) and 2 949 s (a = 4).
- An integer-polynomial representation over the fixed denominators q^K(q+1)^L (`r2poly.py`) certifies the whole list in 1 s (a = 3)
  and 3 s (a = 4), including end-to-end validation.
- Not a correctness issue.

---

## 3. Answers to audit items 1–8

1. **Reduction.** Valid for general a; see §1 and F6.
   - Proposition 1 is re-derived and checked exactly against the matrix model: 880 random (Y, p, q), a = 2 to 5, both regions,
     including non-integer parameters (`t1_prop1.py`).
   - The exact anti-checkerboard state and G(Y⁻) = Θ are checked for a ≤ 6, b ≤ 13. Hence, by Proposition 1, every s_j = 0
     along Y⁻.
2. **Uniform surplus formula.**
   - *Derivation.* For A ≥ 0 the cell takes four values:
     - 0 ≤ B ≤ A: h = −2(Q−μ)B;
     - B > A: h = 2(μB − QA);
     - −QA ≤ B < 0: h = 0;
     - B < −QA: h = 2μ(|B| − QA).

     Also h(0,B) = 2μ|B| and h(−A,−B) = h(A,B). With B = εm v_i (m > 0) and A replaced by M(εc) this gives T_i = −h exactly as in
     §11: T_i = 2 min{(Q−μ)m|v_i|, Q|A_i| − μm|v_i|} for A_i v_i > 0, because the two arguments differ by Q(m|v_i| − |A_i|).
     Add the missing case T_i = 0 when v_i = 0 (F4).
   - *Tests.*
     - 200 000 random exact cell evaluations;
     - 12 000 random exact surplus evaluations of my implementation against the direct cell computation (a = 3, 4, both regions,
       random g including s_a, random ε, m, μ);
     - 450 exact evaluations of the authors' `surplus_terms` (min over its alternatives) against the direct computation.

     All agree (`t2_uniform.py`).
   - *Concavity.* The formula is concave in μ and in m separately: a minimum of affine functions, and −2μ(·)^+ is linear in μ and
     concave in m. The same holds for the direct form, which is affine in μ and concave in m.
3. **Lemma S_a (crude form).**
   - For ζ in the cube, |(Mζ)_i| ≤ Σ_k |M_ik| = ‖row_i M‖₁. The states ζ_j are convex combinations of sign vectors.
   - Paper 1 Lemma 6 needs 0 ≤ μ ≤ 1 ≤ Q, which holds.
   - The bound is nondecreasing in Q, since Δ(c) and |A_i| are ≥ 0 and independent of Q, and affine in μ.
   - Strictness: the value is QΔ(c) > 0 at μ = 0, and positive at μ = 1 by the certificate.
   - The code checks exactly this, at μ = 1 and Q = Q_min, including the alternating-column requirement; see F3 for the implicit
     parts.
   - My certificate (S: 32 checks for a = 3, 64 for a = 4, Δ(c) > 0 certified separately) agrees, and fails where it should: the
     region p = q = 3 is rejected.
4. **FD1_a.**
   - *Regimes.* The index pairs (J−1, b−2−J) and ρ are as follows.

| b | J | regime | μ = μ_{J−1} | m = μ_{b−2−J} | ρ used |
|---|---|---|---|---|---|
| even | 0 | R0 | 1 | [μ₀, L) | exact (Q−m)/q |
| even | b − 1 | R1 | [μ₀, L) | 1 | exact (Q−μ)/q |
| even | 1 … b−2, J odd | R2b | [μ₀, L) | (L, μ₁] | upper bound m |
| even | 1 … b−2, J even | R2a | (L, μ₁] | [μ₀, L) | upper bound μ |
| 1 | 0 | B1 | 1 | 1 | exact μ₀ |
| odd ≥ 3 | 0 | R0 | 1 | (L, μ₁] | exact (Q−m)/q |
| odd ≥ 3 | b − 1 | R1 | (L, μ₁] | 1 | exact (Q−μ)/q |
| odd ≥ 3 | 1 … b−2 | R2odd / R2even | both indices share the parity of J − 1 | – | upper bound L (b − 1 even ⇒ ρ < L) |

     All ρ-replacements are strict upper bounds (Lemma M; odd-indexed μ decrease, and b − 1 exceeds the odd index). Every
     J ∈ 0 … b−1 is covered for every b.
   - *Concrete check.* For a = 3, 4, b ≤ 31 and 16 parameter points, every J is mapped to one regime and its box and ρ condition hold
     (`t3_fd1_true.py`).
   - *Vertex reduction.* Valid: separately concave functions on a product box attain their minimum at a vertex, and positivity at
     the vertices is strict.
   - *True values, no reduction.* s_J − 2δ_aρ > 0 for every deviation. Minimum ratio 1.197 for a = 3 (p = 5, q = 3, J = b − 1) and
     1.120 for a = 4 (p = 5, q = 3, b = 2, J = 1).
   - *Independent vertex certificates* (direct form, `c3_certify.py`):
     - a = 3: 528 branch expressions at 390 vertex points;
     - a = 4: 1 233 at 744;

     all positive. The negative control "need × 5/4" fails exactly at the predicted item: a = 3 deviation (−1,1,−1,−1) and a = 4
     deviation (−1,1,−1,1,1), both regime R1, region big.
5. **CH_a.**
   - *Chain.* The chain is c_j = (−1)^{b−j} g. Its cells vanish because B_i = −μ A_i with |B_i| ≤ Q|A_i|. The state after k chain
     steps is (−1)^k μ_{k−1} g exactly. The chain cost is Σ_{n=1..k} Q(1 + it(y,n))/q · Δ(g) and ρ = it(y, k+1), with
     y = μ_{b−2−k} and it(y,n) the n-fold map y ↦ (Q−y)/q.
   - *Parameter y.* y lies in [μ₀, L) if b − k is even, in (L, μ₁] if b − k is odd, and y = 1 exactly when b = k + 1.
   - *Chain alone for k ≥ 5.* This case requires b ≥ 6, so y = μ_{b−6} is a genuine parity-range value. The bound is therefore
     valid for every b.
   - *Full-chain bounds.* From D̂_{b+1} = D̂_b + 2μ_b:
     - b even: D̂_b/ρ_b = D̂_1/μ_{b−1} + 2Σ_{1≤k≤b−2}μ_k/μ_{b−1} + 2 ≥ D̂_1/μ₁ + 2;
     - b = 1: D̂_1/ρ_1 = D̂_1/μ₀;
     - b odd ≥ 3: D̂_b/ρ_b ≥ D̂_2/L + 2.

     κ is dropped. Checked for b ≤ 60 at six values of q.
   - *Bookkeeping on actual matrices* (`t4_chain_bookkeeping.py`). Items (a)–(g) of the script hold: 4 832 deviation instances,
     2 752 chain-alone instances (minimum ratio 4.6) and 288 full chains, with Θ − G > 0 in every case.
   - *Coverage.* All last columns are handled; see the table in F5.
   - *Independent certificates:*
     - a = 3: 1 236 branch expressions at 975 points, 10 chain-alone, 10 full-chain;
     - a = 4: 4 131 at 2 604 points, 14 chain-alone, 7 full-chain;

     all positive.
6. **EQ_a.**
   - Δ(g_t) = 2δ_a identically (Appendix A(a); certified by both certifiers).
   - The forcing at column b − 1 is correct; F1 concerns only the strength of the code check.
   - The forcing after column b − 1 via the last coordinate is correct: Qδ_a > p^a is certified for a ≤ 8.
   - G(Y⁺) = Θ holds for general a (Appendix A).
7. **Certification primitive.**
   - *Soundness.* The coefficient test is sound: after P = 4 + s, Q = 2 + t (or P = 2, Q = 4 + t), a polynomial with nonnegative
     coefficients and positive constant term is > 0 for s, t ≥ 0.
   - *Denominators.* The expanded denominator is tested first; otherwise every factor of `factor_list` must have a certified sign,
     multiplied by the sign of the content.
   - *Conservative failure modes.* All of these are counted as failures or abort the run:
     - an undetermined sign, including an undetermined denominator factor;
     - a zero constant term;
     - an identically zero task;
     - any exception.

     A leftover symbol other than s, t would make the comparisons inside `psign` raise.
   - *Other details.* Branch-selection signs raise a RuntimeError if undetermined, so nothing is skipped silently. The srepr cache
     is exact. The fast driver only reorders the same computations.
   - *Soundness of the branching.* Alternatives are exact minima: min{X, Y} for same-sign cells and min{0, −2μZ} for opposite
     signs. Checking every combination is therefore necessary and sufficient at each vertex.
   - *Risk found.* I found no way for a sign to be mis-determined short of a bug in sympy's `expand`, `together` or `Poly`. That
     residual risk is covered by my implementation, which uses no sympy for the certificates.
8. **Independent confirmation**; see §4.

---

## 4. Independent computations (all exact)

| # | script | what | result | log |
|---|---|---|---|---|
| 1 | `r2core.py`, `t1_prop1.py` | own T_k(x), checked against the Ramanujan-sum definition (primes ≤ 13, k ≤ 7); d_k, δ_k closed forms; Prop. 1; S at true states; Y⁻ states; Y⁺ cells, κ(Y⁺), Δ(g_t), G(Y±) = Θ; Qδ_a > p^a | all OK: 880 random matrices, 192 (a,b,p,q), a ≤ 8 symbolic | `logs/t1_prop1.log` |
| 2 | `t2_uniform.py` | uniform formula: derivation, own implementation, the authors' `surplus_terms` | 200 000 / 12 000 / 450 exact agreements | `logs/t2_uniform.log` |
| 3 | `t3_fd1_true.py` | FD1_a at true μ-values, all J and deviations, b ≤ 31, 16 parameter points; regime boxes | all > 1 (min 1.197 for a = 3, 1.120 for a = 4) | `logs/t3_fd1_true.log` |
| 4 | `t4_chain_bookkeeping.py` | CH_a bookkeeping on actual matrices, chain-alone, full-chain ratio bounds | all OK | `logs/t4_chain_bookkeeping.log` |
| 5 | `r2poly.py`, `c3_certify.py` | full re-certification of S_a, FD1_a, CH_a (K = 4), full chain and EQ_a (incl. the direct s(wrong) > 0 check) by direct cell expansion with own integer polynomial arithmetic; every certified item validated end-to-end at a random exact point | 0 failures for a = 2, 3, 4 (and 5 to 8) | `logs/c3_certify_a{2,...,8}.log` |
| 5′ | `c3_certify.py` (negative controls) | need × 5/4 fails FD1 R1 as predicted; need × 11/10 passes; enlarged regions p = q = 3 and Q ≥ 1 fail, p ≥ 4 and (p = 3, q ≥ 4) pass | as expected | `logs/c3_certify_a{3,4}_nc_*.log` |
| 6 | `bnb.py`, `t5_bnb_validate.py` | exact branch and bound (column-path identity plus potential bound; S_a verified exactly at each point first) compared with plain brute force at thresholds Θ and the 5th and 12th largest G | identical sets in 41 comparisons over 14 cases | `logs/t5_bnb_validate.log` |
| 7 | `t6_bnb_runs.py`, `t9_bnb_random.py` | the conjecture (max G = Θ, maximisers exactly Y⁻ and Y⁺). t6: (3,b) for b = 5 … 21 and 25; (4,b) for b = 4 … 16 and 20; (5,b) for b = 3 … 11; (6,b) for b = 4 … 10; (2,10), (2,12), (2,20); at 11 prime pairs of both regions, plus 4 rational points when b ≤ 11. t9: (3,1), (3,3), (3,5), (3,7), (3,9), (4,2), (4,4), (4,6), (4,8) at 60 points each (4 corners and 56 random rationals of both regions), plus (3,31), (3,41), (4,30), (4,40), (5,25), (6,20) at 4 points each | 966 runs, 0 failures (plus 18 runs for a = 7, 8 in `logs/t11_bnb_a78.log`) | `logs/t6_bnb_runs.log`, `logs/t9_bnb_random.log` |
| 8 | `t7_brute_numpy.py` | plain exhaustive brute force from Z = MYNᵀ (int64 with an asserted overflow bound, meet in the middle), no lemma used: (3,5), (5,3), (4,4) at (5,3) and (3,5); **(3,7) at (5,3), (3,5), (7,3) with 2^31 matrices each; (4,6) at (5,3) and (3,5) with 2^34 matrices each** | max G = Θ, exactly Y⁻ and Y⁺, every time | `logs/t7_brute_numpy.log` |
| 9 | `t8_rerun_authors.py` | the authors' code, imported read-only: regenerated task lists match the logs (a = 3: 4 056 + 10 140; a = 4: 15 648 + 54 768); direct checks 0 failures; stratified samples of 1 534 tasks (a = 3) and 1 040 (a = 4), then **all 14 196 a = 3 tasks**, certified with the authors' `work`; every such expression evaluated exactly at 4 points including the region corner (all > 0) | 0 failures | `logs/t8_rerun_authors_a3.log`, `_a4.log` (samples), `logs/t8_rerun_authors_a3_full.log` (all 14 196 a = 3 tasks) |
| 10 | `t10_eq_symbolic.py` | facts A1–A6 of Appendix A (F1–F6 in the script), certified on both regions for a = 2 to 8 | OK | `logs/t10_eq_symbolic.log` |

The exhaustive (3,7) and (4,6) runs cover shapes outside Proposition 13 of Paper 1 directly from the definition. They agree with the
branch and bound at the same points.

---

## 5. Suggested fixes (consolidated)

1. §11 EQ_a: add Appendix A (the forcing after column b − 1, and the proof that all cells of Y⁺ vanish and κ(Y⁺) = 0). In the code,
   replace the same-sign pattern test by a direct certificate that s(wrong) > 0 on the μ-range of column b − 1 (F1, F2).
2. §11 S_a: state the μ = 0 endpoint and the cellwise nonpositivity for alternating columns explicitly (F3).
3. §11 uniform formula: add the case v_i = 0, and say that the signs of A_i and v_i must be certified (F4).
4. §11 classification: record the last-column tables of F5, and define "cheap" as the code does, or certify the strict sign (F5).
5. §11 or the paper: state Theorem B′_a and write out its proof (Appendix B). Replace "identical" by a list of the substitutions
   (F6).
6. Update the status line for a = 4 (F7). Fix the section order and cross-references (F8) and the Lemma 7 remark (F9).
7. Paper: state the trust boundary, meaning two independent implementations and not formalised (F10). Optionally cite this
   report's brute-force and branch-and-bound confirmations as cross-checks.

---

## Appendix A. Proof of EQ_a for general a (for insertion in §11)

Throughout, (P ≥ 4, Q ≥ 2) or (P = 2, Q ≥ 4), and a + b is even. Write α = Ms_a, δ_a = α_a, u = Me_a = (p^{a−1}P, …, P, 1)ᵀ and
g_t = (−1)^b s_a − 2e_a.

**Facts** (certified on both regions for a = 2 to 8, `t10_eq_symbolic.py`, where they are labelled F1–F6).

- (A1) sgn α_i = (−1)^{a−i}.
- (A2) |α_i| ≥ 2u_i for i < a, with equality only for i = 0. (Paper 1 Lemma 4 and Remark 5 give
  |α_i| = p^{a−1}P(1 + μ^{(p)}_{i−1}) for i < a.)
- (A3) μ₀|α_i| ≥ (2/q)u_i for i < a (equality only for i = 0 at Q = 2).
- (A4) δ_a > 2 and (Q−1)δ_a > 2.
- (A5) Qδ_a > p^a = Σ_k |M_ak|.
- (A6) Δ(g_t) = 2δ_a; this is (a) below.

**(a) Δ(g_t) = 2δ_a.**

  ‖Mg_t‖₁ = Σ_i |(−1)^b α_i − 2u_i| = Σ_i ||α_i| − 2(−1)^i u_i|    (by A1 and a + b even)
          = Σ_i (|α_i| − 2(−1)^i u_i)                              (by A2 and A4)
          = D_a − 2 s_aᵀ M e_a = D_a − 2δ_a                         (M is symmetric).

**(b) Path of Y⁺.** By induction from ζ_{b−1} = g_t, with columns c_j = (−1)^j s_a,

  ζ_j = (−1)^{j+1} μ_{b−2−j} s_a − 2q^{−(b−1−j)} e_a.

**(c) All cells of Y⁺ vanish.** At column j < b, A = (−1)^j α and B = Mζ_j, so

  sgn(A_i) B_i = −μ_{b−2−j}|α_i| − 2(−1)^{j+a−i} q^{−(b−1−j)} u_i.

For A_i ≠ 0 the cell vanishes if and only if −Q|A_i| ≤ sgn(A_i)B_i ≤ 0.

- *Upper inequality.* At j = b − 1 it follows from A2 for i < a and from A4 for i = a. For j ≤ b − 2 it follows from
  μ_{b−2−j} ≥ μ₀ and q^{−(b−1−j)} ≤ 1/q, together with A3 for i < a and (Q−1)δ_a ≥ 2 (A4) for i = a.
- *Lower inequality.* μ|α_i| + 2u_i ≤ 2|α_i| ≤ Q|α_i| for i < a (A2, Q ≥ 2), and μδ_a + 2 ≤ Qδ_a for i = a (A4).

Hence s_j = 0 for every j < b.

**(d) κ(Y⁺) = 0.** (Mζ_{−1})_a = μ_{b−1}δ_a − 2q^{−b} > 0.

**(e) G(Y⁺) = Θ.** Proposition 1 gives (Θ − G(Y⁺))/q^b = 0 + 2δ_aρ + 0 − 2δ_aρ = 0.

**(f) Uniqueness.** Suppose c_b = g_t and G = Θ. Then every s_j = 0 and κ = 0.

- By S_a (strict part), c_j = ±s_a for every j < b.
- By S_a (alternating part), every cell is ≤ 0, so every cell vanishes.
- *Column b − 1.* The state is g_t exactly, and s((−1)^b s_a) > 0 there (the certified "EQ wrong choice" check). Hence
  c_{b−1} = (−1)^{b−1} s_a.
- *Columns j ≤ b − 2, by induction.* If c_{j+1} = (−1)^{j+1} s_a, then

    (Mζ_j)_a = ((Mζ_{j+1})_a + (−1)^{j+1} Q δ_a)/q

  has sign (−1)^{j+1} and absolute value ≥ (Qδ_a − p^a)/q > 0. This uses |(Mζ_{j+1})_a| ≤ p^a and A5.
- Now suppose c_j = (−1)^{j+1} s_a. Then A_a = (−1)^{j+1}δ_a has the sign of B_a. The cell at coordinate a is either
  −2(Q−μ)|B_a| < 0, or 2(μ|B_a| − Qδ_a) ≤ 2(p^a − Qδ_a) < 0. Either way it does not vanish, a contradiction.
- Therefore c_j = (−1)^j s_a for every j < b, that is, Y = Y⁺. ∎

## Appendix B. Theorem B′_a (the general statement the code supports)

**Theorem B′_a.** Fix a ≥ 1 and let ℛ be the region (P ≥ 4, Q ≥ 2) or (P = 2, Q ≥ 4). Suppose that on ℛ the following hold:

1. (S_a) the crude one-step bound, strict for c ≠ ±s_a and cellwise for c = ±s_a;
2. (FD1_a) for the regimes of §3, item 4;
3. (CH_a) with K = 4, for every non-trunc last column g whose sign of 2δ_a − Δ(g) is not certified ≤ 0;
4. (EQ_a) Δ(g_t) = 2δ_a, and s((−1)^b s_a) > 0 at state g_t for the μ-range of column b − 1.

Then for every b ≡ a (mod 2) and every Y ∈ {±1}^{(a+1)×(b+1)} with Y_ab = −1, G(Y) ≤ Θ, with equality exactly for Y⁻ and Y⁺.

*Proof.* §1 of this report together with Appendix A. Hypotheses 1–4 are certified for a = 2, 3 and 4 by the authors' runs and
independently by `c3_certify.py`. ∎
