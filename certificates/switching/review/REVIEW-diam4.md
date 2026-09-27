# REVIEW — Theorem 9.22 (switching conjecture for main eigenvalues, trees of diameter ≤ 4)

Referee: independent Claude subagent, standing in for the unavailable cross-model review. I did not produce the work under review.
- Time: 2026-09-27 00:20–00:50 UTC (`date -u`), at most 4 cores.
- No Lean lock was taken and nothing was built.
- PROOF.md was not edited. Nothing was pushed, posted or published.

Reviewed claim: PROOF.md §9.22 **Theorem 9.22**. Every tree of diameter ≤ 4 other than K₂ has a switching s such that every distinct eigenvalue of T^s is main.

## Verdict: ACCEPT, with MINOR revisions

- No BLOCKER and no MAJOR finding.
- Every mathematical step of the proof was re-derived by hand and is correct:
  - Lemma S (spectrum) and Lemma M (reduced form);
  - Lemma 9.15.1 (realizability), Lemmas 9.15.2 and 9.15.3 (Row Lemmas);
  - Lemma 9.22.1 (refined counts), Theorem 9.22.2 (b* ≥ 13), Lemma 9.22.3 (the finite set);
  - the b* ≤ 1 families.
- Every computational claim of the proof was reproduced by my own code:
  - it shares no code with `diam4/code/`;
  - its enumeration and certificates are different, and it does not use PARI (not installed) or their scripts, except that it imports their `final_region.region()` once, read-only, only to compare the two sets.
- The finite part matches exactly:
  - the same set of **13,376** trees (set equality, not just the count);
  - the same **3** survivors, T(2,2), D(2,2) = T(2,0,0) and K₁,₄ = T(3);
  - a certified good switching for **every** tree in the set.
- Fresh G1 (00:37–00:42 UTC) found no prior or competing claim. The diameter-≤4 case is new, as far as can be determined.
- The Lean statements say what PROOF.md says they formalize, with one mild wording overreach (MINOR-2).

## Findings

| # | Grade | Location | Finding | Suggested fix |
|---|---|---|---|---|
| 1 | MINOR | PROOF.md §9.22, "Proof of Theorem 9.22" step 3; CONTRACT §6.2 "b* ≥ 13" | The b* ≥ 13 case is cited as "Theorem 9.22.2 and Lemma 9.15.2". Criterion (a′) uses the *refined* count, which is Lemma 9.22.1; Lemma 9.15.2 alone gives only 4 bad members per pair. | Cite Lemma 9.22.1 (with 9.15.2 for the construction). |
| 2 | MINOR | PROOF.md §0 row 22 ("the inequality of Thm 9.22.2 and the refined count are formalized"); CONTRACT §6.2 "Lean" ("…: the refined count"); docstring of `SwitchingThmH.lean` | `sol_subsingleton` and `indep_of_irrational` formalize only the abstract step: if 1 and w are ℚ-independent, then ε + Λw = u has at most one solution in ℤ². The link to trees is on paper, namely that w = 1/(t − β) (leaf row) or w = −2/θ (bare row) is irrational for an irrational pair, and that "bad ⇔ this equation". "For each sign" in the docstring is ambiguous: it means each of the two equations G(θ) = 0 and G(−θ) = 0, not each ε. | Say "the linear-independence step of the refined count is formalized". Reword the docstring. |
| 3 | MINOR (suggestion) | PROOF.md §9.7, family A | The argument (analytic bounds plus a finite resultant check on [2,400)²) is plausible, but I did not re-verify its individual inequalities. It is needlessly long, and a complete 3-line exact proof exists, which I checked. The secular quadratic h = t² − (1+k₀+k₁)t + k₀ has no integer root, since its roots lie in (0,1) and (k₀+k₁, k₀+k₁+1), so it is irreducible. A failure needs h \| f with f = t(t+k₁−3)² − (t−2)²(t−1)². Write f mod h = c₁t + c₀. Then gcd(c₁, c₀) = 1 and Res_{k₀}(c₁, c₀) = (k₁−1)(k₁⁶ − 11k₁⁵ + 60k₁⁴ − 148k₁³ + 224k₁² − 192k₁ + 64). The resultant criterion is valid because the k₀³-coefficients of c₁ and c₀ are ∓1. The sextic has no integer root (checked on the divisors of 64). Hence there is no failure for any k₀, k₁ ≥ 2. | Use the remainder/resultant argument (log `rv_families.log`). |
| 4 | MINOR | PROOF.md §9.9 D1 (used for spiders) | "A failure forces θ³ − θ + 2 = 0" covers G(θ) = 0. A failure G(−θ) = 0 gives θ³ − θ − 2 = 0, whose roots are the negatives. The argument still applies because −θ is also an eigenvalue (bipartite), and the Lean lemma is then applied to −θ. | Add one sentence. |
| 5 | MINOR (presentation) | PROOF.md §9.22 "The finite search" | "two independent implementations": both of theirs rely on sympy factorisation, of R(x²) in one and of R(t) in the other. A third implementation now exists (this review) with its own certificates for each orbit (see §4 below). | Mention it if the note cites independent checks. |

No other errors were found. Minor wording ("N_I … each is a linear factor t − q² of R") and all dimension, parity and counting statements checked out.

## 1. Definitions and statement (Task 1)

Source: arXiv e-print 2609.27046, fetched 00:24 UTC, sha256 `acce4369…eeed`.
- Only v1 exists: `/abs/…v2` and `/abs/…v3` return 404.
- The e-print file is `Switching_v1.tex`.

The definitions match CONTRACT §1–2:
- A switching is s ∈ {±1}ⁿ with A(G^s) = D_s A D_s (l.95–106).
- An eigenvalue λ is main iff E_λ ⊄ 𝟏^⊥ (l.116).
- Conjecture 1.1 is "For any unsigned connected graph G ∉ {K₂, K₄−e} …" (l.129–131).
- The Problem is "… holds for trees and connected regular graphs of order n ≥ 3" (l.201–203).
- The 2021 wording, as restated in Shao–Yuan (arXiv:2106.07878v3, main.tex l.62–63), is "Let G ≠ K₂, K₄\{e}…", with the same notion of switching (sign reversal across a cut) and of main eigenvalue. "Connected" is irrelevant for trees.

**Equivalence (N1).** "All eigenvalues of T^s are main ⇔ P_θ s ≠ 0 for every eigenvalue θ of A(T)" is correct as used:
- P_θ(G^s) = D_s P_θ D_s, so 𝟏ᵀP_θ(G^s)𝟏 = ‖P_θ s‖²;
- the source itself defines M_*(s) = Σ_λ 1{E_λ ⊄ s^⊥} as the number of distinct main eigenvalues of G^s (l.176–181).

The Krylov criterion (N2) and the certificate "rank_{F_p} = d with d exact" are sound: rank_{F_p} ≤ rank_ℚ ≤ d = deg rad φ. Galois closure (N3) is used only with rational s, which is correct.

## 2. Spectrum lemma (Task 2)

**Hand check.** All of the following are right:
- the leaf, branch and centre equations;
- the secular condition F(t) = 1 and the interlacing t_j ∈ (b_j, b_{j+1}), t_r > b_r;
- that secular roots are simple, are never poles, and are distinct from ±√b and from 0;
- the leaf-group eigenspaces, of dimension k_b − 1;
- both kernel cases;
- the dimension count, which equals n in both cases k₀ ≥ 1 and k₀ = 0;
- Lemma M, i.e. (S), (L) and (Z);
- the reduced form G(θ) = Σ_b (A_b + S_bθ)/(t − b).

**Exact check** (`code/rv_spectrum.py`, log `logs/rv_spectrum_seed7_400.log`): 400 trees, n ≤ 34, including all named trees of §9. **0 failures.** For each tree:
- (1) the charpoly from a generic tree recursion equals R(x²)·∏_{b≥1}(x² − b)^{k_b−1}·x^{m₀} as polynomials;
- (2) d = deg φ − deg gcd(φ, φ′) equals the formula 2r + 2#{b ≥ 1 : k_b ≥ 2} + [m₀ > 0];
- (3) the secular eigenvector satisfies Ax = θx modulo R(θ²), the leaf-group vectors satisfy Ax = θx modulo θ² − b, and the kernel dimension (exact rank) is m₀;
- (4) for 4 random switchings (1,600 in total):
  - s·x, G(θ) and the reduced form vanish on the same irreducible factors;
  - the goodness predicted by (S), (L) and (Z) equals goodness by exact ℚ Krylov rank.

## 3. Row Lemmas, refined counts, b* ≥ 13, b* ≤ 1 (Task 3)

**Lemma 9.15.1 (realizability).** The proof was re-derived, including the single exception (β, k, Λ) = (2, 2, 0). A brute force over β ≤ 9 and k ≤ 6 gives realizable set = 𝓛_β and |𝓛_β| = the formula, with 0 mismatches (`logs/rv_realizability.log`).

**Lemmas 9.15.2 and 9.15.3, and Lemma 9.22.1.** Correct:
- Leaf row: G = θ + ε + U_β(t) + Λ/(t − β).
- Bare row: G = ε + U(t) + θ − 2m/θ.
- Even orbits:
  - they never spoil a leaf-row member;
  - they spoil at most 1 bare-row member, and only when t = 2m is an even non-square integer.
- Integer pairs: at most 2 per ε, so ≤ 4.
- Irrational pairs:
  - 1 and w are ℚ-independent, with w = 1/(t − β) or w = 1/θ;
  - so each of the two equations has at most one solution (ε, Λ) or (ε, m);
  - so ≤ 2.
- (L) and (Z) hold for every member.
- (a′) and (b′) follow.

**Theorem 9.22.2.** Correct:
- N_I ≤ sq + 1 (interlacing; integer roots are not poles), sq ≤ g, and N_I + 2N_II ≤ r = b* + 1 − g.
- Hence 2(2N_I + N_II) ≤ 2⌊√(b*−1)⌋ + b* + 4 ≤ 2b* − 3 for b* ≥ 13, using 2⌊√(b*−1)⌋ + 7 ≤ b*.
- By integrality, 2N_I + N_II ≤ b* − 2 < b* − 1 ≤ |𝓛_{b*}|.

**Lemma 9.22.3.** Correct:
- the bound M = 2·NI_max + ⌊(r − NI_max)/2⌋, since the maximum of 2N_I + N_II is increasing in N_I;
- 4N_I + 2N_II + N_ei ≤ 3N_I + r, since the three root types are disjoint.

**Stress tests with exact goodness of every member.** `code/rv_rows.py`, `rv_endtoend.py`, `rv_hard13.py`.
- **69 trees with N ≥ 1** (b* up to 40, n ≤ 90), all leaf rows and bare rows:
  - bad counts are always ≤ 4N_I + 2N_II (+ N_ei);
  - the bounds are **attained**: T(15) has 4 bad; T(18,0,0) has 2 bad with N_II = 1; T(3,2,1,1,0,0) has 2 bad at β = 3.
  - So the refined count is tight, and it is not violated.
- **End to end on all 9,114 trees with b* ≥ 2 and n ≤ 26:**
  - every row respects its bound;
  - every row certified by (a′) or (b′) contains a good member;
  - every tree satisfies (a′) or (b′), except exactly T(2,2), T(2,0,0) and T(3);
  - 0 issues (`logs/rv_endtoend_3-22.log`, `logs/rv_endtoend_23-26.log`).
- **All 8,232 trees with b* ≥ 13 and n ≤ 34:** (a′) holds at β = b* and the b*-row has a good member; 0 issues (`logs/rv_endtoend_big34.log`).
- **31 worst-case trees with b* ≥ 13 and two perfect-square secular roots** (n ≤ 156; one has N = 3): every b*-row is within its bound, and the bound 8 is attained twice (8 bad of 154); 0 violations (`logs/rv_hard13.log`).

**b* ≤ 1 (§9.7, D1, Main Theorem).** Checked by hand, with my own derivations:
- Stars: failure needs (k₀ − 2)² = k₀, i.e. k₀ ∈ {1, 4}; E = 0 is used for k₀ = 4.
- T(1, 0^{k₀}): G ∝ (θ² − 2)(θ² + θ − 1), so a failure needs t = 2 (R(2) = −k₀ ≠ 0) or R = t² − 3t + 1 (k₀ = 1). There is no failure for k₀ ≥ 2.
- Family A: remainder argument, see finding 3.
- Spiders (D1): G = θ or θ + 2/(t − 1); the cubic argument; finding 4.
- k₀ = 1: R = t² − (k₁+2)t + 1 has discriminant k₁(k₁+4), strictly between consecutive squares, so N ≤ 1. There is no zero eigenvalue, and the pair {x ± 1} is impossible. Theorems E and F apply (P⁻ = P⁺ − 2 forces θ = ±1).
- Direct certificates (`logs/rv_families.log`), 0 failures:
  - family A and T(1, 0^{k₀}) for k₁ ≤ 40 and 2 ≤ k₀ ≤ 40;
  - stars for k₀ ≤ 80;
  - spiders (s⁺) and T(1^{k₁}, 0) (s⁺ or s⁻) for k₁ ≤ 80.
- The case split of the proof of Theorem 9.22 is exhaustive: n ≤ 2; all a_i ≤ 1 with k₀ ≥ 2, k₀ = 1 or k₀ = 0; 2 ≤ b* ≤ 12; b* ≥ 13.

## 4. The finite part (Task 4)

**My enumeration** (`code/rv_region.py`) is different from theirs:
- itertools.product over multiplicity vectors (k₀, …, k_{b*}) with global caps, then a per-B filter;
- the bounds Mx and K0 are computed by brute force over the feasible (N_I, N_II, N_ei), not by formula.

**Exact invariants for every tree in the set**, not only for survivors of a cheap test:
- integer secular roots by exact Fraction evaluation of F(t) = 1;
- orbits from `sympy.factor_list` of R(t) (degree ≤ 13), with my own certificates for each orbit:
  - irreducible: my own Rabin test mod p;
  - even: a simple root c of h mod p with c a quadratic non-residue, which by Hensel implies t is not a square in ℚ(t);
  - non-even: an explicit g with g(x)g(−x) = ±h(x²), checked by expansion.

**Result** (`logs/rv_region.log`, 78 s):
- **13,376 trees**, max n = 124;
- the set is equal to theirs: `theirs == mine`, 0 on either side only;
- 0 uncertified orbits and 0 violations of the a-priori bounds;
- N distribution {0: 13,199; 1: 176; 2: 1};
- **survivors of (a′) and (b′): exactly T(2,2) [N_I=1], T(2,0,0) [N_I=2] and T(3) [N_I=1].**

**A good switching for every tree in the set** (`code/rv_certify.py`, `logs/rv_certify_region.log`), independent of Lemmas S, M and the Row Lemmas:
- method: random switchings;
- certificate: rank over F_p = d for p = 2³¹−1 and p = 2147483629, with d exact from the generic tree charpoly;
- **13,376 of 13,376 certified**, 0 failures, at most 11 tries;
- 3,029 trees (n ≤ 40) were also confirmed by exact ℚ-rank;
- d equals the Lemma S formula on all of them.

**The three exceptional trees** (`code/rv_exceptional.py`, `logs/rv_exceptional.log`). For each, exhaustive search over all 2ⁿ switchings with exact ℚ-rank, plus an exact eigenspace-projection check:

| Tree | Good switchings | Stated s | Charpoly |
|---|---|---|---|
| T(2,2) | 72 of 128 | `+++++--` is good | x³(x∓2)(x²−2) |
| D(2,2) | 16 of 64 | `+++-+-` is good | x²(x∓1)(x∓2) |
| K₁,₄ | 12 of 32 | `+++--` is good | x³(x∓2) |

By hand with Lemma M:
- T(2,2): G = 1 + θ, which is 3 or −1 at θ = ±2; (L) holds via 1 ± 2/θ; (Z) holds since s_c = 1 ≠ 0 = Σε_i.
- D(2,2): G(±1) = 4 and −2, G(±2) = 1 and 1; (Z) holds via the (+,−) leaves.
- K₁,₄: G = θ ≠ 0.

**Full spot check, all 23,023 T(a) with n ≤ 30** (the same count as PROOF §9.2). Every tree has a good switching confirmed by **exact ℚ-rank**, with 0 failures and d equal to the Lemma S formula for all (`logs/rv_certify_upto30.log`). Diameter ≤ 4 ⇔ radius ≤ 2 ⇔ height ≤ 2 from a centre, so these multisets contain every tree of diameter ≤ 4 with n ≤ 30.

## 5. Lean (Task 5)

I read the files and did not build them. The copies in `switching/lean/` are byte-identical (sha256) to `research-lean/Research/`. A grep for forbidden tokens (sorry, admit, native_decide, bv_decide, implemented_by, extern, axiom, debug.) finds nothing. The recorded build log `diam4/s3/lake_build_SwitchingThmH.log` shows axioms ⊆ {propext, Classical.choice, Quot.sound}.

| Declaration | What it states | PROOF.md claim | Assessment |
|---|---|---|---|
| `SwitchingThmH.two_sqrt_add_seven_le` | b ≥ 13 → 2·⌊√(b−1)⌋ + 7 ≤ b | step 6 of Thm 9.22.2 | exact match |
| `SwitchingThmH.row_budget` | b ≥ 13, sq ≤ ⌊√(b−1)⌋, sq ≤ g, NI ≤ sq+1, NI + 2NII + g ≤ b+1 → 2NI + NII + 1 ≤ b − 1 | "steps 4–6 as a statement about ℕ" | exact match; the hypotheses (interlacing, root disjointness) are on paper, as stated |
| `SwitchingThmH.sol_subsingleton`, `indep_of_irrational` | char-0 field: 1, w ℚ-independent → ≤ 1 solution (ε, Λ) ∈ ℤ² of ε + Λw = u; w ∉ ℚ → independence | "the refined count" | correct, but it is only the abstract step (MINOR-2) |
| `SwitchingRow.card_bad_le_two`, `card_bad_le_one_of_ne` | {Λ ∈ ℤ : u + Λw ∈ {θ, −θ}} has ≤ 2 elements, and ≤ 1 if 2θ ∉ wℤ | the counting step of 9.15.2/9.15.3 | exact match |
| `SwitchingDiam4.no_eigenvalue_root_cubic` | A ∈ M_n(ℚ), Aᵀ = A, θ a real root of the charpoly → θ³ − θ + 2 ≠ 0 | the algebraic step of D1 | exact match; used for spiders (finding 4) |
| `SwitchingWalkProfile.*` (Theorem R, regular graphs; not part of Thm 9.22) | annihilator / eigen_nonorth / main_after_switching / walkRegular | PROOF §1 | statements match §1 |

**Not formalized, and correctly declared as such:** Lemma S, Lemma M, realizability, the case analysis and the finite search. **Nothing is overclaimed beyond MINOR-2.**

## 6. Novelty / G1 (Task 6)

Queries were run 00:37–00:42 UTC 27 Sep; see `querylog.tsv` and `g1/`. No e-mail address appeared in any request, and OpenAlex was used anonymously.

- **arXiv:**
  - 2609.27046: v1 only (v2, v3 → 404).
  - API searches ("main eigenvalues" AND switching; "main eigenvalue" AND signed; "switching conjecture"; "main eigenvalues" AND trees AND signed; "main eigenvalues" AND "signed graphs"), newest first: nothing after 2609.27046v1 except the unrelated 2607.17805 (signless Laplacian) and 2603.04063 (two main eigenvalues, unicyclic).
  - The math.CO/new listing has no "main eigen" item.
- **MathDB #350999** ("Akbari et al.'s switching conjecture for main eigenvalues of signed graphs"): status open, 0 solutions, 0 comments, last activity null.
- **trureturing:**
  - issues and PRs for `2609.27046v1`, "switching conjecture", "main eigenvalues", "Akbari switching", "signed graph main": 0 (positive control "arXiv": 5);
  - code search: 0 (positive control "theorem": 26,048);
  - tree grep: 0 path hits, but the API tree is truncated at 51,652 entries.
- **GitHub-wide:**
  - commits (4 phrasings), repos and issues: 0;
  - code search: 2 hits, both arXiv-RSS mirror files (ehijano/rss_fetch), which are not claims.
- **MathOverflow** (StackExchange API, 4 queries): no relevant question.
- **What was known:**
  - stars, double stars (= all diameter-3 trees), paths and complete bipartite graphs (Akbari et al. 2021, as summarized in Shao–Yuan main.tex l.65 and in the zbMATH abstract);
  - harmonic trees T_a (Shao–Yuan 2022). These are a diameter-4 subfamily T((a−1)^{a²−a+1});
  - all connected graphs with n ≤ 9 (2609.27046 l.159).
- **Citing papers of the 2021 paper** (Semantic Scholar):
  - França–Brondani 2021 (generalized Bethe trees) concerns unsigned main spectra, not switching;
  - Andrade et al. 2026 (LAMA) concerns normal mixed graphs; I obtained its abstract via OpenAlex, and it has nothing on switching or trees.
- 2609.27046 (Sept 2026, co-authored by Akbari) still calls trees "another interesting unresolved case".

**G1 verdict:** no prior or competing claim for trees of diameter ≤ 4. **The diameter-≤4 case is new**, except for its known subfamilies: stars, double stars, P₃–P₅, harmonic trees, and n ≤ 9.

Residual risk (low): nobody has read the full text of the 2021 paper (paywall). Three independent summaries list its tree results as double stars, paths and stars only, and later work by the same senior author calls trees unresolved.

## 7. Recomputation log (all under `review/`, UTC 27 Sep)

| Time | Command | Result |
|---|---|---|
| 00:24 | `curl -sL https://arxiv.org/e-print/2609.27046` | `Switching_v1.tex`; definitions checked |
| 00:27–00:28 | `python3 code/rv_spectrum.py 7 400` | 400 trees; 0 failures |
| 00:30–00:31 | `python3 code/rv_region.py logs` | 13,376 trees; survivors T(2,2), T(2,0,0), T(3); 0 uncertified |
| 00:31 | `python3 code/rv_certify.py region logs/rv_region_list.txt 2` | 13,376 of 13,376 certified; 0 d-mismatches; 3,029 exact-ℚ |
| 00:31–00:32 | `python3 code/rv_certify.py upto 30 2` | 23,023 of 23,023, exact ℚ-rank |
| 00:33 | set comparison with their `final_region.region()` (read-only import) | identical sets |
| 00:33 | `python3 code/rv_exceptional.py` | 72/128, 16/64, 12/32 good; stated s good |
| 00:34 | `python3 code/rv_families.py` | family A: no integer solution; direct certificates 0 failures |
| 00:35–00:36 | realizability brute force; `rv_rows.py` (two ranges) | 0 mismatches; 69 trees, 0 violations |
| 00:43–00:45 | `rv_endtoend.py 3 22`, `23 26`, `big 34` | 3,374 + 5,740 + 8,232 trees; 0 issues |
| 00:46–00:48 | `rv_hard13.py 5 150` | 31 worst-case trees; 0 violations |

Checksums: `review/SHA256SUMS`. Scripts: `review/code/`. Logs: `review/logs/`.

## 8. Not checked by me

- Their implementation 2 (the 7,892,382-tree superset) and their n ≤ 44 census and direct certificates.
- The NT = 2..5 region searches. These are superseded and not needed.
- Family B, D1+, D2, D3 and Theorem F2. None of them is used in the proof of Theorem 9.22.
- The Lean build itself (not run, as instructed). I relied on the recorded logs, the sha256 match and the grep.

## 9. Recommendation

1. Fix MINOR-1 and MINOR-2 (wording only). Optionally adopt the shorter family-A proof (MINOR-3) and the D1 sentence (MINOR-4).
2. The result is then ready for a short note: "The switching conjecture for main eigenvalues holds for trees of diameter at most 4". Keep the finite search of 13,376 trees as a documented, reproducible computer-assisted step; it has now been reproduced three times.
3. Before release, re-run G1 on the day, as §9.23 already says. 2609.27046 is five days old, and trees are named in it as an open case.
