# Referee report 3: Conjecture 14 for min(a,b) ≤ 8 (certification for a = 5, 6, 7, 8)

Independent referee (Claude agent, folder `review3/`), 2026-09-26, 18:08–18:50 UTC. I did not write any of the material under
review.

**Scope.**
- Paper 1, `outputs/ICG-q3-general/note.tex` v1.4: Section 10 (Lemmas 21–24, facts (12)–(13)), Proposition 31 and its proof,
  the "certificates" and "checks" paragraphs of Section 12.
- `PROOF.md` §10 and the programs `generic_prover.py`, `generic_fast2.py`, with their logs
  `logs/generic_fast2_a{5,6,7,8}.log`.
- `review2/`: `REVIEW_GENERIC.md`, `c3_certify.py`, `r2poly.py`, `r2core.py` and their logs, and `crosscheck/logs/`.

**Ground rules kept.**
- Nothing was published, pushed or posted, and the paper was not edited.
- No file outside `review3/` was created or modified. The authors' and referee 2's programs were run from `review3/` or
  imported read-only, with `PYTHONDONTWRITEBYTECODE=1`. Three files changed during the session: `outputs/HANDOFF.md`,
  `outputs/results-registry.json` and `outputs/AI4Math-项目元文档.md` (at 18:08 and 18:42 UTC). They were changed by another
  process, not by this review.
- At most 6 worker processes ran at a time. One 0.4 s test briefly used about 10 numpy threads before the thread limits were set.
- Total CPU: **35.6 min of the 90 min budget**. Every run is listed in `logs/cpu_ledger.tsv`.
- All arithmetic is exact: Python integers, `Fraction` and SymPy rationals.
- Environment: Python 3.12.4, SymPy 1.13.1, NumPy 1.26.4, macOS.

---

## 0. Verdict

| a | verdict | blocker | major | minor |
|---|---|---|---|---|
| **5** | **ACCEPT WITH MINOR REVISIONS** | 0 | 0 | m1–m6 (write-up and repository only) |
| **6** | **ACCEPT WITH MINOR REVISIONS** | 0 | 0 | same |
| **7** | **ACCEPT WITH MINOR REVISIONS** | 0 | 0 | same |
| **8** | **ACCEPT WITH MINOR REVISIONS** | 0 | 0 | same |

I found no mathematical error, and no computation failed.

- **The reduction holds for every a ≥ 2, verbatim.** Proposition 31 and the lemmas it uses (21–24, (12)–(13)) are stated and
  proved for general a. No step uses a ≤ 4, including the five points named in the task (§1). The equality step is proved by
  hand in Lemma 24 for all a. The issue behind referee 2's finding F1 therefore does not arise in the paper's version, and both
  programs also certify it directly.
- **The only a-dependent input is the finite list (S_a), (F_a), (C_a).** For a = 5, 6, 7, 8 it is complete (§2):
  - My own list, generated from the text of Proposition 31, matches the authors' list item by item (instrumented re-run).
  - It matches referee 2's list: the numbers of branch expressions are identical in every category.
  - All three programs select the same sets of last columns that need (C_a).
- **Certified three times, in full, 0 failures** (§2):
  - the authors' `generic_fast2.py`, re-run: identical to their logs;
  - referee 2's `c3_certify.py`, re-run: identical to their logs;
  - a third implementation written for this review, `rv3_certify.py`.
  No sampling was needed; every task was run for every a.
- **Negative controls fire** (§3).
  - With the target strengthened by 0.1 %, the certificate fails exactly at the items that correspond to Y⁺, and nowhere else.
  - It also fails for b of the wrong parity, and on regions containing p = q = 3 or q = 2.
- **The theorem holds in every spot check** (§4).
  - Exact branch and bound: 208 runs on 17 shapes with min(a,b) ≥ 5, at prime and rational points of both regions.
  - The branch and bound was validated against 13 plain exhaustive searches, up to 2³¹ matrices.
  - A replay of the proof's case analysis on 1 600 random sign matrices with a = 5–8 found no problem.

**Consequence.** Paper 1 may claim Conjecture 14 for every exponent pair with a + b even and min(a,b) ≤ 8, and all pairs of
distinct odd primes, as a computer-assisted result that is not formalised in Lean. The text needs the revisions of §5 and the
wording of §7. The smallest open pairs then become (9,9), (9,11), (11,9) and (10,10).

---

## 1. Task 1: does the reduction apply verbatim for each a ≤ 8?

The proof of Theorem 5 for min(a,b) = a (p on the a-side) reduces to Proposition 31 on the two regions R₁ (p ≥ 5, q ≥ 3) and
R₂ (p = 3, q ≥ 5). Every ordered pair of distinct odd primes lies in one of them. The passage from G(Y) to the energy and the
prime swap do not depend on a. I checked every step of Section 10 and of the proof of Proposition 31 for a hidden use of
a ≤ 4 and found none. Details:

| step | where a could enter | finding |
|---|---|---|
| facts (12)–(13) | row structure of T_a(p), sign pattern of α = M s_a, 2uᵢ ≤ \|αᵢ\|, δ_a ≥ 3, Pδ_a > p^a, ωᵢ ≤ P\|αᵢ\| | proved for all a; re-verified symbolically for a = 2–8 on both regions (`rv3_facts.py`, SymPy) |
| Lemma 21 (column identity) | none: Lemma 18 applied to each of the a + 1 rows | general; checked exactly on 1 600 random (Y, p, q) with a = 5–8 (`rv3_replay.py`) |
| Lemma 22, first part of the proof of Prop. 31 (S_a ⇒ ψ > 0) | monotonicity in P ≥ P_min, affine in μ; alternating columns via (13) | general |
| regimes R0–R2 (the families of F_a) | only the parity of b ≡ a and the monotonicity (4) of μ_j | general; for a = 5–8 the true (μ_{J−1}, μ_{b−2−J}, ρ) lie in the box of the assigned family with r ≥ ρ, and ψ_J > 2xδ_aρ, in all 371 replayed cases J < b (families F0–F4 all hit) |
| set of column types | the a = 2 proof used a table of 4 types up to sign; for general a all 2^{a+1} vectors are enumerated | all three programs enumerate every c ∈ {±1}^{a+1} (and every state sign), with no type table |
| classification of last columns (cheap / Δ(g) > 2δ_a / g₊) | signs of Δ(g) − 2δ_a | for a = 5–8 every sign is certified strict on both regions (no undetermined case); identical lists in all three programs (§2) |
| chain analysis for cheap last columns | K = 4 in (C1)/(C2); the intervals I_k; the special point y = 1 when b = k + 1; the full-chain bounds (C3) | general; certified for a ≤ 8 with K = 4; replayed for chains with k = 0–4, k ≥ 5 and the full chain |
| equality step (Lemma 24) | Δ(g₊) = 2δ_a; all cells of Y⁺ vanish; forcing of every column of Y⁺ | proved by hand for all a from (12)–(13); identity re-checked symbolically for a ≤ 8 (my certifier checks it in each region) |
| the F1 fix ("equality forces the next column") | column b − 1 when b = 1 (μ = 1) | not needed in the paper's version: the cell at coordinate a has AB > 0 and \|B\| ≤ δ_a + 2 < Pδ_a (since (P−1)δ_a ≥ 3), so it is negative by (11) for every μ ∈ [0,1], including μ = 1; both programs also certify s(wrong) > 0 directly ("EQwrong", "EQ wrong choice") |
| certificate primitive | coefficient test after p = 5 + s, q = 3 + t (R₁) or p = 3, q = 5 + t (R₂); denominators q^K(q+1)^L | sound for all a; vertex reduction valid because each quantity is affine in μ (or y) and concave in m for m > 0 |

The places where a enters are all finite and certified:
- the certified signs of all entries of Mc (no program aborted, and none found an undetermined sign);
- the classification of the 2^a last columns;
- the three lists (S_a), (F_a), (C_a).

---

## 2. Task 2: completeness of the task lists, and certification

### 2.1 My independent certifier `rv3_certify.py`

It is written from the text of Proposition 31 and imports nothing from the authors or from referee 2. It differs from both by
design:

- T_a(p) is built from the Ramanujan-sum definition t_ij = φ(p^{a−i}) c_{p^{a−j}}(p^i) with symbolic p. It is compared with the
  closed formula of Section 2 coefficient by coefficient, and with genuine Ramanujan sums at p = 3, 5, 7.
- The task list is enumerated from the statement of Proposition 31: the families of F_a, the sets I_k, and (C1)–(C3).
- Each cell comes from the case table of the proof of Lemma 10. The case is chosen by a *certified* comparison of m|vᵢ| with
  |Aᵢ| (same signs) or with P|Aᵢ| (opposite signs); both case formulas are kept only when that comparison is undetermined.
- Every expression is built from separable terms and expanded into integer arrays.
- A fraction of the items is validated end to end: the certified quantity is evaluated at a random exact point and compared
  with a direct evaluation from the definitions (closed-form T_a, μ by recursion, h by its definition). Every comparison
  agreed exactly. For a = 5 a separate run validated **all** 10 771 items.

Results (both regions, K = 4, target exactly as in Proposition 31):

| a | S items | F items / branches | C1 items / branches | C2 | C3 | last columns needing (C_a), R₁ / R₂ | failures | CPU |
|---|---|---|---|---|---|---|---|---|
| 2 | 12 | 168 / 193 | 168 / 198 | 4 | 2 | 1 / 1 | 0 | 0.0 s |
| 3 | 28 | 390 / 528 | 975 / 1 236 | 10 | 10 | 2 / 3 | 0 | 0.2 s |
| 4 | 60 | 744 / 1 233 | 2 604 / 4 131 | 14 | 7 | 3 / 4 | 0 | 0.6 s |
| **5** | 124 | 1 638 / 3 227 | 9 009 / 16 680 | 22 | 22 | 4 / 7 | **0** | 1.5 s |
| **6** | 252 | 3 048 / 7 505 | 25 908 / 57 655 | 34 | 17 | 5 / 12 | **0** | 8.4 s |
| **7** | 508 | 6 630 / 19 556 | 69 615 / 182 508 | 42 | 42 | 6 / 15 | **0** | 21.1 s |
| **8** | 1 020 | 12 264 / 45 753 | 159 432 / 514 111 | 52 | 26 | 7 / 19 | **0** | 54.4 s |

- **Item counts.** The item counts are exactly those that Proposition 31 prescribes: 2 regions × (2^{a+1} − 1) columns × 12
  (a even) or 13 (a odd) vertices for (F_a). For (C1) the same product is taken per last column needing (C_a).
- **Agreement with referee 2.** For every a = 2,…,8 and every category, the branch counts coincide with those of `c3_certify.py`
  (FD1, CH, CHalone, full). Both programs expand the cells directly and split exactly the same undetermined comparisons.
- **Reviewed cases.** For a = 3, 4 the lists of last columns are exactly those printed in the paper.

### 2.2 Re-runs of the two existing implementations (full, not sampled)

| program | a | result | identical to the existing log? | CPU |
|---|---|---|---|---|
| `review2/c3_certify.py` (referee 2) | 5 | S 128, FD1 3 227, CH 16 680, CHalone 22, full 22, EQ 20; 0 failures; 10 647 items validated | yes (`review2/logs`, `crosscheck/logs`) | 6.9 s |
|  | 6 | S 256, FD1 7 505, CH 57 655, 34, 17, 20; 0 failures | yes | 20.6 s |
|  | 7 | S 512, FD1 19 556, CH 182 508, 42, 42, 24; 0 failures | yes | 67.9 s |
|  | 8 | S 1 024, FD1 45 753, CH 514 111, 52, 26, 24; 0 failures; 171 696 validated | yes | 184.9 s |
| `generic_fast2.py` (authors) | 5 | FD1 69 368, CH 381 524, S 128, other 299; 0 failures | yes (`logs/generic_fast2_a5.log`) | 4.1 s |
|  | 6 | 259 104 / 2 202 384 / 256 / 430; 0 failures | yes | 21.3 s |
|  | 7 | 1 129 336 / 11 858 028 / 512 / 1 101; 0 failures | yes (run twice, plain and instrumented) | 131.4 + 134.4 s |
|  | 8 | 4 182 048 / 54 366 624 / 1 024 / 1 604; 0 failures | yes (instrumented run) | 664.8 s |

**Item-by-item completeness of the authors' list** (`rv3_fast2_items.py`). The script subclasses `FastProver` and records
every call of `certify()`, then compares the list with the structure required by Proposition 31: every c ≠ −s_a, every family,
every vertex, and for (C1) every k = 0,…,4, every c ≠ (−1)^{k+1}g and every vertex of I_k.

| a | 5 | 6 | 7 | 8 |
|---|---|---|---|---|
| discrepancies | 0 | 0 | 0 | 0 |
| recorded F items | 1 638 | 3 048 | 6 630 | 12 264 |
| recorded C1 items | 9 009 | 25 908 | 69 615 | 159 432 |

The recorded counts equal mine. (C2), (C3), (S_a) and the EQ checks are counted by the program's own counters and also equal
mine.

**Last columns** (`rv3_compare_cheap.py`, `logs/rv3_compare_cheap.log`). The sets of last columns that need (C_a) are
*identical as sets* in the three programs, for a = 5–8 on both regions:
- R₁: 4, 5, 6, 7 columns for a = 5, 6, 7, 8;
- R₂: 7, 12, 15, 19 columns.

Every other admissible last column g, other than the anti-checkerboard column and g₊, has Δ(g) > 2δ_a certified strictly.

### 2.3 Soundness and independence

- **Primitive.** A polynomial in s, t ≥ 0 with nonnegative coefficients and a positive constant term is positive. The
  denominators q^K(q+1)^L are positive. The vertex reduction is exact (§1). Coefficient growth is harmless, since only Python
  integers are used.
- **Where the three programs differ.** They are three separate code bases, with separate matrix construction, list generation,
  cell evaluation (uniform min-formula / |·|-splitting / case table) and polynomial arithmetic. The authors' `generic_fast2.py`
  is a port of their SymPy `generic_prover.py` and shares its list logic; independence comes from the two referee programs.
- **What they share.**
  - The mathematical reduction. I checked it by hand (§1) and replayed it numerically.
  - The coefficient test. It is sound.
- **Guard against a shared error.** The branch-and-bound runs of §4 check the conclusion directly.

---

## 3. Task 3: negative controls (`rv3_negctl.py`; each must fail)

| control | a = 5 | a = 6 | a = 7 | a = 8 |
|---|---|---|---|---|
| NC1: 2δ_a → 2·1.001·δ_a (g₊ then an ordinary last column) | 6 failures | 4 | 6 | 4 |
| NC2: 2δ_a → 2·(5/4)·δ_a | 10: F family F2 (regime R1) ×2, C1 at g₊ ×6, C3 for b = 1 ×2 | 6: F2 ×2, C1 at g₊ ×4 | – | – |
| NC3: b of the wrong parity (a + b odd) | 10 | 16 | 10 | 16 |
| NC4: region p = q = 3 | 2 (S_a) | 2 | 2 | 2 |
| NC5: region p ≥ 5, q ≥ 2 | 266 | 140 | 1 304 | – |

- **NC1 is sharp.** For every a, *all* its failures are (C1) with g = g₊, k = 0 and c = (−1)^{a−1}s_a, at every vertex of I₀
  and in both regions (3 vertices × 2 regions for odd a, 2 × 2 for even a). This is the column of Y⁺ at the state g₊, where all
  cells vanish. So a 0.1 % stronger target breaks the certificate exactly where the extremal matrix Y⁺ lies, and nowhere else.
- **NC3.** For a + b odd the checkerboard s_a s_bᵀ is admissible and has G = d_a d_b > Θ. As predicted, the full-chain
  condition (C3) fails for g = (−1)^b s_a, for every a.
- **NC4.** At p = q = 3 the step (S_a) fails for c = ±(1,1,−1,1,−1,…), for every a.
- **Coverage.** NC2 was run for a ≤ 6 and NC5 for a ≤ 7, to save CPU.

**Margin probe** (informational, not a negative control). With 2δ_a → 2·(11/10)·δ_a and g₊ kept aside:
- a = 6 and a = 8 still certify completely.
- For a = 5 and a = 7 only the full-chain condition (C3) for b = 1 fails, for two last columns on R₂ (p = 3). For b = 1 that
  bound is exact (D̂₁/ρ₁ = D̂₁/μ₀), so this is a genuine but positive margin below 10 %, which tends to a positive limit as
  q → ∞.
- At the true target every item is certified by the coefficient test, so this is not a correctness issue.
- Referee 2's 11/10 control for a = 3, 4 flagged only the g₊ identity.

---

## 4. Task 4: spot checks of the theorem itself

**Plain exhaustive search** (`rv3_brute.py`: int64 with an asserted overflow bound, no lemma used), each compared with the
branch and bound at the largest and the 6th-largest value of G.

| shape (a,b) | (p,q) | matrices |
|---|---|---|
| (5,1) | (5,3), (3,5), (7,3) | 2¹¹ |
| (5,3) | (5,3), (3,5) | 2²³ |
| (6,2) | (5,3), (3,5), (7,3) | 2²⁰ |
| (7,1) | (5,3), (3,5) | 2¹⁵ |
| (7,3) | (5,3) | 2³¹ |
| (8,2) | (5,3), (3,5) | 2²⁶ |

In all 13 runs the maximum is Θ, attained exactly at Y⁻ and Y⁺, and the two methods agree on every threshold. These shapes
have min ≤ 3, so they validate the searches and the small-b end of the a = 5–8 lists, not new cases.

**Exact branch and bound** (`rv3_bnb.py`, written independently of `review2/bnb.py`):
- It enumerates columns from the right, using the Lemma 7 identity for G and the bound Σψ ≥ 0 (Lemma 18 summed over rows).
- The crude form of Lemma 22 that the bound needs is verified exactly at each point before use.
- Every reported matrix is recomputed from Z = T_a(p) Y T_b(q)ᵀ.

It was run **208 times on 17 shapes with min(a,b) ≥ 5**, with **0 failures**. In every run exactly Y⁻ and Y⁺ attain G = Θ,
using at most 27 392 nodes.

| shapes | points |
|---|---|
| (5,5), (5,7), (7,5), (6,6), (7,7), (8,8) | 18 each |
| (5,9), (5,11), (6,8), (8,6), (6,10), (7,9), (8,10) | 12 each |
| (5,25), (6,20), (7,15), (8,16) | 4 each |

The points:
- the prime pairs (5,3), (3,5), (7,3), (3,7), (5,7), (7,5), (11,3), (3,11), (31,3), (3,31);
- the rational points (11/2, 7/2) and (3, 13/2);
- for the six shapes with 18 points, six more random rational points of R₁ and R₂ (fixed seed; listed in
  `logs/rv3_bnb_random_rational.log`).

Earlier branch-and-bound coverage of new shapes (referee 2): (5,b) for b ≤ 11 and b = 25; (6,b) for b ≤ 10 and b = 20; (7,5),
(7,9) and (8,6). There was none for (7,7), (8,8), (8,10) or (8,16).

**Replay of the proof** (`rv3_replay.py`, 1 600 random sign matrices, a = 5–8, b ≤ 13, rational points of both regions).
Lemma 21 held exactly in every case, and ψ_j ≥ 0 held, with ψ_j > 0 off ±s_a. Every branch of the case analysis was hit and
checked at the true parameter values:

| branch | cases |
|---|---|
| J < b (families F0–F4) | 371 |
| g₊ | 279 |
| Δ(g) > 2δ_a | 472 |
| chains with k = 0,…,4 | 191 |
| chains with k ≥ 5 | 40 |
| full chain | 126 |
| Y⁻ or Y⁺ | 121 |

Θ − G > 0 held in every non-extremal case, with 0 problems.

---

## 5. Findings

**BLOCKER.** None.

**MAJOR.** None.

**MINOR** (all concern the write-up or the repository; none affects correctness):

- **m1. The paper is written for min ∈ {3,4} throughout.** Claiming ≤ 8 needs consistent changes at (line numbers of
  `note.tex` v1.4):
  - the version note (l. 21–29) and the abstract (l. 57–60);
  - Theorem 5 (l. 167–175) and the paragraphs after it (l. 177–183, 187–192);
  - l. 475, and l. 516–522 ("remains open when min ≥ 5; smallest open pairs (5,5)…");
  - Section 12 (l. 1265–1278, the certificates paragraph l. 1396–1451, the checks l. 1453–1468);
  - Section 13 (l. 1471–1477, 1645) and the disclosure (l. 1671–1704).

  Suggested text is in §7.
- **m2. Which of the authors' programs ran for a = 5–8.** Only `generic_fast2.py` was run; the SymPy `generic_prover.py` /
  `generic_prover_fast.py` have logs only for a ≤ 4. The certificates paragraph currently says that `generic_prover.py`
  certifies the lists "with SymPy" and that `generic_fast2.py` "repeats" them. For a = 5–8 it must say that the lists were
  certified by `generic_fast2.py` and `c3_certify.py`, and by `rv3_certify.py` if it is cited.
- **m3. The lists are too long to print.** For a = 5–8 there are 4/7, 5/12, 6/15 and 7/19 last columns needing (C_a) on R₁/R₂.
  Give the counts, state that every other admissible last column has Δ(g) > 2δ_a certified strictly, and point to the logs for
  the lists. Also give the certificate counts per a (§2.2, §7).
- **m4. Repository.** If `review3/` is cited, add its programs and logs to
  `certificates/icg-equal-parity/theorems-b-c`. Its README currently has a section "Not claimed" for a = 5–8, which must be
  rewritten.
- **m5. Open pairs.** The smallest open exponent pairs become (9,9), (9,11), (11,9) and (10,10). `PROOF.md` §10 omits (11,9).
- **m6. Process.** Per the project playbook, refresh the literature and prior-work check (gate G3) before the extended claim is
  released. The paper's searches covered equal-parity exponents in general, but they predate this claim.

**Remarks.**
- **Trust boundary.** 3 ≤ min(a,b) ≤ 8 is computer-assisted and not formalised. Lean covers min ≤ 2.
- **Margins** (§3) are positive but, for b = 1 and odd a on R₂, below 10 %. This is expected and not a concern.
- **Beyond 8.** I did not test a ≥ 9.

---

## 6. Exactly what was re-run

Every command was run through `run_timed.py`, which records CPU time in `logs/cpu_ledger.tsv`. Total **2 136 s = 35.6 min**
over 34 runs, plus under 10 s of small unlogged interactive checks (a listing of the NC2 failures, a test that the SymPy
coefficient test can fail, the set comparison). One run failed immediately (a shell word-splitting error, 0 s) and was repeated.

| label | command (cwd `review3/` unless noted) | CPU |
|---|---|---|
| c3_a5 … c3_a8 | `python3 ../review2/c3_certify.py a 4 VALN` (VALN = 400, 200, 100, 50; cwd `rerun_c3/`, logs in `rerun_c3/logs/`) | 6.9 + 20.6 + 67.9 + 184.9 s |
| fast2_a5 … fast2_a7 | `python3 ../generic_fast2.py a` (logs in `rerun_fast2/`) | 4.1 + 21.3 + 131.4 s |
| fast2_items_a5 … a8 | `python3 rv3_fast2_items.py a` (full re-run of `generic_fast2` plus the item list) | 3.9 + 21.9 + 134.4 + 664.8 s |
| rv3_a2 … rv3_a8 | `python3 rv3_certify.py a --val 0.2/0.05/0.02/0.01` | 86.2 s in all |
| rv3_a5_fullval | `python3 rv3_certify.py 5 --val 1.0 --seed 7` | 19.7 s |
| negctl | `python3 rv3_negctl.py 5 6` (run twice; the second after a cosmetic fix of the summary filter) and `python3 rv3_negctl.py 7 8` | 20.5 + 20.7 + 310.2 s |
| margin | `rv3_certify.py a --need 11/10 --skip-gplus` for a = 5–8 | 12.6 s |
| facts | `python3 rv3_facts.py` | 0.4 s |
| replay | `python3 rv3_replay.py 400 20260926` (plus a 10-per-a test) | 24.1 s |
| brute | `python3 rv3_brute.py … --cmp` (13 runs, plus a 4-run test) | 199.2 + 4.3 s |
| bnb | `python3 rv3_bnb.py …` (172 runs; 36 rational-point runs; 7 timing tests) | 139.5 + 25.1 + 11.0 s |
| compare | `python3 rv3_compare_cheap.py` | < 1 s |

---

## 7. Recommended wording for Paper 1

Only the claim-bearing sentences are given. Everything else in m1 changes "{3,4}" to "{3,…,8}" (or "≤ 4" to "≤ 8") and "≥ 5"
to "≥ 9".

- **Abstract** (replacing the last computer-assisted sentence):
  > A computer-assisted extension of the argument, whose certificates were checked by three independently written programs,
  > proves the conjecture also when one of the exponents is at most $8$.
- **Theorem 5:**
  > Let $p,q$ be distinct odd primes, let $a,b\ge1$ with $a+b$ even and $\min\{a,b\}\le8$, … For $3\le\min\{a,b\}\le8$ the
  > proof is computer-assisted, and it is not formalised in Lean.
- **After Theorem 5:**
  > For $3\le\min\{a,b\}\le8$, the method of Theorem 4 reduces the claim, separately for each of these exponents and for all
  > values of the other exponent at once, to a finite list of inequalities between explicit rational functions of $p$ and
  > $q$. We verified these lists by exact computer calculation with independently written programs, two of them written by
  > referee agents (Section 12).

  and later:
  > … for every order $p^aq^b$ with $\min\{a,b\}\le8$ … The conjecture remains open when $\min\{a,b\}\ge9$.
- **Section 8** (l. 521–522):
  > Conjecture 14 remains open when $\min\{a,b\}\ge9$; the smallest open exponent pairs are $(9,9)$, $(9,11)$, $(11,9)$ and
  > $(10,10)$.
- **Section 12, certificates paragraph** (to add after the a = 3, 4 counts; replace the sentence "Runs of the same
  certification for a = 5, 6, 7 and 8 have not been reviewed, and we do not claim these cases"):
  > For $a=5,6,7,8$ the lists were generated and certified by \texttt{generic\_fast2.py} (the SymPy version was run only for
  > $a\le4$), with $69\,368$, $259\,104$, $1\,129\,336$ and $4\,182\,048$ branches for (F$_a$) and $381\,524$, $2\,202\,384$,
  > $11\,858\,028$ and $54\,366\,624$ for (C1), and independently by \texttt{c3\_certify.py}, all without failures. The last
  > columns that need (C$_a$) number $4$, $5$, $6$, $7$ on $\mathcal R_1$ and $7$, $12$, $15$, $19$ on $\mathcal R_2$; they
  > are listed in the logs, and every other last column $g$ with $g_a=-1$, other than $-(-1)^as_a$ and $g_+$, satisfies
  > $\Delta(g)>2\delta_a(p)$ on the region. A third program, written by a second referee agent
  > (\texttt{review3/rv3\_certify.py}), builds $T_a(p)$ from the Ramanujan-sum definition, enumerates the conditions of
  > Proposition 31 from its statement, evaluates each cell by the case analysis of Lemma 10, and checks certified items
  > against a direct evaluation at random exact points. It certifies (S$_a$), (F$_a$) and (C$_a$) for $2\le a\le8$ on both
  > regions without failures. As negative controls, the certificates fail exactly at the items corresponding to $Y^+$ when
  > $2\delta_a(p)$ is replaced by $2.002\,\delta_a(p)$, for $b$ of the other parity, and on regions containing $p=q=3$ or
  > $q=2$.
- **Checks paragraph** (add):
  > For $5\le a\le8$ the conclusion of Proposition 31 was checked by an exact branch-and-bound search in $208$ runs on the
  > shapes $(5,5)$, $(5,7)$, $(7,5)$, $(5,9)$, $(5,11)$, $(6,6)$, $(6,8)$, $(8,6)$, $(6,10)$, $(7,7)$, $(7,9)$, $(8,8)$,
  > $(8,10)$, $(5,25)$, $(6,20)$, $(7,15)$ and $(8,16)$ at prime and rational points of both regions, and the search was
  > validated against complete enumeration for $(5,1)$, $(5,3)$, $(6,2)$, $(7,1)$, $(7,3)$ and $(8,2)$.
- **Section 13 and the disclosure:** replace "{3,4}" by "{3,…,8}", and add:
  > A third Claude Code referee agent checked the extension to exponents $5$ to $8$ and wrote a third certification program.

  This claims only what was done. The author's own role is unchanged.

---

## 8. Files in `review3/`

| file | purpose |
|---|---|
| `REVIEW_A5_8.md` | this report |
| `rv3_certify.py` | independent certifier of (S_a), (F_a), (C_a); negative-control switches `--need`, `--bpar`, `--regions`, `--K`, `--skip-gplus` |
| `rv3_fast2_items.py` | instrumented re-run of the authors' `generic_fast2.py`, with an item-by-item list check |
| `rv3_negctl.py` | negative controls NC1–NC5 |
| `rv3_facts.py` | SymPy check of (12)–(13), the closed forms, and Δ(g₊) = 2δ_a for a ≤ 8 |
| `rv3_replay.py` | replay of the proof on random sign matrices |
| `rv3_bnb.py`, `rv3_brute.py` | branch and bound; exhaustive search and its comparison |
| `rv3_compare_cheap.py` | set comparison of the lists of last columns across the three programs |
| `run_timed.py` | runner with the CPU ledger |
| `logs/` | all logs, including `cpu_ledger.tsv`: `rv3_certify_a{2..8}.log`, `rv3_certify_a5_fullvalidation.log`, `fast2_items_a{5..8}.log`, `rv3_negctl_a5_a6.log`, `rv3_negctl_a7_a8.log`, `rv3_margin_*.log`, `rv3_facts.log`, `rv3_replay.log`, `rv3_brute_validate.log`, `rv3_bnb_spotchecks.log`, `rv3_bnb_random_rational.log`, `rv3_compare_cheap.log`, and the test logs `test_*.log` |
| `rerun_c3/`, `rerun_fast2/` | outputs of the plain re-runs of referee 2's and the authors' programs |
