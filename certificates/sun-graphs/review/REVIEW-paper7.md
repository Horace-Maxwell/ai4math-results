# REVIEW (paper 7): *The minimum order of a counterexample to a conjecture on integral generalized sun graphs*

Second independent referee, fresh eyes. I did not write the paper, did not do the research, and did not write implementation C or the first report. 2026-09-26, 22:03–22:46 UTC (`date -u`). Reviewed file: `note.tex`, SHA-256 `40807e32…a048522` (not edited). Time box 2 h, at most 4 concurrent processes, no Lean locks taken, nothing published or pushed. No e-mail address was sent in any request.

- **Reviewed:**
  - `outputs/Sun-graphs/note.tex` and `note.pdf` (10 pages);
  - `work/round6/sun-graphs/`: `CONTRACT.md`, `PROOF.md`, `code/`, `logs/` (including `logs/n42/INDEX.txt`), `review/REVIEW.md`, `review/code/`, `review/logs/`;
  - `outputs/Sun-graphs/checks-addition/`.
- **Source re-fetched:** `curl -sL https://arxiv.org/e-print/2609.28754` at 22:07 UTC. The e-print serves the latest version, and its `ArXiv__1_.tex` is byte-identical to v1: SHA-256 `21a822ee…c64f8`, the same as CONTRACT.md. So there is still no v2 with changed source.
- **Everything I produced** is in `review/paper7/`:
  - `code/`: `sunD_v1.c`, `sunD2.c`, `sunD3.c`, `sunD3_maxb16.c`, `validate_D.py`, `confirm_D.py`, `numcheck.py`, `bms21_spot.py`;
  - `logs/`, including `D_code_hashes.txt`.
  - Scratch copies (binaries, the TeX build, rebuilt A/B binaries) are in the session scratchpad, `…/scratchpad/paper7-review/`.

Line numbers refer to `outputs/Sun-graphs/note.tex` (795 lines).

## 1. Verdict: **FIX FIRST (minor). No BLOCKER.**

**What checks out:**
- **Mathematics.** Every step of Theorems 1 and 2 is correct. This includes Lemma 4.1 and the parts the first referee never saw: Lemma 4.2, Corollary 4.3, the hand proofs for b = 14, 18, odd b ≥ 5 and even b ≥ 22, Proposition 3 and Corollary 3.1.
- **Computation.**
  - A fifth program D, written by me with a different enumeration and a different exact test, confirms the two central claims at N = 42:
    - b = 6: 153,225,129 sequences tested; the only integral graph is one dihedral orbit, C_{6,1}(0,6,6,12,6,6);
    - b = 10: 119,245,995 sequences, none integral.
  - It also confirms b = 3 (unpruned, up to 49 vertices), b = 4 (the 3 graphs; 4 classes up to 49 vertices), and b = 8, 10, 12 at N = 41.
  - The unrefereed program versions check out:
    - I read their code; it is sound.
    - Rebuilt from the hashed sources, they reproduce their logged counters exactly (§4.6).
- **Tables.** Every number in Tables 1–3 matches the logs, and all ten SHA-256 prefixes in Table 2 match the files.
- **Faithfulness.** Conjecture 2 and the Braga–Moraes–Santos (BMS) question are restated exactly. The credit to Braga–Rodrigues–Trevisan (BRT) 2017 is exact.
- **Build.** Compilation is clean.

**Fix before posting:**
- **S1:** check and cite Veras 2021.
- **S2:** the cited repository version must exist before posting.
- **S3:** update the "not refereed" sentences.

The NITs are optional.

| # | Claim | Verdict |
|---|---|---|
| 1 | Theorem 1: C_{6,1}(0,6,6,12,6,6) is the only counterexample with n ≤ 42 | **Correct.** Hand proofs checked; b = 3, 6, 10 independently recomputed (D) |
| 2 | Theorem 2 and its credit to BRT 2017 | **Correct.** BRT p. 296 and Table 1 on p. 297 checked on the PDF. Possible missing citation: S1 |
| 3 | Proposition 3 (q ∣ 2g·c_g), Corollary 3.1 (≥ 102 vertices for b ≥ 15) | **Correct.** All numbers recomputed |
| 4 | Independent recomputation | **Done:** b = 6 and b = 10 at N = 42; b = 4 at N = 41 and 49; b = 8, 10, 12 at N = 41; b = 3 at N = 42 and 49; b = 14, 18, 22, 26, 30 at N = 42 |
| 5 | Faithfulness | **Exact** |
| 6 | Tables 1–3 against the logs | **All match** (one log-annotation NIT, N9) |
| 7 | Wording | **Hedged and dated.** It says "not a guarantee of priority", has no priority-race framing, and does not list AI as an author. It makes no claim about the author beyond the handbook template ("under the author's direction"). The placeholder `%% AUTHOR-ROLE-SENTENCE` is present (line 741), as expected. Two updates: S3 and N1 |
| 8 | Compile | **Clean:** 3 × pdflatex, exit 0; 0 warnings, 0 overfull or underfull boxes, 0 undefined references; 10 pages; text identical to the shipped `note.pdf` |

## 2. Findings

### SHOULD

**S1 — Veras 2021 is neither cited nor checked (lines 112–116, 141–156).**
- BMS cite `[veras]`: M. S. T. Veras, *Buscando grafos unicíclicos integrais* [Searching for integral unicyclic graphs], XXXIII Salão de Iniciação Científica, UFRGS, 2021, https://lume.ufrgs.br/bitstream/handle/10183/243963/Resumo_72921.pdf.
- It is a computer search for integral unicyclic graphs. BMS credit it with C_{4,1}(0,16,32,16), on 68 vertices.
- Its search range may overlap Theorem 2 ("no other integral generalized sun graph up to 41 vertices") and the prior-work statement.
- I could not open it: WebFetch failed with "unable to verify the first certificate", and I did not force it.
- **Fix:** read the abstract (1–2 pages) and cite it next to BRT in lines 112–116, stating its search range.
  - If the range covers part of Theorem 2, say so and credit it.
  - If not, a one-line mention is enough.
  - Add it to the prior-work list in lines 141–156.
  - It cannot contradict Theorem 2 (four programs agree); the issue is credit only.

**S2 — The cited release does not exist yet (lines 643–644, 762–766).**
- The paper points to "version 1.6.0 of [repo], directory `certificates/sun-graphs/`".
- The local release copy `outputs/release/ai4math-results` is at 1.5.0 (`CITATION.cff`) and has no `certificates/sun-graphs/`.
- **Fix:** release v1.6.0 before the paper is posted, as README step 2 already plans. It should contain:
  - the sources of Table 2 (no binaries);
  - `logs/` with `logs/n42/`, the superseded logs and `code_hashes*.txt`;
  - `review/` with C, C2, `C_code_hash.txt` and `C2_code_hash.txt`;
  - optionally `review/paper7/`.
- Then check the ten hash prefixes of Table 2 against the released files. If the paper goes out first, change the reference.

**S3 — The refereeing statements are now out of date (lines 645–651 and 735–737).**
- The paper says Lemma 4.2, Corollary 4.3 and the later versions "have not been refereed" / "were not refereed".
- This report checks them:
  - the proofs line by line;
  - the sources of A v5 and v6, B v2 and v3, and B2 v2;
  - key counters reproduced;
  - an independent program D.
- **Fix, if the author accepts this report.** For example, in the disclosure:
  > A second referee agent, which had produced neither the results nor implementation C, later checked Lemma 4.2, Corollary 4.3 and the later program versions, and recomputed the cases b = 3, 4, 6, 8, 10, 12, 14, 18 with a fifth program (D) of its own.
- Change the Versions paragraph accordingly, and add "D" to Table 3 (b = 3, 6, 10 for Theorem 1; b = 4, 8, 10, 12 for Theorem 2).
- The current text under-claims, so it is not wrong. But the disclosure should describe what was actually done.

### NIT

- **N1 (line 50; lines 137–138; line 707).** "Independent programs" and "independent confirmations" need qualifying.
  - A and B were written by the same agent in one session (line 491 says only "written separately"). B v3 adopted A's rotation rule, and A v6 and B v3 share Lemma 4.2.
  - The claim still holds: each of b = 3, 6, 10 has A plus C or C2, written by different agents.
  - Suggest: "separately written programs, one of them by an independent referee agent".
- **N2 (line 135).** "The referee agent" appears before it is introduced. Add "(see the disclosure)", as line 430 does.
- **N3 (line 83).** [bms, Corollary 3.6] proves that the family is infinite. "Smallest member" is stated in the remark after it, in BMS §4 (last sentence) and in the BMS abstract. Cite "Corollary 3.6 and the remark after it".
- **N4 (lines 480–484).** A v6 with Lemma 4.2 switched on also uses Lemma 4.2 in the node test (`sunsearch_v6_39a87195.c`, feasibility check). That test is monotone in p_k and q_k, so the loop breaks stay sound; say so.
- **N5 (lines 505–508).** B2 (v1 and v2) is more than "B (version 1) with an interlacing test".
  - It also uses A's rotation rule and takes the greatest image as canonical form; B v1 has neither.
  - The code comments are stale too: `sunB.c` line 10 and the `sunB2` header still say "least" image.
- **N6 (lines 521–523).** "Off-diagonal entries 1 between consecutive indices of Y" can be read as consecutive elements of Y. That would bridge gaps, and the proof of Lemma 5.1 would then fail.
  - The intended meaning, and what A's code does (it restarts the pivot sequence at each removed index), is "between k and k+1 when both lie in Y".
  - Reword.
- **N7 (lines 682–687).** The proof of Theorem 2 should also invoke [bms, Theorem 2.1] (only P_1 and P_2 occur), as the proof of Theorem 1 does.
- **N8 (line 716).** "b = 3 needs n ≥ 50" rests on computation. Add "(by the searches of Section 5)".
- **N9 (logs, not the paper).** `logs/n42/B2ctrl_b6_N42.out` contradicts itself.
  - It contains a normal `B2-DONE … moment_ok=1128560 canonical=449500 tested=449500 candidates=1` line, followed by "STOPPED by agent at 20:08:29Z after the positive-control hit". INDEX.txt and PROOF.md line 276 also say "stopped".
  - B2 has no signal handler. Its final line is printed only on normal exit and would be lost in the stdout buffer if the process were killed.
  - So the run almost certainly completed; the file's mtime is 20:08:29 UTC.
  - Fix: correct INDEX.txt and PROOF.md. Optionally list B2 v2 at b = 6 as a completed run: its moment_ok, 1,128,560, equals A v4's exact-tested count.

## 3. Line-by-line check of the mathematics

**Setup (Section 2).**
- The formula for Θ(G) is right: the middle vertex of each P_2 contributes 2.
- The dihedral-orbit correspondence is right.
- The |K| = 1 gap convention is stated (first report, MINOR-5).

**Lemma 2.1.**
- The Schur complement is correct: the (1,1) entry of [[−λ,1],[1,−λ]]⁻¹ is −λ/(λ²−1).
- H is definite for |λ| > 1.
- In (c), Haynsworth plus lower semicontinuity of n₊ is correct.

**Lemma 2.2.** I re-derived all three kernels.
- (a) Transfer matrices in SL₂ and the trace criterion.
- (b) y = 0 on K_p. The equations split along the gaps: an even gap gives 1, an odd gap 0. With K_p = ∅, dimension 2 iff 4 ∣ b.
- (c) y = 0 on K_q. q_k − 1 free values. At most 1 per gap. With K_q = ∅, at most 2.
- (d) follows.
- My exact test re-derives (b) and (c) in matrix form and matches exact ranks over Q on 3,250 graphs (§4.4).

**Lemma 2.3.**
- The closed 4-walk count is right: 2 per edge, 4 per pair of adjacent edges, 8 per 4-cycle.
- The odd-walk argument is right.

**Identities (1) and (2).** Correct.

**Lemma 2.4.**
- (a) ρ > 2 by strict monotonicity, hence ρ ≥ 3; −ρ is an eigenvalue only in the bipartite case.
- (c) S₂ = n − mult(1) ≥ b + P + 2Q − max(Q,2) ≥ b + P + Q − 2.
- (d) 5 values need {4,3,3,2,2}, giving S₂ = 42; 6 values need at least 67. I recomputed the minimal S₂ for each |B⁺|: 9, 13, 17, 33, 42, 67.

**Proposition 3.** Correct.
- For odd L: Σ_{v≥2} η_v(v^L − v) = tr A^L.
- Fermat gives λ^g ≡ λ (mod q) whenever (q−1) ∣ (g−1).
- Vandermonde step: subtracting the row of 1 turns det(w_v^j − 1) into the Vandermonde determinant of {1, w_v}.
- The case s = 0 contradicts tr A^g = 2g·c_g > 0. So s ≥ (g−1)/2 and 2e ≥ Σ_{v=2}^{(g+1)/2} v².

**Corollary 3.1.**
- κ_b = 30, 42, 30, 66, 2730 for b = 5, …, 13; none divides 2b.
- The list below 200 is right.
- Σ_{v=2}^{8} v² = 203, so n ≥ 102.
- κ_b equals the denominator of B_{b−1} (von Staudt–Clausen), checked for odd b ≤ 61.
- All recomputed in `numcheck.log`.

**Lemma 4.1.**
- Interlacing with the induced C_b.
- 2cos(2πj/b) > 1 ⇔ 6|j| < b, which gives 2⌈b/6⌉ − 1 values. Checked numerically for b ≤ 60.
- With Lemma 2.4(d): b ≤ 12 for n ≤ 41, and b ≤ 18 for n ≤ 42. For b = 14, 16, 18 the count is 5, which forces B⁺ = {4,3,3,2,2}. Hence b ∈ {6, 10, 14, 18} for b ≡ 2 (mod 4). Correct.

**Lemma 4.2 (unrefereed).** Correct.
- Symmetry gives n = mult(0) + 2·mult(1) + 2s, and the 2nd moment gives mult(1) = n − S₂.
- So mult(0) = 2S₂ − n − 2s.
- Nonnegativity gives S₂ ≤ n ≤ 2S₂ − 2s, and Lemma 2.2(d) gives the last bound. Nothing else is used.

**Corollary 4.3 (unrefereed).** Correct.
- s = 5 and S₂ = 42, so n = 42, mult(1) = 0, mult(0) = 32 ≤ max(P,2).
- Hence P ≥ 32 and n ≥ 14 + 32 = 46 > 42.
- (C₁₄ and C₁₈ themselves are not integral, so "not a cycle" is automatic.)

**Lemma 4.4.**
- (a) r = r₀ + 2|K_q| − δ₁ − δ₋₁ ≥ b − 4, in both cases.
- (b) Each ±v, v ≥ 2, occurs at most twice, so σ(r) ≤ Σλ² = 2n.
- (c) Case K_q ≠ ∅: σ(r₀) + 4x ≤ 2n − 2Q + x, so σ(r₀) ≤ 2n − 2|K_q|. Case K_q = ∅: σ(r₀ − 4) ≤ 2n − 16 + 3y ≤ 2n − 4.
- b ≥ 15 gives 100 ≤ 84, a contradiction.
- b = 14 gives r₀ = 14 (δ₀ = 0 when K_p = ∅, since 4 ∤ 14). Then 166 ≤ 82 or 84 ≤ 80, both false.
- The numbers σ(9, 10, 11, 14) = 68, 84, 100, 166 and r_max(41, 42) = 9, 10 are recomputed. So is the Section 6 bound b ≤ (96n)^{1/3} + 7, for all n < 10⁵.

**Lemmas 5.1–5.3.**
- 5.1: S(m)_X is a principal submatrix, since b−1 ∉ X. Weyl and interlacing apply, and ΔS(−m)_XΔ = −S(m)_X. For T′ on X∖Y, deleting U costs at most |U|. Monotonicity holds.
- 5.2: at a zero pivot, strict interlacing gives Δ_k(ε) opposite in sign to Δ_{k−1}(0). Then d_{k+1} → +∞ and d_{k+2} → t_{k+2}.
- 5.3: g(w) − g(w−q) ≥ 2q, and g(a) + g(c) = g(a+c) + g(0) − 2ac.
- A's code (v4–v6) implements this faithfully: the Y vertices restart the pivot sequence, and the zero-pivot rule is correct for both n₊ and n₋. The only caveat is the wording in N6.

**Theorem 1 proof.** The case split b odd / b ≡ 0 / b ≡ 2 (mod 4) is complete. What remains is b ∈ {3, 6, 10}, settled by the N = 42 searches. Correct.

**Theorem 2 proof.** Correct: b ∈ {3, 4, 6, 8, 10, 12}.
- BRT §5 (p. 296) says: "besides the cycles C3, C4 and C6, we found only three integral unicyclic graphs".
- Table 1 (p. 297), which I rendered at 220 dpi, draws exactly:
  - C_{4,1}(6,0,3,0) (13 vertices);
  - C_4(5P₂, P₁, 2P₂, P₁) (20);
  - C_{4,2}(4,4,0,0) (20; the two loaded vertices are adjacent).
- The spectra match.

**The P₁/P₂ reduction (BMS Theorem 2.1).**
- The wording in the paper ("pendant path of at least three edges") matches BMS ("length t ≥ 3", t edges).
- Numerical spot check: 3,000 random generalized sun graphs with a pendant path of ≥ 3 edges all have eigenvalues in (1, 2cos(π/9)] and in [−2cos(π/9), −1) (`bms21_spot.log`).
- The first report re-derived the proof.

**Faithfulness.**
- **Conjecture 2.** BMS lines 91–92: "If a generalized sun graph that is not a cycle is integral, then the order of the generalized sun graph's cycle is a multiple of 4." The paper's lines 73–76 say the same (order of the cycle = its length).
- **Which graphs count.** Each cycle vertex may carry any multiset of pendant paths, including mixed lengths at one vertex. This contains BMS's C_b(n₁P_{t₁}, …), and every graph named is in that subclass, so both readings are covered. Per BMS 2.1 the attachments are P₁ = one pendant vertex and P₂ = v–w–w′ (lines 160–162).
- **The question** (BMS line 805, §4). The 12-word quotation is verbatim. The paraphrase ("vectors outside the boxes … copies of P₂ were not searched") is faithful, since BMS's "both types" is included in "containing copies of P₂".
- **Citations.** Theorem 2.1, Proposition 3.2, Corollary 3.6, §4 and §5 resolve to the right items; I compiled the BMS source to check the numbering. N3 applies.

**Bibliography.**
- BRT (AADM 11 (2017) 273–298, doi …1702273B): checked on the PDF (`review/lit/brt2017.pdf`).
- Omidi (Graphs Combin. 25(6), 841–849, Dec 2009; DOI registered 2010): checked on the saved Crossref record (`review/lit/omidi_cr.json`).
- BDR (LAA 614, 281–300, doi 10.1016/j.laa.2020.05.002): checked on the saved OpenAlex record (`g1/oa_doi.json`).
- I made no new bibliographic queries. The remaining classical entries look right.

## 4. Recomputation log (implementation D, written from scratch)

### 4.1 Design (different from A, B and C)

**Enumeration.**
- A plain DFS over *all* sequences ((p_k, q_k))_k. There is no rotation filter and no support pattern first.
- Pruning is *exact reachability* of the moment identities only, by a DP table R[r][w][Q] = the set of Θ-contributions of r vertices of total weight w and P₂-count Q. A node is expanded iff some completion satisfies Θ + 4[b=4] = T(B⁺), S₂(B⁺) ≤ n ≤ N and n − max(Q,2) ≤ S₂.
- Admissible B⁺: ρ ≥ 3 and simple; other values at most twice; S₂ ≤ N.
- D1 (used for b = 6) omits the n − max(Q,2) ≤ S₂ condition.
- None of the following is used: interlacing, inertia, Lemma 4.1, Lemma 4.2, Lemma 4.4, the window of Lemma 5.3, or the pattern rank bound.
- Modes:
  - `all`: no symmetry reduction; every leaf is tested, and the integral sets must come out as full dihedral orbits;
  - `canon wmax`: orderly, with w₀ = max w and the canonical form being the greatest image under the key 64w + p (different from A, B and C);
  - `np` (D3): no pruning at all, any b.

**Exact test.**
- For each k ∈ [−9, 9], ν_k is the nullity over GF(2³¹−1) of a b×b matrix:
  - |k| ≥ 2: k(k²−1)(A(C_b) − kI) + diag(p_j(k²−1) + q_j k²), a Schur complement;
  - k = 0: Σ(p_j − 1) + nullity E₀;
  - k = ±1: Σ(q_j − 1) + nullity E_±, with the kernels re-derived.
- Rank over GF(p) ≤ rank over Q, so ν_k ≥ mult(k). Since |λ| ≤ √(2n) < 10, Σν_k < n certifies that G is not integral.
- Candidates are confirmed with SymPy (charpoly of the full adjacency matrix, factored over Z).
- This differs from A (monodromy mod 4 primes), B (interpolation of F(x)) and C (Schwenk φ).

**Hashes** (`D_code_hashes.txt`):
- `sunD_v1.c` 167d5a43…;
- `sunD2.c` 5d913b62…;
- `sunD3.c` e1a42832… (MAXB 32), and `sunD3_maxb16.c` 18a172d9… (the build used for the b = 3 runs).
- The exact-test code is identical in all versions (checked with diff).

### 4.2 Results (all times UTC; at most 4 processes at a time)

| Run | b | N | Mode | Sequences tested exactly | Candidates → SymPy |
|---|---|---|---|---|---|
| D1, 3 parts, 22:20:50–22:25:47 | 6 | 42 | all (weakest pruning) | **153,225,129** (= dry count) | **6 sequences = one orbit (size 6) of C_{6,1}(0,6,6,12,6,6)**; integral, {0³², ±2², ±3², ±4} |
| D2, 22:41:43–22:41:50 | 6 | 42 | canon wmax | 1,187,991 classes | 1: the same graph |
| D2, 3 parts, 22:27:13–22:34:23 | 10 | 42 | all | **119,245,995** (= dry count) | **0** |
| D2, 22:22:21–22:23:23 | 10 | 42 | canon wmax | 5,965,024 | 0 |
| D1 / D2 | 4 | 41 | all | 1,057,590 / 410,544 | 12 sequences = 3 orbits (13, 20, 20 vertices) |
| D2, 22:27:59 | 4 | 49 | all | 1,896,852 | 16 sequences = 4 classes: C_{4,1}(6,0,3,0), C_4(2P₂,P₁,5P₂,P₁) ≅ C_4(5P₂,P₁,2P₂,P₁), C_{4,2}(4,4,0,0), C_{4,2}(10,10,0,0) (44 vertices); all integral. Same list as A v6 |
| D2, 22:28:16 | 8 | 41 | canon wmax | 2,156,331 | 0 |
| D3 | 10 / 12 | 41 | canon wmax | 2,124,182 / 618,755 | 0 / 0 |
| D3 | 3 | 42 / 49 | **np (no pruning)** | 1,246,783 / 3,031,469 (= closed-form count of all sequences) | 0 / 0 |
| D3 | 14 / 18 | 42 | canon wmax | 1,128,742 / 67,817 | 0 / 0 |
| D3 | 22, 26, 30 | 42 | canon wmax | 0: no sequence satisfies the moment identities | 0 |

### 4.3 Cross-checks with the authors' logs

- D2's moment-feasible counts equal those of B v1 exactly: b = 4, N = 41: 410,544; b = 6, N = 42: 14,215,675.
- D2's class counts equal those of B v1 exactly: 52,641 and 1,187,991. This holds despite a different enumeration and a different canonical form.

### 4.4 Validation of D's exact test (`validate_D.py`)

- **Method:** two batches, 250 graphs (seed 11) and 3,000 graphs (seed 2026). Each batch mixes the 6 known graphs with random ones (b = 3..12, n ≤ 60, mixed P₁/P₂, 45% with an imposed rotation or reflection symmetry). I compared ν_k, for all 19 values of k, with:
  - the exact nullity of A − kI over Q, by fraction-free elimination on the full n×n matrix (no structure used);
  - numpy eigenvalue counts.
- **Result:** 0 unsound, 0 mismatches.
- The 3,000-graph batch contained 69 integral graphs and 35 double eigenvalues with |k| ≥ 2.
- I also tested the rank routine against SymPy on 300 low-rank matrices: 0 mismatches.

### 4.5 Numbers and the BMS spot check

- `numcheck.log`: the κ_b list, von Staudt–Clausen, 203, N_{>1}(C_b), σ, r_max, the (96n)^{1/3} + 7 bound, and the minimal S₂ for each |B⁺|. All as in the paper.
- `bms21_spot.log`: 0 violations out of 3,000.

### 4.6 Unrefereed versions, rebuilt from their hashed sources (`cc -O2`)

These reproduce the logged counters exactly:

| Run | Nodes / tested | Integral / candidates |
|---|---|---|
| A v5, b = 14, N = 42 | 904,115 nodes / 850 exact | 0 |
| A v6 with Lemma 4.2, b = 4, N = 49 | 972,890 / 313,822 | 7 entries |
| A v6 with Lemma 4.2, b = 10, N = 42 | 19,679,948 / 71,680 | 0 |
| B v3, b = 3, N = 42 | 3,991 / 2,030 | 0 |
| B v3, b = 10, N = 42 (22:38:04–22:42:43) | 401,175 moment_ok / 200,579 canonical | 0 |

Logs: `review/paper7/logs/reproduce_unrefereed/`.

The rebuilt binaries are not byte-identical to the shipped ones (flags or signature), so provenance rests on the source hashes plus these identical counters.

### 4.7 Code reading of the unrefereed versions (all sound)

- **A v5:** adds the cycle filter on spectra, |B⁺| ≥ N_{>1}(C_b) and, for odd b, |B⁻| ≥ N_{<−1}(C_b). The tests 6|j′| < b and 3|2j − b| < b are exact.
- **A v6:** adds optional Lemma 4.2 at nodes, monotone, and turns off the Pareto reduction when it is on. That is correct, because feasibility is then no longer monotone in the features.
- **B v2:** adds the cycle filter and the Lemma 5.3 window as skip-only.
- **B v3:** adds Lemma 4.2 at nodes (skip-only) and at leaves, the max-key rotation break, which is consistent with the greatest-image canonical form, and partitioning.
- **B2 v2:** interlaces on the weighted reduction of the induced subgraph "path 0..b−2 plus the assigned attachments".
  - The weighted reduction only removes eigenvalues 0 and ±1, so the counts > m for m ≥ 1 are unchanged.
  - The breaks are monotone, since adding a pendant vertex gives a supergraph.
  - A 10⁻⁶ margin can only undercount.
- **Leaf tests:** A's magnitude bound (< 2²⁴⁰ against four ≈2⁶² primes), B's F(x) (monic of degree 4b, 4b + 1 interpolation points), and the dihedral canonicity all check out.

### 4.8 Compile

`pdflatex` ×3 in `…/scratchpad/paper7-review/tex`:
- exit 0 each time;
- `note.log`: no warnings, no overfull or underfull boxes;
- 10 pages; fonts all embedded Type 1;
- the `pdftotext` output is identical to that of `outputs/Sun-graphs/note.pdf`;
- the PDF metadata has the title and author set.

## 5. Recommendation

The mathematics is ready. Before posting:
- do S1 (Veras);
- do S2 (release v1.6.0 first);
- do S3 (the refereeing sentences, and optionally D in Table 3);
- fill in the author-role sentence (line 741).

The NITs take about 15 minutes, and none of them changes a result. Also run the release-day G3 recheck: arXiv v2 (the e-print is still v1 as of 22:07 UTC), trureturing, MathDB, GitHub.
