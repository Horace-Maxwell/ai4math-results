# REVIEW: integral generalized sun graphs (arXiv:2609.28754v1): Q-min, reduction lemmas, odd-girth theorem

Independent referee (did not produce the work). 2026-09-26, 19:58–20:48 UTC (`date -u`). Time box 2 h, ≤ 4 cores, no Lean locks taken.

- **Material reviewed:** `CONTRACT.md`, `PROOF.md`, `code/` (A = `sunsearch.c`, B = `sunB.c`, B2 = `sunB2.c`) and `logs/`.
- **Source re-fetched:** `curl -sL https://arxiv.org/e-print/2609.28754` → `review/src/ArXiv__1_.tex`, SHA-256 `21a822ee…c64f8`, identical to the contract's file. arXiv lists **v1 only**: API check at 20:26 UTC, and `…/abs/2609.28754v2` returns 404.
- **Privacy:** no e-mail address in any request. No `mailto=`; User-Agent was the default or `Mozilla/5.0`.
- **Everything the referee produced** is in `review/`:
  - `code/`:
    - `sunC.c` (C) and `sunC2.c` (C with the refined bound);
    - `sunC_batch.c`, `check_lemmas.py`, `validate_C.py`, `confirmC.py`, `compare_leaves.py`;
    - the leaf-dump copies of the audited versions: `A4_dump.c` (= `sunsearch_v4_f5a38c28.c` plus one printf) and `B2v1_dump.c` (= `sunB2_v1_54531ad0.c` plus one printf). The earlier copies `A_dump.c` and `B2_dump.c` were made from files already modified by the other process (see MINOR-7), so they and their logs are superseded;
    - the schedulers `sched.sh` and `runjob*.sh` (≤ 4 processes);
  - `logs/`;
  - `lit/`: downloaded sources and API results;
  - `querylog.tsv`.

## 1. Verdicts

| # | Claim | Verdict | One-line reason |
|---|---|---|---|
| 1a | Q-min: no counterexample to Conjecture 2 with ≤ 41 vertices; so 42 is the minimum order | **ACCEPT** | Proofs check; independently recomputed by a third implementation C with a different enumeration, a different pruning and a different exact test: 0 counterexamples for every b ≢ 0 (mod 4) with n ≤ 41 |
| 1b | Classification up to 41 vertices: only b = 4, exactly C_{4,1}(6,0,3,0), C_4(5P2,P1,2P2,P1), C_{4,2}(4,4,0,0) | **ACCEPT** (minor fixes) | C confirms b = 3, 4 (no pruning at all), 8, 12, and every other b. The literature cross-check (BRT 2017, Table 1) is exact. Attribution slip: all three graphs were already known (MINOR-2) |
| 1c | b = 6, n ≤ 42: C_{6,1}(0,6,6,12,6,6) is the only integral graph | **ACCEPT**. Bonus: it is also the unique counterexample of order 42 over all b (Section 6, item 3) | C (unpruned for b = 3, 4; rank-bound pruning otherwise) finds exactly this graph among 201,673,369 leaves with b = 6, n ≤ 42; A and B agree |
| 2 | Reduction lemmas (Lemmas 1–8; b ∈ {3, 6, 10} for Q-min) | **ACCEPT with MINOR revisions** | All lemmas checked line by line and against exact arithmetic (3,000 graphs, 0 failures). One wrong side remark on N = 42 (MINOR-1) |
| 3 | Odd-girth theorem (K_b ∣ 2b, 3 ∣ b, b ≥ 15 needs n ≥ 102) | **ACCEPT** (mathematics). G2: no prior statement found (Section 5) | The proof is short and correct. Novelty confidence is moderate: two paywalled papers were not read in full, and the argument is elementary (MINOR-4) |

**No BLOCKER and no MAJOR finding.** The main result (42 is the minimum order of a counterexample) is correct, in the strong reading and hence in every weaker reading.

## 2. Findings

**MINOR-1 (Lemma 6, N = 42 remark).** "For N = 42: b ∈ {6, 10, 14}" is wrong. At N = 42 one has |B⁺| ≤ 5, since {2,2,3,3,4} gives exactly 42. And N_{>1}(C_18) = #{j : 6|j| < 18} = 5. So interlacing does not exclude b = 18: the list should be {6, 10, 14, 18}.
- This only affects the unfinished order-42 uniqueness remark, not Theorem 1.
- b = 18 and b = 14 are excluded at N = 42 by the rank-deficiency bound of Section 3.1 below. C also searched b = 14 at N = 42 and found 0.

**MINOR-2 (attribution).** PROOF.md says of the three b = 4 graphs that "the first two are the known examples". All **three** are known.
- Braga–Rodrigues–Trevisan, *Locating eigenvalues of unicyclic graphs*, Appl. Anal. Discrete Math. 11 (2017) 273–298, doi:10.2298/AADM1702273B.
  - §5, p. 296: "We performed a computer search for all integral unicyclic graphs up to 21 vertices and, besides the cycles C3, C4 and C6, we found only three integral unicyclic graphs, shown in Table 1."
  - Table 1, p. 297, draws exactly C_{4,1}(6,0,3,0) (n = 13), C_4(5P2,P1,2P2,P1) and C_{4,2}(4,4,0,0) (n = 20 each; cospectral). The referee identified the drawings by rendering the page: `lit/brt_p297-25.png`.
- Cite this primary source rather than the source paper's paraphrase.
- Note: BRT's acknowledgement says the search used a program by D. Stevanović. The source paper's phrase "a computer search based on [the location algorithm]" is therefore slightly loose. This does not affect PROOF.md.

**MINOR-3 (overstatement in the status table).** "Independent implementations B and B2 confirm every case" is true only for the Q-min cases (b = 3, 6, 10 and odd b). For the classification claim (1b), b = 8 and b = 12 were A-only; the corollary text says so correctly. This review closes that gap (Section 3).

**MINOR-4 (how to present Theorem 2).**
- The mathematics is correct (Section 4). The ingredients are classical: tr A^L counts closed walks; an odd closed walk contains an odd cycle; Fermat's little theorem.
- "p divides the number of closed p-walks" is a standard feasibility condition, valid for every integer matrix: tr A^p ≡ tr A (mod p).
- What the proof adds is the integrality refinement λ^b ≡ λ (mod q) for (q−1) ∣ (b−1), applied at the odd girth. The referee found no prior statement of it (Section 5), but it should be presented as a short observation, not as a deep theorem.
- It generalises verbatim, and the general form should be stated and novelty-checked too. For any integral graph with odd girth g and c_g shortest odd cycles, tr A^L = 0 for odd L < g and tr A^g = 2g·c_g. Hence every prime q with (q−1) ∣ (g−1) divides 2g·c_g, and in particular 3 ∣ g·c_g.
  - Sanity check, Petersen graph: g = 5, c_5 = 12, and 2·5·12 = 120 is divisible by 2, 3 and 5.
- The "moreover" part (≥ (b−1)/2 values with mult(v) ≠ mult(−v)) is the usual odd-polynomial/Vandermonde argument behind classical odd-girth bounds. Compare van Dam–Haemers, JCTB 101 (2011) 486–489 (arXiv:1202.2300, §2): odd girth ≥ 2d+1 with d+1 distinct eigenvalues forces equality. Cite it as a variant.

**MINOR-5 (clarity).**
- Lemma 3 should state the convention for |K_p| = 1: the single "pair" is at distance b, so δ₀ = 1 iff b is even. The same applies to |K_q| = 1 for δ±.
- The referee's exact check (Section 3.3) confirms that the formulas hold with this convention.

**MINOR-6 (B2 evidence; resolved by this review).** PROOF.md's b = 10 cross-check compared counts only. The referee compared the actual leaf sets (Section 3.5). Result: the sets are **identical** (52,652 = 52,652, no leaf unique to either side), and none of the leaves is integral under the referee's exact test.

**MINOR-7 (provenance: the material changed during the review).**
- Between 20:01 and 20:27 UTC another process edited `code/`:
  - `sunsearch.c` moved to v5 (`bfcca593`, which adds a C_b-interlacing filter on spectra) and then v6 (`39a87195`, which adds an optional "Lemma N" pruning);
  - `sunB2.c` became `c80538f9` (interlacing on the whole path 0..b−2);
  - `sunB.c` became `f0eb3d9c` (canonical form = greatest image, plus a C_b filter);
  - the binaries were rebuilt, and new runs appeared in `logs/n42/`.
- The audited versions are still present as `sunsearch_v4_f5a38c28.c`, `sunB2_v1_54531ad0.c` and `sunB_v1_4d92eb48.c`. Their hashes match `logs/code_hashes.txt`, and they are the versions that produced the logs cited in PROOF.md.
- This review refers to those versions. The v4→v5→v6 diffs touch only spectrum generation and an optional filter; the DFS, the leaf test and UB₄ are unchanged.
- Consistency checks:
  - B v1 enumerates without a rotation filter and takes the smallest image as canonical, which is consistent. The later B uses max-key rotation plus the greatest image, also consistent.
  - A v5 re-run on b = 10, N = 41, part 0: same 30,343 exact-tested leaves as the v4 log, with fewer nodes (17.8M vs 30.7M) because of the extra filter.
  - Modified B2, part 2: same moment_ok (10,442) as the v1 log.
- Action: PROOF.md should name the preserved v4/v1 files as the ones behind its tables, and anything produced by v5, v6 or `logs/n42/` needs its own check.

**Remarks, no action needed.**
- The two self-found bugs in A (v1: the full path is not a principal submatrix; v3: a non-monotone window filter was used to break the loop) show that A's pruning is delicate. The logic of the audited A v4 (`sunsearch_v4_f5a38c28.c`, the version behind the logs) checks out (Section 4, Lemma 7).
- B2 v1 interlaces with the caterpillar on the assigned cycle vertices 0..k−1 only. That is an induced subgraph because the edge (b−1, 0) is absent, so the bound is valid, if weaker than the later whole-path version. The LAPACK margin (> m + 10⁻⁶) can only undercount, which is safe.
- The results no longer depend on A: C reproduces every claim with none of A's pruning lemmas.

## 3. Independent recomputation (implementation C, written from scratch)

### 3.1 Design (deliberately different from A and B/B2)

**Enumeration: support pattern first.**
- Each cycle vertex gets a symbol s_k ∈ {0,1,2,3}: bit 0 means p_k > 0, bit 1 means q_k > 0. Symbol 3 (P1 and P2 at the same vertex, the strong reading) is included.
- One lexicographically smallest representative is taken per dihedral orbit of patterns.
- Then all positive values on the support with n ≤ N are enumerated. There is no spectral pruning inside a pattern.

**Pruning: rank-deficiency bound (new, pattern level only; `noprune` switches it off).**
- For integral G, r := #{λ : |λ| ≥ 2} = n − m₀ − m₊₁ − m₋₁.
- From the eigenvector structure, m₀ ≤ P − |K_p| + δ₀(K_p). The same statement is Lemma 3, but it was re-derived here.
- m₊₁ + m₋₁ ≤ 2Q if K_q ≠ ∅, since each gap between consecutive K_q vertices adds ≤ 1; and ≤ 4 if K_q = ∅, since the solution space of the recurrence has dimension 2.
- Hence **r ≥ b + |K_p| − δ₀ − 4·[K_q = ∅] ≥ b − 4.**
- Multiplicity ≤ 2 for |λ| ≥ 2 and Σλ² ≤ 2N give r ≤ r_max(N): r_max(41) = 9 and r_max(42) = 10. The smallest admissible squares are 4,4,4,4,9,9,9,9,16,….
- Consequences:
  - **b ≤ 13 for n ≤ 41**, and b ≤ 14 for n = 42, independently of Theorem 2 and Lemma 6;
  - for b = 10 and b = 12 (n ≤ 41) only P1-only graphs survive;
  - for b = 12, K_p must lie in one parity class.

**Refined bound (`sunC2`, mode `prune2`, used only for the N = 42 bonus runs).** Write R₀ = b + |K_p| − δ₀ and let sumsmallest(r) be the sum of the r smallest admissible squares.
- **Case K_q ≠ ∅.** Put x = 2|K_q| − δ₊ − δ₋ ≥ 0. Then r = R₀ + x, m₊₁ + m₋₁ = 2Q − x, and Σ_{|λ|≥2} λ² = 2n − 2Q + x.
  - Each extra large eigenvalue adds ≥ 4, so sumsmallest(R₀) + 3x ≤ 2N − 2Q.
  - Hence **sumsmallest(R₀) ≤ 2N − 2|K_q|**.
- **Case K_q = ∅.** Put y = δ₊ + δ₋ ≤ 4. Then r = R₀ − y and Σ_{|λ|≥2} λ² = 2n − y.
  - Hence **sumsmallest(R₀ − 4) ≤ 2N − 4**.
- **Effect at N = 42.** This excludes b = 14, 18 and every b ≥ 15, and for b = 10 it leaves only P1-only patterns with at most 2 odd gaps: 4.6·10⁶ leaves instead of 4.46·10⁸.
- **Dry-run consistency.** At N = 41 the leaf counts equal C's for b = 4, 5, 7, 8, 10, 11, 12, and are smaller for b = 9 (4,692,656 vs 4,716,966). At N = 42, b = 3 is unchanged and b = 6 drops from 2.02·10⁸ to 8.2·10⁷.

**Leaf test: exact characteristic polynomial, a different algorithm from both A (monodromy) and B (determinant interpolation).**
- Schwenk's cycle-edge formula φ(G) = φ(G−e) − φ(G−u−v) − 2φ(G−V(C)), with e = v_{b−1}v₀.
- The caterpillar φ's come from the bridge recurrence A′ = R_k A − ℓ_k B, B′ = ℓ_k A. Here ℓ = x^p(x²−1)^q and R = xℓ − p x^{p−1}(x²−1)^q − q x^{p+1}(x²−1)^{q−1}.
- Everything is computed modulo 2^61−1 and 10^18+3, both certified prime by sympy.
- Root multiplicities for m ∈ [−10, 10] modulo p are upper bounds on the true ones. A sum < n under either prime **certifies** non-integrality.
- Survivors are confirmed exactly with sympy (`confirmC.py`: factor the characteristic polynomial of the full adjacency matrix, then reduce to dihedral canonical form).

### 3.2 Validation of C
- φ from C equals sympy's exact characteristic polynomial (mod 2^61−1) on **400/400** random mixed P1/P2 graphs with b ≤ 12 and n ≤ 41 (`validate_C.py`). A deliberately corrupted coefficient is detected.
- C(3,0,…) gives x³−3x−2. The known graphs give rootsum = n: 13, 20, 20, 42.
- Positive controls inside the searches:
  - b = 4 (unpruned) returns exactly the 3 known graphs;
  - b = 6 at N = 42 (pruned) returns C_{6,1}(0,6,6,12,6,6).

### 3.3 Exact check of PROOF.md Lemmas 2–4 and of the referee's bound (`check_lemmas.py`)
- **Sample:** 3,000 random graphs, b = 3..14, n ≤ 60, biased to small p_k, q_k, 40% of them rotation/reflection-symmetric.
- **Compared against** exact root multiplicities of sympy's characteristic polynomial:
  - Lemma 3: m₀, m₊₁, m₋₁ exactly;
  - Lemma 2: the monodromy criterion for every m ∈ [−12, 12] \ {0, ±1};
  - Lemma 4: tr A² = 2n and tr A⁴ = 2Σd² − 2n + 8[b = 4], computed exactly;
  - the rank-deficiency bound.
- **Result: 0 failures.**
- The sample exercised the special cases: 1,551 graphs with δ₀ > 0, 953 with δ₊ + δ₋ > 0, 63 eigenvalues |m| ≥ 2 of multiplicity 2 and 225 of multiplicity 1.

### 3.4 Search results (logs in `review/logs/C_*.out`; code SHA-256 in `logs/C_code_hash.txt`)

| b | N | pruning | patterns kept / canonical patterns | leaves tested exactly | mod-p candidates | exact result (sympy) |
|---|---|---|---|---|---|---|
| 3 | 41 | **none** | 19 / 19 | 521,056 | 0 | none |
| 3 | 42 | **none** | 19 / 19 | 606,367 | 0 | none |
| 3 | 49 | **none** | 19 / 19 | 1,601,329 | 0 | none. Confirms PROOF.md's "no triangle up to 49 vertices" (strong reading) |
| 4 | 41 | **none** | 54 / 54 | 5,683,267 | 5 | **3 graphs**: C_{4,1}(6,0,3,0) (n=13, spec ±3, ±2, 0⁹); C_4(5P2,P1,2P2,P1) and C_{4,2}(4,4,0,0) (n=20, spec ±3, ±2, ±1⁷, 0²) |
| 5 | 41 | rank bound | 128 / 135 | 20,292,905 | 0 | none (Theorem 2 not used) |
| 6 | 42 | rank bound | 417 / 429 (3 parts) | 201,673,369 | 1 | **exactly C_{6,1}(0,6,6,12,6,6)** (n=42, spec 0³², ±2², ±3², ±4); nothing with n ≤ 41 |
| 7 | 41 | rank bound | 586 / 1,299 (2 parts) | 82,161,850 | 0 | none (Theorem 2 not used) |
| 8 | 41 | rank bound | 617 / 4,434 (3 parts) | 57,561,471 | 0 | none |
| 9 | 41 | rank bound | 77 / 15,083 | 4,716,966 | 0 | none |
| 10 | 41 | rank bound | 36 / 53,763 | 3,814,116 | 0 | none |
| 11 | 41 | rank bound | 23 / 192,691 | 1,239,693 | 0 | none |
| 12 | 41 | rank bound | 12 / 703,563 | 677,237 | 0 | none |
| 13 | 41 | rank bound | 0 / 2,558,095 | 0 | 0 | none (excluded by the bound) |
| 14 | 42 | rank bound | 17 / 9,260,683 | 1,951,786 | 0 | none |
| ≥ 14 | 41 | – | – | – | – | excluded analytically: r ≥ b − 4 ≥ 10 > r_max(41) = 9 |
| 10 | 42 | rank bound | 36 / 53,763 (`sunC2`, `prune2`) | 4,601,920 | 0 | none. With b = 6 and b = 14 this gives the order-42 uniqueness below | |

Wall times (UTC, 1 core per part): b = 8: 220–250 s per part; b = 7: 856 s + 120 s; b = 6 (N = 42): 780–804 s per part; b = 4 unpruned: about 50 s; b = 3: 5 s. The leaf counts equal the dry-run counts (`SUNC_DRY=1`), e.g. 57,561,471 for b = 8. The strong reading (symbol 3) was allowed in every run.

**Conclusion of the recomputation.**
- Up to 41 vertices, the integral generalized sun graphs other than cycles are exactly the three b = 4 graphs.
- There is no counterexample to Conjecture 2 up to 41 vertices.
- For b = 6 up to 42 vertices, the only integral graph is C_{6,1}(0,6,6,12,6,6).
- C used **no pruning at all** for b = 3 and 4. For b ≥ 5 it used only the rank-deficiency bound, which is independent of A's inertia, window and moment pruning and of B's spectrum-first pruning. Every b not searched (b ≥ 14 at N = 41) is excluded by r ≥ b − 4 > 9.

### 3.5 Leaf sets for b = 10, N = 41: A versus B2 (task 2)
**Setup.**
- The audited sources were re-run with a single added `printf` at the moment-feasible leaf:
  - A v4 (`sunsearch_v4_f5a38c28.c`) → `A4_dump`;
  - B2 v1 (`sunB2_v1_54531ad0.c`) → `B2v1_dump`.
- **The re-runs reproduce the logged counters exactly:**
  - A: nodes 30,707,736 / 20,008,359; leaves 9,415,293 / 5,930,690; exact-tested 30,343 / 22,309;
  - B2: moment_ok 19,901 / 13,804 / 10,442 / 8,505; lapack_pruned 55,389,257 / 37,729,435 / 25,366,447 / 16,491,603.
- `compare_leaves.py`, output in `logs/compare_leaves_b10_N41.out`:

| | A v4 | B2 v1 |
|---|---|---|
| leaves (with multiplicity) | 52,652 | 52,652 |
| distinct | 52,652 | 52,652 |
| only in this set | 0 | 0 |

**Findings.**
- **A = B2 as sets.** Every leaf satisfies the shared "v₀ carries the maximal key" rotation filter.
- The referee's independent exact test (`sunC_batch`: Schwenk φ modulo 2 primes) was run on all 52,652 leaves: **0 integral**.
- Breakdown by type:
  - 50,712 leaves contain a P2. All are excluded a priori by the rank-deficiency bound (r ≥ b = 10 > 9).
  - 1,940 leaves are P1-only. Of these, 703 lie in C's own pattern set, so C tested them too, and 1,237 are excluded by the bound.
- So the equality of counts in PROOF.md reflects equality of the sets. Neither pruning removes a moment-feasible configuration in this case.

### 3.6 Recomputation log (commands; all times UTC; ≤ 4 processes at any time)

**Build.**
- `cc -O2 -march=native -o sunC sunC.c` (SHA-256 `9401061c…`, `logs/C_code_hash.txt`).
- `sunC2.c` adds only the `prune2` mode (`logs/C2_code_hash.txt`).
- `cc -O2 -o A4_dump A4_dump.c -lm`.
- `cc -O2 -o B2v1_dump B2v1_dump.c -framework Accelerate -lm`. Hashes of the sources are in `logs/dump_provenance.txt`.

**Validation.**
- `python3 validate_C.py ./sunC 400`: 400/400 agree with sympy.
- `python3 check_lemmas.py 3000 7`: 0 failures.
- An odd-trace check (tr A^L = 0 for odd L < b, tr A^b = 2b) on 60 random odd-cycle unicyclic graphs with arbitrary attached trees: 0 violations.

**Searches.**
- `sunC b N {noprune|prune} 1 part nparts`, run from 20:06 to 20:31 by `xargs -P 4` and `runjob.sh`. Outputs in `logs/C_b*_N*_*.out`; start/end times and `/usr/bin/time` in `.err`.
- `sunC2 b N prune2 …`: `logs/C2_*.out`.
- Candidates confirmed with `python3 confirmC.py logs/C_b4_N41_noprune_p0of1.out logs/C_b6_N42_prune_p*of3.out`: 4 distinct graphs, all integral.

**Leaf dumps.**
- `A4_dump 10 41 p 2` and `B2v1_dump 10 41 p 4`, run by `sched.sh`. Outputs in `logs/A4dump_*`, `logs/B2v1dump_*`.
- Compared with `python3 compare_leaves.py`.

**Superseded (see MINOR-7).**
- Dumps from the modified A v5 and B2 are in `logs/superseded_modified_versions/`.
- A `prune` run of b = 10 at N = 42, part 0/4, was stopped: its split held 442.5M of 446M leaves. It was replaced by the `prune2` run.

## 4. Line-by-line check of CONTRACT.md and PROOF.md

**Contract and definitions.** Checked against the LaTeX:
- the verbatim quotes: line 78 (integral), line 85 (generalized sun graph), line 97 (attaching P_t; notation C_b(n₁P_{t₁},…), C_{b,t}), lines 91–92 (Conjecture 2), line 805 (Q-min) and lines 839–841 (Q-girth);
- "order of the cycle" = b.

Which graphs count:
- A counterexample is integral, not a cycle, and has b ≢ 0 (mod 4).
- The strong reading (any multiset of P1/P2 at each vertex, mixing allowed) is the most general reading compatible with "attaching pendant paths to the vertices of a cycle" once Theorem 2.1 removes P_t for t ≥ 3. It contains the paper's one-type-per-vertex notation.
- All three b = 4 graphs, and the 42-vertex graph, are in the paper's notation. So the classification is the same in both readings.

**Theorem 2.1 of the paper**, used for the P1/P2 reduction: re-derived.
- q(λ) = (λ²−1)/(λ(2−λ²)).
- (r−1) + q(r) = (r−1)(r³−3r−1)/(r(r²−2)) > 0 for r ∈ (ρ, 2).
- The inertia comparison gives an eigenvalue in (1, r) for every r ∈ (ρ, 2), hence one in (1, ρ].
- Correct.

**Lemma 1 (Schur reduction).** Correct.
- The (1,1) entry of (E_{P2} − λI)⁻¹ is −λ/(λ²−1). This gives f_k = p_k/λ + q_kλ/(λ²−1) with S = A(C_b) − λI + diag f.
- E(λ) has eigenvalues −λ and −λ ± 1, so it is negative definite for λ > 1 and positive definite for λ < −1.
- At λ → 1⁺, f_k → +∞ exactly on K_q. Haynsworth then gives n₊(S) = #q + n₊(Schur complement), and the Schur complement → R. The positive inertia is lower semicontinuous.
- The case λ → −1⁻ is symmetric, with R′ = (A + I − diag p)|_Z.

**Lemma 2 (multiplicity ≤ 2 and the monodromy criterion).** Correct.
- An eigenvector with m ∉ {0, ±1} vanishing on the cycle vanishes on every P1 (m x = 0) and on every P2 ((m² − 1) x = 0), also at mixed vertices.
- The periodic solutions of x_{k−1} + x_{k+1} = c_k x_k form ker(M − I) with M ∈ SL₂.
- The trichotomy M = I / tr M = 2 / otherwise is right. Checked exactly in Section 3.3.

**Lemma 3.** Correct, with the convention of MINOR-5. Checked exactly.
- The bound mult(±1) ≤ max(Q, 2) holds.

**Lemma 4.**
- (a) Holds, since |E| = n.
- (b) tr A⁴ = 2|E| + 2Σd(d−1) + 8c₄ = 2Σd² − 2|E| + 8c₄, so Σ_{|λ|≥2} λ²(λ²−1) = 2Σd(d−1) (+8 if b = 4). Correct. The P2 middle vertices add 2 each, which is the code's `+2q`.
- (c) The bounds P + Q ≤ S₂ − b + 2 (bipartite) and P + Q ≤ S₂/2 − b + 2 (odd) are right, if slightly loose when Q ≤ 1.

**Lemma 5.** Correct:
- ρ > 2 strictly (G ⊋ C_b connected), so ρ ≥ 3;
- −ρ is not an eigenvalue for odd b;
- |λ| ≤ ⌊√(2N)⌋;
- |B⁺| ≤ 4 for N ≤ 41 (five values need ≥ 4+4+9+9+16 = 42);
- the odd-L trace identities hold, since 0, ±1 contribute λ^L − λ = 0.

**Theorem 2.** Correct.
- Odd closed walks shorter than b would contain an odd cycle shorter than b. A closed b-walk contains an odd cycle of length ≤ b, which must be the cycle itself, traversed once: 2b walks.
- Fermat: λ^b ≡ λ (mod q) for every integer λ when (q−1) ∣ (b−1). Hence q ∣ 2b.
- "Moreover": det[w_i^j − 1]_{i,j ≤ s} equals the Vandermonde determinant on {1, w₁, …, w_s}, with w = v² ≥ 4 distinct. It uses the first s odd exponents L = 3, …, 2s+1 < b. Correct.
- The corollary list below 200 (3, 15, 27, 39, 63, 75, 87, 99, 123, 135, 147, 159, 183, 195) was recomputed and matches.
- b = 15 ⇒ 2n ≥ Σ_{v=2}^{8} v² = 203 ⇒ n ≥ 102. Correct.

**Lemma 6.**
- Odd b: K_b ∤ 2b for b = 5, 7, 9, 11, 13. Recomputed: correct.
- b ≡ 2 (mod 4): N_{>1}(C_b) = 2⌈b/6⌉ − 1 was recomputed for b = 6..22 and is correct. This gives b ∈ {6, 10} for N ≤ 41.
- The N = 42 list is wrong (MINOR-1).

**Lemma 7 (pruning soundness).** Correct as stated.
- Paths inside 0..b−2 are principal submatrices.
- For the negative side, the alternating-sign similarity on a path gives D·S(−m)|_X·D = −S(m)|_X, since f is odd.
- Bare completion is valid: the diagonal f_k(m) ≥ 0 for m > 1 (Weyl). A P2 moves a vertex from Z to #q (net change ≥ 0).
- Every bound is monotone in p_k and q_k.
- UB₄ is attained by putting the remaining weight as pendants on one vertex: g is superadditive in the required sense, and pendants beat P2's per unit of order.
- The non-monotone window filter only skips; it never breaks the loop (the v3 bug is fixed in the final code).
- The last vertex is solved from the exact 4th-moment identity over all admissible targets.

**Lemma 8 (zero pivots).** Correct.
- For a Jacobi matrix with nonzero off-diagonals, strict interlacing gives sign Δ_i′(0) = −sign Δ_{i−1}(0) at a singular leading block. So the perturbed pivot is −0 and the next one is +∞ (for T − εI), and symmetrically for n₋.
- Dropping a vertex on overflow leaves a principal submatrix. No overflow occurred in any final run.

**Leaf tests.**
- A: s_k = D·c_k with D = m(m²−1). The magnitude bound < 2^240 is below the 4-prime modulus of about 2^248: entries ≤ (2·2^14)^15.
- B: φ_G = x^{P−b}(x²−1)^{Q−b}·F(x). So F is monic of degree 4b, and all its roots are integers in [−9, 9] when G is integral. A root sum below 4b therefore certifies non-integrality.
- Both are correct.

## 5. G2: literature for Theorem 2 and for the "three graphs up to 21 vertices" claim

**"Three integral unicyclic graphs up to 21 vertices besides the cycles."** This is **confirmed and matched exactly.**
- BRT 2017, §5 (p. 296) and Table 1 (p. 297), quoted in MINOR-2. Their search covers all unicyclic graphs, not only sun graphs, up to 21 vertices.
- Its three graphs are exactly our three b = 4 graphs, with spectra {±3, ±2, 0⁹} (n = 13) and {±3, ±2, ±1⁷, 0²} (n = 20, twice).
- The BRT introduction (p. 275) also summarises Omidi 2009: an integral unicyclic graph with no eigenvalue 0 is C3 or C6, and no non-bipartite integral unicyclic graph has exactly one eigenvalue 0. These are nullity statements, not cycle-length congruences.

**Theorem 2 (odd girth).** No prior statement was found. This includes the special case "3 ∣ b" and the general-graph form of MINOR-4. The searches, all in `querylog.tsv`:
- **Web:** 20 web searches in total. Fourteen target the congruence itself, combining "integral graph(s)", "odd girth", "shortest odd cycle", "closed walks", "Fermat", "unicyclic", "divisible by 3", "tr(A^p)", "λ^p ≡ λ" and "Sachs/Newton". The other six locate the sources (BRT 2017, Omidi 2009, the surveys).
- **arXiv API:** 9 queries:
  - `abs:"generalized sun graph"` finds only the source paper;
  - `abs:"integral unicyclic"` finds 0;
  - `"integral graph" AND "odd girth"` finds 0;
  - `"integral graphs" AND "closed walks"` finds 0;
  - `ti:"integral graphs"` finds 42 titles, none relevant.
- **MathOverflow and Math.SE via the StackExchange API:** 24 queries, all titles scanned. Nothing on integral unicyclic graphs, sun graphs or odd-girth congruences.
- **Full texts grepped:**
  - L. Wang, *Integral trees and integral graphs* (PhD thesis, Twente 2005), including its §1.3 "Survey of results". The paper cites Wang's survey Memorandum 1763 from the same year. The thesis contains only Pell-type congruences for integral trees; nothing on closed walks or odd girth.
  - Chung–Koolen–Sano–Taniguchi, arXiv:1011.6133 (non-bipartite integral graphs with spectral radius 3). It uses moment equations and mod-3 arguments via spanning trees; no odd-girth congruence.
  - van Dam–Haemers, arXiv:1202.2300: the Vandermonde and odd-polynomial technique only (see MINOR-4).
  - BRT 2017.
- **Nearest known facts:**
  - tr A^p ≡ tr A (mod p) for all integer matrices ("p divides the number of closed p-walks", a standard feasibility condition for strongly regular and distance-regular graphs). It is vacuous here, since 2b ≡ 0 (mod b).
  - The odd-girth / distinct-eigenvalue bounds (van Dam–Haemers 2011; Lee–Weng).
  - Neither gives K_b ∣ 2b.
- **Not obtained (failures):**
  - Omidi, Graphs Combin. 25 (2009) 841–849: Springer auth redirect; Crossref has no abstract; Semantic Scholar reports the abstract elided and the paper closed-access.
  - Braga–Del-Vecchio–Rodrigues, LAA 614 (2021) 281–300: ScienceDirect HTTP 403.
  - The Balińska et al. survey: doiserbia connection refused.
  - Indirect evidence that BDR 2021 has no such result: the source paper (Braga is first author of both) summarises BDR 2021's necessary conditions without any odd-cycle restriction, and in lines 839–841 still asks "whether b must be even". A known restriction on odd b would naturally have been cited there.
- **Other literature named in the task** (Brouwer 2008 small integral trees; Watanabe–Schwenk 1979 starlike trees; Csikvári 2010; Ghorbani–Mohammadian–Tayfeh-Rezaie 2012):
  - These concern trees, which are bipartite, so odd-girth congruences are vacuous there.
  - Their number theory is Pell/Diophantine conditions on arm lengths and degrees; the referee knows of no odd-cycle trace congruence in them.
  - The source paper's own survey of the area (line 81–83) mentions none.
- **G2 verdict:** apparently new, but elementary, with moderate confidence. Present it as a proposition with a two-line proof. State the general "odd girth g, c_g shortest odd cycles" form, and re-run the novelty check on that form (for example against strongly-regular feasibility literature, and the full texts of Omidi 2009 and BDR 2021 through the user's library access).

## 6. Recommendations
1. The main result can be claimed as proved: 42 is the minimum order of a counterexample to Conjecture 2, in the strong reading and hence in every reading. It now rests on **three** implementations. Two of them (A, C) cover every b; C shares none of A's pruning and uses an unpruned exhaustive search for b = 3, 4. The b = 10 leaf sets of A and B2 are identical.
2. Fix MINOR-1 through MINOR-5 before any write-up:
   - the b = 18 remark;
   - "all three graphs known (BRT 2017, Table 1)";
   - status-table wording;
   - present Theorem 2 as elementary, with its general-graph form;
   - the |K_p| = 1 convention.
3. Order-42 uniqueness for all b (bonus). **Done in this review.**
- C2 at b = 10, N = 42: 4,601,920 leaves, 0 integral.
- C at b = 14, N = 42: 0.
- b = 18 and all b ≥ 15 are excluded by the refined bound. Odd b ∈ {5, …, 13} are excluded by Theorem 2 (checked in Section 4). b = 3 at N = 42 found 0 (unpruned).
- Hence **C_{6,1}(0,6,6,12,6,6) is the unique counterexample of order 42**, in the strong reading.
- This rests on C/C2 plus Theorem 2. A and B agree for b ∈ {3, 5, 6, 7, 9}.
- It would be worth a second implementation for b = 10 at N = 42 before it is claimed. The original author's `logs/n42/` runs (not reviewed here) may serve.
- A `prune2` positive control on b = 6, N = 42 (part 2/3: 25,810,356 leaves, 20:43–20:48) returns exactly the 42-vertex graph, confirmed by sympy.
4. The rank-deficiency bound of Section 3.1 is a cleaner replacement for Lemma 6 in a write-up. It gives b ≤ r_max(n) + 4 in one line and also handles N = 42.
   - It also gives a general Q-girth statement: every integral generalized sun graph other than a cycle has b ≤ r_max(n) + 4 = O(n^{1/3}), for even and odd b alike. Here r_max(n) is the largest r with sumsmallest(r) ≤ 2n.
   - Examples: r_max(186) = 20, so the n = 186 member of the hexagon family could in principle have b ≤ 24.
   - This is worth adding to the partial Q-girth results, after its own check.
