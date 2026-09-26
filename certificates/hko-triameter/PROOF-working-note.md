# HKO triameter problems 1–3: results, proofs, checks

Agent: Claude Code subagent (round 6, `hko-triameter`), 2026-09-26.
Contract: `CONTRACT.md`. Query log: `querylog.tsv`. Code: `code/`. Logs: `logs/`. Lean: `lean/` (copies of
`work/research-lean/Research/HKOTriameter{,DH,Audit}.lean`).

## 0. Status table

| Problem | Literature (G1) | Statement | Mathematics | Formal (Lean 4.33.1 + Mathlib) |
|---|---|---|---|---|
| P1: Q3' for median graphs? | **no prior answer found** (listed as open on Wikipedia; invited in LSB 3:154) | fixed (CONTRACT §4) | **No.** 8-vertex median graph G1; minimal; unique minimal up to isomorphism | **done**: `not_problem1Claim` (and `not_problem1ClaimPair`) |
| P2: Q4 for median graphs? | **already answered NO**: MathOverflow answer 506536 (2025-12-31), an 11-vertex median counterexample to (B) and (B'). Ours is smaller (8), minimal and unique, and must credit it | fixed; typo-reading R2 noted | **No.** 8-vertex median graph G2 (also violates Q4' = (B')); minimal; unique minimal up to isomorphism | **done**: `not_problem2Claim`, `not_problem2ClaimWeak` |
| P3: DH ⇒ Q3' or Q4 (per graph)? | **no prior answer found** | fixed (per-graph reading) | **Yes**, even Q3 ∨ Q4 (Theorem B). Complete proof, assuming the Bandelt–Mulder four-point characterisation of DH graphs (cited, 1986) | **done modulo the cited theorem**: `problem3ClaimFP`, i.e. every finite connected graph satisfying the four-point condition has Q3' ∨ Q4. DH ⇒ four-point is **not** formalised. |

## 1. Literature status (G1)

The sweep ran 2026-09-26 06:43–07:30 UTC (background agent, plus my own verifications). About 150 queries are logged in `querylog.tsv`; raw data is in `logs/g1/` and `logs/g1v/`.

**Hits that matter**
- **MathOverflow 506431, "Diameter-triameter problem"** (posted 2025-12-28 by the Lviv Scottish Book account).
  - It relays Hak–Kozerenko's LSB problem 3:154 (2025-02-10): does (B) = Q4, or at least (B') = Q4', hold for median graphs?
  - **Accepted answer 506536** (rgvalenciaalbornoz, 2025-12-31 20:38 UTC, score 7): an 11-vertex median graph, four 4-cycles glued in a tree of squares around a vertex s, with diam 4, tr 12, and the unique triametral triple {a,b,c}.
  - The diametral pair {a,x} does not extend, and x is a peripheral vertex in no triametral triple. So (B) and (B') both fail.
  - The LSB account confirmed the prize.
  - Verified by us via the StackExchange API (`logs/g1v/mo_*.json`); re-checked by brute force by the G1 agent.
  - **Consequence: Problem 2's negative answer is prior work.**
- **Wikipedia "Triameter (graph theory)"** (revid 1317724680, 2025-10-19; substantive edits by user "Artem Hak").
  - "Open problems" lists (DT) = Q4 for median graphs (now stale), and suggests investigating (D'T) and (TD') for median graphs. (TD') = Problem 1.
  - Problem 3 is not listed.
  - The figure caption error is discussed in CONTRACT §6.
- **Kozerenko, Discrete Math. Lett. 18 (2026) 55–62** (published 2026-08-29). The full text was read (scout, G1 agent, and my grep). It only says related questions "were also posed" for median and distance-hereditary graphs; it answers none of them.

**Checks with no relevant hit** (with positive controls where applicable):
- MathDB, 13 title-word queries (controls: superpartition / overpartition / cube polynomials);
- SCOPE2026, full tree (26,042 paths, commit 796426b8f241) plus a full-content grep of a shallow clone;
- trureturing: versioned-id and phrase searches of issues and PRs (control 2609.25128v1 → #9523), and all 11 top-level subtrees untruncated (49,048 paths);
- trureturing-pages;
- GitHub-wide issues, PRs, commits (5 phrasings), repos and code;
- google-deepmind/formal-conjectures (tree plus code search);
- arXiv API (6 queries, including au:Kozerenko);
- Crossref, and Semantic Scholar citations (4 citing works, all irrelevant);
- OpenAlex cites: W3137324314 (2 citing works, irrelevant);
- zbMATH Open (triameter 10 documents, triametral 2);
- web search (7 phrasings), Math.SE, Artem Hak's 2022 bachelor thesis, and the HKO 2022 conference abstract.

**Failed or weak checks** (recorded as failures, to redo at G2):
- OpenAlex `search=triameter` / `search=triametral` returned HTTP 429.
- Semantic Scholar keyword search returned HTTP 429.
- The Symmetry 2025 full text returned HTTP 403 (judged from the abstract).
- The zbMATH citation search was unclear.
- GitHub code search for "triameter" was flaky.
- The trureturing-pages content check had no positive control.
- **Not covered:** Google Scholar cited-by, Scopus/WoS, ResearchGate.
- **Web search did not surface the MO thread; only the StackExchange API did.** So G2 should also re-search MO and the LSB for later follow-ups on (A').

## 2. Problem 1: negative answer

**Theorem A1.** Let G1 be the graph on {0,…,7} with the 10 edges
01, 02, 04, 06, 13, 23, 25, 45, 47, 67. These are the three 4-cycles 0-1-3-2, 0-2-5-4 and 0-4-7-6, glued like a fan at 0. Then:
- G1 is a median graph;
- diam(G1) = 4, and the peripheral vertices are exactly 3 and 7;
- tr(G1) = 8;
- {1,5,6} is a triametral triple (d(1,5) = 3, d(1,6) = 2, d(5,6) = 3) containing no peripheral vertex (ecc(1) = ecc(5) = ecc(6) = 3).

So Question 3' fails for median graphs. G1 also violates Question 3, since d ≤ 3 < 4 inside {1,5,6}.

Distance matrix of G1 (rows and columns 0..7):
```
0: 0 1 1 2 1 2 1 2      4: 1 2 2 3 0 1 2 1
1: 1 0 2 1 2 3 2 3      5: 2 3 1 2 1 0 3 2
2: 1 2 0 1 2 1 2 3      6: 1 2 2 3 2 3 0 1
3: 2 1 1 0 3 2 3 4      7: 2 3 3 4 1 2 1 0
```
- Eccentricities: 2, 3, 3, 4, 3, 3, 3, 4.
- Triametral triples, as sets: 13 of them. Exactly one, {1,5,6}, avoids {3,7}.

*Why G1 is median (human argument).* G1 is built from 4-cycles in two gluing steps:
1. Glue the squares 0-1-3-2 and 0-2-5-4 along the edge 02, giving the domino P2×P3.
2. Glue the square 0-4-7-6 to the domino along the edge 04.

Each gluing is along a gated (convex) edge, so both steps are gated amalgams. Median graphs are closed under gated amalgamation; see Klavžar–Mulder's survey or Bandelt–van de Vel. The formal and computational checks below verify the definition directly, triple by triple.

## 3. Problem 2: negative answer

**Theorem A2.** Let G2 be the graph on {0,…,7} with the 8 edges 02, 03, 06, 12, 25, 34, 35, 67: the 4-cycle 0-2-5-3, a leaf 1 at 2, a leaf 4 at 3, and the path 0-6-7. Then:
- G2 is a median graph (a 4-cycle with pendant trees);
- diam(G2) = 4 and tr(G2) = 12. The unique triametral triple is {1,4,7}, with all pairwise distances 4.
- {5,7} is a diametral pair with d(5,7) = 4.
- Its best extension: d(5,z) + d(7,z) takes the values 4, 6, 4, 4, 6, 4, 4, 4 for z = 0..7. So d(5,7,z) ≤ 10 < 12 for **every** z, including z ∈ {5,7}.

So Question 4 fails for median graphs, under both the weak and the strong reading of "extended".

Distance matrix of G2:
```
0: 0 2 1 1 2 2 1 2      4: 2 4 3 1 0 2 3 4
1: 2 0 1 3 4 2 3 4      5: 2 2 1 1 2 0 3 4
2: 1 1 0 2 3 1 2 3      6: 1 3 2 2 3 3 0 1
3: 1 3 2 0 1 1 2 3      7: 2 4 3 3 4 4 1 0
```
Remarks:
- G2 also violates **Q4'** ((B') on MathOverflow).
  - The vertex 5 is peripheral (d(5,7) = 4), but every triple through 5 has sum ≤ 10 < 12.
  - Formal: `not_question4'_G2`, `not_problem2ClaimWeak`.
- G2 satisfies Q3' and Q3. G1 satisfies Q4 (tr(G1) = 2·diam).
- **G2 is also distance-hereditary.** It satisfies the four-point condition: formal `G2_fourPoint`, and it is C4 plus pendant trees.
  - So Q4 fails even for graphs that are both median and DH.
  - This is consistent with Theorem B, because G2 satisfies Q3.
- Reading R2 of Problem 2 (the preceding sentence, i.e. Q3 for median graphs) is already refuted in HKO by their Fig. 2, and also by G1.

## 4. Minimality and uniqueness (Problems 1, 2)

Exhaustive labeled enumeration by `code/median_enum.c`:
- every subset of the n(n−1)/2 edges, for n ≤ 8;
- the median test straight from the definition, over all triples;
- canonical forms by full n! relabelling for n ≤ 7, and by invariant-refined relabelling (all n);
- the two canonical forms agree for n ≤ 7.

Results (`logs/median_enum_le8.log`):

| n | connected labeled graphs | median, labeled | median up to iso | Q3' fails | Q4 fails |
|---|---|---|---|---|---|
| 3 | 4 | 3 | 1 | 0 | 0 |
| 4 | 38 | 19 | 3 | 0 | 0 |
| 5 | 728 | 185 | 4 | 0 | 0 |
| 6 | 26,704 | 2,556 | 11 | 0 | 0 |
| 7 | 1,866,256 | 45,577 | 23 | 0 | 0 |
| 8 | 251,548,592 | 1,008,904 | 69 | 20,160 labeled = **1 class** | 20,160 labeled = **1 class** |

Checks and conclusions:
- The connected counts equal OEIS A001187. The median counts 1, 1, 1, 3, 4, 11, 23, 69 equal OEIS A292623 ("Number of median graphs on n nodes").
- `code/iso_check.py` checks all 8! bijections: the unique Q3'-violator is isomorphic to G1, and the unique Q4-violator to G2. Each has |Aut| = 2, and 8!/2 = 20,160.
- **Hence 8 is the minimum order for both counterexamples, and G1, G2 are the unique minimum counterexamples.**
- The same holds for Q4' ((B')):
  - Q4 ⇒ Q4', so no median graph on ≤ 7 vertices violates Q4'.
  - On 8 vertices the only candidate is G2, which does violate Q4'.
  - The MathOverflow counterexample has 11 vertices.
- This agrees with the scout's count of 42 median graphs on 3..7 vertices (1+3+4+11+23 = 42), which used the networkx atlas.
- **Second, independent implementation** (`code/median8_second_impl.py`, `logs/median8_second_impl.log`):
  - Generation: the networkx atlas (n ≤ 7), plus one-vertex augmentation of the 59 connected triangle-free 7-vertex graphs by an independent neighbourhood (1,857 candidates). Every connected 8-vertex graph has a non-cut vertex, and triangles violate the median definition, so this covers everything.
  - Median test: from the definition via Floyd–Warshall.
  - Isomorphism: networkx.
  - Result: the same counts, and exactly one Q3'-violator (≅ G1) and one Q4-violator (≅ G2) at n = 8.

## 5. Problem 3: affirmative answer

Throughout, G is a finite connected graph with path metric d, D = diam(G), T = tr(G).

**Four-point condition (FP).** For all u, v, w, x, among S1 = d(u,v)+d(w,x), S2 = d(u,w)+d(v,x), S3 = d(u,x)+d(v,w), some two are equal and the third is at most their common value + 2.

By Bandelt–Mulder (JCTB 41 (1986); statement as in Dragan–Leitert, arXiv:1511.05109, Prop. "(4-point condition)"), every connected distance-hereditary graph satisfies FP. The converse also holds but is not needed.

**Lemma (arithmetic core).** Let D, e_ab, e_ac, e_bc, p_a, p_b, p_c, q_a, q_b, q_c be integers with:
- (E) e_uv ≤ D − 1 for the three pairs;
- (F_uv) FP(D + e_uv, p_u + q_v, p_v + q_u) for the three pairs;
- (N_u) D + p_u + q_u ≤ T − 1 for u = a, b, c, where T := e_ab + e_ac + e_bc.

These hypotheses are inconsistent.

*Proof.* Write s_u = p_u + q_u and t_u = p_u − q_u. For a pair {u,v} with third vertex w, put σ0 = D + e_uv, σ1 = p_u + q_v, σ2 = p_v + q_u. By (F_uv) at least one case holds:
- (A_uv) σ0 = σ1;
- (A_vu) σ0 = σ2;
- (C_uv) σ1 = σ2 and σ0 ≤ σ1 + 2.

*Claim 1.* (A_uv) implies q_v − q_u ≥ k and p_u − p_v ≥ k, where k := 2D + 1 − e_uw − e_vw ≥ 3. In particular t_u − t_v ≥ 6.

Proof of Claim 1:
- Substituting p_u = D + e_uv − q_v into (N_u) gives q_v − q_u ≥ k.
- Substituting q_v = D + e_uv − p_u into (N_v) gives p_u − p_v ≥ k.
- k ≥ 3 by (E).

*Claim 2.* (C_uv) implies t_u = t_v and 2D + 2e_uv ≤ s_u + s_v + 4.

Proof of Claim 2: σ1 = σ2 is exactly t_u = t_v. Then σ1 = (σ1+σ2)/2 = (s_u+s_v)/2.

So for each pair: if (C) holds then t_u = t_v; otherwise |t_u − t_v| ≥ 6, and the sign determines which (A) holds. (C together with an (A) is impossible.) Count the pairs in case (C):
- **All three.** Summing Claim 2 and using (N):
  - 6D + 2T ≤ 2(s_a+s_b+s_c) + 12 ≤ 6(T − D − 1) + 12, so T ≥ 3D − 3/2.
  - But T ≤ 3D − 3 by (E). Contradiction.
- **Exactly two.** Transitivity gives t_a = t_b = t_c, so the third pair has t_u = t_v while not in (C). This contradicts Claim 1.
- **Exactly one**, say {u,w}, with v the third vertex; so t_u = t_w ≠ t_v.
  - Swapping x and y (p ↔ q, t ↦ −t) preserves all hypotheses. So we may assume t_u = t_w > t_v, which gives (A_uv) and (A_wv).
  - Then p_u = D + e_uv − q_v and p_w = D + e_wv − q_v.
  - By Claim 1 (third vertices w and u): s_u + s_w = 2D + e_uv + e_vw − (q_v−q_u) − (q_v−q_w) ≤ 2(e_uv + e_vw + e_uw) − 2D − 2.
  - Claim 2 for {u,w} then gives e_uv + e_vw ≥ 2D − 1, contradicting (E).
- **None.** The t-values are distinct; label them t_1 > t_2 > t_3.
  - Then (A_12), (A_23) and (A_13) hold.
  - Hence s_2 = (D + e_23 − q_3) + (D + e_12 − p_1) = 2D + e_12 + e_23 − (D + e_13) = D + e_12 + e_23 − e_13.
  - (N_2) then gives 2e_13 ≥ 2D + 1, contradicting (E). ∎

Note: only e_uv ≤ D − 1 and the three quadruples {x,y,u,v} are used. No triangle inequality, no bounds on p or q, and not T ≥ 2D + 1.

**Theorem B.** Assume G satisfies FP (e.g. G is connected distance-hereditary). Let {a,b,c} be a triametral triple containing no diametral pair, i.e. d(a,b), d(a,c), d(b,c) < D. Then every diametral pair {x,y} extends to a triametral triple by a vertex of {a,b,c}: max{d(a,x,y), d(b,x,y), d(c,x,y)} = T.

*Proof.* Put e_uv = d(u,v), p_u = d(x,u) and q_u = d(y,u).
- d(x,y) = D, and FP applied to (x,y,u,v) is exactly (F_uv).
- (E) is the hypothesis.
- Every triple sum is ≤ T. So if no u ∈ {a,b,c} made {x,y,u} triametral, (N_u) would hold for all three u, contradicting the Lemma. ∎

(More generally the same argument gives the inequality max_u d(u,x,y) ≥ d(a,b,c) for **any** triple {a,b,c} without a diametral pair and any diametral pair {x,y}, in a graph satisfying FP.)

**Corollary B1.** Every finite connected graph satisfying FP (in particular every connected distance-hereditary graph) satisfies Q3 or Q4.

Proof: if Q3 fails, some triametral triple has no diametral pair, and Theorem B gives Q4. ∎

**Corollary B2 (HKO Problem 3: yes).** For every connected distance-hereditary graph, at least one of Questions 3' and 4 holds.

Proof: Q3 ⇒ Q3', since a vertex of a diametral pair is peripheral. ∎

*Readings.*
- B1 and B2 also hold under the strong reading of Q4 (z ∉ {x,y}), for n ≥ 3:
  - if T = 2D, every z works;
  - if T > 2D, the extending vertex u ∈ {a,b,c} satisfies d(u,x,y) = T > 2D = d(x,x,y), so u ∉ {x,y}.
- For n ≤ 2, Q3 holds trivially.
- B1 also implies "Q3' or Q4'", since Q4 ⇒ Q4'.

*Sharpness and context.*
- **Theorem B needs the "no diametral pair" hypothesis.** In HKO Fig. 1 H (DH), the triametral triple {a,b,c} has pairwise distance 2 = D, and the diametral pair {x,y} extends to no triametral triple.
- **The DH hypothesis cannot be dropped.** HKO's own figure in Sec. 3.2 (12 vertices, diam 5, tr 12) violates Q3, Q3' and Q4 at once, and fails FP (`logs/hko_fig0_check.log`).
- **The alternative is genuinely needed.**
  - Fig. 1 G (DH) violates Q3' (and Q3); Fig. 1 H and G2 (DH) violate Q4. All three are formalised.
  - So neither Q3' nor Q4 holds for all DH graphs.
- **The scout's proposed reduction is false.**
  - The reduction was: DH and tr > 2·diam ⇒ Q3'.
  - Among all connected DH graphs with n ≤ 11 there is exactly one counterexample, on 11 vertices (`logs/dh_reduction_cex.log`). Larger random ones exist, e.g. n = 20 with diam 5, tr 12 (`logs/dh_h0_example.log`).
  - The 11-vertex counterexample:
    - Structure: K_{2,3} with parts {0,4} and {1,2,3}; leaves 6, 7, 8 at 1, 2, 3; a leaf 9 at 4; the path 0–5–10.
    - Edges: 01, 02, 03, 05, 14, 16, 24, 27, 34, 38, 49, 5‑10.
    - diam = 5 = d(9,10) and tr = 12 > 10.
    - The triametral triple {6,7,8} has pairwise distances 4 and eccentricities 4, so it has no peripheral vertex.
    - The only diametral pair {9,10} is extended by each of 6, 7, 8, exactly as Theorem B predicts.
    - Verified DH from the definition, over all 2^11 induced subgraphs (`logs/dh_reduction_cex_verify.log`).
  - In these graphs Problem 3 holds through Q4. That is what Theorem B provides.

## 6. Checks performed

Mathematics:
1. **Independent re-verification of G1, G2.**
   - `code/verify_g1_g2.py`: Floyd–Warshall, no networkx; median property via the interval definition over all 512 ordered triples. Output in `logs/verify_g1_g2.log` and `.json`.
   - `code/median_enum.c`: BFS; separate code path.
   - The Lean kernel (below): third path.
2. **Minimality and uniqueness**: §4.
3. **Five-point infeasibility search** (`code/fivepoint.c`, `fivepoint_ablate*.c`):
   - With all constraints, no counter-model for D ≤ 14.
   - The ablation shows that FP on the three quadruples {x,y,u,v} plus e_uv ≤ D−1 already suffices (D ≤ 12). This guided the Lemma.
   - Positive control: without the negated conclusion, feasible configurations exist, e.g. D = 5, e = 4, 4, 4, p = 4, q = 3.
4. **Exhaustive DH check, n ≤ 11** (`code/dh_exhaustive.py`; graph list from the scout's generator, all properties recomputed by our BFS; `logs/dh_exhaustive_n11.log`):
   - counts 1, 2, 6, 18, 73, 308, 1484, 7492, 40010, 220676 for n = 2..11;
   - FP holds for all 49,394 graphs with 2 ≤ n ≤ 10;
   - Theorem B holds in all 48,108 applicable (triple, diametral pair) cases, 37,472 of them at n = 11; 270,070 graphs in total;
   - Q3 ∨ Q4 and Q3' ∨ Q4 hold for every graph;
   - the scout's reduction fails once (n = 11).
5. **Random DH graphs** (one-vertex extensions):
   - `code/dh_explore.py`: 6,000 graphs, n ≤ 22; FP checked for n ≤ 14; logs `dh_explore_seed*.log`.
   - `code/dh_lemmaS.py`: 9,000 graphs, n ≤ 34; tests the non-peripheral variant.
   - `code/dh_thmB_random.py`: 3,300 graphs, n ≤ 30. It tests Theorem B exactly (578 applicable cases) and the general inequality max_u d(u,x,y) ≥ d(a,b,c) (about 11.6 million cases); log `dh_thmB_random_*.log`.
   - No failure of FP, of Theorem B, of the inequality, or of Q3 ∨ Q4 / Q3' ∨ Q4.
6. **Distance-heredity by definition** (`code/dh_by_definition.py`: every connected induced subgraph is isometric, over all 2^n subsets; independent of the generator and of the four-point theorem):
   - Fig. 1 G, Fig. 1 H and G2 are DH.
   - G1, C5 and HKO's Sec. 3.2 graph are not.
   - Log: `logs/dh_by_definition_tests.log`.

Formal (Lean 4.33.1, Mathlib `0df444a3…`; logs in `logs/`):
- `Research/HKOTriameter.lean` (SHA-256 `a356f94f…`):
  - Definitions: `triDist`, `triameter`, `IsTriametral`, `IsDiametral`, `IsPeripheral` (Mathlib `eccent = ediam`), `IsPeripheralPair` (HKO's wording), `InInterval`, `IsMedian`, `Question3'`, `Question3`, `Question4`, `Problem1Claim`, `Problem2Claim`. All built on Mathlib's `SimpleGraph.dist`, `diam`, `eccent`, `ediam`.
  - Distances come from explicit tables through `dist_eq_of_certificate` (walk certificates plus a 1-Lipschitz lower bound). All finite checks use `decide` / `decide +kernel`.
  - Main theorems: `not_problem1Claim`, `not_problem1ClaimPair`, `not_problem2Claim`, `not_problem2ClaimWeak` (Q4'), `not_question3_G1`, `isPeripheral_iff_isPeripheralPair`.
  - Sanity checks: 3 and 7 are peripheral in G1; C6 is not median.
- `Research/HKOTriameterDH.lean` (SHA-256 `1e701178…`):
  - `FP`, `FourPointBM`, `core` (27-case `omega`), `extends_of_no_diametral` (Theorem B), `question3_or_question4` (B1), `problem3_fourPoint` / `problem3ClaimFP` (B2).
  - Sanity checks: HKO Fig. 1 G and H satisfy FourPointBM; G violates Q3'; H violates Q4. G1 violates FP; G2 satisfies FP.
  - `F1G_not_median`: Fig. 1 G is not median. This refutes the Wikipedia caption that calls it median.
- **Acceptance** (final run 2026-09-26 07:36:40–07:37:59 UTC; `logs/acceptance_final.log`):
  - `lake build Research.HKOTriameterDH`: exit 0 (builds both modules), no warnings.
  - Scripted axiom audit (`code/axiom_audit.py`): 21/21 final declarations printed once each, all with axioms ⊆ {propext, Classical.choice, Quot.sound}. `core` uses only {propext, Quot.sound}.
  - Forbidden-token grep: the only hit is a doc comment saying "no `native_decide`".
  - `lake env leanchecker` on both modules: exit 0.
  - Clean-directory replay (fresh copy; `.lake/packages` symlinked to the trusted Mathlib cache):
    - build, audit and both leanchecker runs exit 0;
    - its axiom lines are identical to the dev-tree audit;
    - source, olean and audit hashes are in the log.
  - Toolchain: Lean 4.33.1 (commit 819816b2); Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- **Not formalised.** The Bandelt–Mulder theorem "connected DH ⇒ FourPointBM". The formal Problem-3 statement is therefore for graphs *satisfying the four-point condition*.
- **Not yet done** (playbook 3.3/3.5): third-party review of the statements, a frozen `Challenge.lean`, and the author's reading of a statement table.

## 7. What is new / what is known

| Item | Known before? | What we add |
|---|---|---|
| P1 negative (Q3' fails for median graphs) | No answer found | **New**: the 8-vertex counterexample G1, proved minimal and unique up to isomorphism; Lean-verified |
| P2 negative (Q4 fails for median graphs) | **Yes**: MathOverflow answer 506536, 2025-12-31 (11 vertices; also refutes (B')) | A smaller counterexample G2 (8 vertices), proved minimal and unique up to isomorphism, also refuting (B'); Lean-verified. **Must credit the MO answer**; not a first answer |
| G2 is median *and* DH | Not seen | Remark: Q4 fails even for median ∩ DH graphs |
| P3 affirmative | No answer found | **New**: Theorem B and Corollaries B1 (Q3 ∨ Q4, stronger than asked) and B2 for all connected DH graphs. Lean-verified for graphs with the four-point condition; the step DH ⇒ four-point is the cited Bandelt–Mulder theorem |
| The scout's reduction "tr > 2·diam ⇒ Q3'" for DH graphs | — | **False**: unique counterexample among DH graphs with n ≤ 11, on 11 vertices (§5). It is not needed |
| Known ingredients used | Bandelt–Mulder four-point characterisation (1986); Mathlib's metric API | — |

**Recommendation**
- Write a short note answering HKO Problems 1 and 3 (new), with Problem 2 as "smallest counterexample, crediting MathOverflow 506536".
- Before any public claim:
  1. G2 refresh: Google Scholar cited-by, OpenAlex retry, and an MO/LSB follow-up search for (A').
  2. Third-party statement review of `HKOTriameter*.lean`.
  3. The author reads the statement table (§8).
  4. The playbook's pre-release checklist.


## 8. 陈述对照表（给作者逐条核对；Lean 原文见 `lean/`）

| # | Lean 原文（节选） | 中文白话 | 论文位置（`src/Hak_Kozerenko_Oliynyk.tex`） | 差异说明 |
|---|---|---|---|---|
| 1 | `triameter G := (univ : Finset (V × V × V)).sup (fun t => triDist G t.1 t.2.1 t.2.2)`，其中 `triDist G u v w = d(u,v)+d(u,w)+d(v,w)` | tr(G)：所有三点组（允许重复）两两距离之和的最大值 | 第 2 节，第 103–106 行 | 一致。原文同样没有要求三点互不相同；n ≥ 3 时要不要求结果都一样 |
| 2 | `IsTriametral G u v w := triDist G u v w = triameter G` | 三点组的距离和达到 tr(G) | 第 107 行 | 一致 |
| 3 | `IsDiametral G u v := G.dist u v = G.diam` | 两点距离等于直径 | 第 101 行 | 一致（用的是 Mathlib 的 `diam`） |
| 4 | `IsPeripheral G u := G.eccent u = G.ediam`；`IsPeripheralPair G u := ∃ v, IsDiametral G u v` | 边缘点：偏心率等于直径；或者说，属于某个直径对 | 第 101 行（原文用的是"属于某个直径对"） | 两个定义都写了。`isPeripheral_iff_isPeripheralPair` 证明二者在有限连通图上等价，问题 1 对两个定义都已反驳 |
| 5 | `IsMedian G := G.Connected ∧ ∀ u v w, ∃! x, InInterval G u v x ∧ InInterval G u w x ∧ InInterval G v w x` | 中位图：连通，且任意三点两两之间的三个"区间"恰好交于一点 | 第 109–111 行 | 一致："交集大小为 1"写成了"恰有一个" |
| 6 | `Question3' G := ∀ a b c, IsTriametral G a b c → IsPeripheral G a ∨ IsPeripheral G b ∨ IsPeripheral G c` | 每个达到 tr 的三点组里都至少有一个边缘点 | 第 437 行 | 一致 |
| 7 | `Question4 G := ∀ x y, IsDiametral G x y → ∃ z, IsTriametral G x y z` | 每个直径对都能补上一个点，凑成达到 tr 的三点组 | 第 77 行（Das 的问题） | 对 z 不加限制，是最弱的读法，因此反驳它就是最强的反驳；推论 B1 在"z 必须另取一点"的读法下同样成立 |
| 8 | `not_problem1Claim : ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), IsMedian G → Question3' G)` | "所有有限中位图都满足 Q3'"是错的 | 第 446 行 | 反例是 G1（8 个点） |
| 9 | `not_problem2Claim : ¬ (∀ … , IsMedian G → Question4 G)` | "所有有限中位图都满足 Q4"是错的 | 第 478 行 | 反例是 G2（8 个点）；另一种读法（问题前那句话）已由原文图 2 否定 |
| 10 | `FourPointBM G := ∀ u v w x, FP (d u v + d w x) (d u w + d v x) (d u x + d v w)` | 四点条件：三个"对边距离和"里总有两个相等，第三个至多比它们大 2 | 第 373 行（原文的简写版漏了"大 2"这一条）；Bandelt–Mulder 1986 | 按 Bandelt–Mulder 的完整表述。"距离遗传图满足四点条件"这一步是引用的定理，**没有**形式化 |
| 11 | `problem3ClaimFP : ∀ (V : Type) [Fintype V] (G : SimpleGraph V), G.Connected → FourPointBM G → Question3' G ∨ Question4 G` | 满足四点条件的有限连通图（也就是距离遗传图）都满足 Q3' 或 Q4 | 第 487 行 | Lean 的前提是"满足四点条件"，而不是"距离遗传"；二者的衔接靠引用的 Bandelt–Mulder 定理。另外还证明了更强的 Q3 或 Q4（`question3_or_question4`） |
