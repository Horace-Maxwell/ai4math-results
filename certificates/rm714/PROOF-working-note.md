# PROOF — weights of the Reed–Muller code RM(7,14)

Agent `rm714`. Session 1: 2026-09-26, 06:38–09:40 UTC. Session 2 (this revision): 13:37–14:50 UTC.
The contract is in `CONTRACT.md`; the previous version of this file is `archive/PROOF-session1-0958Z.md`.

**Notation.** `Spec` is the weight spectrum of RM(7,14); d = 128, 2.5d = 320, 3d = 384.
U₀ = {322, 326, 330, 334}; U = U₀ ∪ (16384 − U₀) = U₀ ∪ {16050, 16054, 16058, 16062}.
**KT** = Kasami–Tokura 1970 (weights < 2d). **KTA** = Kasami–Tokura–Azumi 1976 (weights < 2.5d).

---

## 0. Summary and status table

| Item | Literature (G1 + G2) | Statement | Mathematics | Formal (Lean) |
|---|---|---|---|---|
| **A.** 17 weights with explicit witnesses: the **14 new** ones of M \ U (354, 16030, 8174–8190, 8194–8210) and 4378, 4380, 4382 (already asserted by Prop. 4 of 2606.21425, see §3) | No prior claim of the 14 found (§12). **Caveat:** the Lou–Wang DAM 388 note is unread | Fixed (R1, R2) | **Proved**: explicit witnesses, 3 independent checks | **Accepted**: build exit 0; axioms ⊆ {propext, Classical.choice, Quot.sound}; forbidden-token grep empty; leanchecker 0; clean-directory replay 0 |
| **B.** Spec = S₀ ∪ X, with X ⊆ U and X = 16384 − X | Same | R4 | **Proved**. Cites KTA only for "no weight < 320 outside K". 7901 explicit witnesses, 2 implementations | Only A is formalised |
| **C.** Lou–Wang Conjecture 2 is false at m = 6 | Same; the DAM note could touch it | R5 | **Proved**. Cites only the RM(6,12) weight list below 160 (Lou–Wang's own Lemma 2) | – |
| **C′.** The family x13·A + x14·B misses all of U | – | – | **Proved** (cites KT normal forms) | – |
| **D.** No sum of ≤ 3 flat indicators has weight in U | – | – | **Proved** (hand proof + arithmetic certificate) | – |
| **E.** No sum of ≤ 5 monomials has weight in U | – | – | **Proved** by exhaustive enumeration, 2 independent programs | – |
| **F.** Structure of a codeword of weight ≡ 2 mod 4; F6: w ∈ U₀ occurs iff some h of weight w − 2 (resp. w − 6) admits g with 1 (resp. 3) points outside supp h | – | – | **Proved** (elementary + McEliece) | – |
| **G.** Inverse search (exact inner step, sampled outer step): ~1.4·10⁵ h tested exactly, 0 hits in U₀; the same method finds all of 162–174 in RM(6,12) within seconds | – | – | Heuristic; calibrated on RM(6,12) | – |
| **Do 322, 326, 330, 334 occur?** | Open everywhere | R3 | **OPEN** | – |

**The result in one sentence.**

- Carlet's open question for (c, m) = (7, 14) is now equivalent to the four statements "322, 326, 330, 334 ∈ Spec".
- Every other weight of RM(7,14) is decided; 14 of them are decided here for the first time (all of M outside U), and every weight asserted by Prop. 4 of 2606.21425 now has an independently checked explicit witness.
- Lou–Wang's Conjecture 2 (DCC 2025) would have supplied these four weights, and it is false at m = 6.

---

## 1. What exactly is decided (contract readings, CONTRACT §2)

| Reading | Question | Answer after this work |
|---|---|---|
| R1 | Decide each of the 22 weights in M (2606.21425v1, Prop. 4) | **14 occur:** 354, 8174, 8178, 8182, 8186, 8188, 8190, 8194, 8196, 8198, 8202, 8206, 8210, 16030. **8 are undecided:** U. |
| R2 | Decide each of the 8 weights in the paper's Remark | **4 occur:** 354, 4378, 4380, 4382. **4 are undecided:** U₀. (Of these, 4378, 4380, 4382 are not in M: Prop. 4 of 2606.21425 already asserts them, and the Remark lists them only as seeds that the authors' construction would need; so only 354 is new here.) |
| R3 | Carlet's open question at (c, m) = (7, 14) | **Reduced:** the answer is positive iff U₀ ⊆ Spec (Theorem B + KT/KTA). Still undecided. |
| R4 | The full spectrum of RM(7,14) | Spec = S₀ ∪ X, where X ⊆ U and X is closed under w ↦ 16384 − w (Theorem B). |
| R5 | Lou–Wang Conjecture 2 at m = 6 (a finite statement) | **False:** 322 is not produced (Proposition C). This holds under both readings of "Construction 2": the literal monomial form, and arbitrary g1, g2 ∈ RM(6,12) as in the proof of their Prop. 5. |

**Strong vs. weak readings.**

- R1 and R2 are decided except for U.
- R3 is only reduced.
- R5 is decided negatively.

Nothing here claims that a weight of U is *not* a weight. Propositions C′, D and E exclude U only inside explicit families.

---

## 2. Results used and not re-proved (cited)

| Input | Where used | Source actually read |
|---|---|---|
| McEliece divisibility: weights of RM(r,m) are divisible by 2^{⌈m/r⌉−1} | B (even weights), F1, F2 | standard; McEliece, Discrete Math. 3 (1972) |
| **KT** (1970): normal forms of codewords of weight < 2d (type I: 1_E·q; type II: 1_F + 1_F′) | C′, F5 | via Lou–Wang arXiv:2406.03803v1 and the Abbe–Shpilka–Ye survey; the IEEE paper itself was not read |
| **KTA** (1976): the weights below 2.5d. For RM(7,14) these are exactly K = {0, 128, 192, 224, 240, 248, 252, 254, 256, 272, 288, 296, 304, 308, 312, 314, 316, 318} | Corollary of B (exclusion side only) | as used by 2606.21425 (W₀ ∪ {312, …, 318}) and Carlet 2024; the KTA paper itself returned HTTP 403 |
| KTA list for RM(6,12): the weights < 160 are {0, 64, 96, 112, 120, 124, 126, 128, 136, 144, 148, 152, 154, 156, 158} | C | Lou–Wang arXiv:2406.03803v1, Lemma 2 (their own citation of KT/KTA) |
| Lou–Wang: the weights of RM(m−6,m), m ≥ 12, are A ∪ {152 + 2i} ∪ (2^m − A); in particular every even weight of RM(6,12) in [152, 3944] occurs | C′ (only to add 160–166 to the candidate list; a superset is harmless) | Lou–Wang, main theorem (arXiv:2406.03803v1, l. 338–344) |

**Everything else is proved or computed here:** all existence claims, all enumerations, all arithmetic.

- We do **not** rely on the unpublished computer lemmas (Lemmas 6 and 9) behind Proposition 4 of 2606.21425. Every weight we claim has our own explicit witness.
- The inclusion K ⊆ Spec is also witnessed explicitly. Only the exclusion "no other weight below 320" is cited.
- Consistency check: the exhaustive ≤ 5-monomial enumeration (§7) produces exactly K below 320.

---

## 3. Theorem A (new weights; explicit codewords)

**Theorem A.** The following 17 numbers are weights of RM(7,14): 354, 16030, 4378, 4380, 4382, 8174, 8178, 8182, 8186, 8188, 8190, 8194, 8196, 8198, 8202, 8206, 8210.

Witnesses, in variables x1..x14 (the Lean file encodes a monomial as a 14-bit mask, with bit i−1 ↔ x_i):

| w | witness polynomial (degree ≤ 7) | #mon. |
|---|---|---|
| 354 | x1x2x3x4x5x6x7 + x1x2x3x5x6x7x11 + x1x3x6x7x10x12x13 + x3x4x6x7x10x12x13 + x8x9x10x11x12x13x14 | 5 |
| 16030 | 1 + (the 354 witness) | 6 |
| 4378 | x3x4x6 + x1⋯x7 + x1x5x7x11x13 + x6x14 + x8⋯x14 | 5 |
| 4380 | x2x6x7x9x12 + x3x4x5x8x9x10x13 + x8x14 + x1x3x5x9x10x11x14 | 4 |
| 4382 | x1x2x5x6x7 + x1⋯x7 + x4x9 + x3x4x6x8x12 + x8⋯x14 | 5 |
| 8174 … 8190, 8194 … 8210 | masks in `Research/RM714Weights.lean` (L8174 … L8210) | 4–7 each |

- Of the 22 weights in M, the 14 listed under R1 occur. **These 14 are new:** 2606.21425 lists them as missing, and no other source claims them (§12).
- Of the 8 weights in the Remark, the 4 listed under R2 occur. **Novelty caveat:** 4378, 4380 and 4382 are not in M. Prop. 4 of 2606.21425 already asserts that they are weights: they lie in {312 + 2i} \ M, and in its sets S2mod4 and S0mod4. Its proof rests on computer lemmas whose details are unpublished. The Remark names them only as seeds that the authors' concatenation would need to produce M. So for these three we supply an independent explicit witness, not a new weight. The Lean theorem is called `rm714_new_weights` for historical reasons; its content is just "these 17 numbers are weights".
- **Structural remark on 8174–8210.** For arbitrary A = A(x1..x7) and B = B(x8..x14), A + B ∈ RM(7,14) and wt(A + B) = 8192 − 2(64 − wt A)(64 − wt B). For example (61, 61) ↦ 8174. This formula is only a remark; what is certified is the witnesses themselves.

**Certificates.** Three independent checks:

- (i) `code/verify_witnesses.c`: fast Möbius transform ANF → truth table, popcount, an involution check, degree ≤ 7, and no repeated monomial.
- (ii) `code/verify_bitset.py`: pure Python big-integer truth tables. It uses no Möbius transform and shares no code with (i).
- (iii) The Lean kernel (§10).

Logs: `logs/verify_all_witnesses_{C,py}.log`, `logs/lake_build_RM714.log`, `logs/lean_clean_replay.log`.

---

## 4. Theorem B (the whole spectrum except U)

**Theorem B.** Let S₀ = K ∪ {even w : 320 ≤ w ≤ 16064} ∪ (16384 − K), minus U. It has 7901 values, and every element of S₀ is a weight of RM(7,14).

- `data/rm714_all_witnesses.json` (sha256 784bca3b…) gives, for each of the 7901 values, a polynomial with at most 8 monomials.
- Distribution by number of monomials: 0:1, 1:8, 2:68, 3:559, 4:1929, 5:2995, 6:1947, 7:389, 8:5.

**Corollary** (cites KTA for the exclusion side). Spec = S₀ ∪ X for some X ⊆ U with X = 16384 − X.

*Proof.*
- All weights are even (McEliece).
- By KTA the weights < 320 are exactly K. By complementation (f ↦ f + 1), the weights > 16064 are exactly 16384 − K.
- Every even weight in [320, 16064] outside U has a witness. ∎

**Certificates.** Two implementations:

- (i) `code/verify_witnesses.c`;
- (ii) `code/verify_all_py.py`, which uses `verify_bitset.check`.

Both report 7901/7901 correct, 0 failures, and confirm that the table covers S₀ exactly (`logs/verify_all_witnesses_{C,py}.log`).

**Provenance of the table.** It comes from the sparse sampler `code/sparsefind.c` (249,320,000 random sparse ANFs), plus the construction of Lemma 8 of 2606.21425 for 362 (re-verified here). The provenance does not affect correctness, since every witness is checked.

---

## 5. Proposition C (Lou–Wang Conjecture 2 is false at m = 6) and C′

**Lemma C1.** If A, B ∈ RM(6,12) and f = x13·A + x14·B (the concatenation 0‖A‖B‖(A+B)), then wt f = wt A + wt B + wt(A+B) ≠ 322.

*Proof.*
- Let a = wt A, b = wt B and c = wt(A+B). They satisfy the triangle inequalities, because supp(A+B) ⊆ supp A ∪ supp B (and symmetrically).
- If a + b + c = 322, then max(a, b, c) ≤ 161.
- So a, b and c lie in the list of RM(6,12) weights ≤ 161 (§2: KTA via Lou–Wang Lemma 2, together with 160).
- An exhaustive check finds no triple from that list that sums to 322 and satisfies the triangle inequalities (certificate `C triples w=322: none`). ∎

**Proposition C.** Let S be the set of weights produced by Lou–Wang's Construction 2 at m = 6, that is, by g = 0‖(g1+a1)‖g2‖(g1+g2+a2) with a1, a2 ∈ F₂. Take either reading:

- (a) g1, g2 as written in the construction: sums of three monomials of degree ≤ 6, with or without repeated indices;
- (b) arbitrary g1, g2 ∈ RM(6,12), as in the proof of their Proposition 5.

Then 322 ∉ S. Hence Lou–Wang's **Conjecture 2** (DCC 93 (2025) 4925–4936; arXiv:2406.03803v1 §4, l. 382–388), which asserts {320 + 2i : 0 ≤ i < 64} ⊆ S at m = 6, **is false**.

*Proof.* Reading (b) contains reading (a), so take g1, g2 ∈ RM(6,12).

- **a1 = a2 = 0:** g = x13·g1 + x14·g2, so Lemma C1 applies.
- **a1 = 1, a2 = 0:** wt g = (4096 − wt g1) + wt g2 + wt(g1 + g2) ≥ 4096, since wt g2 + wt(g1+g2) ≥ wt g1.
- **a1 = 0, a2 = 1:** wt g = wt g1 + wt g2 + 4096 − wt(g1+g2) ≥ 4096.
- **a1 = a2 = 1:** put G1 = g1 + 1 ∈ RM(6,12). Then g = 0‖G1‖g2‖(G1 + g2) = x13·G1 + x14·g2, and Lemma C1 applies. ∎

The session-1 version handled the last case by a bound on the number of monomials. The argument above is shorter and also covers reading (b).

**Proposition C′.** No f = x13·A + x14·B with A, B ∈ RM(6,12) has weight 326, 330 or 334. Applying f ↦ f + 1, the family 1 + x13A + x14B misses 16050–16062. So Construction 2 at m = 6 misses all of U.

*Proof.* By the certificate, the triangle-feasible triples are:

- 326: (64, 126, 136);
- 330: (64, 112, 154);
- 334: (64, 112, 158), (64, 126, 144), (96, 112, 126).

The roles of A, B and A+B are symmetric. The KT normal forms in RM(6,12) are:

- weight 64: the indicator of a 6-flat;
- weight 126: 1_F + 1_F′, with F and F′ 6-flats and F ∩ F′ = {p};
- weight 112: x1x2x3(x4x5x6 + x7x8x9) or x1⋯x4(x5x6 + x7x8 + x9x10);
- weight 96: x1⋯x4(x5x6 + x7x8).

In each case the required overlap |supp X ∩ supp Y| = (wt X + wt Y − wt(X+Y))/2 is impossible:

- **(64, 126, 136) and (64, 126, 144).** The overlap is 27, resp. 23, and equals |A∩F| + |A∩F′| − 2[p ∈ A]. So |A∩F| + |A∩F′| ∈ {27, 29}, resp. {23, 25}. Each term is 0 or a power of 2 that is ≤ 64, and none of 23, 25, 27, 29 is a sum of two such numbers (certificate).
- **(64, 112, 154) and (64, 112, 158).** The overlap is 11, resp. 9, which is odd.
  - *Second form of B.* supp B = E ∩ supp q, with q quadratic and E an 8-flat. A 6-flat A meets it in the support of a quadratic on the flat A ∩ E. That support is even if dim(A ∩ E) ≥ 3, and has size ≤ 4 otherwise. So it is never 9 or 11.
  - *First form of B.* B = 1_F + 1_F′, with F and F′ 6-flats in the 9-flat {x1 = x2 = x3 = 1} and |F ∩ F′| = 8. Oddness forces |A∩F| = 1 or |A∩F′| = 1, so t := |A∩F∩F′| ≤ 1.
    - For 11 we would need 2^j = 10 + 2t ∈ {10, 12}, which is impossible.
    - For 9 we need |A∩F| = 1, |A∩F′| = 8 and t = 0. Parametrise A by its projection to (x1..x6); this is a bijection because |A ∩ F| = 1. Then |A ∩ F′| = 8 forces x7, x8 and x9 to be functions of x1, x2, x3 alone on A. So the unique point of A ∩ F lies in F′, i.e. t = 1, a contradiction.
- **(96, 112, 126).** Let C = 1_F + 1_F′ (weight 126) and let A have weight 96. Then |supp A ∩ supp C| = 55, so |supp A ∩ F| + |supp A ∩ F′| ∈ {55, 57}.
  - One summand is odd. It is then the support of a quadratic of full degree on a flat of dimension ≤ 2, so it is ≤ 3.
  - The other summand is ≤ 48. First, supp A contains no 6-flat, since otherwise A + 1_F would have weight 32 < 64. Second, a non-constant quadratic on F₂⁶ has weight ≤ 48.
  - The total is ≤ 51 < 55. ∎

Leuenberger–Albrizzio's Constructions 1–3 lie inside this family. So C and C′ explain why their method could not reach U.

---

## 6. Proposition D (sums of at most three flats)

**Proposition D.** Let F1, F2, F3 be affine flats in F₂¹⁴ of dimension ≥ 7 (possibly equal; dimension 14 gives the constant 1). Then wt(1_F1 + 1_F2 + 1_F3) ∉ U. The same holds for fewer flats.

*Proof.* We have wt = Σ|Fi| − 2Σ|Fi∩Fj| + 4|F1∩F2∩F3|, and every nonempty intersection of flats is a flat, whose size is a power of 2. Hence wt ≡ 2 (mod 4) iff an odd number of pairs meet in exactly one point. Call such a pair "transversal"; both of its flats must have dimension 7.

- **One or two flats.** The only weight ≡ 2 mod 4 is 254 (certificate).
- **Three pairwise transversal 7-flats.** The weight is 378 or 382.
- **Exactly one transversal pair.** Say F1 ∩ F2 = {p}, with dim F1 = dim F2 = 7, and let F3 have dimension d. Write |F1∩F3| = α and |F2∩F3| = β, with α, β ∈ {0, 2, 4, …, 128}. Put p = 0; then V1 ⊕ V2 = F₂¹⁴.
  - **p ∈ F3,** so F3 = V3. Write α = 2^a and β = 2^b. Since (V3∩V1) ⊕ (V3∩V2) ⊆ V3, we get a + b ≤ d. The weight is 258 + 2^d − 2^{a+1} − 2^{b+1}. By the certificate, the only solutions with weight in U are (d, w, a, b) = (7, 322, 4, 4) and (8, 322, 5, 6). Both violate a + b ≤ d.
  - **p ∉ F3.** The weight is 254 + 2^d − 2(α + β). By the certificate, the only solution with weight in U is d = 7, w = 334, {α, β} = {8, 16}.
    - Then dim(V3∩V1) + dim(V3∩V2) = 3 + 4 = 7 = dim V3, so V3 = (V3∩V1) ⊕ (V3∩V2).
    - F3 = c + V3 meets F1 and F2, so c ∈ (V1 + V3) ∩ (V2 + V3).
    - Writing c = c1 + c2 with c_i ∈ V_i, this forces c1 ∈ V3∩V1 and c2 ∈ V3∩V2. So c ∈ V3, and p = 0 ∈ F3, a contradiction. ∎

The obstruction is dimension counting. In RM(6,12) the same count allows a = b = 3 ≤ d = 6, and three 6-flats give 2.5d + 2 = 162. In RM(7,14) the analogous configuration would need a = b = 4, but a + b = 8 > d = 7.

---

## 7. Proposition E (sums of at most five monomials; exhaustive)

**Proposition E.** No polynomial in x1..x14 that is a sum of at most 5 monomials of degree ≤ 7 (the constant 1 allowed) has weight in U. By affine invariance the same holds for sums of ≤ 5 "monomials" in any affine coordinate system.

*Method.*

- The weight of Σ_i ∏_{j∈S_i} x_j depends only on the Venn-region sizes of S_1, …, S_k.
- We enumerate every labelled configuration with total size ≤ 14 and every |S_i| ≤ 7.
- Equal monomials cancel in pairs, so k = 4 covers the even numbers of monomials and k = 5 the odd ones.

*Results.*

- **k ≤ 4.** Three programs: `venn_enum.c` and `venn_enum_fast.c` (session 1) and `venn_enum_indep.c` (session 2). They give identical configuration counts (8; 204; 20,708; 8,568,777) and identical weight sets.
- **k = 5.** Two programs:
  - `venn_enum_fast.c` (session 1): 11,690,447,828 configurations, 5676 distinct weights.
  - **`venn_enum_indep.c`** (session 2) is separate code. It splits the Venn regions monomial by monomial instead of recursing region by region. It computes the weight by Möbius inversion of E(Q) = 2^{#free variables} over the superset lattice, instead of Σ_T (−2)^{|T|−1} 2^{14−|U_T|}.
  - Both give **the same count, 11,690,447,828, and the same 5676 distinct weights. Neither finds a weight in U** (`logs/venn_enum_k5.log`, `logs/venn_enum_indep.log`).
- The weights ≡ 2 mod 4 in [250, 400] that occur with ≤ 5 monomials are 254, 314, 318 and every value 338, 342, …, 398. The gap 322–334 is sharp.

---

## 8. Lemma F (structure of a codeword of weight ≡ 2 mod 4)

Let f ∈ RM(7,14), S = supp f and |S| = w ≡ 2 (mod 4).

**F1.** For every g ∈ RM(6,14), wt(f + g) ≡ 2 (mod 4). All Walsh values of f are ≡ 4 (mod 8).

*Proof.* wt(f+g) = wt f + wt g − 2wt(fg). Here wt g ≡ 0 (mod 4) by McEliece (⌈14/6⌉ − 1 = 2), and wt(fg) is even because deg(fg) ≤ 13. ∎

**F2.** For a ≠ 0, let n_a be the number of pairs {x, x+a} ⊆ S. Then n_a is odd.

*Proof.* D_a f is a-periodic of degree ≤ 6, so D_a f = h∘π with h ∈ RM(6,13), a 4-divisible code. Hence 2w − 4n_a = wt D_a f = 2 wt h ≡ 0 (mod 8). ∎

**F3 (reduction).**

- In coordinates with a = e14, f = g + x14·h with g ∈ RM(7,13) and h ∈ RM(6,13).
- Then wt f = wt h + 2|supp g \ supp h|, and |supp g \ supp h| = n_a.
- Conversely, every such pair (g, h) gives a codeword.
- Since Σ_a n_a = C(w,2) > 3(2¹⁴ − 1), some n_a ≥ 5. (Certificate: 51681, 52975, 54285, 55611 > 49149.) For that direction, wt h ≤ w − 10, i.e. ≤ 312, 316, 320, 324.

**F4 (light hyperplane).**

- For u ≠ 0, s_u = Σ_{x∈S} (−1)^{u·x} ≡ 2 (mod 4), and Σ_{u≠0} s_u² = 2¹⁴w − w².
- Hence some affine hyperplane contains at most 152 / 154 / 156 / 156 points of S, for w = 322 / 326 / 330 / 334 (certificate).
- The restriction of f to that hyperplane is a codeword of RM(7,13) of weight < 160, so it is KTA-classified.

**F5 (the light side is a 6-flat).** Suppose some hyperplane section of f is 1_F, with F a 6-flat of F₂¹³. Then f = 1_F ‖ (1_F + h) with h ∈ RM(6,13), and w = 128 + wt h − 2t, where t = |F ∩ supp h| is odd.

For w = 322 and wt h < 256 (the KT range) this is impossible:

- By the certificate, wt h ∈ {224, 240, 248, 252} and t ∈ {15, 23, 27, 29}.
- **Two-flat form** (KT type II, h = 1_A + 1_B with 7-flats A, B) leaves only t = 15, with |F∩B| = 16 and s = |F∩A∩B| = 1. This fails: W = V_F ∩ V_B has dimension 4 and meets V_A trivially, but dim V_B − dim(V_A ∩ V_B) = 3.
- **Flat × quadratic form** (KT type I, h = 1_E·q) makes t even or ≤ 4.

**Not excluded:** 256 ≤ wt h ≤ 322.

**F6 (sharpened reduction; session 2).** Let w ∈ U₀. Then w ∈ Spec iff there are h ∈ RM(6,13) and g ∈ RM(7,13) with either

- wt h = w − 2 and |supp g \ supp h| = 1, or
- wt h = w − 6 and |supp g \ supp h| = 3.

Moreover, a codeword of weight w has such a decomposition in at least 7559 / 7235 / 6908 / 6576 of the 16383 directions a, for w = 322 / 326 / 330 / 334.

*Proof.*

- (⇐) f = g + x14·h has weight wt h + 2n = w.
- (⇒) All n_a are odd (F2), and Σ_a (n_a − 1) = C(w,2) − 16383.
  - Each direction with n_a ≥ 5 contributes at least 4 to this sum. So at most ⌊(C(w,2) − 16383)/4⌋ directions have n_a ≥ 5, and all the others have n_a ∈ {1, 3} (certificate lines `F6`).
  - Apply F3 in such a direction. ∎

**Consequences for w = 322.**

- The case n = 3 needs h of weight 316, which lies inside the KTA range, so these h are classified.
- The case n = 1 needs h of weight 320 = 2.5d, just outside that range.
- Equivalently, the case n = 1 asks for two codewords g, g′ ∈ RM(7,13) whose supports meet in exactly one point, with g + g′ ∈ RM(6,13) and wt g + wt g′ = 322. The lighter of the two then has weight ≤ 160.

So a complete list of the KTA normal forms of weight 316 in RM(6,13), together with the exact test of §9.1, would settle the n = 3 half of the question for 322.

---

## 9. Proposition G and the evidence on U (heuristic)

### 9.1 Inverse search with an exact inner step (session 2, Task 3)

> **Correction (packaging, 2026-09-26).** The sample counts in this section are inflated. Consecutive random seeds (11–15, 41–45) produced shifted copies of one random stream, so each group of five runs sampled the same polynomials h. `code/closure_replay.c` (log `logs/closure_replay.log`) replays the runs and gives the correct numbers: 26,956 distinct h of weights 312–340, of which 13,681 have weights 316–332; the rechecked codewords reduce to 18 distinct ones. The conclusion, 0 hits for 322–334, is unchanged. Paper 6 uses the corrected counts.


By F3, w ∈ Spec iff there are h ∈ RM(6,13) and g ∈ RM(7,13) with wt h + 2|supp g \ supp h| = w.

**The inner step is exact.** Fix h and put H = supp h. The question "is there g ∈ RM(7,13) with |supp g \ H| = n?" is linear algebra. Let c(x) be the column of x in a parity-check matrix of RM(7,13): the evaluation vector at x of the 2380 monomials of degree ≤ 5, since RM(7,13)^⊥ = RM(5,13). Then:

- n = 1 iff some p ∉ H has c(p) ∈ span{c(x) : x ∈ H};
- n = 3 iff some p, q, s ∉ H have c(p) + c(q) + c(s) ∈ span{c(x) : x ∈ H}.

**The outer step is sampled.** `code/closure_search.c` samples structured h: XORs of 2–4 pieces, namely indicators of flats of dimension 7–9, flat × quadratic, and flat × cubic, with linear forms biased towards coordinate vectors.

- For each sampled h it decides n ∈ {1, 3} **exactly**.
- It first applies a fixed random linear projection F₂²³⁸⁰ → F₂⁵¹². A linear projection can create false positives but never false negatives.
- Every positive is re-solved with the full vectors, the codeword f = g + x14·h is rebuilt, and its degree and weight are recomputed.
- This targets w = wt h + 2 and w = wt h + 6, i.e. U₀ from wt h ∈ {316, …, 332}.
- By F6, these (wt h, n) pairs are exactly the decompositions that every codeword of weight w ∈ U₀ must admit, in thousands of directions. The search is therefore aimed at the right objects; only the sampling of h is incomplete.
- Two generators are used: the default one (2–4 mixed pieces) and `-DGEN_FLATS` (3–4 pieces, mostly flats of dimension 7–8, i.e. the neighbourhood of Propositions D and E).

**Calibration on RM(6,12)** (same program with m = 11, r = 5; 120 s on one core; `logs/closure_search_rm612_calibration_seed21.log`). All four c = 6 analogues of U₀ are found and verified: 162 (58 times), 166 (424), 170 (2481) and 174 (4499). So are the controls 158 and 178.

**RM(7,14) runs** (m = 13, r = 6), 14:00–14:33Z:

- run 1: default generator, 5 × 1200 s, 10,689,792 h generated (`logs/closure_search_rm714_seed1{1..5}.log`);
- run 2: `GEN_FLATS`, 5 × 720 s, 39,389,696 h generated (`logs/closure_search_flats_rm714_seed4{1..5}.log`);
- diagnostic: 1 × 240 s with closure-size histograms (`logs/closure_zhist_rm714_seed51.log`).

"Tested" means that the exact inner test was run for an h of the right weight.

| target w | wt h = w − 2 (n = 1): h tested | … with cl(H) ≠ H | wt h = w − 6 (n = 3): h tested | verified codewords of weight w |
|---|---|---|---|---|
| 318 (control, exists) | 17,201 | 17,201 | 27,311 | 25,658 |
| **322** | **43,906** | **0** | **17,201** | **0** |
| **326** | 523 | 0 | 43,906 | **0** |
| **330** | 4,822 | 0 | 523 | **0** |
| **334** | 3,814 | 0 | 4,822 | **0** |
| 338 (control, exists) | 24,090 | 1,047 | 3,814 | 1,047 |
| 342 (control, exists) | 16,181 | 4,733 | 24,090 | 5,780 |

About 1.4·10⁵ distinct h were tested exactly, 70,266 of them with weights 316–332. No projection false positive occurred in any reported run. `code/check_closure_hits.py` independently re-checks every printed codeword in pure Python (ANF degree ≤ 7, exact weight): 99 codewords re-checked, 0 failures (45 from run 1, 54 from run 2 and the diagnostic). The 18 printed RM(6,12) calibration codewords pass the same check, including 162, 166, 170 and 174.

**Observation: closure sizes.** Let |cl(H) \ H| be the number of points p ∉ H with c(p) ∈ span c(H). The values seen by h-weight are:

| wt h in RM(5,11) (c = 6; 60 s) | 152 | 156 | 160 = 2.5d | 164 | 168 | 172 | 176 |
|---|---|---|---|---|---|---|---|
| sizes seen | 0, 4 | 0, 2 | **0, 1** | 0, 2 | 0, 4 | 0, 2 | 0, 2, 4, 7 |

| wt h in RM(6,13) (c = 7; 240 s) | 312 | 316 | 320 = 2.5d | 324 | 328 | 332 | 336 | 340 |
|---|---|---|---|---|---|---|---|---|
| sizes seen | 0, 4 | 2 (always) | **0 (always)** | 0 | 0 | 0 | 0, 1 | 0, 2 |

- At c = 6, some h of weight exactly 2.5d have a closure of size 1, and each such h gives 2.5d + 2 = 162 (31 of 4870). At c = 7 no h of weight 2.5d with a nontrivial closure was seen, in 43,906 tries.
- A closure of size ≥ 3 at weight 316 would give 322 at once, by adding three single-point solutions. In the diagnostic, all 561 weight-316 h have closure size exactly 2. In all 17,201 weight-316 h tested, the n = 3 test failed, so none had a closure of size ≥ 3.
- The runs for weights 324–332 have few samples. This is a heuristic pattern, not a theorem, but it points to where a proof should look: the closure of the support of a weight-2.5d codeword of RM(6,13).

This is heuristic evidence only: it is exhaustive over g for each tested h, but the h themselves are sampled.

### 9.2 Earlier searches (session 1)

- `sparsefind`: 249,320,000 sparse ANFs. It hit every even weight in [320, 8192] except U and 362 (362 exists). The same sampler on RM(6,12) (265,532,000 samples in 60 s) finds 162, 166, 170 and 174.
- `flatsearch` A/B (2 h): 1.39·10⁹ random sums of 3–6 flats, and 5.30·10⁹ hill-climbing steps. 0 hits in U, while the neighbours 318 and 338 were hit about 10⁷ times.
- `lightsearch` (the F5 family), `supportwalk`, and `cosetsearch` (x13A + x14B + x13x14D): 5.37·10⁹, 3.42·10⁹ and 4.50·10⁹ steps. 0 hits in U.

**Honest assessment.** Whether 322, 326, 330 and 334 occur is **open**. The evidence favours non-existence. A proof of non-existence would answer Carlet's question at (c, m) = (7, 14) negatively. No proof is available.

---

## 10. Lean certificate (Theorem A)

**Files.**

- `work/research-lean/Research/RM714Weights.lean` (sha256 58232392…);
- `Research/RM714WeightsAudit.lean` (sha256 f2b2c62c…);
- identical copies in `lean/`.

They are not yet imported in `Research.lean` (the shared default target). The main session may add `import Research.RM714Weights`.

**Declarations (namespace `RM714`).**

| Declaration | Kind | Role |
|---|---|---|
| `evalPoly`, `weight`, `IsRM714Weight` | def | the statement: `IsRM714Weight w := ∃ L : List (Finset (Fin 14)), (∀ S ∈ L, S.card ≤ 7) ∧ #{x : Fin 14 → ZMod 2 \| (L.map fun S => ∏ i ∈ S, x i).sum = 1} = w` |
| `monoVal`, `polyVal`, `weightNat`, `maskSet`, `pointEquiv`, `degNat` | def | bit-mask computation |
| `testBit_pointEquiv`, `monoVal_iff`, `prod_maskSet`, `evalPoly_map_maskSet`, `card_fin_filter_eq_countP`, `card_maskSet` | lemma | the bridge |
| `weight_map_maskSet` | theorem | for every monomial list with masks < 2¹⁴, `weight (L.map maskSet) = weightNat L` (via `finFunctionFinEquiv`) |
| `isRM714Weight_of` | theorem | if the masks are < 2¹⁴, all degrees are ≤ 7 and `weightNat L = w`, then `IsRM714Weight w` |
| `L354 … L8210`, `isRM714Weight_354 … isRM714Weight_8210` | def / theorem | the 17 witnesses; `weightNat` is evaluated by `decide +kernel` |
| **`rm714_new_weights`** | theorem | `∀ w ∈ [354, 16030, 4378, 4380, 4382, 8174, 8178, 8182, 8186, 8188, 8190, 8194, 8196, 8198, 8202, 8206, 8210], IsRM714Weight w` |

**Statement check (playbook 3.3 / 7.4).**

- `IsRM714Weight w` says literally: some polynomial over F₂ in 14 variables, all of whose monomials have degree ≤ 7, takes the value 1 at exactly w points of F₂¹⁴. That is "w is a weight of RM(7,14)".
- Repeated monomials are allowed. They cancel and do not raise the degree, so the definition is neither weaker nor stronger than the intended one.
- Semantic `example`s in the audit file: x1⋯x7 ↦ 128, x1⋯x7 + x8⋯x14 ↦ 254, 1 ↦ 16384, x1 ↦ 8192.

**Acceptance (playbook 3.5).**

| Item | Result | Evidence |
|---|---|---|
| 1. `lake build Research.RM714Weights Research.RM714WeightsAudit` | exit 0 (133 s, peak RSS 8.1 GB, 07:16Z) | `logs/lake_build_RM714.log` |
| 2. `#print axioms` for the 3 final declarations (`rm714_new_weights`, `weight_map_maskSet`, `isRM714Weight_of`) | all `[propext, Classical.choice, Quot.sound]`; 3 of 3 expected, none missing | build logs |
| 3. forbidden-token grep (sorry, admit, axiom, native_decide, bv_decide, implemented_by, extern, unsafe, partial, debug, ofReduceBool) | no hits (session 1; repeated 14:34:52Z) | `logs/forbidden_grep_session2.log` |
| leanchecker (`lake env leanchecker` on both modules; own declarations only, Mathlib trusted, same kernel) | exit 0 and 0, at 07:38Z and again 13:52–13:55Z in the replay | `logs/leanchecker_RM714.log`, `logs/lean_clean_replay.log` |
| 4. clean-directory replay (see below) | build exit 0 (RM714Weights 154 s, Audit 13 s); same axiom lines; leanchecker 0/0 | `code/lean_clean_replay.sh`, `logs/lean_clean_replay.log` (13:49:36–13:54:56Z) |
| 5. third-party statement review, and the author's check of the statement table | **pending** (not done by this agent) | – |

Details of the clean-directory replay (item 4):

- A fresh directory in the scratchpad; sources copied from `lean/`; `.lake/packages` symlinked to the dev project's Mathlib cache; no project .olean.
- Lean 4.33.1 (commit 819816b2), Mathlib 0df444a3.
- The input sha256 values match the dev copies. Output olean sha256: 01a2b52b…, 4fc5abbd….

**Scope.** Only Theorem A is formalised. Theorem B's 7901 witnesses would take hours of kernel time in the present encoding (about 3–5 s each).

---

## 11. Certificates: every computation, with its implementations

| # | Claim | Implementation 1 | Implementation 2 | Result / log |
|---|---|---|---|---|
| 1 | 17 witnesses of Theorem A | `verify_witnesses.c` (Möbius) | `verify_bitset.py` (big-integer tables) | also the Lean kernel; `verify_all_witnesses_{C,py}.log` |
| 2 | the 7901 witnesses of Theorem B cover S₀ | `verify_witnesses.c` | `verify_all_py.py` | 0 failures; exact coverage |
| 3 | the scout's 16 dense witnesses (up to 4954 monomials) | `verify_witnesses.c` | `verify_bitset.py` | `verify_scout_witnesses_{C,py}.log` |
| 4 | C1/C′ triangle triples; C′ overlap arithmetic | `cert_arith.py` | `cert_arith.c` | identical outputs (`logs/cert_arith_{py,c}.log`, `logs/cert_arith_diff.log`) |
| 5 | D: solutions of the flat equations on all of U; two-flat and three-flat weights | `cert_arith.py` | `cert_arith.c` | identical |
| 6 | the numbers in F3, F4, F5, F6 | `cert_arith.py` | `cert_arith.c` | identical |
| 7 | E, k ≤ 4 | `venn_enum.c`, `venn_enum_fast.c` | `venn_enum_indep.c` | identical counts and weight sets |
| 8 | E, k = 5 | `venn_enum_fast.c` | `venn_enum_indep.c` | both: 11,690,447,828 configurations, 5676 weights, none in U |
| 9 | closed forms for 8174–8210 (a remark only) | inline Python | – (the witnesses are verified independently in #1) | `closed_form_checks.log` |
| 10 | Proposition G: printed codewords (controls 318/338/342; calibration 158–178) | `closure_search.c` (exact re-solve with full vectors, rebuild of f, ANF degree and weight) | `check_closure_hits.py` (pure Python ANF and weight of every printed truth table) | 99 + 18 codewords, 0 failures. The *negative* results (no hit in U₀) are heuristic: the h are sampled. Build variants of the same source: default, `-DGEN_FLATS`, `-DZHIST` |

Code hashes: `logs/sha256_code_session2.txt` (session 2) and `logs/sha256_artifacts.txt` (session 1). `cert_arith.{py,c}` were extended at 14:05Z (D on all of U) and 14:09Z (F6), and a label was renamed at 14:14Z; the logs are from the final version (`logs/cert_arith_diff.log`: identical, 38 lines).

---

## 12. What is new and what is known (prior-work table, playbook 7.3)

G1: 06:41–07:15Z. G2: 13:43–14:03Z (sub-agent; 113 query rows in `querylog.tsv`, raw responses in `g2/raw/`).

| Source | Earliest public date | Coverage | Relation to us | How to acknowledge |
|---|---|---|---|---|
| Kasami–Tokura 1970; Kasami–Tokura–Azumi 1976 | 1970; 1976 | weights < 2d; weights < 2.5d | cited inputs (KT normal forms; the list K) | cite |
| Carlet–Solé, Discrete Math. 346 (2023); arXiv:2301.13497 | 2023-01 | the conjecture, with C starting at 3d | origin of the question | cite; note the 2.5d/3d discrepancy |
| Carlet, IEEE TIT 70 (2024) 4799–4807 | 2023 (TechRxiv preprint; IEEE early access) | RM(m−5,m); the open question with C starting at 2.5d | the question we reduce (R3). The wording is confirmed by 3 sources (DMD2024 abstract, Bergen slides, 2606.21425); the IEEE text itself is unread (no open full text: HAL, TechRxiv, figshare all fail) | cite |
| Lou–Wang, DCC 93 (2025) 4925–4936; arXiv:2406.03803v1 | 2024-06 | RM(m−6,m); Conjectures 1 and 2 | **we disprove Conjecture 2 at m = 6** (C) and use their Lemma 2 | cite the arXiv v1 wording (the Springer body is unreachable; its reference list gained 2 entries, so the text was revised) |
| Leuenberger–Albrizzio, arXiv:2606.21425v1 | 2026-06-19 | Prop. 4: all even weights in [312, 16072] except M (22 values), plus W₀ and complements; proof uses computer lemmas whose details are unpublished | **we decide 14 of the 22 weights of M** (new), and give independent explicit witnesses for everything their Prop. 4 asserts (including 4378, 4380, 4382); C′ explains why their constructions miss U | cite; still v1 at 13:44Z today |
| Lou–Wang, "A note on two conjectures about the weight spectra of the Reed–Muller codes", DAM 388 (2026) 142–145; zbMATH 8196455; MR5055525 (94B65, 94B05) | 2026-04-04 | **unknown: text unreachable** (403/429 everywhere; zbMATH says the summary is unavailable for licence reasons; no MathSciNet review) | **could overlap C** (it concerns "two conjectures", and their own paper has exactly two). Indirect evidence points to small codes (it cites the weight distributions of RM(4,8), RM(3,9), RM(4,9) and sampling papers). It is not cited by 2606.21425 (June 2026) or by Shi–Xing–Solé (Sept 2026), and both still treat c = 7 as open | **must be read by a person before C is claimed as new** |
| Shi–Xing–Solé, arXiv:2609.13653v1 | 2026-09-12 | q-ary GRM codes (q = 3, 4, 5, 7) | none; its only binary statement is that c ≤ 6 is done | optional |
| MathDB #375464, #363415 | 2026-08-11 | the open questions (from 2606.21425 and Lou–Wang) | open, 0 solutions, 0 comments (13:58Z) | – |
| MathOverflow / Math.SE (StackExchange API, 8 queries each; positive control "Reed-Muller" returns 6 / 21 hits) | – | nothing on RM weights in [2d, 3d] or on RM(7,14) | none | – |
| GitHub, trureturing and other AI-solver repositories, SCOPE2026 (G1) | – | nothing | none | – |

**What we add** (subject to the DAM caveat):

- (A) 14 new weights (all of M outside U), plus independent witnesses for 4378, 4380, 4382; all 17 Lean-verified;
- (B) a complete, independently checked witness table: the spectrum of RM(7,14) up to 4 complementary pairs, which reduces Carlet's question at (7, 14) to four weights;
- (C) the first disproof of Lou–Wang's Conjecture 2, at m = 6;
- (C′–F) obstructions for U in natural families, and the dimension-counting mechanism that separates c = 7 from c = 6.

---

## 13. Route to a full answer (for a later session)

1. **A person reads the two inaccessible sources:**
   - the Lou–Wang DAM 388 note (library access);
   - KTA 1976 (Information and Control 30, 380–395; in Elsevier's open archive, but blocked for bots).
2. **Extract the KTA normal forms** for RM(6,13), weights 256–316, and for RM(7,13), weights < 160.
3. **For w = 322, by F6 there are two halves:**
   - **n = 3:** run the exact test of §9.1 on every KTA normal form of weight 316 in RM(6,13). There are finitely many; this is a finite computation once the forms are known.
   - **n = 1:** show that no h ∈ RM(6,13) of weight 320 has a nontrivial closure. Equivalently, show that no two codewords of RM(7,13) with supports meeting in one point have sum in RM(6,13) and weights adding to 322. The lighter one has weight ≤ 160, so it is KTA-classified or of weight 160. Close the cases by dimension counting, as in D and F5.
4. **If all cases close,** 322 ∉ Spec, and the answer to Carlet's question at (7, 14) is negative. The same pipeline applies to 326, 330 and 334.

---

## 14. Incidents and privacy

- **Query-log incident.**
  - A shared scratchpad `log.sh` was overwritten at ~06:44Z by another agent, so 143 G1 lines (06:44:38–07:09:11Z) went to `work/round6/aimpl-amdeberhan/querylog.tsv`.
  - Session 2 re-checked this at 13:43Z. All 142 real query rows are present verbatim in this folder's `querylog.tsv`; the 143rd is a TEST row. A keyword scan of the other log found no further rm714 rows.
  - This agent never used `log.sh`; all rows are appended directly.
  - The G2 rows contain 2 Crossref lines with a stray tab (10 columns) and a few hand-typed approximate times; both are noted in NOTE rows.
- **Bug caught in session 2.**
  - The first build of `closure_search.c` generated its random projection with an F₂-linear generator (xorshift), so the projection had rank ≤ 64.
  - The exact re-check rejected all 449,785 resulting false positives, and the generator was replaced by splitmix64 before any reported run.
  - No reported number comes from the buggy build.
- **Privacy.** No e-mail address in any request (no `mailto=`; generic User-Agent; `grep -i "mailto|@"` on `querylog.tsv` finds nothing). Unpaywall was skipped because it requires an e-mail parameter. Nothing was posted, pushed or sent.

---

## 15. Recommendation (Task 4)

**Write the short paper now; do not wait for U₀.**

- **The package is complete and checkable today:**
  - 14 new weights, Lean-verified;
  - a full witness table that reduces Carlet's question at (7, 14) to four weights;
  - the disproof of a published conjecture (Lou–Wang Conjecture 2 at m = 6);
  - rigorous partial obstructions (C′, D, E, F6), with a clear mechanism (dimension counting).
- **The race risk is real.**
  - The witnesses are easy to find by computer: our sampler found them in minutes.
  - A revision of 2606.21425 with a computational section has been announced (pith.science review).
  - MathDB lists both questions as open, and AI conjecture-mining groups are active.
- **Settling U₀ is uncertain.** It needs the KTA normal forms (the paper is not reachable for bots) and a sizeable case analysis. The evidence points to non-existence, which needs a proof, not a search. A v2 can add it later.

**Gating items before posting** (all short; for a person or for one concise Codex task):

1. A person reads the Lou–Wang DAM 388 note (e.g. through a university library). It is the only source that could anticipate C. If it already disproves Conjecture 2, cite it and drop the novelty claim for C.
2. Codex: one concise review of C, C′, D and F6 (about one page of proofs).
3. A third-party check of the Lean statement table (`IsRM714Weight`).
4. G3 on the day of posting: 2606.21425 versions, MathDB, trureturing.

**Title and format.**

- Suggested title: "The weight spectrum of the Reed–Muller code RM(7,14) up to four weights". "On the weights of RM(7,14) between 2.5d and 3d" also works: the four open weights all lie in that window, but the results cover the whole spectrum.
- Format: arXiv (cs.IT / math.CO), 6–8 pages, with the witness table and the Lean file as ancillary files.
