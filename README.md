# Research papers with Lean 4 proofs: graph energy, OEIS congruences, almost independent sets, triameter, Brauer monoids and Reed–Muller weights

This repository contains six papers, their Lean 4 formalizations and
computational certificates. It is archived on Zenodo: all versions
[10.5281/zenodo.22970254](https://doi.org/10.5281/zenodo.22970254); version 1.0.0
[10.5281/zenodo.22970255](https://doi.org/10.5281/zenodo.22970255); version 1.1.0
[10.5281/zenodo.22970816](https://doi.org/10.5281/zenodo.22970816); version 1.2.0
[10.5281/zenodo.22972115](https://doi.org/10.5281/zenodo.22972115); version 1.2.1
[10.5281/zenodo.22979318](https://doi.org/10.5281/zenodo.22979318); version 1.3.0
[10.5281/zenodo.22979323](https://doi.org/10.5281/zenodo.22979323); version 1.4.0
[10.5281/zenodo.22981669](https://doi.org/10.5281/zenodo.22981669).

## Index

| | What | Status | Main Lean declarations | Where |
| --- | --- | --- | --- | --- |
| Paper 1 (version 1.5) | Maximal energy of integral circulant graphs of orders `p^(2r)·3^(2s+1)`, `pq^m` and `p²q^b`; for exponents of equal parity, every order `p^a q^b` with `min(a,b) ≤ 8` | new theorems; Theorem 5 (for `3 ≤ min(a,b) ≤ 8`) and Proposition 15 are computer-assisted | `ICGGeneral.jiang_yang_q3`, `ICGGeneral.jiang_yang_thmA`, `ICGEqualParity.corollaryA`, `ICGEqualParityB.theoremB` | [`papers/icg-q3-general`](papers/icg-q3-general/note.pdf) |
| Paper 2 | Hanna's OEIS congruence conjectures: eleven proved, three more resolved | proofs; several follow quickly from classical results (stated in the corrected version 1.2.1) | `Oeis389472Mod3.*`, `HannaA*.*` | [`papers/oeis-hanna`](papers/oeis-hanna/note.pdf) |
| Paper 3 | A negative answer to a question of Carenini on almost independent sets in regular graphs | new theorems (counterexamples and an asymptotic result) | `Carenini.not_careniniQuestion_six`, `Carenini.not_careniniQuestion_two_d` | [`papers/carenini-almost-independent`](papers/carenini-almost-independent/note.pdf) |
| Paper 4 | Answers to three problems of Hak, Kozerenko and Oliynyk on the triameter of graphs | Problems 1 and 3 answered (new); Problem 2 was first answered on MathOverflow, and we add its smallest counterexample | `HKOTriameter.not_problem1Claim`, `HKOTriameter.not_problem2Claim`, `HKOTriameter.problem3ClaimFP` | [`papers/hko-triameter`](papers/hko-triameter/note.pdf) |
| Paper 5 | Complete mappings of the Brauer and partial Brauer monoids | Problem 15.11 of arXiv:2608.25092 settled in its existence reading; Lean covers only two constructions | `BrauerCMCore.lemmaB`, `BrauerCMCore.lemmaC` | [`papers/brauer-complete-mappings`](papers/brauer-complete-mappings/note.pdf) |
| Paper 6 | The weight spectrum of the Reed–Muller code RM(7,14) up to four weights | 14 new weights; spectrum determined except for four weights and their complements; Conjecture 2 of Lou and Wang fails for m = 6 (with a caveat, see below) | `RM714.rm714_new_weights` (all 17 weights of Theorem A) | [`papers/rm714-weights`](papers/rm714-weights/note.pdf) |
| Also | A246056 and A376230: Lean proofs of results that follow from published theorems | formalizations of known results | `HannaA246056.*`, `HannaA376230.*` | see below |
| Also | Case q = 3 of Roldán's Conjecture 1.3 (order `27p²`) | formalization of a known result | `ICGBridge.roldan_q3` and related | see below |

**Paper 1: [`papers/icg-q3-general`](papers/icg-q3-general/note.pdf) (version 1.5).**
*The maximal energy of integral circulant graphs of orders p^(2r)·3^(2s+1), pq^m and p²q^b.*

- Jiang and Yang (arXiv:2608.29523, Theorem A) determined the maximal energy
  of integral circulant graphs of order `p^(2r) q^(2s+1)` for distinct odd
  primes with `q ≥ 5`. They noted that `q = 3` is not covered by their method.
- **Theorem 2.** We prove the remaining case `q = 3`: for every prime `p ≥ 5`
  and all `r ≥ 1`, `s ≥ 0`, the checkerboard set `{p^i 3^j : i + j even}` is
  the unique energy maximiser, and the maximal energy is given by their
  formula.
- The key step is a sign-matrix inequality for weighted Ramanujan transforms,
  proved by a path identity and an explicit potential. It also gives a proof
  of Jiang–Yang's theorem without semidefinite certificates.
- **Theorem 3 (exponents of equal parity, one exponent equal to 1).** For
  distinct odd primes `p, q` and odd `m`, the maximal energy for order
  `n = pq^m` is `½[n + (3p−4)d_m(q)] − (p−2)δ_m(q)`, attained exactly by
  `{p^i q^j : i + j odd}` and by `{p^i q^j : i + j even} \ {n}`; the same
  holds for `p^m q`. Together with Theorem 2 and Jiang–Yang, this settles
  every order `pq^m`. The case `n = pq` follows from earlier formulas of
  Ilić and Ilić–Bašić.
- **Theorem 4 (new in version 1.4; one exponent equal to 2).** For distinct
  odd primes `p, q` and even `b ≥ 2`, the maximal energy for order
  `n = p²q^b` is `½[n + (5p² − 8p + 4) d_b(q)] − (p² − 2p + 2) δ_b(q)`,
  attained exactly by `{p^i q^j : i + j odd}` and by
  `{p^i q^j : i + j even} \ {n}`; the same holds for `p^b q²` with the roles
  of the primes exchanged. The proof gives a sign-matrix inequality for the
  exponent 2 (Theorem 25).
- **Theorem 5 (new in version 1.4 for exponents 3 and 4, extended in version
  1.5 to exponents up to 8; computer-assisted).** For distinct odd primes
  `p, q` and `a, b ≥ 1` with `a + b` even and `min(a, b) ≤ 8`, the maximal
  energy for order `n = p^a q^b` is `½[n + d_a(p) d_b(q)] − δ_a(p) δ_b(q)`,
  attained exactly by the same two sets. For `min(a, b) ≤ 2` this is
  Theorem 3 or 4. For `3 ≤ min(a, b) ≤ 8` the method of Theorem 4 reduces the
  claim to a finite list of inequalities between explicit rational functions
  of `p` and `q`, which were verified by exact computation with independent
  programs: for exponents 3 and 4 by two programs, one of them written by a
  referee agent; for exponents 5 to 8 by three programs, two of them written
  by referee agents. This case is not formalized.
- So the equal-parity conjecture (Conjecture 14) holds whenever
  `min(a, b) ≤ 8`, and with Theorems 1 and 2 the maximal energy and all
  maximisers are known for every order `p^a q^b` with `min(a, b) ≤ 8`; for
  `min(a, b) ≤ 2` the proof does not depend on a computer. The conjecture
  remains open when `min(a, b) ≥ 9`; the smallest open shapes are (9, 9),
  (9, 11), (11, 9) and (10, 10).
- **Proposition 15 (Proposition 13 in version 1.2; computer-assisted, not
  formalized).** Exact certificates verify the equal-parity conjecture for
  every shape with `(a+1)(b+1) ≤ 27`. These shapes are now covered by
  Theorem 5, and the proposition is an independent check of them.
- **Lean:** `ICGGeneral.jiang_yang_q3` and `ICGEqualParity.corollaryA`, both
  starting from the adjacency matrix of the graph and its eigenvalues, and
  `ICGGeneral.jiang_yang_thmA`, which covers all pairs of distinct odd primes.
  Theorem 4 is `ICGEqualParityB.theoremB` (with `theoremB_swap` for
  `p^b q²` and `corollaryB`), from the same starting point, and Theorem 25 is
  `ICGEqualParityB.thmB'`. The closed forms of `d_k` and `δ_k` are proved in
  the paper but not formalized; neither are Theorem 5 for
  `3 ≤ min(a, b) ≤ 8` and Proposition 15.

**Paper 2: [`papers/oeis-hanna`](papers/oeis-hanna/note.pdf).** *Proofs of
eleven congruence conjectures of Hanna from the OEIS, and the resolution of
three more.*

> **Correction (version 1.2.1).** Version 1 of Paper 2 did not cite that
> several of these conjectures are quick consequences of classical results
> or of identities stated in the OEIS entries; the revised paper now states
> this, in the abstract, in a new paragraph
> "Relation to classical results" and in remarks at the relevant theorems.
> In short:
> - **A240998, A295762, A301933, A338633, A338634:** modulo 2 they reduce to
>   the Catalan series, so the patterns follow from the parity of the
>   Catalan numbers (Deutsch–Sagan 2006; Theorem 2.1 in arXiv:math/0407326v1).
> - **A273958:** modulo 2, `xA ≡ C(C(x²))`.
> - **A184894:** the classical correspondence for linearised polynomials
>   over F₃ (Ore 1933; Lidl–Niederreiter).
> - **A120566, A274479, A388734:** identities stated in the entries
>   themselves give short proofs.
> - **A107099, A361047:** the reduced series are classical series (for
>   A361047 that of the ternary numbers A001764, whose residues modulo 3 are
>   recorded in A113047), identified by a routine uniqueness argument.
> - **No classical connection found:** A389472 (mod 3) and A377100.
>
> The theorems, proofs and Lean formalisation are unchanged.

**Paper 3: [`papers/carenini-almost-independent`](papers/carenini-almost-independent/note.pdf).**
*A negative answer to a question of Carenini on almost independent sets in
regular graphs.*

- For a `d`-regular graph `G` on `n` vertices, `i_γ(G)` counts the vertex
  sets spanning at most `γdn` edges. Carenini (arXiv:2609.28527, Question 1.3)
  asked whether, when `2d | n`, the disjoint union of `n/(2d)` copies of
  `K_{d,d}` maximises `i_γ` for every `γ ≥ 0`; for `γ = 0` this is the
  Kahn–Zhao theorem.
- **The answer is no.** The smallest counterexample is `(n,d,γ) = (6,3,1/18)`:
  the triangular prism has 28 vertex sets spanning at most one edge, `K_{3,3}`
  has 24.
- **Theorem A.** For every `(n,d)` with `n > 0` and `2d | n`, except the trivial cases
  `d = 1` and `(4,2)`, some `γ < 1/2` gives a counterexample.
- **Theorems B and B′.** A switched `K_{d,d}` wins on `2d` vertices for every
  `d ≥ 3`; a connected bipartite graph wins on `4d` vertices for every
  `d ≥ 2`.
- **Theorem D.** For every fixed `γ ∈ (1/8, 1/2)` and `d ≥ 2`, a bipartite
  competitor wins for all large `n`.
- **Proposition C.** At the exponential scale the union of copies of `K_{d,d}`
  is optimal for every `γ` (the upper bound is Carenini's biclique reduction,
  which rests on Sah–Sawhney–Stoner–Zhao).
- Still open: the exact question for fixed `γ ∈ (0, 1/8]` as `n → ∞`, and
  the `(1 + o(1))` form for fixed `d` and `0 < γ < 1/8` (at `γ = 1/8` the
  `(1 + o(1))` form holds, as shown in the paper).
- Lean: the counterexample at `(6,3,1/18)`, the switched family for every
  `d ≥ 3`, and three further instances (`lean/Research/Carenini.lean`).
  Theorems A, B′ (general `d`), D and Proposition C are proved in the paper,
  not in Lean.

**Paper 4: [`papers/hko-triameter`](papers/hko-triameter/note.pdf).**
*Answers to three problems of Hak, Kozerenko and Oliynyk on the triameter of
graphs.*

- The triameter `tr(G)` of a connected graph is the largest value of
  `d(u,v) + d(u,w) + d(v,w)`. Hak, Kozerenko and Oliynyk (Discrete Appl.
  Math. 309 (2022); arXiv:2103.10806, Section 4) asked whether every median
  graph has property (Q3′), that every triametral triple contains a
  peripheral vertex (Problem 1); whether every median graph has property
  (Q4), that every diametral pair extends to a triametral triple (Problem 2);
  and whether every distance-hereditary graph has (Q3′) or (Q4) (Problem 3).
- **Problem 1: no (Theorem A).** In an 8-vertex median graph `G1`, the
  triametral triple `{1, 5, 6}` contains no peripheral vertex. Exhaustive
  enumeration shows that every median graph with at most seven vertices has
  (Q3′), and that `G1` is the only 8-vertex exception up to isomorphism.
- **Problem 2: no, first answered on MathOverflow.** The user
  rgvalenciaalbornoz answered the question on 31 December 2025, in the
  accepted [answer 506536](https://mathoverflow.net/a/506536) to question
  506431, with an 11-vertex median graph in which both (Q4) and (Q4′) fail.
  Our contribution to Problem 2 is only the smallest counterexample
  (Theorem B): an 8-vertex median graph `G2`, unique up to isomorphism, which
  lacks (Q4) and (Q4′) and is also distance-hereditary.
- **Problem 3: yes, in a stronger form (Theorem C).** Every connected
  distance-hereditary graph has property (Q3), that every triametral triple
  contains a diametral pair, or property (Q4). The proof uses the four-point
  condition of Bandelt and Mulder (1986), and Theorem C holds for every
  finite connected graph that satisfies it.
- Still open: does every median graph have (Q3′) or (Q4)?
- Lean: `G1` and `G2` are median graphs with the stated diameters and
  triameters, `G1` lacks (Q3′) and `G2` lacks (Q4) and (Q4′)
  (`HKOTriameter.not_problem1Claim`, `not_problem2Claim`,
  `not_problem2ClaimWeak`), and Theorem C holds for finite connected graphs
  that satisfy the four-point condition (`question3_or_question4`,
  `problem3ClaimFP`). The theorem of Bandelt and Mulder is cited, not
  formalized: the formal statement of Problem 3 assumes the four-point
  condition, and for `G2` only the four-point condition, not
  distance-heredity, is formal. The uniqueness and minimality statements rest
  on the enumerations, not on Lean.

**Paper 5: [`papers/brauer-complete-mappings`](papers/brauer-complete-mappings/note.pdf).**
*Complete mappings of the Brauer and partial Brauer monoids.*

- A complete mapping of a semigroup `S` is a bijection `α : S → S` such that
  `x ↦ x · xα` is also a bijection. Problem 15.11 of Araújo, Bentz, Cameron,
  Hendrey and Kinyon (arXiv:2608.25092) asks for a classification of the
  complete mappings of the Brauer monoid `B_n` and the partial Brauer monoid
  `PB_n`. By their reduction to principal factors and the Hall–Paige
  theorem, the open cases were the principal factors of ranks 2 and 3, and
  the question of which of the monoids have a complete mapping.
- **Theorem 1.1 settles the existence question in all cases.** Every proper
  principal factor of `B_n` has a complete mapping. So does every proper
  principal factor of `PB_n`, except the rank-2 factor of `PB_3` (the Brandt
  semigroup `B(S_2, 3)`), which has none. Hence `B_n` and `PB_n` have a
  complete mapping if and only if `n ∉ {2, 3}`.
- The new case is `B_n` with `n ≡ 2, 3 (mod 4)`, in which the rank-2 or
  rank-3 factor has an odd number of L-classes. For it the paper gives an
  explicit complete mapping, built from a triangle of half-diagrams and a
  perfect matching of the other half-diagrams. The other cases follow
  directly from results of Araújo et al. once the Rees structure of the
  principal factors is written down.
- Scope: "classify" is read as in the second sentence of Problem 15.11,
  that is, deciding existence for every factor and every monoid. The set of
  all complete mappings is not described.
- Lean: only the two explicit constructions on which the proofs rest, for
  Rees 0-matrix semigroups over `Z_2` with identity diagonal and any finite
  index set (`BrauerCMCore.lemmaB` and `BrauerCMCore.lemmaC`, Lemmas 4.3 and
  4.4). The facts about diagrams, the lifting lemma, the cited results of
  Araújo et al. and of East, Mitchell, Ruškuc and Torpey, and Theorem 1.1
  itself are not formalized; they rest on the written proofs, and the
  certificates are additional checks.

**Paper 6: [`papers/rm714-weights`](papers/rm714-weights/note.pdf).**
*The weight spectrum of the Reed–Muller code RM(7,14) up to four weights.*

- Leuenberger and Albrizzio (arXiv:2606.21425) showed that every even
  number from 312 to `2^14 − 312` is a weight of RM(7,14), except possibly
  22 values.
- **Theorem A.** 17 of these values are weights, each given by an explicit
  codeword with at most seven monomials. Fourteen are, to our knowledge,
  new. The other three, 4378, 4380 and 4382, are weights by Proposition 4 of
  arXiv:2606.21425 and are not new.
- **Theorem B.** With explicit codewords for all other weights (7901
  codewords, checked by two independent programs) and the theorem of Kasami,
  Tokura and Azumi on weights below `2.5d`, the weight spectrum of RM(7,14)
  is determined except for 322, 326, 330, 334 and their complements. We cite
  the theorem of Kasami, Tokura and Azumi (1976) for the absence of other
  weights below 320 but could not consult it ourselves. Independently of that
  theorem, Carlet's question on the weight spectra of RM(m − c, m) has, for
  (c, m) = (7, 14), a positive answer if and only if these four numbers are
  weights.
- **Theorem C.** Conjecture 2 of Lou and Wang is false for m = 6: no
  codeword of their Construction 2 has weight 322. Caveat: a note of Lou and
  Wang (Discrete Appl. Math. 388 (2026) 142–145) on two conjectures about
  these weight spectra could not be read, and it may anticipate Theorem C or
  other results of the paper.
- Propositions C′, D and E show that no open weight occurs in several
  natural families of codewords (E by an exhaustive computation with two
  programs), and Proposition F reduces each of 322, 326, 330 and 334 to a
  question about RM(6,13) and RM(7,13). Searches found no codeword of an
  open weight; this is heuristic evidence only.
- Still open: are 322, 326, 330 and 334 weights of RM(7,14)?
- Lean: `RM714.rm714_new_weights` verifies all 17 weights of Theorem A. Its
  name is historical: only 14 of the 17 weights are new. Theorems B and C,
  Propositions C′–F and the searches are not formalized.

**Also formalized (known results): OEIS A246056 and A376230.** Both are
Hanna conjectures listed as open on the OEIS, but their content follows from
published theorems, so we claim no new mathematics here:
- A246056: `a(n) ≡ A001850(n) (mod 3)` (central Delannoy numbers), and the
  conjectured mod-3 pattern is a theorem of E. Deutsch and B. E. Sagan,
  *Congruences for Catalan and Motzkin numbers and related sequences*,
  J. Number Theory 117 (2006) 191–215 (Theorem 5.15, p. 212, in the journal
  version; Theorem 5.8 in arXiv:math/0407326v1). Lean:
  `HannaA246056.hanna_a246056_one`, `hanna_a246056_zero` (proved directly
  from the defining series).
- A376230: the parity comment is false as stated (`a(4) = 8`). Modulo 2 the
  series is the reversion of `x + x² + x³`. M. Gawron and M. Ulas, *On formal
  inverse of the Prouhet–Thue–Morse sequence*, Discrete Math. 339 (2016)
  1459–1470 (arXiv:1601.04840v1, Theorems 2.1 and 3.1), study the series
  `S = X(1+G)` with `S + S² + S³ = X`; so `a(n) mod 2` is the coefficient of
  `x^(n−1)` in `1 + G` for `n ≥ 1`, and their Theorem 3.1 gives the corrected
  pattern (`a(n)` odd iff `⌊n/2⌋ ∈ A000695`); see also OEIS A270803. Lean:
  `HannaA376230.hanna_a376230`, `hanna_a376230_literal_false`.

**Also included:** a complete Lean formalization of the case q = 3 of
Roldán's Conjecture 1.3 (order `27p²`). This is a known result, proved earlier
by others; see below.


### Formalization of a known result: the case q = 3 of Roldán's Conjecture 1.3 (arXiv:2604.09491)

- For every prime `p ≥ 5`, the divisor set `D* = {1, 9, 3p, 27p, p², 9p²}`
  uniquely maximizes the energy of the integral circulant graph `ICG(27p², D)`.
- **This case was proved before us:**
  - S. Park (PDF posted 2026-08-21 at github.com/coshaman/papers) claims the
    whole conjecture;
  - J. A. Schreib (2026-09-05, github.com/jamesschreib/roldan-universality-conjecture)
    gives a written proof of the case q = 3 with the same bound
    `E(D*) − E(D) ≥ 24(p² − 2p + 2)`;
  - an arithmetic certificate was also announced in trureturing issue #8338
    (2026-09-16).
- **What this repository adds:**
  - a complete Lean 4 formalization, from the adjacency matrix of the graph and
    its eigenvalues, with no additional axioms and no `native_decide`;
  - the observation, also formalized, that the bound is attained at
    `D* ∪ {3p²}`, so the second-largest energy is `242p² − 356p + 154`.

### Paper 2 in detail

**Eleven congruence conjectures of P. D. Hanna from the OEIS**, proved and
formally verified. Each Lean theorem holds for every integer power series
satisfying the defining equation, with the normalizations fixed by the
entry's indexing and initial coefficients.

| Entry | Defining equation | Theorem |
| --- | --- | --- |
| A389472 | `A(x² + x³) = x²(1 + A(x))` | `3 ∣ a(3n − 1)` for `n > 1` |
| A240998 | `A(x)² = x + A(x + 2x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 |
| A295762 | `A(x − 2A(x²)) = x + A(x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 (the entry conjectures one direction) |
| A273958 | `xA + x²A² = C²`, with `C = x + C²` | `a(n)` is odd iff `n = 2·4^k − 1` |
| A301933 | `A = x(1 + 4AA′)/(1 + AA′)` | `a(n)` is odd iff `n` is a power of 2 |
| A377100 | `A(x) = A(x³)/A(x²) + A(x)²` | `a(n) ≡ 1 (mod 3)` for `n ≥ 1` |
| A274479 | `A(x)² = A(x²/(1 − 2x − 4x²))` | `a(n) ≡ 1 (mod 3)` for `n ≥ 1` |
| A388734 | `A = 1 + xA² + x²(1 − x)A³` | every `a(n)` is odd |
| A338633 | `1 = A − x/(A − 2³x/(A − 3³x/(A − …)))` | for `n > 0`, `a(n)` is odd iff `n` is a power of 2 |
| A338634 | `1 = A − x/(A − 2⁴x/(A − 3⁴x/(A − …)))` | for `n > 0`, `a(n)` is odd iff `n` is a power of 2 |
| A120566 | `A(x) = A(A(x)) − x·A(A(A(x)))` | every `a(n)`, `n ≥ 1`, is odd |

**Three further OEIS conjectures, resolved:**

| Entry | Conjecture | What is proved |
| --- | --- | --- |
| A184894 | `a(m) ≡ 0 (mod 3)` except at `m = (3^n + 1)/2` | the statement as written (vanishing outside the exceptions) holds, and `a(m) ≡ C(m, j) (mod 3)` when `2m − 1 = 3^j`; the stronger reading "non-zero at every exception" fails at OEIS index 365 = (3⁶ + 1)/2 |
| A107099 | `[x^n]A ≡ 0 (mod 3)` except at `n = 3^k`, where `A(A(x)) = x + 4x³` | the statement as written holds; the stronger reading fails at `x^729` (OEIS index 364), since `3 ∣ [x^729]A` |
| A361047 | stated with an index slip that the entry's own data contradict | the intended statement, in exponent form: `[x^m]A ≡ 1 (mod 3)` if `m = 3^k`, and `≡ 0` otherwise |

## What is verified, and how

| Claim | Lean 4 declarations | Independent computation |
| --- | --- | --- |
| Paper 1: unique maximiser for `p^(2r)·3^(2s+1)`, `p ≥ 5`; value of the maximum, expressed through the norms `d_k(x) = ‖T_k(x) s_k‖₁` (their closed form is proved in the paper but not formalized); the sign-matrix inequality (all real `p ≥ 5`, `q ≥ 3`, all exponents); energy formula for all `p^a q^b`; Jiang–Yang Theorem A for all distinct odd primes | `ICGGeneral.jiang_yang_q3`, `jiang_yang_q3_value`, `energy_DstarPQ`, `thm5_le`, `thm5_eq`, `energy_icgAdj_pq`, `jiang_yang_thmA`, `checkerboard_unique_max_odd` | exhaustive exact searches over all divisor sets (shapes and primes listed in the paper); sign-matrix enumeration for `(a+1)(b+1) ≤ 25`; floating-point spectra of the actual graphs (`certificates/icg-q3-general/`) |
| Paper 1, Theorem 3: maximal energy for `pq^m` and `p^m q`, `m` odd; both maximisers; uniqueness | `ICGEqualParity.corollaryA` | exact arithmetic for every step (`verify_1m.py`); graph spectra by FFT and dense eigenvalues (`certificates/icg-equal-parity/`) |
| Paper 1, Theorem 4: maximal energy for `p²q^b` and `p^b q²`, `b` even; both maximisers; uniqueness; the sign-matrix inequality for the exponent 2 (Theorem 25) | `ICGEqualParityB.theoremB`, `theoremB_swap`, `corollaryB`, `thmB'`; the 325 inequalities of a first proof, not needed for the paper's proof, in `ICGEqualParityBCert1`–`6` | exhaustive searches over all divisor sets of 21 orders `p²q^b`, `b ∈ {2, 4, 6}`, up to `n = 1 058 841`, with exact eigenvalues from Ramanujan sums (`review/rv_graph.py`); exact replays of the steps of the proof (`paper-checks/`); both in `certificates/icg-equal-parity/theorems-b-c/` |
| Paper 1, Theorem 5 for `3 ≤ min(a,b) ≤ 8` | not formalized (computer-assisted) | exact certification of the reduced inequalities: for exponents 3 and 4 with SymPy (`generic_prover.py`) and with separate integer arithmetic (`generic_fast2.py`); for exponents 3 to 8 with `generic_fast2.py` and the independent certifier of a referee agent (`review2/c3_certify.py`); for exponents 5 to 8 also with the certifier of a third referee agent (`review3/rv3_certify.py`); negative controls; complete enumeration and branch-and-bound checks at sample shapes and parameters (`review2/`, `review3/`) |
| Paper 1, Proposition 15 (Proposition 13 in version 1.2): equal-parity conjecture for all shapes with `(a+1)(b+1) ≤ 27` | not formalized (computer-assisted) | polynomial non-negativity certificates in exact integer arithmetic (`cert22.py`, `cert_fast.py`, which share polynomial routines), a SymPy rebuild for five shapes, and a negative control (`certificates/icg-equal-parity/negative-control/`) |
| Roldán q=3 for the genuine graph energy: unique maximizer, gap, value of `E(D*)`, sharpness | `ICGBridge.roldan_q3`, `roldan_q3_gap`, `energy_Dstar`, `roldan_q3_sharp`, `roldan_q3_gap_attained`, plus `*_graph` versions for mathlib's `SimpleGraph.circulantGraph` | three independent programs for the certificate; direct numerical diagonalization of the adjacency matrices for p = 5, 7 (all 2047 sets) |
| Roldán, whole conjecture (two-variable certificate, all real p, q ≥ 3) | not formalized | two independent programs |
| A389472 | `Oeis389472Mod3.integer_conjecture` | 1000 terms vs. the OEIS b-file |
| A240998 | `HannaA240998.hanna_a240998` | exact recomputation vs. the b-file (311 terms) |
| A295762 | `HannaA295762.hanna_a295762` | b-file (1030 terms), modulo 2^64 and two primes; 260 terms exactly |
| A273958 | `HannaA273958.hanna_a273958` | exact recomputation vs. the b-file (520 terms) |
| A301933, A377100, A274479, A388734 | `HannaA301933.hanna_a301933`, `HannaA377100.hanna_a377100`, `HannaA274479.hanna_a274479`, `HannaA388734.hanna_a388734` | exact recomputation of the full b-files (`certificates/oeis-hanna/batch2/`) |
| A338633, A338634, A120566 | `HannaA338633.hanna_a338633`, `HannaA338633.hanna_a338634`, `HannaA120566.hanna_a120566` | b-files substituted into the defining equation modulo two primes, and the first 60 (A338633, A338634) or 150 (A120566) terms recomputed independently (`batch2/`) |
| A246056 (formalization of a known result) | `HannaA246056.hanna_a246056_one`, `hanna_a246056_zero`; data check `a_initial` | 320 terms recomputed from the definition vs. the b-file (301 terms) (`certificates/oeis-hanna/round5/a246056/`) |
| A376230 (formalization of a known result; the comment is refuted) | `HannaA376230.hanna_a376230`, `hanna_a376230_literal_false` | 48 terms computed exactly from the equation; the parity pattern checked on all 1030 b-file terms (`certificates/oeis-hanna/round5/a376230/`) |
| Paper 3: the answer to Carenini's Question 1.3 is no at `(6,3,1/18)`, at `(2d, d, 1/(2d²))` for every `d ≥ 3`, and at `(8,2,1/16)`, `(12,3,1/36)` (connected bipartite competitor), `(12,3,5/18)` | `Carenini.not_careniniQuestion_six`, `not_careniniQuestion_two_d`, `not_careniniQuestion_eight_two`, `not_careniniQuestion_twelve_bip`, `not_careniniQuestion_twelve_top` | exact edge-count distributions by two independent methods; exhaustive check over all `d`-regular graphs on `2d` vertices for `d = 3, 4, 5`; Theorem D's competitor checked exactly for `γ = 1/10` (`certificates/carenini/`) |
| A184894, A107099, A361047 (resolved) | `HannaA184894.zero_part`, `value_at_pow`, `counterexample`; `HannaA107099.hanna_a107099`, `hanna_a107099_counterexample`; `HannaA361047.hanna_a361047_pow`, `hanna_a361047_nonpow` | A184894: exact recomputation vs. the b-file; A107099: b-file substituted into the defining equation modulo two primes; A361047: the same, plus the first 60 terms recomputed independently (`batch2/`) |
| Paper 4: `G1` refutes Problem 1, `G2` refutes Problem 2 and its weak form (Q4′); Theorem C for connected graphs with the four-point condition (that distance-hereditary graphs satisfy it is the cited theorem of Bandelt and Mulder) | `HKOTriameter.not_problem1Claim`, `not_problem1ClaimPair`, `not_problem2Claim`, `not_problem2ClaimWeak`, `question3_or_question4`, `problem3ClaimFP` | two independent exhaustive enumerations of the median graphs with at most 8 vertices (`median_enum.c`, `median8_second_impl.py`) and a check over all 8! bijections (`iso_check.py`); all 270,070 connected distance-hereditary graphs with at most 11 vertices, up to isomorphism (`dh_exhaustive.py`), and random tests (`certificates/hko-triameter/`) |
| Paper 4: `G1` and `G2` are the only counterexamples with at most 8 vertices | not formalized | the enumerations above |
| Paper 5: Theorem 1.1 (every proper principal factor of `B_n` and `PB_n` has a complete mapping, except the rank-2 factor of `PB_3`; `B_n` and `PB_n` have one iff `n ∉ {2, 3}`) | only the two constructions of Lemmas 4.3 and 4.4, over `Z_2` for any finite index set: `BrauerCMCore.lemmaB`, `BrauerCMCore.lemmaC`; the rest rests on the written proofs | certificates for the rank-2 factor of `B_6`, the rank-3 factor of `B_7`, the whole monoids `B_1`, `B_4`, `B_5`, `B_6`, `PB_1`, `PB_4`, `PB_5`, `PB_6`, and second versions of the first two, each built by one implementation and checked by a second that shares no code with it; an exhaustive search showing that the rank-2 factor of `PB_3` has no complete mapping (`certificates/brauer-complete/`) |
| Paper 6: the 17 weights of Theorem A (14 of them new) | `RM714.rm714_new_weights` (the name is historical: it covers all 17) | two programs (`verify_witnesses.c`, `verify_bitset.py`) |
| Paper 6: Theorems B and C, Propositions C′, D, E and F | not formalized | two programs for every computation used in a proof: `verify_witnesses.c` and `verify_all_py.py` for the 7901 codewords of Theorem B; `cert_arith.py` and `cert_arith.c` for Lemma 4.1 and Propositions C′, D and F; `venn_enum_fast.c` and `venn_enum_indep.c` for Proposition E (`certificates/rm714/`) |

Each OEIS theorem is stated for every integer power series satisfying the
defining equation. The energy is `∑ |eigenvalues|`, using
`Matrix.IsHermitian.eigenvalues`.

All final theorems depend only on the axioms `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry`, no custom axiom and no
`native_decide`. For version 1.4.0 the whole project was rebuilt from a clean
directory (`lake build`, exit code 0; `logs/clean-replay-v1.4.0-build.log`),
and the seven audit files were run (`logs/clean-replay-v1.4.0-audit-*.log`).
Every axiom list printed in these logs, 106 in the build log and 381 in the
audit logs, is a subset of these three axioms. The 14 modules new in version
1.4.0 (`ICGEqualParityBCol`, `ICGEqualParityBFD`, `ICGEqualParityBMain`,
`ICGEqualParityBGraph`, `ICGEqualParityBCert1` to `ICGEqualParityBCert6`,
`HKOTriameter`, `HKOTriameterDH`, `BrauerCMCore` and `RM714Weights`) were
replayed through the Lean kernel with `lake env leanchecker <Module>`, and all
passed (`logs/clean-replay-v1.4.0-leanchecker-new-modules.log`). The other
proof and semantic-check modules are unchanged and passed the same check
earlier: `Carenini` in version 1.3.0
(`logs/clean-replay-v1.3.0-leanchecker-carenini.log`), six modules in version
1.2.0 (`logs/clean-replay-v1.2.0-leanchecker-new-modules.log`) and the other 26
in version 1.1.0 (`logs/clean-replay-v1.1.0-leanchecker.log`). The source
manifest `logs/lean-sources-sha256.txt` lists 58 files, and the procedure and
its parameters are recorded in `logs/clean-replay-v1.4.0-receipt.json`.

### Reproduce the Lean checks

Each code block in this and the following sections starts from the repository
root.

Requirements: [elan](https://github.com/leanprover/elan), about 20 GB of free
RAM for `CirculantQ3.lean` (its kernel-checked certificate peaks near 18 GB),
and about 20 minutes (the clean rebuild for version 1.4.0 took 18 minutes).

```sh
cd lean
lake exe cache get                               # prebuilt mathlib, pinned in lake-manifest.json
lake build                                       # builds everything imported by Research.lean; BrauerCMCore (Paper 5) prints its own axiom audit
lake env lean Research/ICGGeneralAudit.lean      # Paper 1: prints the final statements, definitions and axioms
lake env lean Research/ICGEqualParityBAudit.lean # Paper 1, Theorem 4: the same
lake env lean Research/ICGBridgeAudit.lean       # Roldán q = 3: the same
lake env lean Research/CareniniAudit.lean        # Paper 3: the same
lake env lean Research/HKOTriameterAudit.lean    # Paper 4: the same
lake env lean Research/RM714WeightsAudit.lean    # Paper 6: the same
```

Toolchain: Lean 4.33.1, mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`.

### Reproduce the certificates and numerical checks

Requires Python 3 with SymPy and NumPy.

```sh
cd certificates/roldan-q3
python3 circulant_certificate.py      # (i)   integer polynomial arithmetic, all 2048 sets, two variables
python3 independent_q3_certificate.py # (ii)  Möbius formula, gcd enumeration, exact interpolation (q = 3)
python3 bivariate_sympy_check.py      # (iii) SymPy; cross-checks (i), the closed forms and the Lean table
python3 direct_graph_check.py 5 && python3 direct_graph_check.py 7   # diagnostic: eigenvalues of the actual graphs (n = 675, 1323)
cd ../oeis-hanna
python3 verify_389472.py && python3 verify_parity3.py && python3 verify_a295762_mod.py
cd batch2 && for s in verify_*.py; do python3 $s; done
```

`verify_a295762_mod.py` works modulo 2^64 on purpose, so NumPy's overflow
warnings are expected. `batch2/verify_batch2.py` also rechecks A091713 and
A196523. Those two are not claimed here: they were proved earlier by
A. Perez Fontelles (astrafala/Conjectures, 31 August 2026).


### Reproduce the computations of Paper 1

Requires a C compiler and Python 3 with SymPy and NumPy.

```sh
cd certificates/icg-q3-general
cc -O2 -o icg_search icg_search.c              # exhaustive search over all divisor sets
cc -O2 -DSIGNMODE=1 -o icg_sign icg_search.c   # enumeration of sign matrices
python3 run_search.py 4 1 3 5,7,11             # example: n = p^4·3 for p = 5, 7, 11 (compare logs/search_small.log)
```

Equal-parity results (Theorem 3 and Proposition 15):

```sh
cd certificates/icg-equal-parity
python3 verify_1m.py              # every step of Theorem 3 in exact arithmetic
python3 cert22.py 2 2 5 3         # certificate for the shape (2,2), region p >= 5, q >= 3
python3 cert_fast.py 4 4 5 3      # the same for (4,4), vectorised (about 4 minutes)
python3 cert_sympy_check.py 2 2 5 3
```

Theorems 4 and 5 (versions 1.4 and 1.5). `theorems-b-c/README.md` lists the expected
summary line of each run and the negative controls, which must fail.

```sh
cd certificates/icg-equal-parity/theorems-b-c
python3 generic_prover_fast.py 3     # Theorem 5, min(a,b) = 3: 14 196 branches certified with SymPy, 12 processes (the recorded run took 16 minutes)
python3 generic_prover_fast.py 4     # min(a,b) = 4: 70 416 branches (the recorded run took 49 minutes)
python3 generic_fast2.py 3 && python3 generic_fast2.py 4                    # the same lists, with separate integer arithmetic (seconds)
cd review2 && python3 c3_certify.py 3 && python3 c3_certify.py 4 && cd ..   # the referee agent's independent certifier (seconds)
for a in 5 6 7 8; do python3 generic_fast2.py $a; done                   # version 1.5: exponents 5 to 8, integer arithmetic
cd review2 && for a in 5 6 7 8; do python3 c3_certify.py $a; done && cd ..  # the second referee agent's certifier
cd review3 && for a in 5 6 7 8; do python3 rv3_certify.py $a; done && cd ..  # the third referee agent's certifier (seconds for a = 5; longer for a = 8)
python3 paper-checks/check_proof.py  # Theorem 4: exact replay of the proof of Theorem 25 (about 1 minute)
python3 review/rv_graph.py           # Theorem 4: all divisor sets of 21 orders p²q^b, exact energies
```

Paper 3 (requires Python 3 with NumPy, NetworkX and SymPy):

```sh
cd lean && lake build Research.Carenini && cd ..   # the Carenini module alone (a few minutes)
cd certificates/carenini
python3 small_numbers.py         # the counts quoted in the paper
python3 checkB.py                # Theorem B: the count 4d - 8 and the several-copies condition
python3 exhaustive_n2d.py        # all d-regular graphs on 2d vertices, d = 3, 4, 5
python3 check_gamma_tenth.py     # Theorem D's competitor at gamma = 1/10
```

Paper 4 (requires a C compiler, and Python 3 with NetworkX):

```sh
cd certificates/hko-triameter/code
python3 verify_paper_claims.py   # every concrete graph claim of the paper
cc -O2 -o median_enum median_enum.c && ./median_enum 8 1   # all graphs with at most 8 vertices (about 30 seconds; compare ../logs/median_enum_le8.log)
python3 median8_second_impl.py   # the second enumeration of the median graphs with at most 8 vertices
python3 iso_check.py             # the two violators with 8 vertices are G1 and G2 (all 8! bijections)
python3 dh_exhaustive.py 11      # all connected distance-hereditary graphs with at most 11 vertices (about 4 minutes)
```

Paper 5 (requires zsh, and Python 3 with NetworkX):

```sh
cd certificates/brauer-complete/code
python3 verify_cm.py ../certificates/cm_B7_rank3.txt B 7 3   # the second implementation checks one certificate
zsh run_all.sh                   # all checks of Section 8: rebuilds every certificate, checks it, and rewrites ../logs/ (a few minutes)
```

Paper 6 (requires a C compiler and Python 3):

```sh
cd certificates/rm714
cc -O2 -o verify_witnesses code/verify_witnesses.c && ./verify_witnesses < data/rm714_all_witnesses.txt   # the 7901 codewords of Theorem B (Möbius transform)
python3 code/verify_all_py.py    # the same codewords with big-integer truth tables, and their coverage of the spectrum
python3 code/cert_arith.py > arith_py.txt && cc -O2 -o cert_arith code/cert_arith.c && ./cert_arith > arith_c.txt && diff arith_py.txt arith_c.txt   # Lemma 4.1, Propositions C′, D and F: the same 38 lines
cc -O2 -o venn_enum_fast code/venn_enum_fast.c && ./venn_enum_fast 4   # Proposition E for up to four monomials (five monomials took 23 minutes)
```

Formalizations of the known results A246056 and A376230:

```sh
python3 certificates/oeis-hanna/round5/a246056/check.py
python3 certificates/oeis-hanna/round5/a376230/check.py
```

The logs of all runs cited in the paper are in `certificates/icg-q3-general/logs/`,
`certificates/icg-equal-parity/logs/` and
`certificates/icg-equal-parity/theorems-b-c/` (in `logs/` and in the `logs/`
folders of its subdirectories).
The Lean comments and the scripts in `certificates/icg-q3-general/review/`
use the numbering of the first draft. Draft Lemmas 1–4 and Theorem 5 are
Lemmas 7, 8, 10, 11 and Theorem 12 of Paper 1 (versions 1.4 and 1.5). The "Lemma 3 as
stated" counterexample printed by `review/test_e_misc.py` concerns a
superseded hypothesis (`P > 0`); Lemma 10 of the paper assumes `P ≥ μ`.

## Layout

- `papers/`: LaTeX sources and PDFs of the six papers.
- `certificates/icg-equal-parity/`: programs, logs and a negative control for Theorem 3 and Proposition 15 of Paper 1; `PROOF-working-note.md` is the working note.
- `certificates/icg-equal-parity/theorems-b-c/`: programs and logs for Theorems 4 and 5 of Paper 1, including those of the two referee agents (`review/`, `review2/`); its `README.md` lists the commands.
- `certificates/oeis-hanna/round5/`: checks for A246056 and A376230.
- `certificates/carenini/`: programs and logs for Paper 3.
- `certificates/hko-triameter/`: programs (`code/`) and logs (`logs/`) for Paper 4.
- `certificates/brauer-complete/`: programs, certificates and logs for Paper 5; `review/REVIEW.md` is the referee agent's report.
- `certificates/rm714/`: programs, data and logs for Paper 6.
- The files `PROOF-working-note.md` and `CONTRACT.md` in these folders are the agents' working records; they may refer to files that are not included here.
- `lean/`: Lake project with all Lean 4 proofs (`Research.lean` imports all of them).
- `certificates/`: certificate programs, their outputs and the OEIS b-files used.
- `logs/`: build logs, statement audits and source hashes from the clean
  rebuilds. `roldan-q3-lean-build-receipt.json` predates the formalization of
  the spectral bridge, so it still lists Lemma 2.1 as not formalized. The
  `ICGBridge*` files now formalize it (`ICGBridge.energy_icgAdj_eq_exactEnergy`).

## Prior work

- The conjectures and the numerical evidence are due to P. D. Hanna (OEIS)
  and D. G. Roldán (arXiv:2604.09491).
- Paper 1:
  - the case `q ≥ 5` of the opposite-parity family is due to Jiang and Yang
    (arXiv:2608.29523);
  - for the fixed exponents (2,3), i.e. order `p²q³`, Roldán's conjecture
    was treated earlier by Park and by Schreib (see below);
  - we are not aware of any earlier treatment of `q = 3` for general
    `r, s`;
  - equal parity: the case `n = pq` follows from formulas of Ilić (Linear
    Algebra Appl. 431, 2009) and Ilić–Bašić (Appl. Math. Comput. 218, 2011);
    Le and Sander (Linear Algebra Appl. 437, 2012) determined the maximum over
    multiplicative divisor sets, which is attained for `pq` but not for `pq³`
    (e.g. 584 > 512 for `5·3³`; `certificates/icg-equal-parity/check_lesander.py`);
    we found no earlier treatment of `pq^m` with `m ≥ 3`, or of any other
    equal-parity shape (deep search on 26 September 2026, 03:37–04:32 UTC,
    incremental search at 05:53–05:58 UTC, and a final check of the arXiv,
    GitHub, MathDB and MathOverflow at 15:49–15:52 UTC).
  This reports the coverage of our searches, not a guarantee of priority.
- Paper 3: Carenini's question was posted on 22 September 2026. We found no
  earlier answer to it or discussion of it (arXiv listing and API, Semantic
  Scholar, MathDB, GitHub code, commits, issues, pull requests and
  repositories, the AI-assisted repositories listed below, and web search;
  26 September 2026, 05:12–05:23 and 06:39–06:42 UTC, and again at 13:41 UTC
  before release). This reports the coverage of our searches, not a guarantee
  of priority.
- Paper 4:
  - The negative answer to Problem 2 is not new. Hak and Kozerenko restated
    the question in the Lviv Scottish Book (volume 3, page 154, entry dated
    10 February 2025); it was relayed to MathOverflow as
    [question 506431](https://mathoverflow.net/q/506431) on 28 December 2025,
    and on 31 December 2025 the user rgvalenciaalbornoz answered it, in the
    accepted [answer 506536](https://mathoverflow.net/a/506536), with an
    11-vertex median graph in which both (Q4) and (Q4′) fail. That answer
    does not concern (Q3′). Our contribution to Problem 2 is only the
    smallest counterexample and the observation that it is also
    distance-hereditary.
  - For Problems 1 and 3 we found no earlier answer. We searched on
    26 September 2026, 06:43–07:21 UTC: the arXiv API; the works citing the
    paper of Hak, Kozerenko and Oliynyk listed by OpenAlex and Semantic
    Scholar; Crossref; zbMATH Open; MathDB; MathOverflow and Mathematics
    Stack Exchange, through the Stack Exchange API; the Lviv Scottish Book;
    Wikipedia; MathWorld; GitHub; the repositories trureturing,
    formal-conjectures and SCOPE2026; and web search. Some searches failed:
    the keyword searches of OpenAlex and Semantic Scholar hit rate limits
    (HTTP 429), a citation search in zbMATH Open gave no usable result, and
    one citing paper was judged from its abstract. We did not search Google
    Scholar, Scopus, Web of Science or ResearchGate. General web search did
    not find the MathOverflow thread, which we found only through the Stack
    Exchange API. A final check of the arXiv, GitHub, MathDB and MathOverflow
    at 15:49–15:52 UTC found nothing new.
  This reports the coverage of our searches, not a guarantee of priority.
- Paper 5: Problem 15.11 is from J. Araújo, W. Bentz, P. J. Cameron,
  K. Hendrey and M. Kinyon, *Complete mappings of semigroups*
  (arXiv:2608.25092v1, 25 August 2026, still the only version on
  26 September 2026). We found no solution of it and no announced progress on
  it (searches on 26 September 2026, 06:49–07:46 UTC: the arXiv, GitHub, the
  repositories trureturing, SCOPE2026, AI-Has-Taste, formal-conjectures and
  astrafala, MathDB, MathOverflow, Mathematics Stack Exchange, Crossref, web
  search, the blog post announcing the paper and its comments, and the
  slides of a 2025 talk by M. Kinyon). The only earlier AI-assisted work on
  that paper that we found, trureturing issue #9377 and pull request #9405,
  concerns its Problem 15.5. Our searches for works citing the paper in
  OpenAlex and Semantic Scholar failed (HTTP 429, rate limit), so citing works
  were not checked systematically, and we did not search Google Scholar,
  zbMATH or MathSciNet. The results extend the methods of Araújo et al.
  directly: the reduction to principal factors, the criteria for Rees
  0-matrix semigroups, the lifting lemma and the non-existence theorem are
  theirs, and the treatment of `B_n` follows their proof for the partition
  monoid, including the triangle of half-diagrams. A final check of the arXiv
  (still only version 1 of arXiv:2608.25092), GitHub, MathDB and MathOverflow
  at 15:49–15:52 UTC found nothing new. This reports the coverage of our
  searches, not a guarantee of priority.
- Paper 6:
  - M. Leuenberger and M. Albrizzio (arXiv:2606.21425v1, 19 June 2026)
    reduced the open cases to 22 values. Three of our 17 weights, 4378, 4380
    and 4382, are weights by their Proposition 4 and are not new.
  - The question is C. Carlet's (IEEE Trans. Inf. Theory 70 (2024)); we
    paraphrase the wording of his extended abstract, as the full text was not
    accessible to us. Conjecture 2 is from Y. Lou and Q. Wang (Des. Codes
    Cryptogr. 93 (2025)), quoted from arXiv:2406.03803v1. The paper of
    Kasami, Tokura and Azumi (1976) was not accessible either; the page
    reference we give is the one given by Carlet. The determination of the
    whole spectrum in Theorem B uses that theorem to exclude weights below 320
    other than the known list (Proposition 4 of arXiv:2606.21425 only asserts
    that the listed values are weights); the part below 256 also follows from
    the theorem of Kasami and Tokura (1970). The equivalence with Carlet's
    question does not depend on the 1976 theorem.
  - Caveat: the note of Lou and Wang, *A note on two conjectures about the
    weight spectra of the Reed–Muller codes*, Discrete Appl. Math. 388
    (2026) 142–145, could not be read, and no abstract was available. It may
    concern the conjectures of their earlier paper, and so may anticipate
    Theorem C or other results of Paper 6.
  - Apart from this, we found no earlier claim that one of the 14 new values
    is a weight, no determination of the spectrum and no disproof of
    Conjecture 2. We searched on 26 September 2026, 06:41–07:15 and
    13:43–14:03 UTC: the arXiv, citing works in Semantic Scholar, Crossref,
    zbMATH Open, the MathSciNet reference lookup, MathDB, MathOverflow and
    Mathematics Stack Exchange, the IACR ePrint archive, HAL, GitHub
    including trureturing, and web search. Citation queries to OpenAlex and
    keyword searches of Semantic Scholar hit rate limits; we did not search
    Google Scholar, and Scopus was not accessible. A final check of the arXiv,
    GitHub, MathDB and MathOverflow at 15:49–15:52 UTC found nothing new.
  This reports the coverage of our searches, not a guarantee of priority.
- Roldán's conjecture, case q = 3 (the formalization here is of a known
  result):
  - S. Park, *Exact Energy Maximisation for Integral Circulant Graphs of
    Order p²q³* (github.com/coshaman/papers, 2026-08-21) claims the whole
    conjecture;
  - J. Jiang and C. Yang (arXiv:2608.29523) prove the case `q ≥ 5`;
  - J. A. Schreib (github.com/jamesschreib/roldan-universality-conjecture,
    2026-09-05) gives a written proof of the case q = 3; his Lean file
    assumes the spectral bridge as an axiom and uses `native_decide`;
  - [trureturing issue #8338](https://github.com/the-omega-institute/trureturing/issues/8338)
    (2026-09-16) announces an arithmetic certificate.
  - Our certificate was found independently, before we knew of these works.
- A389472, modulo 2: proved earlier by A. Perez Fontelles
  (astrafala/Conjectures, paper 1042, 2026-08-31) and in the trureturing
  repository. Both leave the modulo-three conjecture open.
- A246056 and A376230 follow from Deutsch–Sagan (2006; Theorem 5.15 in the
  journal version) and Gawron–Ulas (2016, Theorem 3.1) respectively, as
  explained above; we found
  this in a structural prior-work check before releasing them as new, and we
  present them only as formalizations.
- For the OEIS results listed above, apart from the connections with
  classical results and entry identities given in the correction above, we
  found no earlier proof in the following sources (searched 25–26 September
  2026):
  - the OEIS entries and their revision histories;
  - the-omega-institute/trureturing (files, issues and pull requests);
  - astrafala/Conjectures and twentyseventhllc-lgtm/OEIS-Settled;
  - other public repositories of OEIS proofs;
  - the literature and the web.
  This reports the coverage of our searches, not a guarantee of priority.

## Tool and computational resource disclosure

This work was carried out on 25–26 September 2026 in a workflow directed by
the author, using two AI coding agents:

- OpenAI Codex (desktop app; models `gpt-6-astra`, `gpt-6-sol`);
- Anthropic Claude Code (model Claude Opus 5.5).

The author chose the research programme and directed the agents. The agents:

- searched the literature and the OEIS;
- found the proofs and the certificates;
- wrote the programs and the Lean code;
- drafted the papers and this README.

For the results up to version 1.1, each agent audited the other's work. For
the material new in version 1.2, Claude Code agents found the equal-parity
results and wrote the Lean code, and independent Claude agents checked the
proofs; for A246056 and A376230, Codex selected the entries and outlined the
key steps, and Claude Code completed the proofs and the Lean code. The author, who is not a professional
mathematician, has read both papers (Paper 2 in its version 1) and, using a
side-by-side table, compared the statements of the final Lean theorems with
the theorems in the papers. The correction to Paper 2 in version 1.2.1 was
drafted by Claude Code and checked by an independent Claude agent; it changes
no theorem. Paper 3 (version 1.3.0) was selected, proved, formalized and
drafted by Claude Code agents, and independent Claude agents refereed the
proofs, the Lean statements and the paper; before release OpenAI Codex
checked the main statements, the Lean statements and the key counts.
The author has also read Paper 3 and, using the same kind of side-by-side
table, compared its Lean statements with the results in the paper.

The material new in version 1.4.0, namely Theorems 4 and 5 of Paper 1
(version 1.4) and Papers 4, 5 and 6, was found, formalized in Lean (to the
extent stated above) and drafted by Claude Code agents (model Claude Opus
5.5). The agents also selected the problems of Papers 4, 5 and 6 and carried
out the literature searches described in the papers. Independent Claude
referee agents checked each paper; for Paper 1, two referee agents checked
earlier write-ups of the proofs of Theorems 4 and 5, and one of them wrote
the second certification program for Theorem 5. In version 1.5.0 the
extension of Theorem 5 to exponents 5 to 8 was checked by a third independent
Claude referee agent, which reran both certification programs and certified
the same inequalities with its own program.
The author has also read the changes of version 1.5.

The author has also read the new material of version 1.4.0 (Paper 1 in its
version 1.4, and Papers 4, 5 and 6) and, using the same kind of side-by-side
table, compared its Lean statements with the results in the papers.

AI systems are not authors. The author takes full responsibility for the content.

## License

Code (`lean/`, `certificates/`) is licensed under the Apache License 2.0; see
`LICENSE`. The papers in `papers/` are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). The OEIS b-files in
`certificates/oeis-hanna/bfiles/` and `certificates/oeis-hanna/b389472.txt` are from the OEIS and are licensed under
CC BY-SA 4.0.

## Citation

See `CITATION.cff`. To cite all versions, use the concept DOI
[10.5281/zenodo.22970254](https://doi.org/10.5281/zenodo.22970254). Version
DOIs: v1.0.0 [10.5281/zenodo.22970255](https://doi.org/10.5281/zenodo.22970255),
v1.1.0 [10.5281/zenodo.22970816](https://doi.org/10.5281/zenodo.22970816),
v1.2.0 [10.5281/zenodo.22972115](https://doi.org/10.5281/zenodo.22972115),
v1.2.1 [10.5281/zenodo.22979318](https://doi.org/10.5281/zenodo.22979318),
v1.3.0 [10.5281/zenodo.22979323](https://doi.org/10.5281/zenodo.22979323),
v1.4.0 [10.5281/zenodo.22981669](https://doi.org/10.5281/zenodo.22981669); later
versions are listed on the Zenodo record.
