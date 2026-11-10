# Attempts

This file lists the open problems that the AI agents of this project worked
on, and what happened to each of them: the results that were published, the
problems that were dropped because someone had already solved them, and the
problems that were dropped without a result. It gives the denominator behind
the results in this repository: how many problems were tried, and what
became of each.

Status: 10 November 2026, covering the work of 25 September to 10 November 2026 up to version
1.18.0. All dates are UTC.

## How to read this file

- All research was done by AI coding agents (OpenAI Codex in the early
  rounds, then mainly Claude Code) under the direction of the author, who is
  not a professional mathematician. See the disclosure in the README.
- A problem is listed if an agent did research work on it (a statement
  contract, a proof attempt, a computer search or a Lean formalization), or
  if our records list it as dropped because of earlier work. Candidates that
  were only screened are not listed; their number is given under
  [Counts](#counts).
- One row is one item: an OEIS entry, one question or conjecture, or a small
  group of related problems from one source that we worked on together.
- "Found" is the date on which our agents found the earlier work.
- Our searches can miss earlier work. If you know of earlier work on any item
  below, please open an issue.

## (a) Published

The column "Lean" describes the formal verification in version 1.18.0; the
README has the details.

| # | Problem | Source | Published in | What was proved | Lean |
| --- | --- | --- | --- | --- | --- |
| 1 | A389472: `3 ∣ a(3n − 1)` for `n > 1` | OEIS (P. D. Hanna) | v1.0.0 (Lean), v1.1.0 (Paper 2), corrected in v1.2.1; version 2 in v1.15.0 | Proved. The modulo-2 part of the entry had been proved earlier by others (A. Perez Fontelles, astrafala/Conjectures paper 1042; the trureturing repository); we claim only the modulo-3 part | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 2 | A377100: `a(n) ≡ 1 (mod 3)` for `n ≥ 1` | OEIS (P. D. Hanna) | same as row 1 | Proved; we found no earlier proof and no derivation from classical results | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 3–7 | A240998, A295762, A301933, A338633, A338634 (5 entries): `a(n)` is odd if and only if `n` is a power of 2 | OEIS (P. D. Hanna) | same as row 1 | Proved. Modulo 2 each series reduces to the Catalan series, so the patterns follow quickly from the parity of the Catalan numbers; stated in the corrected Paper 2 (v1.2.1) | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 8 | A273958: `a(n)` is odd if and only if `n = 2·4^k − 1` | OEIS (P. D. Hanna) | same as row 1 | Proved; a quick consequence of `xA ≡ C(C(x²)) (mod 2)` (stated since v1.2.1) | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 9–11 | A274479, A388734, A120566 (3 entries): congruences modulo 3 or 2 | OEIS (P. D. Hanna) | same as row 1 | Proved; short proofs from identities stated in the entries themselves (stated since v1.2.1) | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 12 | A184894: vanishing modulo 3 outside `m = (3^n + 1)/2` | OEIS (P. D. Hanna) | same as row 1 | The statement as written holds; a stronger reading fails at OEIS index 365. Follows from the classical theory of linearised polynomials over F₃ (stated since v1.2.1) | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 13 | A107099: vanishing modulo 3 except at `n = 3^k` | OEIS (P. D. Hanna) | same as row 1 | The statement as written holds; a stronger reading fails at `x^729`. No novelty claimed since v1.2.1 | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 14 | A361047: residues modulo 3 | OEIS (P. D. Hanna) | same as row 1 | The intended statement holds (the entry has an index slip). No novelty claimed since v1.2.1 | all mathematical results (version 2, v1.15.0); not the identification with the OEIS entry |
| 15 | Roldán's Conjecture 1.3, case `q = 3` (order `27p²`) | arXiv:2604.09491 | v1.0.0 | Known result, formalized only. Proved earlier by S. Park (2026-08-21, github.com/coshaman/papers, who claims the whole conjecture) and J. A. Schreib (2026-09-05, github.com/jamesschreib/roldan-universality-conjecture); a certificate was announced in [trureturing issue #8338](https://github.com/the-omega-institute/trureturing/issues/8338) (2026-09-16). We add a complete Lean formalization and the second-largest energy | yes |
| 16 | Maximal energy of integral circulant graphs of order `p^(2r)·3^(2s+1)`: the case `q = 3`, which Theorem A of Jiang and Yang does not cover | arXiv:2608.29523 | v1.1.0 (Paper 1, Theorem 2); version 2 in v1.16.0, version 3 in v1.17.0 | Proved for every prime `p ≥ 5`: the checkerboard set is the unique maximiser, and the maximal energy is given by their formula. The case `r = s = 1` (order `27p²`) is row 15; a Lean proof of it for all distinct odd primes was later merged in trureturing (pull request #19390, 2026-10-20) | all results (versions 2 and 3, v1.16.0 and v1.17.0), not checked with comparator |
| 17 | Equal-parity conjecture on the maximal energy of integral circulant graphs of order `p^a q^b` | our Paper 1 (conjecture stated in v1.1.0) | v1.2.0 (Theorem 3), v1.4.0 (Theorems 4 and 5), v1.5.0 (Theorem 5 extended); version 2 in v1.16.0; version 3 in v1.17.0 (one prime equal to 3) | Proved for orders `pq^m` and `p^m q` with `m` odd (Theorem 3) and `p²q^b` and `p^b q²` with `b` even (Theorem 4), that is, for every order `p^a q^b` with `a + b` even and `min(a, b) ≤ 2`, the prime 3 included (Theorem 5 of version 2), and, in version 3, for every order `p^a q^b` with `a + b` even in which one of the primes is 3, with no bound on the exponents or on the other prime (Theorem 5 of version 3, Section 13). The case `n = pq` follows from earlier formulas of Ilić and Ilić–Bašić. Version 1.5 also claimed `3 ≤ min(a, b) ≤ 8` with computer assistance; version 2 withdrew this, because it has no formal proof, not because an error was found. Later work: Jiang and Yang (arXiv:2610.36883v1, 2026-10-27) state the formula for all distinct primes `p, q ≥ 5`; their statement does not include the prime 3. We have not reviewed their proof, and it is not formalized; only if it is correct does the conjecture hold for all distinct odd primes. The remaining orders (`p, q ≥ 5`, `min(a, b) ≥ 3`) are not proved here | all results (version 2, v1.16.0, and version 3, v1.17.0), not checked with comparator; Proposition 31 as an implication, with its conditions proved at the points `(3, q)`, `q` an odd prime other than 3; the conjecture itself is proved only for `min(a, b) ≤ 2` and when one of the primes is 3 |
| 18 | A246056: the pattern of `a(n) mod 3` | OEIS (P. D. Hanna) | v1.2.0 | Known result, formalized only: it follows from a theorem of Deutsch and Sagan (J. Number Theory 117 (2006)) | yes |
| 19 | A376230: a parity comment | OEIS (P. D. Hanna) | v1.2.0 | The comment is false as stated (`a(4) = 8`). The corrected pattern follows from a theorem of Gawron and Ulas (Discrete Math. 339 (2016)): known result, formalized only | yes |
| 20 | Carenini's Question 1.3 on almost independent sets in regular graphs | arXiv:2609.28527 | v1.3.0 (Paper 3); version 2 in v1.10.0 | Answer: no. Smallest counterexample `(n, d, γ) = (6, 3, 1/18)`; counterexamples for every `(n, d)` with `2d ∣ n` apart from trivial cases, and further families; a positive result at the exponential scale. Some cases remain open | all results (version 2) |
| 21 | Problems 1–3 of Hak, Kozerenko and Oliynyk on the triameter of graphs (3 problems) | Discrete Appl. Math. 309 (2022); arXiv:2103.10806 | v1.4.0 (Paper 4); version 2 in v1.9.0 | Problem 1: no (an 8-vertex median graph). Problem 2: no, but this had already been answered on MathOverflow by rgvalenciaalbornoz ([answer 506536](https://mathoverflow.net/a/506536), 2025-12-31; found by us on 2026-09-26); we add only the smallest counterexample. Problem 3: yes, in a stronger form | all results (version 2) |
| 22 | Problem 15.11 of Araújo, Bentz, Cameron, Hendrey and Kinyon: complete mappings of the Brauer and partial Brauer monoids | arXiv:2608.25092 | v1.4.0 (Paper 5); version 2 in v1.12.0 | Settled in its existence reading: `B_n` and `PB_n` have a complete mapping if and only if `n ∉ {2, 3}`, with the answer for every proper principal factor. The set of all complete mappings is not described | all results (version 2) |
| 23 | Weights of the Reed–Muller code RM(7,14) (Carlet's question; 22 undecided values listed by Leuenberger and Albrizzio) | C. Carlet, IEEE Trans. Inf. Theory 70 (2024); arXiv:2606.21425 | v1.4.0 (Paper 6); version 2 in v1.13.0 | Partial answer: 14 new weights (17 found, 3 of them already known); explicit codewords for every even number from 320 to 2^14 − 320 except 322, 326, 330, 334 and their complements, so, in the middle-interval reading of Carlet's question, the question for (7,14) is equivalent to these four being weights (version 1 also claimed the whole spectrum up to these four, citing a 1976 theorem we could not consult; version 2 deletes that claim); Conjecture 2 of Lou and Wang fails for `m = 6` (Theorem C), but this was not new: Lou and Wang had proved it in Discrete Appl. Math. 388 (2026) 142–145, a note we read only after publication (see Corrections) | all results (version 2) |
| 24 | Minimum order of a counterexample to the conjecture of Braga, Del-Vecchio and Rodrigues on integral generalized sun graphs | arXiv:2609.28754 (Braga, Moraes and Santos) | v1.6.0 (Paper 7) | The minimum order is 42, and the 42-vertex counterexample is unique; also a constraint on odd cycles in integral unicyclic graphs, later superseded by arXiv:2610.22773 | complete in version 2 (v1.14.0), not checked with comparator |
| 25 | The switching conjecture for main eigenvalues, for trees (Problem 1.6 of Akbari, Kumar, Mohar and Pragada) | arXiv:2609.27046 | v1.7.0 (Paper 8); version 2 in v1.11.0 | Partial answer: the conjecture holds for every tree of diameter at most 4 other than K₂, and so does its signature version. Open for all trees and for regular graphs | all results (version 2) |
| 26 | Conjecture 3.16 of McInroy and Shpectorov, and Problem 3.11 of Gorshkov and Shpectorov (= Question 9.5 of Mamontov, Shpectorov and Zhelyabin): the finest sum decomposition of an axial algebra and the connected components of its non-annihilation graph | arXiv:2209.08043; arXiv:2606.30048; arXiv:2602.11984 | v1.8.0 (Paper 9, Theorem A and Corollary 1.1) | Answer: no, when arbitrary finite symmetric fusion laws are allowed: a four-dimensional simple primitive axial algebra over ℚ whose non-annihilation graph is disconnected. Not about the Monster-type case (row 5 of section c) | all results |
| 27 | Problem 3.8 of Gorshkov and Shpectorov (= Question 9.2 of Mamontov, Shpectorov and Zhelyabin): is every axial block indecomposable? | arXiv:2606.30048; arXiv:2602.11984 | v1.8.0 (Paper 9, Theorem C) | Answer: no, when arbitrary finite symmetric fusion laws are allowed: a five-dimensional example. Its block is not generated by the axes it contains, so it does not answer the question if only blocks that are axial algebras are meant | all results |
| 28 | Problem 5.1 of Alshammari: are `μ(C_{2n+1}) × W_{2m+1}` and `μ′(C_{2n+1}) × W_{2m+1}` non-word-representable for all `n ≥ 1`, `m ≥ 2`? | arXiv:2609.20881 | v1.9.0 (Paper 10) | Answer: yes. The proof finds a non-word-representable induced subgraph and uses the theorems of Hameed and of Kitaev and Pyatkin, which we also formalize in their word-representability form | all results |
| 29 | Part (i) of the open problem "Distance eigenvalues of cographs below −2 and sharpness" of Manna, Mandal and Tura: is there `ε > 0` such that `(−2 − ε, −2)` contains no distance eigenvalue of any connected cograph? | arXiv:2611.06981 (survey) | v1.18.0 (Paper 11, a short note) | Answer: no. For every `m ≥ 1`, `K_1 ∨ (K_1 ∪ mK_2)` is a connected cograph with a distance eigenvalue in `(−2 − 1/(2m), −2)`. The same graphs were used earlier by Conde, Dratman and Grippo (arXiv:2606.06052, Lemma 6) for the adjacency matrix, and the answer also follows in a few lines from their lemma (Remark 1 of the paper); we found no paper that states it for the distance matrix. The other parts of the open problem are not addressed | all results (Theorem 1), not checked with comparator; Remark 1 is not formalized |

## (b) Dropped because earlier work was found

The column "Our work" shows how much work we did on each item. None of these
items is claimed as a result in this repository.

| # | Problem | Source | Our work | Earlier work | Found |
| --- | --- | --- | --- | --- | --- |
| 1 | A185897: for `n > 1`, `a(n)` is odd when `3·2^k ≤ n ≤ 4·2^k − 1` | OEIS (P. D. Hanna) | A proof of the exact parity pattern, checked by a second agent | A Lean-verified proof had already been deposited on Zenodo by Ruimin Yan on 2026-08-31 ([10.5281/zenodo.22203779](https://doi.org/10.5281/zenodo.22203779)) | 2026-09-25 |
| 2 | A398916: the conjecture `g(4n) = g(n)` for the Sprague–Grundy values of a bit-deletion game | OEIS | A short written proof | Proofs had already been posted in the GitHub repositories farev/Matematica ([note](https://github.com/farev/Matematica/blob/4404f5bd46cd9248807980ea73a8a6467afdb342/conjectures/bit-deletion/NOTE.md), 2026-09-03) and the-omega-institute/trureturing (a Lean proof with a [write-up](https://github.com/the-omega-institute/trureturing/blob/b5e234ba04d648411140fe79d6ec71b249bc30bb/Blueprint/D5/S1/Words/BitDeletionGrundy.md), 2026-09-10) | 2026-09-25 |
| 3 | Conjecture 1 of Wang and Tian: every τ_k-maximal graph of order `n ≥ 2k + 2` has `(k+1)(n−1) − 1` edges | arXiv:2606.28198 | A complete written proof, computer checks of small cases and a partial Lean formalization | A complete proof had already been posted on the blog himbodhisattva.com ([post](https://himbodhisattva.com/blog/wang-tian-tree-packing-conjecture/); [copy on GitHub](https://github.com/himbodhisattva/himbodhisattva.github.io/blob/04016ed667f577adc251286923917c0cb959d8cd/research/tree-packing-conjecture/README.md), commit of 2026-07-21) | 2026-09-25 |
| 4 | Pandey's parity conjecture on the real-rootedness of independence polynomials of generalized Petersen graphs (Conjecture 4.1) | arXiv:2601.03293 | Small computer checks by scouting agents only | A refutation had already been posted in the GitHub repository demonstrandum-research/artifacts ([write-up](https://github.com/demonstrandum-research/artifacts/blob/94db9ed50d48a57aae5ccb72e6a95a2b8f8f39d3/problems/p2-factory/kills/pandey-parity/WRITEUP.md), commit of 2026-06-13); a Lean formalization of the refutation followed in trureturing ([issue #8619](https://github.com/the-omega-institute/trureturing/issues/8619), 2026-09-18; see also [issue #8875](https://github.com/the-omega-institute/trureturing/issues/8875)) | 2026-09-25 |
| 5 | A091713: all terms are odd | OEIS (P. D. Hanna) | A numerical check of 400 terms | A proof had already been posted by Adrian Perez Fontelles in astrafala/Conjectures ([paper 663](https://github.com/astrafala/Conjectures/blob/58cf4596af4541652fb191e177ef9b7771388d53/papers/00501-01000/00663-PROOF.pdf), dated 2026-08-31) | 2026-09-26 |
| 6 | A196523: `a(n) ≡ 1 (mod 3)` for `n ≥ 1` | OEIS (P. D. Hanna) | A numerical check of 400 terms | A proof had already been posted by Adrian Perez Fontelles in astrafala/Conjectures ([paper 1037](https://github.com/astrafala/Conjectures/blob/58cf4596af4541652fb191e177ef9b7771388d53/papers/01001-01500/01037-PROOF.pdf), dated 2026-08-31) | 2026-09-26 |
| 7 | A393170: for `n > 0`, `a(n)` is odd if and only if `n` is a power of 2 | OEIS | A statement contract and a sketch of a method | A Lean proof had already been merged into the-omega-institute/trureturing ([pull request #6566](https://github.com/the-omega-institute/trureturing/pull/6566), 2026-09-09) | 2026-09-26 |
| 8 | Conjectures 1–3 of Bharadwaj, Sujatha and Chandankumar on 2-color overpartitions | arXiv:2607.16608 | Proofs of all nine congruences in Section 5 of the paper, checked by a referee agent | Proofs of Conjectures 1–3 had already been posted on MathDB by Shivam Patel on 2026-08-20 ([1](https://mathdb.com/p/376101), [2](https://mathdb.com/p/376102), [3](https://mathdb.com/p/376103); MathDB lists them as "Claimed solved"). The rest of our work (the congruences (5.1)–(5.3), which the source leaves to the reader, two further theorems and some strengthenings) was set aside as low in value | 2026-09-26 |
| 9 | Conjectures 2.5 and 3.7 of Lee and Liu on the integer {2}-domination number of 3 × n and 4 × n grids (2 conjectures) | arXiv:2502.00134 | Computer-assisted proofs of both (transfer matrices with periodicity certificates), checked by independent programs and a referee agent | Computer-assisted proofs of both had already been posted in the GitHub repository [JMK-vineetarora/integer2proofs](https://github.com/JMK-vineetarora/integer2proofs) (2026-08-12), with the same method and certificates as ours | 2026-09-26 |
| 10 | Problems 6.4, 6.2(a), 6.3 and 3.9 of T. Amdeberhan on the AIM problem list "Polyhedral geometry and partition theory" (4 problems) | AIM problem list | Proofs of 6.4, 6.2(a) and 6.3; partial results on 3.9; some of it in Lean | T. Amdeberhan had posted these problems on MathOverflow, and solutions had already been posted there: 6.4 by Ofir Gorodetsky in 2016 ([question 250609](https://mathoverflow.net/q/250609)), 6.2(a) by D.B. Cooper in 2016 ([question 252156](https://mathoverflow.net/q/252156)), 6.3 by Richard Stanley in 2016 ([question 255252](https://mathoverflow.net/q/255252)), and the first of the three ratios in 3.9 by Fedor Petrov in 2021 ([question 382485](https://mathoverflow.net/q/382485)). The rest of our work on 3.9 was set aside as low in value | 2026-09-26 |
| 11 | Problem 3.9 of Gorshkov and Shpectorov (= Question 9.3 of Mamontov, Shpectorov and Zhelyabin): can dominance between axial blocks be non-symmetric? | arXiv:2606.30048; arXiv:2602.11984 | A further example (Theorem B of Paper 9) and a Lean proof for the earlier example (Proposition 4.1 of Paper 9, credited to its authors); we do not claim the answer | Two-dimensional axial algebras with properly nested blocks were already in print, without mention of blocks: B. Peng (arXiv:2608.28653, 2026-08-20) and I. Kaygorodov, C. Martín González and P. Páez-Guillán (arXiv:2211.00334, 2022; J. Algebra 662 (2025)) | 2026-09-27 |

## (c) Dropped without a result

| # | Problem | Source | What we did | Why we stopped |
| --- | --- | --- | --- | --- |
| 1 | Interpolation of subset products along prime powers | OEIS A060957 | Exact search for all `n ≤ 30` (no gap found); an auxiliary lemma proved in Lean; a second structural pass | No proof found; no new idea for the main step. Stopped on 2026-09-25 |
| 2 | A divisibility property of the number of squares modulo `n` characterizes the odd primes | OEIS A000224 | Bounded Pell-equation search beyond the parameter range of an earlier public search (376 ≤ K ≤ 1500, `n ≤ 10^18`; 8,888 candidates): no counterexample | No proof found. Partial results were already public ([umaia1234/agentic-conjectures](https://github.com/umaia1234/agentic-conjectures/tree/96ea0039d9dc3a1940b9d5ec1cbe616ed58d1da2/problems/oeis-a000224)). Stopped on 2026-09-25 |
| 3 | Conjecture 6.1 of J. W. Sander and T. Sander (framing conjecture for integral circulant graphs of prime-power order) | Discrete Appl. Math. 160 (2012); arXiv:1205.4603 | Exact search: no counterexample (for example `p = 3` up to `s = 102`) | No proof found within the time box; a proof within a day was judged unlikely. Stopped on 2026-09-26 |
| 4 | Hu's question on nonflexible finite generalized polygons | arXiv:2609.28550 | Checked all known projective planes of orders 16 and 25 (22 and 193 planes): all are flexible, so none answers the question | Finite check done, no new result: the same fact can already be read off published tables (arXiv:2506.14060v16). The question remains open. Stopped on 2026-09-26 |
| 5 | Conjecture 6.2 of Khasraw, McInroy and Shpectorov: the question of row 26 for axial algebras of Monster type M(1/4, 1/32) | Trans. Amer. Math. Soc. 373 (2020); arXiv:1809.10132 | Tried to build a counterexample by gluing two copies of a suitable algebra; tested one candidate, the 18-dimensional algebra of McInroy and Shpectorov with Miyamoto group S3 × S3 (arXiv:1804.00587) | The tested algebra does not have the property that the construction needs, and we know no other candidate. Stopped on 2026-09-27 |
| 6 | Problems 5.2–5.4 of Alshammari: the question of row 28 for `μ(C_{2n+1}) × μ′(C_{2m+1})` and `μ′(C_{2n+1}) × μ′(C_{2m+1})`, and whether a tensor product of two non-word-representable graphs can be word-representable | arXiv:2609.20881 | Computer checks of small cases with a SAT solver: the 9 products tested for Problems 5.2 and 5.3, and all 496 products of two graphs from a pool of 31 non-word-representable graphs for Problem 5.4, are non-word-representable | No proof found; the small-case evidence is not published. The problems remain open. Stopped on 2026-09-27 |

## Counts

- Listed in total: 46 items.
  - Published: 29 items (section a). Of these, 3 are known results that we
    only formalized (rows 15, 18 and 19), and 12 of the 14 OEIS entries of
    Paper 2 turned out to follow quickly from classical results or from
    identities stated in the entries (rows 3–14). Several of the other items
    are partial answers.
  - Dropped because earlier work was found: 11 items (section b). For 4 of
    them (rows 4–7) our own work was small: screening checks, a numerical
    check or a statement contract.
  - Dropped without a result: 6 items (section c).
- Work in progress is not listed here. With version 2 of Paper 1 (v1.16.0),
  all ten papers then published were formalized completely in Lean; version 3
  of Paper 1 (v1.17.0) and Paper 11 (v1.18.0) are also formalized completely,
  except Remark 1 of Paper 11.
- Scouted but not attempted: 54 candidates. This counts the candidates that
  scouting agents wrote up and ranked in their reports but on which no
  research was done. Problems rejected during bulk screening (for example,
  of arXiv listings and of several hundred OEIS conjectures) are not counted.

## Corrections

Published corrections so far:

1. **Paper 2, v1.2.1 (2026-09-26).** Version 1 of Paper 2 (v1.1.0) did not
   say that several of the conjectures it proves are quick consequences of
   classical results or of identities stated in the OEIS entries. A
   correction notice was added to the README in v1.2.0, and the corrected
   paper was released in v1.2.1: it states these connections in the
   abstract, in a new paragraph "Relation to classical results" and in
   remarks at the theorems, and it no longer claims A107099 and A361047 as
   new. The theorems, proofs and Lean files did not change.
2. **Working note on RM(7,14), v1.5.0 (2026-09-26).** A line in
   `certificates/rm714/PROOF-working-note.md` (published in v1.4.0) said
   that a revision of arXiv:2606.21425 had been announced. That was wrong:
   the "author response" it relied on, on a third-party review page, is
   marked there as simulated. The line is struck through and corrected.
   The note is a working record, not part of Paper 6.
3. **README description of Paper 7, v1.7.0 (2026-09-27).** The README of
   v1.6.0 called Theorem 2 of Paper 7 not new and gave Corollary 3.1 under
   the name Proposition 3. The v1.6.0 release notes flag this, and the
   README of v1.7.0 follows the paper. The paper itself was not affected.
4. **README of v1.7.1 (2026-09-27): corrections found after publication.**
   The section "Known issues" of the README lists them:
   - Theorem C of Paper 6 had been proved earlier by Lou and Wang (Discrete
     Appl. Math. 388 (2026) 142–145, Proposition 2), in a note we had not
     been able to read;
   - a definition in Section 3 of Paper 5 needs "2-element";
   - Paper 8 counts branch multisets, not trees, and omits a short proof of
     the search bound;
   - the README had overstated the scope of Proposition 15 of Paper 1.
   
   The papers themselves will be corrected in later versions.
5. **README of v1.8.0 (2026-09-28): further corrections.** The completed
   independent check by OpenAI Codex found three missing hypotheses in
   Paper 4, an overstatement of the formalized scope in reading R1 of
   Paper 3, the missing condition `r ≥ 1` in property (P2) of Paper 6 and
   implicit normalizations in Paper 2; they are listed under Known issues.
   The README now states precisely what Lean covers for Papers 3 and 4,
   and how many of the weights of Paper 6 were among the open values.
6. **Paper 4, version 2 (v1.9.0).** Adds the three hypotheses listed under
   Known issues in v1.8.0 and removes three claims that were not formally
   verified: the counts of connected labelled graphs in Section 4, the last
   sentence of Remark 5, and Section 6 of version 1 apart from its last
   sentence. Every result of version 2 is formalized in Lean. Theorems A, B
   and C are unchanged.
7. **Paper 3, version 2 (v1.10.0).** Removes two claims of version 1 for
   which we have no formal proof (the normal approximation at `γ = 1/8` in
   Remark 10, with reading R6 at `γ = 1/8`, and the count of 19,355
   labelled 4-regular graphs on eight vertices) and three unformalized side
   remarks, and corrects the overstatement in reading R1 listed under Known
   issues in v1.8.0. Every result of version 2 is formalized in Lean. The
   theorems are unchanged.
8. **Paper 8, version 2 (v1.11.0).** Removes the computational claims of
   version 1 that are not formally verified (the supporting computations on
   all trees with up to 24 vertices and on the trees of diameter at most 4
   with up to 44 vertices, counts of non-even pairs and of good switchings,
   and the computed values in Remark 8.1), states and proves the bound
   `t_r ≤ b* + k` that version 1 used without proof, and speaks of 13,376
   branch multisets rather than trees (the two points listed under Known
   issues since v1.7.1). Every result of version 2 is formalized in Lean. The
   theorems are unchanged.
9. **Paper 5, version 2 (v1.12.0).** Corrects the definition of `top(x)` and
   `bot(x)` in Section 3 (listed under Known issues since v1.7.1) and removes
   the claims of version 1 for which we have no formal proof: the results of
   the computer checks of its Section 8, Remark 4.5(4) (a comparison of
   Lemma 4.4 with a criterion of Araújo et al.), and several side
   statements, among them the identifications with Green's relations. Every
   result of version 2 is formalized in Lean. The theorems are unchanged.

10. **Paper 6, version 2 (v1.13.0).** Deletes every claim of version 1 that
   rests on the theorems of Kasami and Tokura (1970) or Kasami, Tokura and
   Azumi (1976), which we could not consult and have not formalized: the
   determination of the whole weight spectrum up to four values (the title of
   version 1 is changed to "Fourteen new weights of the Reed–Muller code
   RM(7,14)"), (P4a), (P4b), Lemma 4.1, Proposition C′, the extension of
   Theorem C to arbitrary `g₁, g₂ ∈ RM(6,12)`, and the remark that the
   weights below 320 of sums of five monomials are exactly the known list;
   the computations and heuristic searches of version 1 are no longer
   reported. Theorem C is attributed to Lou and Wang (listed under Known
   issues since v1.7.1), and (P2) states the hypothesis `r ≥ 1`. Every
   result of version 2 is formalized in Lean. Theorems A and B (its explicit
   codewords), the Corollary and Propositions D, E and F are unchanged.

11. **Paper 7, version 2 (v1.14.0).** Every result of version 2 is formalized
   in Lean. Theorems 1 and 2 no longer rest on the computer searches of
   version 1; the cycle lengths 3, 6 and 10 are settled by formal proofs. The
   search tables and counters, the program versions, the controls and random
   tests are deleted, as is the statement that two programs produced the same
   52,652 sequences at cycle length 10 (two frozen statements on these data
   files could not be proved and were deleted by the author). One frozen
   statement was false because of a missing pair of parentheses; the author
   approved this correction and the files were frozen again. The bounds of
   program D at 0 and ±1 and the families of the introduction (`a ≥ 1`) are
   corrected, and Corollary 3.1 is marked as superseded by arXiv:2610.22773.
   The theorems are unchanged.
12. **Paper 2, version 2 (v1.15.0).** All the mathematics is formalized in Lean,
   including the existence and uniqueness of the normalized solutions and their
   first terms, which are new statements in the paper (Table 2). The
   normalizations are separated from the hypotheses of the theorems: the
   equation of A389472 does not determine `a(2)`, that of A240998 forces
   `a(0)` to be 0 or 1, and `F = x/(1+FF′)` determines `F` only with
   `F(0) = 0`. The sentence that new coefficients appear as 1 or 2 is deleted
   (for A120566 the coefficient is −1), as is a remark in Section 6 on `2f(m)`
   and lower-order terms; the reason given in a remark there, Lucas's theorem,
   is replaced by the argument the proof uses. The composition in the abstract
   is written as `C(C(x²))`. Remark 11 says that Theorem 10 contains the intended
   statement, rather than that it is that statement. The statements about
   earlier work are dated, and later proofs are cited. Several qualifiers are
   added (`n ≥ 1` for A301933 in Table 1; `a(0) = 1` for A240998 and "according to
   those entries" in the paragraph on classical results; `j ≥ 1`; "any
   compositional inverse with zero constant term"; "units digit"). Section 7 is
   rewritten around the 84 statements, and the sentence that the author compared
   the Lean statements with the paper, which described version 1, is replaced by
   the author statement of version 2. The theorems are unchanged.
13. **Paper 1, version 2 (v1.16.0).** Every result of version 2 is formalized
   in Lean, including the closed forms of `d_k` and `δ_k`. Theorem 5 is narrowed
   from `min(a, b) ≤ 8` to `min(a, b) ≤ 2`, the other exponent being arbitrary.
   Withdrawn because they have no formal proof, not because an error was found
   in the computations: the case `3 ≤ min(a, b) ≤ 8` of Theorem 5, Proposition 15
   (certificates for eleven exponent pairs; the number 15 is no longer used), and
   the certificates of Section 12 that the conditions of Proposition 31 hold for
   `3 ≤ a ≤ 8`, with their counts, programs and negative controls. Proposition 31
   is kept as a conditional statement, of which no instance is claimed, and
   Section 12 is renamed accordingly. Also deleted: the list of computational
   cross-checks (exhaustive searches, tests of lemmas, floating-point spectra,
   the 325 inequalities of an earlier proof of Theorem 25), a paragraph after
   Lemma 27 on its Lean proof, the restatement of the general results of Le and
   Sander in Remark 16, and the opening and last sentence of Remark 30. Section 1
   no longer says that Conjecture 14 is open for `min(a, b) ≥ 9`; the conjecture
   is kept only as a historical statement, and the section reports the later work
   arXiv:2610.36883 and trureturing pull request #19390 and the revision of
   arXiv:2608.29523. Theorems 1–4 are unchanged. The programs and logs of
   version 1.5 remain in `certificates/` as its records.
14. **Paper 1, version 3 (v1.17.0).** Not a correction: no error was found in
   version 2. Listed here because it changes statements of version 2 about the
   scope of the paper. Theorem 5 now also covers every order of equal parity in
   which one of the primes is 3, with no bound on the exponents or on the other
   prime; the new Section 13 (statements 32–43) proves this case by verifying,
   for the prime 3, the conditions of Proposition 31 at every exponent and every
   other odd prime, and every new result is formalized in Lean (the main
   statement `SameParityThree`, frozen on 8 November 2026 before its proof was found).
   The heading of Conjecture 14 and the paragraph after it now say that the
   conjecture is proved when `min(a, b) ≤ 2` or one of the primes is 3, and
   that the remaining orders are covered by the statement of Jiang and Yang
   (arXiv:2610.36883), whose proof we have not reviewed; the note on the
   withdrawn Proposition 15 says that its orders with a prime 3 are now covered
   by Theorem 5. Section 1 reports a further literature search
   (8 November 2026, 21:07–21:22 UTC), the introduction of Section 12 says which
   conditions are proved, and the section on formal verification, now
   Section 14, describes the new Lean package. The statement that the three
   conditions hold at every point of both regions for every `a ≥ 3` is not
   proved. Proposition 31 and all proofs of version 2 are unchanged, and the
   statements of version 2 keep their numbers.
