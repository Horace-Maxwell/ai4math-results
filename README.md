# Research papers formalized in Lean 4: graph energy, OEIS congruences, almost independent sets, triameter, Brauer monoids, Reed–Muller weights, integral sun graphs, main eigenvalues, axial algebras, word-representability, distance eigenvalues of cographs, Frobenius forms of axial algebras, cycles of length 0 modulo k in critical graphs, the rank of groups of equivariant permutations, the longest Manhattan paths through boxes, the decomposition lengths of numerical semigroups, antichains of trees in the independence polynomial order, invariant parking with cars of different lengths, medial racks of prime order, the generalized Wilf conjecture for graded semigroups, the covering radius of a lattice simplex, a terrace for the alternating group A7, the largest domination roots of friendship graphs, bars that do not tile a 2 × n rectangle, the Minkowski length of lattice simplices, the covering minima of the standard terminal simplex and the integer group determinants of the Heisenberg group of order 125

This repository contains twenty-seven papers, their Lean 4 formalizations and
computational certificates. It is archived on Zenodo: all versions
[10.5281/zenodo.22970254](https://doi.org/10.5281/zenodo.22970254); version 1.0.0
[10.5281/zenodo.22970255](https://doi.org/10.5281/zenodo.22970255); version 1.1.0
[10.5281/zenodo.22970816](https://doi.org/10.5281/zenodo.22970816); version 1.2.0
[10.5281/zenodo.22972115](https://doi.org/10.5281/zenodo.22972115); version 1.2.1
[10.5281/zenodo.22979318](https://doi.org/10.5281/zenodo.22979318); version 1.3.0
[10.5281/zenodo.22979323](https://doi.org/10.5281/zenodo.22979323); version 1.4.0
[10.5281/zenodo.22981669](https://doi.org/10.5281/zenodo.22981669); version 1.5.0
[10.5281/zenodo.22982516](https://doi.org/10.5281/zenodo.22982516); version 1.6.0
[10.5281/zenodo.23000177](https://doi.org/10.5281/zenodo.23000177); version 1.7.0
[10.5281/zenodo.23000178](https://doi.org/10.5281/zenodo.23000178); version 1.7.1
[10.5281/zenodo.23002935](https://doi.org/10.5281/zenodo.23002935); version 1.8.0
[10.5281/zenodo.23004801](https://doi.org/10.5281/zenodo.23004801); version 1.9.0
[10.5281/zenodo.23043604](https://doi.org/10.5281/zenodo.23043604); version 1.10.0
[10.5281/zenodo.23045882](https://doi.org/10.5281/zenodo.23045882); version 1.11.0
[10.5281/zenodo.23070713](https://doi.org/10.5281/zenodo.23070713); version 1.12.0
[10.5281/zenodo.23200924](https://doi.org/10.5281/zenodo.23200924); version 1.13.0
[10.5281/zenodo.23272267](https://doi.org/10.5281/zenodo.23272267); version 1.14.0
[10.5281/zenodo.23989248](https://doi.org/10.5281/zenodo.23989248); version 1.15.0
[10.5281/zenodo.24039349](https://doi.org/10.5281/zenodo.24039349); version 1.16.0
[10.5281/zenodo.24048983](https://doi.org/10.5281/zenodo.24048983); version 1.17.0
[10.5281/zenodo.24091026](https://doi.org/10.5281/zenodo.24091026); version 1.18.0
[10.5281/zenodo.24116516](https://doi.org/10.5281/zenodo.24116516); version 1.19.0
[10.5281/zenodo.24150853](https://doi.org/10.5281/zenodo.24150853); version 1.20.0
[10.5281/zenodo.24201129](https://doi.org/10.5281/zenodo.24201129); version 1.21.0
[10.5281/zenodo.24321346](https://doi.org/10.5281/zenodo.24321346); version 1.22.0
[10.5281/zenodo.24352560](https://doi.org/10.5281/zenodo.24352560); version 1.23.0
[10.5281/zenodo.24370025](https://doi.org/10.5281/zenodo.24370025); version 1.24.0
[10.5281/zenodo.24399110](https://doi.org/10.5281/zenodo.24399110).

> **Verification status (version 1.25.0, 22 November 2026).** No human
> mathematician has reviewed these papers. All twenty-seven papers are formalized
> completely: Paper 1 in its version 3, Papers 2, 3, 4, 5, 6, 7 and 8 in their
> versions 2, Papers 10 and 13 in their versions 2, and Papers 9, 11, 12 and 14 to 27. Every mathematical result in them has a Lean
> proof, checked against independently reviewed and frozen statement files. In
> Paper 11, Remark 1, which derives its answer from a lemma of Conde, Dratman
> and Grippo, is not formalized; it is not needed for Theorem 1, the paper's
> only result, which is formalized. In Paper 12, the frozen statements say
> that an example exists; that the example is simple, that its form is
> non-degenerate and that its fusion law is graded are proved in Lean about
> the algebra of the paper, but are not part of the frozen statements. In Paper 13
> the formal result is the uniqueness asked for in the question, for every
> `k ≥ 4`; that `K_{k+1}` itself has exactly `(k+1)!/(2k)` such cycles is
> formalized only for `k ≤ 7`. In Paper 14, four remarks that the paper marks
> as written arguments (on transitive actions, a corrected bound, a second
> reading of the preprint's definition of `δ`, and a smaller variant of the
> family of Theorem 3) are not formalized; they are not needed for its three
> theorems, which are formalized. In Paper 15, the formal result is Theorem 1;
> Corollary 2 (when one ordering attains the largest contribution of every
> coordinate at once) also uses Yuan's formula for a single coordinate, which
> is not formalized. In Paper 16, the frozen statements are Theorem 1 and
> Corollary 1, the latter in the form of Conjecture 3.9 of the source
> (`k < j < 2k`); the bound of Theorem 2 is proved in Lean on the way, but is
> not one of the frozen statements, and the assertion `r(S) ∈ L(S)` of
> Remark 2 and the finiteness of `L(S)` are not formalized; they are not
> needed for Theorem 1 and Corollary 1. In Paper 17, the bound 5 on the
> maximum degree of the trees (Remark 1) is a written argument and is not
> formalized, and the last sentence of its Theorem 1 (the trees have pairwise
> different independence polynomials) is derived in the paper from the formal
> statement and is not stated separately in Lean. In Paper 18, the three
> remarks of Section 5 (the whole set `W(y)` under Chen's necessary
> condition, the invariant parking assortments in the equality case, and the
> cost of computing `W(y)`) are written arguments and are not formalized;
> they are not needed for its Theorems 1 and 2, which are formalized. In
> Paper 19, the frozen statements are the three parts of Theorem 1 (the
> conjecture of Vojtěchovský and Yang); the classification of Theorem 2 is
> proved in Lean on the way, but is not one of the frozen statements. In
> Paper 20, the deduction of Corollary 1 from Theorem 1 is a few lines of
> text and is not a separate Lean statement. In Paper 21, Lean proves that
> the simplex lies outside a family `Generated`; that this family contains
> every polytope of the equality list of Conjecture A of Codenotti, Santos
> and Schymura (Lemma 4) is a written argument, and so are the remarks of
> its Section 5. In Paper 22, the consequences for the conjectures of
> Bailey and Anderson (Section 4) combine the Lean result with published
> theorems and are not formalized, nor is the remark that the terrace is not
> directed (Remark 1). In Paper 23, the frozen statements are
> limits as `m → ∞`; no explicit bound for a fixed `m` is claimed, and the
> comparison with the bounds of Rather (Remark 1), the numerical values, the
> examples of `(c, s)` other than `K_2` and the consequence `M_m/log m → ∞`
> are not formalized. In Paper 24, the matching lower bound is claimed only
> along subsequences of widths, as in its frozen statement; the two-row
> criterion for tileability is proved in Lean on the way, but is not one of
> the frozen statements; Corollary 1 (the case `k ≤ 8`) is not a separate Lean
> statement, and the computed small values (Remark 1 and Table 1) are not in
> Lean. In
> Paper 25, the Lean statements cover dimension `d ≥ 3`; the positive answer
> to Problem 3 for `d ≤ 2` is a result of the source, and the periodicity
> remark and the remarks of Section 6 (on Remark 2.21 of the source) are not
> formalized. In Paper 26,
> the frozen statements are Theorem 1 (Conjecture B of González Merino and
> Schymura, as stated by Codenotti, Santos and Schymura) and Theorem 2
> (Conjecture C of Codenotti, Santos and Schymura); Theorem 2′, a form with
> Lebesgue measures of the projected sets, is also proved in Lean but is
> not a frozen statement; Corollary 3, the d/2 bound of Conjecture A for
> every non-hollow lattice polytope, follows by published arguments of
> Codenotti, Santos and Schymura and is not formalized, nor are the remarks
> of Section 5 and the independence of the projected volumes from the choice
> of projection (Lemma 11); the equality clause of Conjecture A is false
> (Paper 21). In Paper 27, the frozen
> statements are Theorem 1 (the whole set of integer group determinants of
> the Heisenberg group of order 125) and Corollary 1 (the least positive
> value divisible by 5, stated and verified separately, before Theorem 1);
> Corollary 2 (the exponent 33) follows from Theorem 1 in two lines and is
> not a separate Lean statement, and Remark 1 (on the density of the
> visible primes, with a numerical observation) and Lemma 2 (not needed for
> Theorem 1) are not formalized. For
> Paper 2 this includes the existence and uniqueness of the normalized series
> and their first terms. It does not include what the paper says about the OEIS
> entries and the literature: no Lean statement mentions the OEIS, and the
> agreement with further terms of the b-files is checked numerically. In
> Paper 1, Proposition 31 is proved as an implication, and its three conditions
> are proved, for every exponent `a ≥ 3` of the prime 3, at the points `(3, q)`
> with `q` an odd prime other than 3; the statement that they hold at every point
> of both of its regions for every `a ≥ 3` is not proved. The equal-parity
> conjecture of Paper 1 (Conjecture 14) is proved, with Lean proofs, when
> `min(a, b) ≤ 2` or one of the primes is 3. For the remaining orders (primes
> `p, q ≥ 5` and `min(a, b) ≥ 3`) it follows from Theorem A of Jiang and Yang
> (arXiv:2610.36883), whose proof we have not reviewed and which is not
> formalized; only on that condition does it hold for all distinct odd primes.
> Our protocol requires independent statement
> review and freezing before proof development; Paper 8 records an exception
> to this order in its development timeline, versions 2 of Papers 5 and 6
> reuse Lean code of version 1 that was written before their statement files
> (for two lemmas of Paper 5 and for the codewords of Theorem A of Paper 6),
> the statements of version 2 of Paper 2 were written after that paper
> and its version 1 Lean proofs, and version 2 of Paper 1 reuses the proofs of
> 29 of its 51 statements, written in September 2026 against an earlier frozen
> statement file (these statements are unchanged in the files of version 2), and
> older Lean modules (`lean/Research/ICG*.lean`), which were written in
> September 2026 before any statement file. The proofs of version 3 of Paper 1
> were found after its main statement had been frozen; we do not claim this order
> for its six auxiliary statement files, which are not hypotheses of the main
> statement. The proof files of Paper 11 were drafted while its statement file
> was under independent review, before it was frozen; the statement file was not
> changed to fit them. In
> Paper 7, one frozen statement turned out to be false because of a missing
> pair of parentheses; the author approved this one correction, and the
> statement files were reviewed and frozen again.
> Computations are checked by the Lean kernel, and only
> the three standard axioms are allowed. Versions 2 of Papers 1, 3, 4, 5, 6, 7
> and 8 removed the claims that could not be formalized completely. Problems
> found so far are listed under
> [Known issues](#known-issues); every problem we worked on, including the
> ones we dropped, is listed in [ATTEMPTS.md](ATTEMPTS.md).

## Index

| | What | Status | Main Lean declarations | Where |
| --- | --- | --- | --- | --- |
| Paper 1 (version 3) | Maximal energy of integral circulant graphs of order `p^a q^b` when one prime is 3 or one exponent is at most 2: the orders `p^(2r)·3^(2s+1)`, `pq^m` and `p²q^b`; for exponents of equal parity, every order `p^a q^b` with `min(a,b) ≤ 2`, and every order in which one of the primes is 3 | new theorems; version 3 adds the orders of equal parity in which one of the primes is 3 (no bound on the exponents or on the other prime); the computer-assisted results of version 1.5 (Theorem 5 for `3 ≤ min(a,b) ≤ 8`, Proposition 15) were withdrawn in version 2; completely formalized (not checked with comparator, see below) | `CodexPaper1.check_Theorem2`, `check_Theorem4`, `check_Theorem5MinTwo`, `check_Proposition31` (51 checked statements of version 2); `CodexPaper1.TaskE.check_SameParityThree` (version 3) | [`papers/icg-q3-general`](papers/icg-q3-general/note.pdf) |
| Paper 2 (version 2) | Hanna's OEIS congruence conjectures: eleven proved, three more resolved | proofs; several follow quickly from classical results (stated since version 1.2.1); completely formalized, without the identification with the OEIS entries (not checked with comparator, see below) | `BackfillPaper2.Check.check_Thm4`, `check_Thm5_1`, `check_Thm12_firstFailure`, `check_EX_A389472` (84 checked statements) | [`papers/oeis-hanna`](papers/oeis-hanna/note.pdf) |
| Paper 3 (version 2) | A negative answer to a question of Carenini on almost independent sets in regular graphs | new theorems (counterexamples and an asymptotic result); completely formalized | `BackfillPaper3.Check.check_AnswerNegative`, `check_TheoremA`, `check_TheoremD`, `check_PropositionC` (60 checked statements) | [`papers/carenini-almost-independent`](papers/carenini-almost-independent/note.pdf) |
| Paper 4 (version 2) | Answers to three problems of Hak, Kozerenko and Oliynyk on the triameter of graphs | Problems 1 and 3 answered (we found no earlier answer); Problem 2 was first answered on MathOverflow, and we add its smallest counterexample; completely formalized | `BackfillPaper4.Check.check_TheoremA_i`, `check_TheoremA_unique`, `check_TheoremB_unique`, `check_TheoremC_ii` (50 checked statements) | [`papers/hko-triameter`](papers/hko-triameter/note.pdf) |
| Paper 5 (version 2) | Complete mappings of the Brauer and partial Brauer monoids | Problem 15.11 of arXiv:2608.25092 settled in its existence reading; completely formalized | `CodexPaper5.MainABCheck.check_Thm11a`, `check_Thm11b`, `CodexPaper5.MainCCheck.check_Thm11c`, `CodexPaper5.FullPaperAllNCheck.check_AllNClassification` (45 checked statements) | [`papers/brauer-complete-mappings`](papers/brauer-complete-mappings/note.pdf) |
| Paper 6 (version 2) | Fourteen new weights of the Reed–Muller code RM(7,14) | 14 new weights by explicit codewords; explicit codewords for every even number from 320 to 2^14 − 320 except 322, 326, 330, 334 and their complements, so, in the middle-interval reading of Carlet's question, the question for (7,14) is equivalent to these four numbers being weights (later, Lou and Wang, arXiv:2610.36687, state that they are not); Theorem C (Conjecture 2 of Lou and Wang fails for m = 6) was proved earlier by Lou and Wang; completely formalized | `Paper6FinalPackageV4.check_ThmA`, `check_ThmB_witnesses`, `check_CarletEquiv`, `check_ThmC_literal` (35 checked statements) | [`papers/rm714-weights`](papers/rm714-weights/note.pdf) |
| Paper 7 (version 2) | The minimum order of a counterexample to a conjecture on integral generalized sun graphs | new result: the minimum order is 42, and the counterexample with 42 vertices is unique; completely formalized (not checked with comparator, see below) | `Paper7FinalPackage.final_Theorem1`, `final_Theorem1MinOrder`, `final_Theorem2`, `final_Proposition3` (58 checked statements) | [`papers/sun-graphs`](papers/sun-graphs/note.pdf) |
| Paper 8 (version 2) | The switching conjecture for main eigenvalues holds for trees of diameter at most 4 | new theorem; completely formalized, including the finite search | `BackfillPaper8.Check.check_Theorem1`, `check_Theorem1_mathlib`, `check_Theorem1_signed` (38 checked statements) | [`papers/switching-diam4`](papers/switching-diam4/note.pdf) |
| Paper 9 | A simple primitive axial algebra with a disconnected non-annihilation graph, and a decomposable axial block | new theorems (counterexamples when arbitrary finite symmetric fusion laws are allowed); completely formalized | `AxialMSZ.Check.check_TheoremA`, `check_TheoremB`, `check_TheoremC`, `check_Corollary`, `check_not_Simple_connected` | [`papers/axial-nonannihilation`](papers/axial-nonannihilation/note.pdf) |
| Paper 10 (version 2) | Tensor products of Mycielskians of odd cycles with odd wheels and with extended Mycielskians of odd cycles are not word-representable | Problems 5.1, 5.2 and 5.3 of arXiv:2609.20881 answered (we found no earlier answers); completely formalized; the proof of Theorem 3 rests on a finite check carried out by the Lean kernel; Theorem 3 not checked with comparator (see below) | `WordRepTensor.Check.check_Problem5_1`, `check_MycielskiOddCycleNotWR`, `WordRepTensor.TaskF.Proof.check_Problem5_2`, `check_Problem5_3` (13 checked statements) | [`papers/wordrep-tensor`](papers/wordrep-tensor/note.pdf) |
| Paper 11 | Connected cographs with distance eigenvalues just below −2 | a short note: part (i) of an open problem in the survey arXiv:2611.06981 answered (no); the same graphs were used earlier by Conde, Dratman and Grippo (arXiv:2606.06052) for the adjacency matrix, and the answer also follows in a few lines from their lemma; completely formalized, except Remark 1, the derivation from their lemma (not checked with comparator, see below) | `CographDist.Audit.check_OpenProblemI_negative`, `check_family` | [`papers/cograph-distance`](papers/cograph-distance/note.pdf) |
| Paper 12 | An axial algebra whose automorphism group does not preserve its Frobenius form: an answer to a question of Shpectorov | a short note: Shpectorov's question (Problem 3.3 of the survey arXiv:2606.30048v1, Problem 2.3 of its journal version) answered (yes) by a 4-dimensional example over the field with 11 elements, with a 1-dimensional space of Frobenius forms; the fusion law is chosen for the example and is not of Jordan or Monster type; completely formalized (not checked with comparator, see below) | `TaskG.Check.check_ShpectorovAnswer`, `check_StrongShpectorovAnswer` | [`papers/axial-frobenius`](papers/axial-frobenius/note.pdf) |
| Paper 13 (version 2) | Critical graphs with the fewest cycles of length 0 modulo k | answer: Question 8 of Choi and Sieniawski (arXiv:2611.13580v1) answered yes for every `k ≥ 4` (`K_{k+1}` is the only `(k+1)`-critical graph with exactly `(k+1)!/(2k)` cycles of length 0 modulo `k`); version 1 (v1.21.0) covered `k = 4, 5, 6, 7`; completely formalized (not checked with comparator, see below) | `TaskH.original_question_two_all_k` | [`papers/critical-cycles-mod-k`](papers/critical-cycles-mod-k/note.pdf) |
| Paper 14 | On the rank of groups of equivariant permutations: a counterexample to an upper bound | Theorem 4 of Lara-Gómez, Romero-Rosales and Ruiz-Medina (Semigroup Forum, published online 2 November 2026; the right-hand side of Theorem 5 of arXiv:2607.04053v1), an upper bound for the rank of the group of `G`-equivariant permutations of a finite `G`-set, fails for the group of order 2 acting on two points; a five-point example and, for every `n ≥ 3`, a cyclic action show that their packet expression, which they expected to be the exact rank, can exceed the rank by any amount (their own 21-point example already shows that it is not always exact); completely formalized, except four remarks marked as written arguments (not checked with comparator, see below) | `TaskJ.Rank.check_TwoPointCounterexample`, `check_FivePointCounterexample`, `TaskJ.Rank.Extension.check_UnboundedGap` (7 checked statements) | [`papers/equivariant-rank`](papers/equivariant-rank/note.pdf) |
| Paper 15 | The maximum Manhattan length of a path through all lattice points of a box | answer to the first open question of §6.3 of Yuan (arXiv:2611.19908v1): the exact maximum for every box with positive integer sides, in every dimension, with orderings attaining it; with at least three sides larger than 1, the gap to Yuan's coordinatewise bound is 1 when all sides are odd and `2^(e−1) − 1` when `e ≥ 1` sides are even, the expression Yuan had suggested from computed data; the hypercube, the plane and closed circuits on equal-sided cubes were treated earlier (see below); completely formalized, except Corollaries 1 and 2 (Corollary 2 uses Theorem 2.3 of Yuan) (not checked with comparator, see below) | `check_LengthUpperBound`, `check_LengthAttained`, `check_YuanGapAtLongest` | [`papers/lattice-box-paths`](papers/lattice-box-paths/note.pdf) |
| Paper 16 | The decomposition lengths of a numerical semigroup form an interval | answer: Conjecture 1.1 of García-Sánchez and O'Neill (arXiv:2602.00404v1), that the lengths of the irredundant decompositions of a numerical semigroup into irreducible numerical semigroups form an interval, proved for every numerical semigroup (they had proved it for multiplicity at most 6), and their Conjecture 3.9 on even multiplicity, through a decomposition with at most `k` components when the multiplicity is `2k`; the tools used (special gaps, an exchange of Blanco and Rosales, a bound of Rosales and Branco) are earlier work (see below); completely formalized, except Remark 2 (`r(S) ∈ L(S)`) and the case `j ≥ 2k` of Corollary 1; the bound for even multiplicity is proved in Lean but is not a frozen statement (not checked with comparator, see below) | `TaskL.Semigroup.check_LengthsExist`, `check_LengthsInterval`, `check_EvenMultiplicityDescent` (4 checked statements) | [`papers/numerical-semigroup-lengths`](papers/numerical-semigroup-lengths/note.pdf) |
| Paper 17 | Arbitrarily large antichains of trees of equal order in the independence polynomial order | answer: Question 6 of Beaton and Cameron (Open J. Discrete Appl. Math. 5 (2022); Question 5.3 of arXiv:2006.05511v2) answered yes: for every `n ≥ 11` there are `⌊n/11⌋ + 1` trees on `n` vertices that are pairwise incomparable in Csikvári's order `⪯` by the independence polynomial (Beaton and Cameron had given pairs of incomparable trees at infinitely many orders); completely formalized, except the bound 5 on the maximum degree (Remark 1); the last sentence of Theorem 1 is derived in the paper and is not a separate Lean statement (not checked with comparator, see below) | `TaskN.Antichain.check_WidthLowerBound`, `check_ArbitrarilyLarge` | [`papers/tree-antichains`](papers/tree-antichains/note.pdf) |
| Paper 18 | The equality case of Chen's bound for invariant parking with one special preference | answer: a necessary and sufficient condition for equality in Theorem E(b) of Chen (arXiv:2311.15699v1), the bound `2^(n−1)` for the number of elements of `W(y)`, for every number of cars; it closes the gap between his sufficient condition E(c) and his necessary condition E(d), which his Remark 4.7 shows is not sufficient (Chen does not list this among his open problems); also, for a fixed tail, the number of first-car lengths that attain equality; the bound, the necessary condition and the gap reduction are earlier work (see below); completely formalized, except the three remarks of Section 5, marked as written arguments (not checked with comparator, see below) | `TaskN.Parking.check_ExtremalClassification`, `check_FirstLengthCount` | [`papers/variable-length-parking`](papers/variable-length-parking/note.pdf) |
| Paper 19 | Medial racks and quandles of prime order: a proof of a conjecture of Vojtěchovský and Yang | answer: Conjecture 6.5 of Vojtěchovský and Yang (Math. Comp. 88 (2019)) proved for every prime `p`: the medial racks of order `p` exceed the 2-reductive ones by exactly `p − 2` isomorphism classes, the same holds for quandles, and every medial rack of order `p` that is not 2-reductive is a quandle; connectedness and idempotence are not assumed (the classification of connected quandles of prime order, due to Etingof, Soloviev and Guralnick, is earlier work, see below); completely formalized; the classification behind it (Theorem 2) is proved in Lean but is not a frozen statement (not checked with comparator, see below) | `TaskP.PrimeMedialRacks.check_RackCount`, `check_QuandleCount`, `check_AutomaticIdempotence` | [`papers/prime-medial-racks`](papers/prime-medial-racks/note.pdf) |
| Paper 20 | The generalized Wilf conjecture for semigroups graded by a two-generated numerical semigroup | answer: the generalized Wilf conjecture holds for every `T`-graded generalized numerical semigroup with `T = ⟨a, b⟩`, in every dimension, the class that Cisto and Navarra (An. Ştiinţ. Univ. Ovidius Constanţa 33 (2025), §6) left open for `a > 2`; new only for dimension `d ≥ 3`, `a ≥ 3` and the parameters not covered by Theorem 5.6 of Bhardwaj, Cisto and Deshpande (arXiv:2611.20086v1), the other cases being known (see below); completely formalized (not checked with comparator, see below) | `TaskP.GradedWilf.check_Wilf` | [`papers/graded-wilf`](papers/graded-wilf/note.pdf) |
| Paper 21 | A non-hollow lattice 4-simplex of covering radius 2 outside the equality list of a conjecture of Codenotti, Santos and Schymura | answer (counterexample): the 4-simplex `conv{e_1, e_2, e_3, e_4, −(2,1,1,1)}`, known from toric geometry, has covering radius exactly `2 = d/2` and normalized volume 6, and is not obtained by direct sums and lattice translations of standard terminal simplices, so the "only if" part of the equality clause of Conjecture A (Discrete Comput. Geom. 67 (2022)) fails in dimension 4; the inequality of Conjecture A and Conjecture C are not refuted; completely formalized, except Lemma 4 (that the family excluded in Lean contains the equality list) and the remarks of Section 5 (not checked with comparator, see below) | `TaskR.CSS.check_NonHollow`, `check_Radius`, `check_Volume`, `check_OutsideList` | [`papers/css-covering-equality`](papers/css-covering-equality/note.pdf) |
| Paper 22 | A terrace for the alternating group `A_7` | new verified case: an explicit terrace of `A_7` (order 2520), a group that none of the terraced families listed in Ollis's 2025 survey is known to contain, apart from an asymptotic theorem without explicit bound; with a theorem of Anderson and Ihrig it gives symmetric sequencings for the binary groups of the `A_7` branch of their reduction; Bailey's conjecture and Anderson's conjecture are not settled, and the terrace is not directed, so whether `A_7` is sequenceable remains open; completely formalized, except Remark 1 (the terrace is not directed) and the consequences of Section 4 (not checked with comparator, see below) | `TaskR.A7.check_HasTerrace` | [`papers/a7-terrace`](papers/a7-terrace/note.pdf) |
| Paper 23 | The largest domination roots of friendship graphs and of joins with repeated petals | answer, in a sharp asymptotic sense, to Question 3.2 of Alikhani, Brown and Jahari (Filomat 30 (2016)) on the modulus of the domination roots of friendship graphs: for `K_a ∨ mB` the largest modulus of a domination root is attained and is asymptotic to `(c s m/(a log m))^(1/c)`, where `c = 1 + δ(B)` and `s` counts the distinct closed neighbourhoods of size `c`; for friendship graphs `√(2m/log m)`; the upper half for friendship graphs already follows from an implicit bound of Rather (arXiv:2604.08998), and the new parts are the matching lower bound and the general family; no explicit bound for a fixed `m` (see below); completely formalized, except the comparison with Rather's bounds, the numerical values and the examples of `(c, s)` other than `K_2` (not checked with comparator, see below) | `TaskP.GraphRootRadius.check_Attainment`, `check_GeneralAsymptotic`, `check_FriendshipAsymptotic` | [`papers/domination-root-radius`](papers/domination-root-radius/note.pdf) |
| Paper 24 | Multisets of bars that do not tile a `2 × n` rectangle: the optimal growth order | answer to the question of Remark 5.11 of Gajdzica, Visser and Zakarczemny (Ann. Comb., 2026) in the sense of the optimal polynomial order: the number of multisets of bars of lengths at most `k` and total area `2n` that do not tile the `2 × n` rectangle is 0 for `k ≤ 2` and `O(n^(e_k))` for `k ≥ 3`, `e_k = max(0, ⌊k/2⌋ − 2)`, and the exponent cannot be lowered; the lower bound is claimed only along subsequences of `n`; completely formalized, the specialization to `k ≤ 8` and the computed values excepted (not checked with comparator, see below) | `TaskP.RectangleDefect.check_SharpBound` | [`papers/bar-tiling-defect`](papers/bar-tiling-defect/note.pdf) |
| Paper 25 | Lattice simplices whose Minkowski length exceeds the lattice diameter, and dilates whose Minkowski length is not quasi-linear | answer (counterexamples) to Problems 2 and 3 of Soprunov and Soprunova (European J. Combin. 58 (2016)): a lattice tetrahedron with lattice diameter 1 and Minkowski length 2, and an empty tetrahedron `U` with `L(U) = 1` and `L(tU) = 3t` for `t ≥ 2`, carried to every dimension `d ≥ 3` by lattice pyramids; with the known case `d ≤ 2`, Problem 3 is true for `d ≤ 2` and false for every `d ≥ 3`; both tetrahedra are known objects (see below); Problem 1 is not addressed; completely formalized for `d ≥ 3`, except the periodicity remark and the remarks of Section 6 (not checked with comparator, see below) | `TaskP.GeomSimplex.check_TetrahedronDiameter`, `check_TetrahedronDilations`, `check_EveryDimensionDiameter`, `check_EveryDimensionDilations` | [`papers/minkowski-length-simplices`](papers/minkowski-length-simplices/note.pdf) |
| Paper 26 | Covering minima of the standard terminal simplex and a discrete surface area bound for the covering radius of simplices | answer: Conjecture B of González Merino and Schymura (Discrete Comput. Geom. 58 (2017); Conjecture B of Codenotti, Santos and Schymura), `μ_i(T_n) = i/2` for all `1 ≤ i ≤ n`, proved (known before for `i ≤ 3`, `i = n` and `i = 1`), and Conjecture C of Codenotti, Santos and Schymura (Discrete Comput. Geom. 67 (2022)), the discrete surface area bound for simplices with the origin in the interior and rational vertex directions, proved in every dimension (known for `d ≤ 2` and up to a constant factor); by published arguments of these authors either gives the d/2 bound of Conjecture A for non-hollow lattice polytopes (not formalized; the equality clause of Conjecture A is false, Paper 21); the averaging lemma is elementary and claimed as no novelty; completely formalized, except Corollary 3, Section 5 and Lemma 11 (the independence of the projected volumes from the choice of projection); two independent final reviews per conjecture (not checked with comparator, see below) | `TaskS.B.check_ConjectureB`, `TaskS.C.check_conjectureC`, `TaskS.C.MeasureModel.measured_conjectureC` | [`papers/css-covering-minima`](papers/css-covering-minima/note.pdf) |
| Paper 27 | The integer group determinants of the Heisenberg group of order 125 | answer: Olga Taussky-Todd's integer group determinant question for the Heisenberg group `H_5` of order 125, whose multiples of 5 Mossinghoff and Pinner (Michigan Math. J. 74 (2024)) had left undetermined: the whole value set `S(H_5)` consists of the integers `m` with `m^4 ≡ 1 (mod 125)` (their result), all multiples of `5^33`, and the integers `5^28·n` with `n ≠ 0` divisible by a visible prime (a prime `ℓ ≡ 1 (mod 5)` for which an element of norm `ℓ` in `Z[ζ_5]` is not congruent modulo 5 to a unit); the least positive value divisible by 5 is `11·5^28`; the factorization, the values prime to 5 and the bound `5^28` are due to Mossinghoff and Pinner, and the seeds of the constructions to Panraksa (see below); completely formalized, except Corollary 2 (a two-line deduction), Remark 1 and Lemma 2 (not needed for Theorem 1); one final review of the minimum and two independent final reviews of the classification (not checked with comparator, see below) | `TaskU.H5.Check.check_witnessValue`, `TaskU.H5.Check.check_leastPositiveMultiple`, `TaskU.H5.check_fullSpectrum` | [`papers/heisenberg-125-determinants`](papers/heisenberg-125-determinants/note.pdf) |
| Also | A246056 and A376230: Lean proofs of results that follow from published theorems | formalizations of known results | `HannaA246056.*`, `HannaA376230.*` | see below |
| Also | Case q = 3 of Roldán's Conjecture 1.3 (order `27p²`) | formalization of a known result | `ICGBridge.roldan_q3` and related | see below |

**Paper 1: [`papers/icg-q3-general`](papers/icg-q3-general/note.pdf) (version 3).**
*The maximal energy of integral circulant graphs of order p^a q^b when one prime is 3 or one exponent is at most 2.* (Until version 2 the title was *The maximal energy of integral circulant graphs of orders p^(2r)·3^(2s+1), pq^m and p²q^b*.)

> **Version 3 (version 1.17.0).** Version 3 extends Theorem 5 to every order
> `p^a q^b` of equal parity in which one of the primes is 3, with no bound on
> the exponents or on the other prime. The new Section 13 (statements 32–43)
> proves this case by verifying, for the prime 3, every exponent and every
> other odd prime, the conditions (S_a), (F_a) and (C_a) of Proposition 31,
> the conditional reduction of version 2, and applying it at each such point.
> The main statement, `SameParityThree`, was frozen on 8 November 2026 after
> an independent review, and its Lean proof was written after that. The
> statements of version 2 keep their numbers, and their proofs are unchanged;
> the section on formal verification is now Section 14. The title is
> unchanged. Version 2 remains available in release v1.16.0 and on Zenodo.
> The changes are listed at the end of Section 14 of the paper and in
> [ATTEMPTS.md](ATTEMPTS.md).
>
> **Version 2 (version 1.16.0).** All the mathematics of this paper is proved in
> Lean 4: the 51 statements (31 main and 20 supplementary) of statement files
> frozen on 7 November 2026, including the closed forms of `d_k` and `δ_k`,
> which version 1.5 did not formalize. Version 2 narrows the results on
> exponents of equal parity: Theorem 5 is now stated for `min(a, b) ≤ 2`, the
> other exponent being arbitrary, instead of `min(a, b) ≤ 8`. The case
> `3 ≤ min(a, b) ≤ 8` of Theorem 5, Proposition 15 and the certificates of
> Section 12 rested on computer calculations that have no formal proof, so
> they are withdrawn; the withdrawal does not report an error in those
> calculations. The number 15 is not used, and the other numbers are
> unchanged. Version 1.5 remains available in release v1.5.0 and on Zenodo,
> and its programs remain in `certificates/` as its records; version 2 does
> not use them. Statements about the literature are not formalized. The
> changes are listed under Corrections in [ATTEMPTS.md](ATTEMPTS.md).

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
- **Theorem 5 (version 3).** For distinct odd primes `p, q` and `a, b ≥ 1`
  with `a + b` even, if `min(a, b) ≤ 2` or one of `p, q` equals 3, the maximal
  energy for order `n = p^a q^b` is `½[n + d_a(p) d_b(q)] − δ_a(p) δ_b(q)`,
  attained exactly by the same two sets. For `min(a, b) ≤ 2` this is Theorem 3
  or 4 (version 2); the other exponent is arbitrary, and the prime 3 is
  allowed. New in version 3 is the case in which one of the primes is 3 and
  `min(a, b) ≥ 3`, proved in Section 13 with no bound on the other prime or on
  the exponents. With Theorems 1 and 2, the maximal energy and all maximisers
  are known for every order `p^a q^b` with `min(a, b) ≤ 2`, for every order
  `3^a q^b`, and for every order whose exponents have opposite parity.
  Version 1.5 stated Theorem 5 for `min(a, b) ≤ 8`, the case
  `3 ≤ min(a, b) ≤ 8` with computer assistance; version 2 withdrew that case
  and stated the theorem for `min(a, b) ≤ 2`.
- **Conjecture 14** (the equal-parity conjecture, stated in earlier
  versions) is proved in the paper, with Lean proofs, when `min(a, b) ≤ 2` or
  one of the primes is 3. The remaining orders, with `p, q ≥ 5` and
  `min(a, b) ≥ 3`, are covered by the statement of Theorem A of Jiang and Yang
  (arXiv:2610.36883v1). We have not reviewed its proof, it is not formalized,
  and nothing in the paper or its Lean proofs uses it. Only if it is correct
  does the conjecture hold for all pairs of distinct odd primes. No Lean
  statement depends on the conjecture.
- **Proposition 31** is a conditional reduction for larger exponents: if
  conditions (S_a), (F_a) and (C_a) hold, the inequality that the method of
  Theorem 4 needs follows for that exponent `a` and every `b` of the same
  parity. It is proved in Lean as an implication; its proof also gives the
  conclusion at each single point at which the conditions hold. Version 3
  proves, for every `a ≥ 3` of the prime 3: (S_a) on both regions of the
  proposition (`p ≥ 5, q ≥ 3` and `p = 3, q ≥ 5`, for real `p, q`), (C_a) at
  every point of the region `p = 3, q ≥ 5`, and (F_a) at the points `(3, q)`
  with `q = 5`, `q = 7` or real `q ≥ 8`, which covers every odd prime `q ≠ 3`.
  It does not claim (F_a) or (C_a) at any point of the region `p ≥ 5`, so the case
  `p, q ≥ 5`, `min(a, b) ≥ 3` is not proved; the statement that the three
  conditions hold at every point of both regions for every `a ≥ 3`
  (`UniformConditionsBothRegions` in Lean) is not proved and not claimed.
  Version 1.5 verified the conditions for `3 ≤ a ≤ 8` by computer; version 2
  withdrew that verification, and version 3 does not use it.
- **Later work.** After version 1.5, Jiang and Yang (arXiv:2610.36883v1,
  27 October 2026) stated the equal-parity formula and the same two
  maximisers for all distinct primes `p, q ≥ 5`, which contains Theorem 5 for
  those primes and `min(a, b) ≤ 2`; their statement does not include the
  prime 3, and the orders of equal parity with `min(a, b) ≥ 3` in which one of
  the primes is 3 are not covered by it. Theorem 5, in the form extended in
  version 3, treats them. We have compared the statements only; we have not
  reviewed their proof, and nothing in the paper or its Lean proofs uses it.
  The revision arXiv:2608.29523v2 (30 October 2026) still requires the primes
  with odd exponent to be at least 5. A Lean proof of Roldán's conjecture for
  the exponents (2,3), including `q = 3`, was merged in the trureturing
  repository on 20 October 2026
  ([pull request #19390](https://github.com/the-omega-institute/trureturing/pull/19390));
  it concerns only the case `r = s = 1` of Theorem 2.
- **Lean (version 2):** `lean/Research/Backfill/Paper1/` holds the four frozen
  statement and test files (`Challenge.lean`, `SupplementStatements.lean`,
  `ChallengeTests.lean`, `NarrowContractTests.lean`), the proofs and
  `FinalContractAudit.lean`, which restates each of the 51 statements with its
  frozen type, proves it by a theorem `CodexPaper1.check_X` and prints its
  axioms. The proofs also use 17 older modules `lean/Research/ICG*.lean`,
  written in September 2026 (13 of them differ from version 1.15.0 only in the
  names of three Mathlib lemmas). The declarations of version 1.5
  (`ICGGeneral.jiang_yang_q3`, `ICGEqualParity.corollaryA`,
  `ICGEqualParityB.theoremB` and others) remain. These 70 modules are
  unchanged in version 3, byte for byte.
- **Lean (version 3):** `lean/Research/TaskE/` holds 45 new modules (3356
  lines): the frozen main statement file `Challenge.lean` (`SameParityThree`),
  six frozen auxiliary statement files (`ChallengeS.lean`, `ChallengeF.lean`,
  `ChallengeFC.lean`, `ChallengeC0.lean`, `ChallengeC1.lean`,
  `ChallengeC1Alt.lean`; 20 intermediate steps of Section 13, which are not
  hypotheses of the main statement), seven tests (`StatementTests.lean`), 36
  proof modules and `FinalTaskEAudit.lean`. The main theorem is
  `CodexPaper1.TaskE.check_SameParityThree` (in `Main.lean`).
  `FinalTaskEAudit.lean` restates `SameParityThree`, the condition (C_a) at
  `(3, q)` for real `q ≥ 5`, (F_a) at the points above and (S_a) on both
  regions, checks two instances of the main statement and prints the axioms of
  the main theorem and its main lemmas. `C1High.lean` proves an auxiliary
  statement that the main theorem does not use. The statement files of version
  3 use only definitions of the statement file of version 2. Comments inside
  the proof modules are development notes of Codex and may be out of date.

**Paper 2: [`papers/oeis-hanna`](papers/oeis-hanna/note.pdf) (version 2).**
*Proofs of eleven congruence conjectures of Hanna from the OEIS, and the
resolution of three more.*

> **Version 2 (version 1.15.0).** All the mathematics of this paper is proved in
> Lean 4: the 84 statements of a statement file frozen on 5 November 2026,
> before these proofs were written. Besides the theorems and remarks, they
> cover the existence and uniqueness of the normalized solutions and their
> first terms, which version 1 only checked numerically. No Lean statement
> mentions the OEIS: that a series is the sequence of an entry rests on the
> entry's definition by the same equation, and the agreement with further
> b-file terms rests on the numerical checks. The attributions to other
> authors are not formalized. The theorems are unchanged; the changes to the
> text are listed under Corrections in [ATTEMPTS.md](ATTEMPTS.md).

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

**Paper 3: [`papers/carenini-almost-independent`](papers/carenini-almost-independent/note.pdf) (version 2).**
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
  the `(1 + o(1))` form for fixed `d` and `0 < γ < 1/8` (version 2 makes no
  claim at `γ = 1/8`).
- Lean: every result of Paper 3 (version 2) is formalized. The 60 statements
  of the frozen statement file `lean/Research/Backfill/Paper3/Challenge.lean`
  (SHA-256 `846efb56…8777`) are proved in `lean/Research/Backfill/Paper3/`
  (`Check.lean`), including Theorems A, B, B′ and D, Proposition C, the
  minimality of `(6,3,1/18)`, the class counts 2, 6 and 60 of Table 3 (via a
  formalized 2-switch theorem and kernel-checked certificates), the case of
  the theorem of Sah, Sawhney, Stoner and Zhao that the paper uses, the
  Kahn–Zhao theorem, and Lemma 8 without Cramér's theorem. The statements
  were written after the paper, reviewed independently and frozen (version 1
  on 27 September 2026, before any proof; version 2 on 29 September 2026 at
  01:31 UTC); the Lean proofs were written by Claude Code agents while
  Codex's usage quota had run out. Version 2 deletes two claims of version 1
  for which we have no formal proof: the normal approximation at `γ = 1/8`
  (Remark 10, with reading R6 at `γ = 1/8`) and the count of 19,355
  labelled 4-regular graphs on eight vertices. The module
  `lean/Research/Carenini.lean` of version 1 remains.

**Paper 4: [`papers/hko-triameter`](papers/hko-triameter/note.pdf) (version 2).**
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
  triametral triple `{1, 5, 6}` contains no peripheral vertex. Every median
  graph with at most seven vertices has (Q3′), and `G1` is the only 8-vertex
  exception up to isomorphism.
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
- **Version 2 (new in version 1.9.0) is formalized completely.** Every
  result of the paper is proved in Lean: the 50 statements of a statement
  file frozen before the Lean proofs were written
  (`lean/Research/Backfill/Paper4/`): Theorems A, B and C, including the
  minimality and uniqueness statements; Lemmas 1 and 2, Proposition 3 and
  Remarks 4 and 5; the counts of Section 4; and the two facts from Bandelt
  and Mulder that the proofs use (distance-hereditary graphs satisfy the
  four-point condition; a connected graph obtained from a
  distance-hereditary graph by attaching a pendant vertex or adding a twin
  is distance-hereditary), which version 1 only cited. OpenAI
  Codex wrote the proofs of 46 statements; the other four (the uniqueness
  statements of Theorems A and B, and the counts 1, 1, 1, 3, 4, 11, 23, 69
  and 1,008,904 of Section 4) were written by Claude Code while Codex's
  usage quota had run out. Version 2 also adds three hypotheses that
  version 1 omitted, and removes the computations of version 1 that were
  not formally verified (see Known issues). The Lean modules of version 1
  (`HKOTriameter.lean`, `HKOTriameterDH.lean`) remain in the repository.

**Paper 5: [`papers/brauer-complete-mappings`](papers/brauer-complete-mappings/note.pdf) (version 2).**
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
  principal factor of `PB_n`, except the rank-2 factor of `PB_3`, which is
  isomorphic to the Brandt semigroup `B(S_2, 3)` and has none. Hence `B_n`
  and `PB_n` have a complete mapping if and only if `n ∉ {2, 3}` (for every
  `n ≥ 0`).
- The new case is `B_n` with `n ≡ 2, 3 (mod 4)`, in which the number of
  half-diagrams of rank 2 (for `n ≡ 2`) or rank 3 (for `n ≡ 3`) is odd. For
  it the paper gives an explicit complete mapping, built from a triangle of
  half-diagrams and a perfect matching of the other half-diagrams. The other
  cases follow from special cases of results of Araújo et al. once the Rees
  structure of the principal factors is written down.
- Scope: "classify" is read as in the second sentence of Problem 15.11,
  that is, deciding existence for every factor and every monoid. The set of
  all complete mappings is not described.
- Lean: every result of Paper 5 (version 2) is formalized. The 33 statements
  of the frozen statement file `lean/Research/Backfill/Paper5/Challenge.lean`
  (SHA-256 `ca2ff711…c373`) and the 12 statements of three supplementary
  statement files frozen on 1 October 2026 (associativity of the product of
  diagrams and of Rees 0-matrix multiplication, the monoid structure of
  `B_n` and `PB_n`, the classification for every `n` including 0, the
  isomorphism of the groups `{(λ, g, λ)}` with `S_r`, Cayley tables, and the
  counts 45 and 105; two of the twelve are auxiliary statements about
  reachability) are proved in `lean/Research/Backfill/Paper5/`
  (`Check.lean`). Among them are Theorem 1.1, Proposition 3.1, Lemmas
  4.1–4.4, 5.1–5.4 and 6.1, Proposition 6.2, and the special cases (R1) and
  (R2) of results of Araújo et al. that the proofs use; the special cases
  (R3) and (R4) are proved inside the proof of Theorem 1.1(c). The
  statements were written after the paper, reviewed independently and
  frozen before the new proofs were written (the main file on 27 September
  2026). The proofs were written by OpenAI Codex; for Lemmas 4.3 and 4.4
  they reuse a copy of the Lean code of version 1 (`BrauerCMCore`, written
  by Claude Code before the statement file). Version 2 corrects the
  definition of `top(x)` and `bot(x)` in Section 3 (the error was found by
  Codex) and deletes the claims of version 1 for which we have no formal
  proof, among them the results of the computer checks of its Section 8, a
  remark comparing Lemma 4.4 with a criterion of Araújo et al., and the
  identifications with Green's relations. The module
  `lean/Research/BrauerCMCore.lean` of version 1 remains.

**Paper 6: [`papers/rm714-weights`](papers/rm714-weights/note.pdf) (version 2).**
*Fourteen new weights of the Reed–Muller code RM(7,14).*

- Leuenberger and Albrizzio (arXiv:2606.21425) showed that every even
  number from 312 to `2^14 − 312` is a weight of RM(7,14), except possibly
  22 values.
- **Theorem A.** 17 explicit weights, each given by a codeword with at most
  seven monomials, including 14 of those 22 values; these 14 are, to our
  knowledge, new. The other three, 4378, 4380 and 4382, are weights by
  Proposition 4 of arXiv:2606.21425 and are not new.
- **Theorem B.** Explicit codewords, each with at most eight monomials, for
  every element of `S₀`, 7901 numbers: the even numbers from 320 to 16064
  other than 322, 326, 330, 334 and their complements, together with the 18
  numbers below 320 that Leuenberger and Albrizzio list as weights and their
  complements. Version 1 also claimed that these, together with possibly
  some of 322, 326, 330, 334 and their complements, are all the weights of
  RM(7,14); that claim rested on the theorem of Kasami, Tokura and Azumi
  (1976), which we could not consult and have not formalized, and version 2
  deletes it (the title of version 1 is changed accordingly).
- **Corollary.** In the middle-interval reading of Carlet's question on the
  weight spectra of RM(m − c, m) used in the paper, every even number in
  [320, 16064] is a weight of RM(7, 14) if and only if 322, 326, 330 and 334
  are weights.
- **Theorem C.** Conjecture 2 of Lou and Wang is false for m = 6: no codeword
  of their construction (Construction 2 of arXiv:2406.03803v1, Construction 1
  of their later note) has weight 322. **This is not new:** Lou and Wang
  proved it in Discrete Appl. Math. 388 (2026) 142–145 (Proposition 2;
  online 4 April 2026), a note we could not read before publishing version 1;
  version 2 attributes it to them and gives a formalized proof. The extension
  of version 1 to arbitrary `g₁, g₂ ∈ RM(6,12)` used the weights of RM(6,12)
  below 160 from Kasami–Tokura(–Azumi) and is deleted.
- Propositions D and E show that no open weight occurs in two natural
  families of codewords (sums of at most three indicators of flats of
  dimension at least 7; sums of at most five monomials), and Proposition F
  reduces each of 322, 326, 330 and 334 to a question about RM(6,13) and
  RM(7,13). Proposition C′ of version 1 and the heuristic searches of version
  1 are deleted.
- Later work (after version 1.13.0 of 9 October 2026): Y. Lou and Q. Wang
  (arXiv:2610.36687v1, 27 October 2026) state in their abstract that they
  exclude the eight conjectured weights of RM(7,14), which we read as 322,
  326, 330, 334 and their complements (the abstract does not list them), and
  determine the weight spectrum of RM(m − 7, m) for all m ≥ 14. With the Corollary, their
  result answers Carlet's question for (7,14), in the middle-interval reading,
  in the negative. Z. Wei, B. Zhou, X. Zhang and H. Chen (arXiv:2610.29807v1,
  21 October 2026) show that for all m ≥ 14 every even number in
  [336, 2^m − 336] is a weight of RM(m − 7, m), and study the four values in
  restricted families of codewords. We have not reviewed these proofs, and
  they are not formalized here; the paper (version 2) still describes the four
  values as open.
- Lean: every result of Paper 6 (version 2) is formalized. The 35 statements
  of the frozen statement files `lean/Research/Backfill/Paper6/ChallengeV3.lean`
  (SHA-256 `83ea2291…b6d78`) and `BridgeChallenge.lean` are proved in
  `lean/Research/Backfill/Paper6/` (`CheckPaper6.lean`): Theorem A and
  Table 1, the 7901 codewords of Theorem B, the Corollary, Theorem C,
  Propositions D, E and F, Lemmas 2.1, 2.2 and 5.1, Remark 3.1, (P1)–(P3)
  and the other preliminary facts the proofs use. The main statement file
  was written after the paper, reviewed independently and frozen before the
  proofs were written (36 statements on 6 October 2026; one statement, the
  five numbers of the enumeration of version 1, deleted on 7 October 2026
  because its kernel certificates would have taken about a week, and the
  file frozen again); the proofs were written by OpenAI Codex. Version 2
  deletes every claim of version 1 that rests on the theorems of Kasami and
  Tokura (1970) or Kasami, Tokura and Azumi (1976): the determination of the
  spectrum, (P4a), (P4b), Lemma 4.1, Proposition C′, the extension of Theorem
  C, and the statement that the weights below 320 of sums of five monomials
  are exactly the known list; it states the hypothesis `r ≥ 1` in (P2) and
  no longer reports the computations and searches of version 1. The module
  `lean/Research/RM714Weights.lean` of version 1 remains: the statement
  `Sec7Bridge` identifies its notion of weight with the one defined in the
  statement file, and the proof of Theorem A reuses its codeword lists and
  definitions and checks their weights again in the kernel (that module was
  written before the statement files).

**Paper 7: [`papers/sun-graphs`](papers/sun-graphs/note.pdf) (version 2).**
*The minimum order of a counterexample to a conjecture on integral generalized
sun graphs.*

- A graph is integral if its adjacency eigenvalues are integers; a
  generalized sun graph is a cycle with pendant paths attached. Braga,
  Del-Vecchio and Rodrigues conjectured that the cycle of an integral
  generalized sun graph that is not a cycle has length divisible by 4.
  Braga, Moraes and Santos (arXiv:2609.28754) disproved this with the graph
  `C_{6,1}(0,6,6,12,6,6)` on 42 vertices and remarked that their search does
  not show that no smaller counterexample exists.
- **Theorem 1.** Up to isomorphism, `C_{6,1}(0,6,6,12,6,6)` is the only
  counterexample with at most 42 vertices, also when pendant paths of
  different lengths share a vertex. So 42 is the minimum order.
- **Theorem 2.** Every integral generalized sun graph with at most 41
  vertices that is not a cycle has a 4-cycle and is one of the three integral
  unicyclic graphs that Braga, Rodrigues and Trevisan (2017) found in a
  search up to 21 vertices. Theorem 2 adds that there are no others up to 41
  vertices.
- **Proposition 3** (presented in the paper as an observation). In an
  integral graph whose shortest odd cycles have length `g` and number `c_g`,
  every prime `q` with `(q − 1) | (g − 1)` divides `2g·c_g`, and at least
  `(g − 1)/2` integers `v ≥ 2` have different multiplicities as eigenvalues
  `v` and `−v`. Hence (Corollary 3.1), if an integral unicyclic graph has a
  cycle of odd length `b`, then `3 | b`, and `b = 3` or `b ≥ 15`.
- **Later work.** After version 1 was made public, Braga, Moraes and Santos
  (arXiv:2610.22773v1, 16 October 2026) proved that `C_3` is the only
  integral unicyclic graph with a cycle of odd length, and that `(g − 1)!`
  divides `2c_g`. The first result supersedes Corollary 3.1, and the second
  implies the first part of Proposition 3. That paper does not address
  Theorems 1 and 2.
- Method: up to 42 vertices, hand proofs exclude every cycle length
  `b ≢ 0 (mod 4)` except 3, 6 and 10. Version 1 settled these three by
  exhaustive computer searches; version 2 does not use the searches. The
  cycle lengths 3 and 6 are settled by Propositions 6.1 and 6.2, and 10 inside
  the proof of Theorem 1. For these three cases the proofs are formal only:
  the paper gives no written proof of them.
- Lean: every result of Paper 7 (version 2) is formalized. The 58 statements
  of the frozen statement files in `lean/Research/Backfill/Paper7/` (the copies
  there differ from the files frozen on 18 October 2026 only in their `import`
  lines; hashes in `certificates/sun-graphs/lean-package-v2/package-manifest.json`)
  are proved in that directory and restated in `ClaudePaper7FinalPackage.lean`: Theorems
  1 and 2, Proposition 3, all numbered lemmas and corollaries, the results of
  Section 6, the classification of the integral unicyclic graphs with at most
  21 vertices of Braga, Rodrigues and Trevisan, Theorem 2.1 and Proposition
  3.2 of Braga, Moraes and Santos, and the statements of Section 5 on the
  mathematics behind the search rules of version 1. The statements are about
  formally defined sets of sequences, not about the programs of version 1. The
  files were reviewed independently and frozen on 8 October 2026. One
  statement proved false as frozen (a missing pair of parentheses in a bound,
  shown by a Lean proof of its negation on 9 October); the author approved
  adding this pair, and the corrected files were reviewed and frozen again on
  18 October. OpenAI Codex proved 57 statements; Codex and Claude Code proved
  the last one, `LegacyMomentCounts`, which needed large computations in the
  kernel. Two of the 60 frozen statements, on two data files of 52,652
  sequences each, were not proved (the kernel could not read in the files),
  and the author deleted them, with every claim of version 1 that only they
  would support. They remain in the frozen files; nothing depends on them.
- Deleted from version 1 for lack of a formal proof: the search tables and
  counters, the program versions, the controls and random tests, and the
  statement that two programs produced the same 52,652 sequences at cycle
  length 10. The programs and logs remain in `certificates/sun-graphs/` as
  the record of version 1. Lean's limit on the work of one step (heartbeats)
  is removed in 191 modules and raised in 10 (Section 8 of the paper); this
  changes how long Lean may work, not what it accepts.

**Paper 8: [`papers/switching-diam4`](papers/switching-diam4/note.pdf) (version 2).**
*The switching conjecture for main eigenvalues holds for trees of diameter at
most 4.*

- A switching of a graph changes the signs of the edges between a vertex set
  and its complement; an eigenvalue is main if its eigenspace is not
  orthogonal to the all-ones vector. The switching conjecture (Akbari, França,
  Ghasemian, Javarsineh and de Lima, Linear Algebra Appl. 614 (2021)), in the
  form for connected graphs given by Akbari, Kumar, Mohar and Pragada
  (arXiv:2609.27046), says that every connected graph other than K₂ and
  K₄ − e has a switching in which all eigenvalues are main. In their Problem
  1.6 they asked for a proof for trees and for connected regular graphs.
- **Theorem 1.** Every tree of diameter at most 4 other than K₂ has a
  switching in which all eigenvalues are main. This class contains the stars,
  the double stars and the harmonic trees, for which the conjecture was known.
  Since every signature of a tree is a switching of the all-positive one, the
  signature version of the conjecture also holds for these trees.
- The proof uses the explicit spectrum of these trees, a counting argument
  for the switchings that can fail, a hand proof when the largest branch has
  at least 13 leaves, a finite search over 13,376 branch multisets, and
  explicit switchings for three small trees and for the trees whose branches
  have at most one leaf.
- Lean: every result of Paper 8 (version 2) is formalized. The 38 statements
  of the frozen statement file `lean/Research/Backfill/Paper8/Challenge.lean`
  (SHA-256 `69332eca…c715`) are proved in `lean/Research/Backfill/Paper8/`
  (`Check.lean`), including Theorem 1 (also in a form that uses only Mathlib's
  definitions), its signature version, the spectrum of the trees `T(a)`, the
  rows of switchings and their counts, and the finite search of
  Proposition 5.5, which the Lean kernel checks. The statements were written
  after the paper, reviewed independently and frozen (version 1 on
  27 September 2026; version 2 on 29 September 2026 at 17:01 UTC); the
  proofs were written by Claude Code agents while Codex's usage quota had run
  out. Version 2 deletes the computational claims of version 1 that we could
  not prove formally: the supporting computations on all trees with up to 24
  vertices and on the trees of diameter at most 4 with up to 44 vertices, some
  counts in Section 6, and the computed values in Remark 8.1.
  The problem for all trees, and for regular graphs, remains open.

**Paper 9: [`papers/axial-nonannihilation`](papers/axial-nonannihilation/note.pdf).**
*A simple primitive axial algebra with a disconnected non-annihilation graph,
and a decomposable axial block.*

- An axial algebra is a commutative, not necessarily associative algebra
  generated by idempotents, called axes, whose eigenvectors multiply
  according to a fusion law. The non-annihilation graph `Δ(X)` has the
  generating axes as vertices, two of them adjacent when their product is
  non-zero. McInroy and Shpectorov (arXiv:2209.08043, Conjecture 3.16)
  conjectured that the finest sum decomposition of an axial algebra comes
  from the connected components of `Δ(X)`; Gorshkov and Shpectorov
  (arXiv:2606.30048, Problem 3.11) and Mamontov, Shpectorov and Zhelyabin
  (arXiv:2602.11984, Question 9.5) ask the same for primitive axial
  algebras.
- **Theorem A.** A four-dimensional simple algebra over ℚ, generated by
  three primitive axes for the fusion law J⁺(½) (the Jordan-type law J(½)
  with `0⋆0` and `0⋆½` enlarged to {1, 0, ½}), has a disconnected graph
  `Δ(X)`, and the subalgebras generated by its two components do not
  annihilate each other. So, when arbitrary finite symmetric fusion laws
  are allowed, the answer to these questions is negative, even for simple
  algebras (Corollary 1.1).
- **Theorem C.** A five-dimensional primitive axial algebra, for a similar
  law J°(½), in which the block of an axis (the ideal it generates) is the
  sum of two of its proper ideals. When arbitrary finite symmetric fusion
  laws are allowed, this answers Question 9.2 of Mamontov, Shpectorov and
  Zhelyabin (Problem 3.8 of Gorshkov and Shpectorov) negatively. The
  block is not generated by the axes it contains; if the question is meant
  only for blocks that are axial algebras, this example does not answer it.
- **Theorem B** is a further four-dimensional example, for J⁺(⅓): it is
  indecomposable, has blocks `I_a = I_b ⊊ I_c`, and its graph `Δ(X)` is
  disconnected. **Proposition 4.1** points out that a known
  two-dimensional algebra of Peng (arXiv:2608.28653), which also appears in
  the classification of Kaygorodov, Martín González and Páez-Guillán
  (arXiv:2211.00334), has properly nested blocks, which answers Question
  9.3 of Mamontov, Shpectorov and Zhelyabin (Problem 3.9 of Gorshkov and
  Shpectorov) positively. The example is theirs; we claim only the
  observation.
- Scope: the laws J⁺(½), J⁺(⅓) and J°(½) are finite and symmetric but not
  Seress, so the positive results for Seress laws (Khasraw, McInroy and
  Shpectorov, Trans. Amer. Math. Soc. 373 (2020), Theorem 6.14) and for
  Jordan type (Hall, Segev and Shpectorov) do not apply. Nothing is claimed
  about the conjecture of Khasraw, McInroy and Shpectorov for axial
  algebras of Monster type (their Conjecture 6.2), about Seress or graded
  fusion laws, or about simple Majorana algebras.
- Lean: every theorem, corollary, proposition and lemma of Paper 9 is
  formalized (`lean/Research/AxialMSZ/`; the 17 checked statements are in
  `Check.lean`). The statements were written first, in a statement file
  that two independent AI reviews compared with the source papers, and the
  file was frozen by its SHA-256 hash before the proofs were written; two
  further statements about the algebra of Theorem C were reviewed and
  frozen in the same way, in a separate file. The proofs were written by
  OpenAI Codex.

**Paper 10: [`papers/wordrep-tensor`](papers/wordrep-tensor/note.pdf) (version 2).**
*Tensor products of Mycielskians of odd cycles with odd wheels and with extended Mycielskians of odd cycles are not word-representable.*

- A graph is word-representable if some word over its vertices, containing
  every vertex, has two distinct letters alternating exactly when the
  vertices are adjacent. Alshammari (arXiv:2609.20881, Problem 5.1) asked
  whether the tensor products `μ(C_{2n+1}) × W_{2m+1}` and
  `μ′(C_{2n+1}) × W_{2m+1}` are non-word-representable for all `n ≥ 1` and
  `m ≥ 2`, where `μ` and `μ′` are the Mycielskian and the extended
  Mycielskian and `W_{2m+1}` is the wheel on an odd cycle.
- **Theorem 1.** The answer is yes. When `n ≥ m`, each product contains an
  induced copy of its first factor, through a homomorphism into the wheel
  (as in the proof of Alshammari's Theorem 3.6); when `n ≤ m`, both contain
  an induced copy of `μ(C_{2m+1})`, by an embedding adapted from the proof
  of her Theorem 4.3. These graphs are not word-representable by theorems
  of Hameed and of Kitaev and Pyatkin (arXiv:2408.05066, Theorem 4 and
  Remark 5), and word-representability passes to induced subgraphs.
- **Theorem 3 (version 2).** Alshammari's Problems 5.2 and 5.3 ask the same
  for `μ(C_{2n+1}) × μ′(C_{2m+1})` and `μ′(C_{2n+1}) × μ′(C_{2m+1})` when
  `n < m`. The answer is again yes, for all `1 ≤ n < m`. The proof folds the
  cycle `C_{2m+1}` onto `C_{2n+1}`; the root together with the top vertices
  and shadows of any three consecutive columns of the fold induces one of two
  seven-vertex graphs. A finite check over the orientations of these two
  graphs, carried out by the Lean kernel (`decide +kernel`, no
  `native_decide`), gives a two-colouring of the orientations of five edges
  that would have to change at each of the `2m + 1` steps around the cycle,
  which is impossible. We know no proof of this check without the computation.
- Scope: nothing is claimed about Problem 5.4 of arXiv:2609.20881: whether a
  tensor product of two non-word-representable graphs can be
  word-representable remains open.
- Lean: every result of Paper 10 is formalized
  (`lean/Research/WordRepTensor/`; the 11 checked statements of version 1 are in
  `Check.lean`), including the non-word-representability of `μ(C_{2t+1})`
  and `μ′(C_{2t+1})` for all `t ≥ 1`, in its word-representability form.
  The Lean proof of that fact does not follow the cited papers: it works
  with words directly, through a chord property of the orientation by first
  occurrences and a finite check, by the Lean kernel, of a window of seven
  vertices. The characterization by semi-transitive orientations
  (Halldórsson, Kitaev and Pyatkin) is not formalized and not needed. The
  statements were written first, in a statement file that an independent AI
  review compared with the source, and the file was frozen by its SHA-256
  hash, after a review by OpenAI Codex, before the proofs were written. The
  proofs were written by Claude Code while Codex's usage quota had run out.
- Lean, version 2: the six modules of `lean/Research/WordRepTensor/TaskF/`.
  OpenAI Codex wrote a second statement file (`Problem5_2`, `Problem5_3`) and
  a file of internal statements (the steps of the proof), which a Codex
  agent that had not written them reviewed; both were frozen on 9 November
  2026 (23:14 UTC) before the proofs were written. Codex wrote the proofs
  (`WordRepTensor.TaskF.Proof.check_Problem5_2`, `check_Problem5_3`), and
  built the 17 modules of the paper in two new empty directories with
  `leanchecker` (`certificates/wordrep-tensor/lean-package-v2/`). The files
  of version 1 are unchanged.

**Paper 11: [`papers/cograph-distance`](papers/cograph-distance/note.pdf).**
*Connected cographs with distance eigenvalues just below −2.* A short note
(4 pages).

- A cograph is a graph with no induced path on four vertices. Lou and Lin
  (Linear Algebra Appl. 608 (2021) 1–12) proved that no connected cograph has
  a distance eigenvalue in the open interval `(−2, −1)`. In their survey
  arXiv:2611.06981v1 (4 November 2026), Manna, Mandal and Tura ask, in
  part (i) of the open problem "Distance eigenvalues of cographs below −2 and
  sharpness", whether there is `ε > 0` such that `(−2 − ε, −2)` contains no
  distance eigenvalue of any connected cograph.
- **Theorem 1.** No. For every `m ≥ 1`, the graph
  `G_m = K_1 ∨ (K_1 ∪ mK_2)` on `2m + 2` vertices is a connected cograph with
  a distance eigenvalue in `(−2 − 1/(2m), −2)`, the smallest root of
  `p_m(x) = x³ + 3x² − x − 3 − m(4x² + 10x + 4)`; numerically it is about
  −2.383, −2.222, −2.155, −2.049 and −2.005 for `m = 1, 2, 3, 10` and `100`.
  `G_3` is the 8-vertex example of the survey. The proof uses an equitable
  partition of the distance matrix, the intermediate value theorem and an
  explicit eigenvector.
- **The answer follows from earlier work.** The graphs `G_m` are the graphs
  `K_1 ∨ (mK_2 + K_1)` of Conde, Dratman and Grippo (arXiv:2606.06052v1,
  4 June 2026, Lemma 6 and its proof), who showed for the adjacency matrix
  that each has an eigenvalue in `(0, 1/(2m+1))`. Their paper does not discuss
  the distance matrix, but the answer follows from their lemma in a few lines
  (Remark 1 of the paper: a connected cograph has diameter at most 2, so
  `D = 2J − 2I − A`; apply this to `K_1 ∨ (G_m ∪ G_m)` and the vector
  `(0, x, −x)`), and the survey cites their paper. We record the answer
  because the survey lists the question as open, and give a direct proof for
  `G_m`, formalized in Lean. This is a short remark on the question, not a
  substantial new result.
- Scope: nothing is claimed about the other parts of the open problem.
- Lean: Theorem 1 is formalized (`lean/Research/CographDist/`, 6 modules;
  `Audit.lean` restates the frozen statement `OpenProblemI_negative` and
  Theorem 1 for each `G_m`). The statement file `Challenge.lean` defines
  induced paths on four vertices, cographs, the distance matrix (with
  Mathlib's `SimpleGraph.dist`, which is 0 between different components; the
  statement asks for connected graphs) and distance eigenvalues; an
  independent Claude Code agent compared it with the question of the survey,
  and it was frozen by its SHA-256 hash on 9 November 2026. The proof files
  were drafted while that review ran; the statement file was not changed to
  fit them. Not formalized: Remark 1, that the root is the smallest root of
  `p_m`, the numerical values above and what the
  paper says about the literature. The statement file, the proofs and the
  text were written by Claude Code; OpenAI Codex was not involved.

**Paper 12: [`papers/axial-frobenius`](papers/axial-frobenius/note.pdf).**
*An axial algebra whose automorphism group does not preserve its Frobenius
form: an answer to a question of Shpectorov.* A short note (6 pages).

- In their survey arXiv:2606.30048v1 (Commun. Math. 35 (2027), no. 2,
  Paper no. 5), Gorshkov and Shpectorov record a question of Shpectorov
  (Problem 3.3 of the arXiv version, Problem 2.3 of the journal version): is there an axial algebra with a
  Frobenius form that the full automorphism group of the algebra does not
  preserve? They want a non-trivial example (not `B ⊕ B` with a form that
  vanishes on one summand), especially one whose space of Frobenius forms is
  1-dimensional; such an algebra cannot have an identity element.
- **Theorem 1.** Yes. The commutative algebra `A` over `F_11` with basis
  `a, b, c, d`, all four idempotent, and `ab = c + d`, `ac = −b − d`,
  `ad = b + c`, `bc = a + d`, `bd = −a − c`, `cd = a + b` is generated by the
  primitive axes `a, b, c, d` for a `C_2`-graded fusion law on `{1, 5, 7, 10}`;
  every bilinear form `γ` with `γ(uv, w) = γ(u, vw)` is a multiple of
  `β = diag(1, −1, 1, −1)`, which is a non-degenerate symmetric Frobenius
  form; the automorphism exchanging `a ↔ b` and `c ↔ d` multiplies `β` by
  `−1`; and `A` is simple and has no identity element.
- Scope: the question allows any field and any fusion law, and the example
  uses `F_11` and a fusion law chosen for it, which does not contain 0 and is
  not of Jordan or Monster type. Whether there is an example of Jordan or
  Monster type, or over a field of characteristic 0, is not addressed. The
  full automorphism group of `A` is not determined.
- Lean: the theorem is formalized (`lean/Research/TaskG/`, 8 modules, which
  reuse the definitions of the statement file of Paper 9,
  `lean/Research/AxialMSZ/Challenge.lean`, unchanged). The statement file
  `TaskG/Challenge.lean` asks for an example of dimension 2 to 8 over `ℚ`,
  `F_5`, `F_7` or `F_11` with a finite symmetric fusion law, a primitive axial
  algebra with no decomposition into two non-zero ideals, a non-zero symmetric
  Frobenius form and an automorphism of order 2 or 3 that multiplies it by a
  scalar `c ≠ 0, 1` (`ShpectorovAnswer`); the stronger `StrongShpectorovAnswer`
  adds that the space of forms `γ` above is 1-dimensional and that there is no
  identity element. These statements say that an example exists; the parts of
  Theorem 1 about the algebra of the paper (including its simplicity, the
  non-degeneracy of `β` and the grading of the fusion law, which are not in
  the frozen statements) are separate Lean theorems about the algebra defined
  in `Data.lean`. A Codex agent that had not written it compared it with
  the question, and it was frozen on 12 November 2026 (16:27 UTC) before the
  proof files were written; three lines that let Lean treat `ZMod 5`, `ZMod 7` and
  `ZMod 11` as fields, and a comment, were then added (by then the proof files
  had been drafted), checked by the same reviewer, and the file was frozen
  again (16:41 UTC). The example, the statement file, the
  proofs and the build of the package were made by OpenAI Codex
  (`certificates/axial-frobenius/lean-package/`); the text was written by
  Claude Code.

**Paper 13: [`papers/critical-cycles-mod-k`](papers/critical-cycles-mod-k/note.pdf)** (version 2).
*Critical graphs with the fewest cycles of length 0 modulo k.* 13 pages.

- Choi and Sieniawski (arXiv:2611.13580v1, Theorem 3) proved that for every
  `k ≥ 3` a graph with no proper `k`-colouring has at least `(k+1)!/(2k)`
  cycles of length 0 modulo `k`, as `K_{k+1}` has, and asked (Question 8)
  whether for `k ≥ 4` `K_{k+1}` is the only `(k+1)`-critical graph with exactly
  that many. For `k = 3` this was proved by Kim and Picollelli (Electron. J.
  Combin. 31(2) (2024)).
- **Theorem 2.** Yes, for every `k ≥ 4`. The proofs use the counting of
  Choi and Sieniawski (at equality every cycle of length divisible by `k` has
  length exactly `k`, and every such cycle is rainbow in every colouring of a
  vertex-deleted subgraph). For `k = 4` and `k = 5` they use a construction of
  Kim and Picollelli for vertices of degree `k` and a case analysis of
  degrees. For `k ≥ 6`, a graph attaining the bound other than `K_{k+1}` would
  have minimum degree at least `2k − 1` (an argument with singleton colours,
  colour classes and Kempe chains), and a connected graph of minimum degree at
  least `2k − 1` has a cycle whose length is a multiple of `k` larger than `k`,
  by a theorem of Gao, Huo, Liu and Ma (IMRN 2022, Theorem 3.1) on paths whose
  lengths form an arithmetic progression with difference 1 or 2.
- Version 1 of the paper (version 1.21.0 of this repository) proved the cases
  `k = 4, 5, 6, 7`, with separate case analyses for `k = 6` and `k = 7`; their
  Lean proofs remain in the repository (`TaskH.case_six`, `case_seven`), but
  the general argument does not use these theorems. That `K_{k+1}` attains the bound is
  the observation of Choi and Sieniawski; it is formalized only for `k ≤ 7`.
- Lean: `lean/Research/TaskH/` (716 modules). The statement file
  `Challenge.lean` defines `EqualityCase k` (every finite `(k+1)`-critical graph,
  with criticality over all proper subgraphs including edge deletions, whose
  number of cycles of length divisible by `k`, counted as edge sets of
  Mathlib cycles, equals `(k+1)!/(2k)`, is isomorphic to `K_{k+1}`) and the full
  question `Question2` (all `k ≥ 4`), proved by
  `TaskH.original_question_two_all_k`; `CaseFive.lean`, `CaseSix.lean` and
  `CaseSeven.lean` add the cases 5, 6, 7 of version 1. Each was reviewed by a
  Codex agent that had not written it and frozen before any proof file
  specific to it was written (`Challenge.lean`, including `Question2`:
  13 November 2026, 18:42 UTC; the others 13 November, 21:15 UTC, and
  14 November, 00:05 and 06:32 UTC). The proof for all `k` includes complete
  Lean proofs of Theorem 3.1 of Gao, Huo, Liu and Ma and of their Theorem 2.1
  (two paths, from a theorem of Fan), which are not assumed. OpenAI Codex wrote
  the statements, the proofs and the build drivers, built each case of version
  1 in two new empty directories on the author's Windows computer and the 717
  files of its all-`k` package in two new empty directories on the author's
  Mac (`certificates/critical-cycles-mod-k/lean-package/`); the text was
  written by Claude Code. See the disclosure below for the reviews.

**Paper 14: [`papers/equivariant-rank`](papers/equivariant-rank/note.pdf).**
*On the rank of groups of equivariant permutations: a counterexample to an
upper bound.* 9 pages.

- For a finite group `G` acting on a finite set `X`, the `G`-equivariant
  permutations of `X` form a group `Aut_G(X)`. Lara-Gómez, Romero-Rosales and
  Ruiz-Medina (*Semigroup Forum*, published online 2 November 2026,
  doi:10.1007/s00233-026-10690-y; preprint arXiv:2607.04053v1) construct a
  generating set of it from the orbits and stabilizers of the action, which
  gives an upper bound for its rank, the least number of generators (Theorem 4
  of the journal version, the right-hand side of Theorem 5 of the preprint).
  They refine it by grouping generators of pairwise coprime orders into
  "packets" (Corollary 6 of the journal version, Corollary 19 of the
  preprint; the two versions differ by 1), and in the Open problem after
  their Example 1 (Example 20 of the preprint) they write that the packet
  bound should be the exact value of the rank.
- **Theorem 1.** For the group of order 2 acting regularly on two points, the
  right-hand side of Theorem 4 is 0 while the rank is 1, so Theorem 4 fails.
  The two packet bounds (1 and 2) hold.
- **Theorem 2.** For the group of order 2 acting on five points through a
  transposition, the rank is 2 while the packet expression is 3 (preprint) or
  4 (journal version). The authors' own 21-point example already shows that
  the packet expression is not always the rank (they show that the rank is at
  most 4, and the expression is 5 or 6); Theorem 2 is a simpler instance. That
  the group involved, `C_2 × S_3`, has rank 2 also follows from a theorem of Lu
  (arXiv:2604.16141v1, Theorem 1.1 and Lemma 3.10).
- **Theorem 3.** For every `n ≥ 3` there is a faithful action of a finite
  cyclic group with rank 2 for which the two versions of the packet expression
  equal `n` and `n + 1`, for every admissible choice of generating sets of
  minimal cardinality; so the difference is unbounded. The orbits have
  pairwise different lengths, products of primes attached to the ordered pairs
  of `{1, …, n}`, chosen so that any two lengths share a prime.
- Scope: in all three examples the packet bounds hold; what fails is Theorem 4
  (for the two-point example) and the expectation of equality. The journal's Introduction also says "We
  conjecture that the upper bound is sharp"; if "sharp" means only that the
  bound is attained for some actions, the examples do not contradict it. Four
  remarks are written arguments and are not formalized: every transitive
  action `G/H` with `N_G(H)/H` nontrivial also violates Theorem 4; removing the
  term `−δ` gives a valid bound (a recount of the authors' own generating set,
  not claimed as new); if `δ` is read as in the sentence that explains it in
  the preprint, the trivial group acting on two points violates Theorem 5 of
  the preprint; and a smaller variant of the family of Theorem 3 (31 points
  for `n = 3`). The computer check of the authors' 21-point example is also
  outside the formalization.
- Lean: `lean/Research/TaskJ/Rank/` (15 modules: 5 for Theorems 1 and 2, and
  10 in `Extension/` for Theorem 3). The statement file `Challenge.lean`
  defines the action of `C_2 = ZMod 2` on two and on five points through a
  transposition, the equivariant group as the centralizer of the action in the
  full permutation group (one of the statements says that it consists exactly
  of the equivariant permutations), the stabilizers, orbits, boxes and
  quotients `N_G(H)/H`, the parameters `r`, `κ`, `Λ`, `ω`, `R` and `δ` (in its
  displayed form) and the packet number, and the bounds of both versions,
  evaluated in the integers. It fixes one generating set for each quotient and
  requires a proof that it has minimal cardinality; the quotients that occur,
  `C_2` and the trivial group, have only one such set. Its six statements give
  the parameters, the ranks and the failures for the two examples.
  `Extension/Challenge.lean` states `UnboundedGap`: for every `n ≥ 3` there is
  a cyclic group acting faithfully on `n` cyclic orbits of different lengths,
  with `r = κ = n`, `Λ = 0` and rank 2, for which every valid choice of
  generating sets of minimal cardinality (at least one exists) gives `n`
  packets. As in the source, the rank of a quotient is computed with nonempty
  generating sets, so the trivial group has rank 1. The isomorphism types
  named in the written proofs (`C_2 × S_3` and `Z/M × Z/M`) are not part of
  the statements. Each statement file was reviewed against both versions of
  the source by a Codex agent that had not written it, and frozen (18 November
  2026, 00:07 and 00:22 UTC); the development logs record no compilation of a
  proof file before the freezes. The same agent had checked the reading of the
  source, so these checks are not independent of each other. OpenAI Codex
  wrote the statements and the proofs and checked the two packages in two new
  empty directories on the author's Mac
  (`certificates/equivariant-rank/lean-package/`); the text was written by
  Claude Code. See the disclosure below for the reviews.

**Paper 15: [`papers/lattice-box-paths`](papers/lattice-box-paths/note.pdf).**
*The maximum Manhattan length of a path through all lattice points of a box.*
10 pages.

- List the `N` lattice points of a box `[d_1] × … × [d_r]` in some order and add
  up the Manhattan distances between consecutive points (both endpoints free,
  no closing step, steps of any length); let `M(D)` be the largest possible
  total. Yuan (arXiv:2611.19908v1) determined `M` for rectangles, gave a
  coordinatewise upper bound `U_r(D)` in every dimension (his (6)), and asked,
  in the first open problem of his §6.3, to determine the gap
  `κ_r(D) = U_r(D) − M(D)` for `r ≥ 3`. From six computed three-dimensional
  values he noted that the gap might be `2^(e−1) − 1`, where `e` is the number
  of even sides, and that he could neither prove nor refute this.
- **Theorem 1.** For every list of positive side lengths, (a) every ordering
  has length at most `U_r(D) − κ(D)`, (b) some ordering has exactly this
  length, and (c) every ordering of maximal length has gap exactly `κ(D)`,
  where `κ(D)` is given by an explicit case formula. If at least three sides
  exceed 1, `κ(D) = 1` when all sides are odd and `κ(D) = 2^(e−1) − 1` when
  `e ≥ 1` sides are even; for example `M(2 × 3 × 4) = 101`, the case Yuan
  names as the smallest unresolved one. Boxes with at most two sides larger
  than 1 are covered as well; there the formula agrees with the known results.
  For the single-point box the printed formula (6) gives `U_r(D) = −r`, so the
  gap is `−r`; this comes from the convention of (6), not from a negative
  deficit. The upper bound measures the coordinates from the centre of the
  box; the orderings that attain it are built from six small seeds by three
  extension lemmas.
- Corollary 2 states exactly when one ordering attains the largest
  contribution of every coordinate at once. With free endpoints, this answers
  and clarifies a conjecture of Jiang (arXiv:1401.6583v1, §7); since its
  clause on placing the endpoints is not made precise, the paper does not
  regard it as refuted.
- Scope and earlier results: the hypercube (all sides 2) is due to Kchikech,
  Khennoufa and Togni (Discuss. Math. Graph Theory 28 (2008), Lemma 2); the
  plane to Jiang (Theorem 3.1, sides larger than 2), Fried (up to an additive
  error of one) and Yuan (Theorem 1.1); one dimension to Bulteau, Giraudo and
  Vialette (CPM 2021, Theorem 8). Simmons (Lecture Notes in Math. 686, 1978)
  maximized the sum of the distances around closed circuits through the
  points of an equal-sided cube `[d]^n`, which he states he solved completely,
  and used the one-coordinate form of the centring identity of the paper,
  which should be credited to him; for equal-sided cubes the closed-circuit
  value is his, and the contribution of Paper 15 there is the open-path value
  (for `4 × 4 × 4` the two maxima are 380 and 378). Only pp. 290–291 of his
  paper could be read. Corollary 2 also uses Yuan's formula for a single
  coordinate (his Theorem 2.3), which is not formalized.
- Lean: `lean/Research/TaskJ/Grid/` (28 modules: the statement file, 25 proof
  modules, `Proof.lean` and `CheckGrid.lean`). The statement file
  `Challenge.lean` lists the points of the box (coordinates numbered from 0),
  defines an ordering as a permutation of this list and its length as the sum
  of the Manhattan distances of consecutive points, defines `U_r(D)` as
  printed in (6) (in the integers, with natural-number floor division) and the
  formula for `κ(D)`, and states the three parts of Theorem 1
  (`LengthUpperBound`, `LengthAttained`, `YuanGapAtLongest`) for every finite
  list of positive side lengths. A Codex agent that had not written it reviewed
  it against Yuan's paper, and it was frozen on 18 November 2026 at 00:03 UTC;
  the development logs record no compilation of a proof file before that time.
  The same agent had checked the reading of the source. OpenAI Codex wrote the
  statements and the proofs and checked the package in two new empty
  directories on the author's Mac
  (`certificates/lattice-box-paths/lean-package/`); the text was written by
  Claude Code. A development file of Codex, `GridLowerPrep.lean`, which
  nothing imports and which was not checked, is not included. See the
  disclosure below for the reviews.

**Paper 16: [`papers/numerical-semigroup-lengths`](papers/numerical-semigroup-lengths/note.pdf).**
*The decomposition lengths of a numerical semigroup form an interval.* 9 pages.

- A numerical semigroup `S` is a set of non-negative integers that contains
  0, is closed under addition and misses only finitely many integers, its
  gaps. Every numerical semigroup is an irredundant intersection of finitely
  many irreducible numerical semigroups (Rosales and García-Sánchez,
  *Numerical Semigroups*, 2009, Chapter 3, Proposition 4.44), often in
  several ways; the number of components is the length of the decomposition,
  and `L(S)` is the set of all lengths. García-Sánchez (Commun. Korean Math.
  Soc. 40 (2025); arXiv:2410.13729v1, §3), who calls decompositions
  factorizations, reported that he had found no numerical semigroup whose set
  of lengths is not an interval and suggested proving that it always is.
  García-Sánchez and O'Neill (arXiv:2602.00404v1) state this as their
  Conjecture 1.1 and prove it for multiplicity at most 6; their Conjecture 3.9
  says that a numerical semigroup of multiplicity `m = 2k` with a
  decomposition of length `j`, `k < j < m`, also has one of length `j − 1`
  (for `m = 6` this is their Theorem 3.5; they report computational evidence
  for `m = 8`).
- **Theorem 1.** For every numerical semigroup `S`, `L(S)` is a nonempty set
  of consecutive integers. In one component at a time, the proof exchanges an
  integer below half the Frobenius number of the component for its
  complement, which keeps the Frobenius number; when this leaves a special
  gap of `S` uncovered, one irreducible component with a smaller Frobenius
  number repairs it, and redundant components are removed. Each step changes
  the length by at most one, and the process ends in a normal form with
  exactly `r(S)` components, the number of special gaps of `S` larger than
  half its Frobenius number.
- **Theorem 2.** A numerical semigroup of multiplicity `2k` has a
  decomposition with at most `k` components: each residue class modulo `2k`
  contains at most one special gap, and one irreducible component covers the
  special gaps of two classes that differ by `k`. This generalizes the
  pairing of residue classes in the proof of Theorem 3.5 of García-Sánchez
  and O'Neill.
- **Corollary 1.** Conjecture 3.9 holds; more precisely, if `S` has
  multiplicity `2k` and a decomposition of length `j > k`, it has one of
  length `j − 1`.
- Scope and earlier results: the criterion by special gaps, the existence of
  decompositions and an algorithm for a decomposition of minimum length are
  in the book of Rosales and García-Sánchez (Chapter 3, Section 4); the
  exchange is a special case of Proposition 5 of Blanco and Rosales (Forum
  Math. 25 (2013); arXiv:1105.2147v1); that every numerical semigroup has a
  decomposition with at most `r(S)` components is due to Rosales and Branco
  (2002, Corollaries 10 and 18), as quoted by Bogart and Seyed Fakhari (Comm.
  Algebra 53 (2025), Theorem 2.1). The full text of the paper of Rosales and
  Branco could not be read; it may also contain a decomposition of length
  exactly `r(S)`, which Paper 16 does not claim as new. Theorem 4.3 of
  García-Sánchez and O'Neill changes decompositions of the ordinary
  semigroups `{0, m, m + 1, …}` by the same kind of steps. Remark 1 of the
  paper notes, with an example, that the condition printed in (2.5) of
  arXiv:2602.00404v1 (`SG(S) ⊆ ⋃ SG(S_i)`) cannot replace the criterion of
  the book (`SG(S) ⊆ ⋃ G(S_i)`), which the paper uses. Remark 2
  (`r(S) ∈ L(S)` for `S ≠ ℕ`), the finiteness of `L(S)` and the examples of
  Remarks 1 and 3 are written arguments and are not formalized.
- Lean: `lean/Research/TaskL/Semigroup/` (12 modules: the statement file, 9
  proof modules, `Proof.lean` and `CheckSemigroup.lean`). The statement file
  `Challenge.lean` defines a numerical semigroup as an additive submonoid of
  `ℕ` with finite complement, irreducibility literally (if `Q = A ⊓ B` for
  numerical semigroups `A` and `B`, then `Q = A` or `Q = B`), a decomposition
  of `S` as a finite set of irreducible numerical semigroups whose
  intersection is `S` and no proper subset of which has intersection `S` (the
  empty set has intersection `ℕ`), its length as the number of its elements,
  and the multiplicity. It states `LengthsExist` and `LengthsInterval`, which
  together are Conjecture 1.1 for every numerical semigroup, including `ℕ`,
  whose only decomposition is the empty one; `PositiveLengthsInterval`, the
  same for positive lengths, as in the paper of García-Sánchez; and
  `EvenMultiplicityDescent`, Conjecture 3.9 as stated (`k < j < 2k`). The
  bound of Theorem 2 is proved on the way as `short_even_decomposition`, and
  Lemma 7 of the paper (every decomposition with all components normal has
  `r(S)` components) as `terminal_card`; neither is a frozen statement. A
  Codex agent that had not written it reviewed the statement file against
  the papers of García-Sánchez and O'Neill and of García-Sánchez, and it was
  frozen on 18 November 2026 at 23:47:45 UTC; the session records and file
  times show no proof file before that time. The same agent had
  checked the reading of the sources, and it then wrote some of the proof
  files. OpenAI Codex wrote the statements and the proofs and checked the
  package in two new empty directories on the author's Mac
  (`certificates/numerical-semigroup-lengths/lean-package/`); the text was
  written by Claude Code. See the disclosure below for the reviews.

**Paper 17: [`papers/tree-antichains`](papers/tree-antichains/note.pdf).**
*Arbitrarily large antichains of trees of equal order in the independence polynomial order.* 10 pages.

- The independence polynomial `I(G, x)` of a graph counts its independent
  sets by size, the empty set included. Beaton and Cameron define `ξ(G)` as
  the independence root of smallest modulus and note, citing Csikvári, that
  it is real and is the largest real root. Csikvári (J. Graph Theory 74
  (2013), Section 8) introduced the relation `H ⪯ G`, which in the form used
  by Beaton and Cameron (Open J. Discrete Appl. Math. 5 (2022), no. 3,
  30–46; arXiv:2006.05511v2) holds when `I(H, x) ≥ I(G, x)` for all `x` in
  `[ξ(G), 0]`; it is a partial order on the classes of graphs with the same
  independence polynomial, and among the trees of a given order the path is
  its minimum and the star its maximum (Csikvári). Beaton and Cameron
  disproved Oboudi's conjecture that any two trees of the same order are
  comparable, with two incomparable trees of order 8 and, by the graph star
  operation, a pair at each order `2^(k+3)`, and asked (their Question 6;
  Question 5.3 of the arXiv versions): can there be arbitrarily large
  antichains with respect to `⪯` among trees of equal order?
- **Theorem 1.** For every `n ≥ 11` there are `⌊n/11⌋ + 1` trees on `n`
  vertices that are pairwise incomparable; their independence polynomials
  are pairwise different, so they are pairwise non-isomorphic and their
  classes form an antichain. **Corollary 1:** for every `k`, some `k` trees
  of one order (for instance `11k`) are pairwise incomparable; this answers
  Question 6. The trees are paths in which each of `⌊n/11⌋` vertices carries
  one of two ten-vertex gadgets `A` or `B`, which differ only in where one
  vertex is attached, and up to ten further vertices carry nothing.
  Replacing one `B` by an `A` lowers the independence polynomial at `−1/10`
  and raises it at `−1/6`; a transfer recursion along the path and three
  polynomial inequalities with explicit certificates show that no
  independence polynomial of the family vanishes on `[−1/6, 0]`, so both
  points lie in the comparison interval of every tree of the family.
- Scope and earlier results: the relation, its transitivity and the extremal
  trees are due to Csikvári; Beaton and Cameron's pair of order 8 is
  certified in the same way, by two points of the common comparison interval
  (they use `−0.1` and `−0.2`), and their pairs give antichains of size two
  at infinitely many orders. The trees of Theorem 1 have maximum degree 5
  (Remark 1); this is a written argument and is not formalized. The largest
  size of an antichain among the trees of order `n` is not known; Theorem 1
  shows only that it is at least `⌊n/11⌋ + 1`.
- Lean: `lean/Research/TaskN/Antichain/` (11 modules: the statement file, 8
  proof modules, `Proof.lean` and `CheckAntichain.lean`). The statement file
  `Challenge.lean` defines the independence polynomial of a finite simple
  graph as the sum of `X^|s|` over its independent vertex sets `s`;
  `LargestRoot G r` (`r` is the largest real root of `I(G, x)`);
  `Precedes H G` (`I(G, x) ≤ I(H, x)` for all `x` in `[r, 0]`, where `r` is
  the largest real root of `G`, the graph on the right); and
  `HasAntichain n k` (`k`
  graphs on the vertex set `{0, …, n − 1}`, each a tree with a largest real
  root, pairwise incomparable). It states `WidthLowerBound` (Theorem 1
  without its last sentence) and `ArbitrarilyLarge` (Question 6, as in
  Corollary 1). Since every member must have a largest real root, which is
  unique, incomparability cannot hold merely because a root is missing; and
  two members with the same polynomial would be comparable, so isomorphic
  copies cannot be counted twice. The Lean statement uses the largest real
  root, which the source states to be the same as its root of smallest
  modulus; the Lean files do not depend on that equivalence. A Codex agent
  that had not written it reviewed the statement file against the journal
  version and the arXiv versions of the source, and it was frozen on 20
  November 2026 at 14:25:12 UTC; the file times and the development logs show
  no proof file before that time. The same agent had checked the reading of
  the source. OpenAI Codex wrote the statements and the proofs and checked
  the package in two new empty directories on the author's Mac
  (`certificates/tree-antichains/lean-package/`); the text was written by
  Claude Code. See the disclosure below for the reviews.

**Paper 18: [`papers/variable-length-parking`](papers/variable-length-parking/note.pdf).**
*The equality case of Chen's bound for invariant parking with one special preference.* 11 pages.

- In the parking model of Chen, Harris, Martínez Mori, Pabón-Cancel and
  Sargent (Enumer. Combin. Appl. 4:1 (2024), Article S2R4;
  arXiv:2211.01063v2), `n` cars of positive integer lengths `y_1, …, y_n`
  arrive in order on a one-way street with `y_1 + … + y_n` spots; each car
  takes the first run of free spots of its length that starts at or after
  its preferred spot, and parking fails if there is none. D. M. Chen
  (arXiv:2311.15699v1, the only version) studied the set `W(y)` of
  preferences `w` such that every car parks whichever car is given the
  preference `w` while every other car prefers the first spot. His Theorem E
  shows that `W(y)` has at most `2^(n−1)` elements (b), that equality holds
  when every length exceeds the sum of the later ones (c), and that equality
  implies `y_1 ≥ y_2` and the same condition for the tail `y_2, …, y_n` (d,
  his condition (3)); his Remark 4.7 shows with `y = (7, 5, 3, 1)` that (3)
  is not sufficient. He does not list the equality case among his open
  problems.
- **Theorem 1.** `W(y)` has `2^(n−1)` elements if and only if `n = 1`, or
  `n ≥ 2` and (i) `y_1 ≥ y_2`, (ii) the tail `y_2, …, y_n` is
  superdecreasing (each length exceeds the sum of the later ones), and (iii)
  `y_1 − y_2 ≥ D`, or `D − (y_1 − y_2)` is symmetric for the set `T` of
  subset sums of `y_3, …, y_n`; here `D = y_3 + … + y_n`, and `z` is
  symmetric for `T` if `z ∈ T` and `z − s ∈ T` for every `s ∈ T` with
  `s ≤ z`. Conditions (i) and (ii) are Chen's condition (3); (iii) is the
  new part. For example `(8, 5, 3, 1)` attains the bound and `(7, 5, 3, 1)`
  does not.
- **Theorem 2** (an addition, not a statement of Chen). For a fixed
  superdecreasing tail `(b, y_3, …, y_n)`, the number of first-car lengths
  `a` in `[b, b + D]` for which equality holds is `1 + Σ(2^(L_i) − 1)`,
  where the `L_i` are the lengths of the maximal runs of equal consecutive
  terms of the jumps `h_i = u_i − (u_1 + … + u_(i−1))`, with `u_1 = y_n`,
  `u_2 = y_(n−1)`, …, `u_(n−2) = y_3`. By Theorem 1, no `a < b` and every
  `a > b + D` attains equality.
- Scope and earlier results: the model, Theorem E and the example are due to
  Chen and to Chen, Harris, Martínez Mori, Pabón-Cancel and Sargent; the gap
  reduction (Lemma 1 of the paper) is essentially their Corollary 4.4 and its
  proof; the bound is Chen's Theorem E(b), and the necessity of (i) and (ii)
  is his Theorem E(d), which the paper reproves by a counting variant of his
  argument. As far as we know, condition (iii) and Theorem 2 are new. The
  three remarks of Section 5 (the whole set `W(y)` under Chen's condition
  (3), the invariant parking assortments in the equality case, and the
  computation of `W(y)` with `O(n² 2^(n−1))` integer operations) are written
  arguments and are not formalized. The paper says nothing about the open
  problems of Chen or of Chen, Harris, Martínez Mori, Pabón-Cancel and
  Sargent.
- Lean: `lean/Research/TaskN/Parking/` (12 modules: the statement file, 9
  proof modules, `Proof.lean` and `CheckParking.lean`). The statement file
  `Challenge.lean` encodes Chen's parking rule directly: spots are numbered
  from offset 0; a street is the list of finite gaps of free spots together
  with a frontier from which on every spot is free; `park` places a car in
  the first gap in which it fits at or after its preference, or else at the
  frontier; and `drive` runs the cars in arrival order. The run succeeds on
  the street of length `m` if and only if the final frontier is at most `m`;
  the argument for this is in the paper and is not part of the Lean proof.
  `allPositions` gives the special preference to each car in turn, the
  others getting preference 1, without reordering the lengths, and `W`
  collects the admissible preferences in `[1, m]`. `ExtremalClassification`
  states the bound and Theorem 1 for every nonempty list of positive lengths,
  with the conditions defined from the lengths alone (subset sums and the
  predicate `dominant`, which is "superdecreasing"); `FirstLengthCount`
  states Theorem 2 (its statements about `a < b` and `a > b + D` follow from
  `ExtremalClassification` but are not stated separately). A Codex agent
  that had not written it and had not worked on this problem before reviewed
  the statement file against Chen's paper, and it was frozen on 20 November
  2026 at 14:25:56 UTC; the development logs record no compilation of a
  proof file before that time (the first is at 14:26:55 UTC). The same agent
  had checked the reading of the source. OpenAI Codex wrote the statements
  and the proofs and checked the package in two new empty directories on the
  author's Mac (`certificates/variable-length-parking/lean-package/`); the
  text was written by Claude Code. See the disclosure below for the reviews.

**Paper 19: [`papers/prime-medial-racks`](papers/prime-medial-racks/note.pdf).**
*Medial racks and quandles of prime order: a proof of a conjecture of Vojtěchovský and Yang.* 10 pages.

- A rack is a set with a binary operation `*` whose left translations are
  bijections and which satisfies `x * (y * z) = (x * y) * (x * z)`; a quandle
  is an idempotent rack; a rack is medial if
  `(x * u) * (v * y) = (x * v) * (u * y)` and 2-reductive if
  `(x * u) * v = (y * u) * v` for all elements. Vojtěchovský and Yang
  (*Enumeration of racks and quandles up to isomorphism*, Math. Comp. 88
  (2019); arXiv:1911.04991v1) counted racks and quandles of order at most 13
  up to isomorphism and stated, as their Conjecture 6.5, that for every
  prime `p` the number of medial racks of order `p` exceeds the number of
  2-reductive racks by `p − 2`, that the same holds for quandles, and that
  every medial rack of order `p` that is not 2-reductive is a quandle.
- **Theorem 1.** The conjecture holds for every prime `p` (its three parts).
  **Theorem 2:** every medial rack of prime order `p` that is not
  2-reductive is isomorphic to exactly one of the affine quandles
  `x * y = (1 − λ)x + λy` on `F_p` with `λ ≠ 0, 1`. Connectedness and
  idempotence are not assumed: every point stabilizer of the displacement
  group lies in one subgroup, whose index divides every orbit size, and for
  a rack that is not 2-reductive this index is larger than 1; when the order
  is prime this forces the displacement group to be transitive, hence
  regular, and coordinates then give the affine form.
- Scope and earlier results: the conjecture, the enumeration and the
  counts of 2-reductive racks and quandles (Jedlička, Pilitowska, Stanovský
  and Zamojska-Dzienio) are earlier work; that a rack is medial if and only
  if its displacement group is abelian is Proposition 2.4 of Hulpke,
  Stanovský and Vojtěchovský (J. Pure Appl. Algebra 220 (2016)); that every
  connected quandle of prime order is affine is due to Etingof, Soloviev and
  Guralnick (J. Algebra 242 (2001)), and the isomorphism criterion for
  connected affine quandles is in Hulpke, Stanovský and Vojtěchovský. What
  the conjecture needs in addition is that a medial rack of prime order that
  is not 2-reductive is connected and idempotent. Theorem 2 is proved in
  Lean, for operations on `{0, …, p − 1}`, on the way to Theorem 1, but it is
  not one of the frozen statements. The values of the tables of the source
  are not used and are not in Lean.
- Lean: `lean/Research/TaskP/PrimeMedialRacks/` (13 modules: the statement
  file, 10 proof modules, `Proof.lean` and `CheckRack.lean`). The statement
  file `Challenge.lean` defines racks, idempotence, mediality and
  2-reductivity for binary operations, isomorphism by one bijection, and
  `classCount n P`, the number of isomorphism classes of binary operations
  on `{0, …, n − 1}` that contain an operation with property `P`; its only
  proof is the short check that isomorphism is an equivalence relation,
  needed to form the quotient. It states `RackCount` and `QuandleCount`
  (parts (a) and (b) of Theorem 1, the two equations in additive form, for
  every prime including 2) and `AutomaticIdempotence` (part (c), for every
  operation on `{0, …, p − 1}`). The four properties are invariant under
  isomorphism, so the counts are those of the source. A Codex agent that had
  written neither the proofs nor the Lean statement reviewed the statement
  file against the source, and it was frozen on 20 November 2026 at 18:04:44
  UTC; the file times and the development logs show no proof file before
  that time. OpenAI Codex wrote the statements and the proofs and checked the
  package in two new empty directories on the author's Mac
  (`certificates/prime-medial-racks/lean-package/`); the text was written by
  Claude Code. See the disclosure below for the reviews.

**Paper 20: [`papers/graded-wilf`](papers/graded-wilf/note.pdf).**
*The generalized Wilf conjecture for semigroups graded by a two-generated numerical semigroup.* 9 pages.

- A generalized numerical semigroup is a submonoid `S` of `N^d` with finite
  complement. Cisto, DiPasquale, Failla, Flores, Peterson and Utano
  (Semigroup Forum 101 (2020)) conjectured that `e(S) n(S) ≥ d c(S)`, where
  `e(S)` is the number of minimal generators and `n(S)` and `c(S)` count the
  elements of `S`, respectively of `N^d`, that lie below some gap. For a
  numerical semigroup `T`, the `T`-graded semigroup consists of the points
  of `N^d` whose coordinate sum lies in `T`. Cisto and Navarra (An. Ştiinţ.
  Univ. Ovidius Constanţa 33 (2025); arXiv:2212.12467v1) proved the
  conjecture for `T = ⟨2, b⟩`, `b ≥ 5` odd, and wrote that it remains open
  for `T = ⟨a, b⟩` with `2 < a < b`. In November 2026 Bhardwaj, Cisto and
  Deshpande (arXiv:2611.20086v1) proved it for `d = 2` (their Theorem 5.5)
  and for `d ≥ 3` under a condition that requires `b` to be large compared
  with `a` and `d` (their Theorem 5.6).
- **Theorem 1.** For every `d ≥ 1` and all coprime `2 ≤ a < b`, the set `C`
  of points below a gap and the set `A` of atoms of `S` are finite, `A`
  generates `S`, every generating set contains `A`, and
  `d·|C| ≤ |A|·|C ∩ S|`. **Corollary 1:** every `T`-graded generalized
  numerical semigroup with `T` two-generated satisfies the generalized Wilf
  conjecture. The proof bounds `n(S)` below by the single layer of total
  degree `F(T) − 1`, which lies in `S` because `1 ∉ T`, and compares it with
  the exact value of `c(S)`.
- Scope and earlier results: the case `a = 2` was known in every dimension
  (Cisto and Navarra), `d = 1` is classical, `d = 2` is Theorem 5.5 of
  Bhardwaj, Cisto and Deshpande, and `d ≥ 3`, `a ≥ 3` under their condition
  is their Theorem 5.6, whose proof already uses a single layer of `N(S)`
  (another one). So the new part is only `d ≥ 3`, `3 ≤ a < b`, with their
  condition failing (infinitely many triples, for example `(a, b, d) = (3,
  4, 3)`); for the other parameters the paper gives re-proofs. The
  formulas for the minimal generators and for `n(S)` are due to Cisto and
  Navarra. The paper does not claim the generalized Wilf conjecture for any
  other class.
- Lean: `lean/Research/TaskP/GradedWilf/` (9 modules: the statement file, 6
  proof modules, `Proof.lean` and `CheckWilf.lean`). The statement file
  `Challenge.lean` defines points of `N^d`, their total degree, the
  submonoid `⟨a, b⟩` of `N`, the graded semigroup, the set of points below a
  gap of the true complement, and the atoms, and states `Wilf`: Theorem 1
  for all `a`, `b`, `d` as above. Because the atoms are shown to generate
  `S` and to lie in every generating set, their number is `e(S)` without any
  formula being assumed, and because `C` and `A` are shown to be finite,
  the counts are true cardinalities. A Codex agent that had not written it
  reviewed the statement file against the paper of Cisto and Navarra, and it
  was frozen on 20 November 2026 at 18:04:44 UTC; the file times and the
  development logs show no proof file before that time. OpenAI Codex wrote
  the statements and the proofs and checked the package in two new empty
  directories on the author's Mac (`certificates/graded-wilf/lean-package/`);
  the text was written by Claude Code. See the disclosure below for the
  reviews.

**Paper 21: [`papers/css-covering-equality`](papers/css-covering-equality/note.pdf).**
*A non-hollow lattice 4-simplex of covering radius 2 outside the equality list of a conjecture of Codenotti, Santos and Schymura.* 10 pages.

- The covering radius `μ(P)` of a convex body is the least `μ ≥ 0` such
  that the lattice translates of `μP` cover space. Codenotti, Santos and
  Schymura (Discrete Comput. Geom. 67 (2022); arXiv:1903.02866v2)
  conjectured that every non-hollow lattice `d`-polytope `P` satisfies
  `μ(P) ≤ d/2`, with equality if and only if `P` is obtained by direct sums
  and/or translations of the standard terminal simplices `S(1_l)` (their
  Conjecture A), and proved this for `d ≤ 3`.
- **Theorem 1.** For `P = conv{e_1, e_2, e_3, e_4, −(2,1,1,1)}`: (a) the
  origin lies in the interior of `P`; (b) `μ(P) = 2`; (c) the normalized
  volume of `P` is 6; (d) `P` does not belong to a family `G` generated from
  finite sets of at least two lattice points with sum zero by lattice
  translations and convex hulls of unions. **Lemma 4**, a written argument
  about the definitions of the source, shows that `G` contains every
  polytope obtained from the simplices `S(1_l)` by direct sums and lattice
  translations, and every unimodular image of one. **Corollary 1:** the
  "only if" direction of the equality clause of Conjecture A fails in
  dimension 4, the smallest dimension not covered by the authors, with
  translations read as lattice translations, as on p. 2 of the source.
- Scope and earlier results: the simplex is not new: up to a unimodular map
  it is the simplex of the weighted projective space `P(1,1,1,1,2)`
  (Kasprzyk's thesis, Proposition 9.7.10), and Lee (arXiv:2610.26186,
  Appendix C) uses it and notes that its normalized volume is 6. The
  inequality `μ(P) ≤ d/2` of Conjecture A holds for `P`, with equality;
  only the equality clause is contradicted. `P` satisfies the inequality of
  Conjecture C of the same paper with equality and does not refute it. The
  remarks of Section 5 (arbitrary real translations, by a volume argument;
  Conjecture C and Corollary 4.3 of the source; the equality clause of
  Conjecture D for `k = 1`; the simplices `S(ω)`) are written arguments, and
  so is Lemma 4; none of them is in Lean. Further written variants found in
  the same search (in every dimension `d ≥ 4`, and for Conjecture D with
  `k ≥ 2`) are not claims of the paper.
- Lean: `lean/Research/TaskR/CSS/` (9 modules: the statement file, 6 proof
  modules, `Proof.lean` and `CheckCSS.lean`). The statement file
  `Challenge.lean` defines `P` in `R^4` as a convex hull, the normalized
  volume as a quotient of Lebesgue measures, `Covers P r` (`rP + Z^4 =
  R^4`) and the inductive family `Generated`, and states `NonHollow`,
  `Radius` (2 is the least `r ≥ 0` with `Covers P r`), `Volume` and
  `OutsideList` (`P` is not in `Generated`). **Freezing, in two versions.**
  Version 1 of the statement file was checked against the source, together
  with the reading of the source, by a Codex agent that had written neither
  the statement nor any proof, and approved on 20 November 2026 at 19:31:21
  UTC before it had been compiled; its compilation then failed with a parse
  error (a notation scope was not opened). Version 2 differs from version 1
  only in that line (all definitions and the four target lines are
  byte-identical), compiled without diagnostics, was approved at 19:33:19
  UTC by a second Codex agent that had not written the statement or the
  proofs for this problem, and was frozen at 19:33:34 UTC. Between the
  approval of version 1 and the freeze two proof files were created:
  `Geometry.lean`, revised after the freeze, and `Residues.lean`, which uses none of the definitions of the statement file and was created in its final form; the
  development logs record no compilation of a proof file before 19:33:41
  UTC, after the freeze. OpenAI Codex wrote the statements and the proofs
  and checked the package in two new empty directories on the author's Mac
  (`certificates/css-covering-equality/lean-package/`); the text was written
  by Claude Code. See the disclosure below for the reviews.

**Paper 22: [`papers/a7-terrace`](papers/a7-terrace/note.pdf).**
*A terrace for the alternating group `A_7`.* 9 pages.

- An arrangement `a_1, …, a_n` of the elements of a finite group is a
  terrace if, among the quotients `a_i^(−1) a_(i+1)`, every involution occurs
  exactly once and every other non-identity element `g` occurs, together
  with `g^(−1)`, exactly twice in total. Bailey conjectured that every finite
  group except the non-cyclic elementary abelian 2-groups has a terrace; the
  families of terraced groups are collected in Ollis's dynamic survey
  (Electron. J. Combin. DS10, version 3, 2025, Theorem 32).
- **Theorem 1.** There is a basic terrace of `A_7`, the group of even
  permutations of `{0, …, 6}` (order 2520). It is explicit, found by a
  hill-climbing search in the style of Ollis and stored in the Lean file
  `Data.lean`. As far as the searches show, none of the families of
  Theorem 32 of the survey is known to contain `A_7` (it is simple, its
  order exceeds the computer searches, which reach order 511, and it is not
  known to be sequenceable); a theorem of Müyesser and Pokrovskiy covers all
  sufficiently large non-abelian groups, without an explicit bound. So this
  is a further verified case of Bailey's conjecture. **Corollary 1**, with
  Theorem 9 of the survey (Anderson and Ihrig): every group with a unique
  involution `G` with `G/O(G)Λ(G) ≅ A_7` has a symmetric sequencing, the
  `A_7` case of their reduction of Anderson's conjecture.
- Scope and earlier results: the search method is that of Ollis, and the
  reduction is due to Anderson and Ihrig, whose paper was read only in
  Ollis's paraphrase. Bailey's conjecture, Anderson's conjecture and the
  cases `PSL(2, q)` and `PGL(2, q)` of the reduction are not settled. The
  terrace is not directed (Remark 1: some quotients occur twice), so it says
  nothing about whether `A_7` is sequenceable (Keedwell's conjecture). The
  consequences of Section 4 combine the Lean result with published theorems
  and are not formalized; Remark 1 is a computation outside Lean.
- Lean: `lean/Research/TaskR/A7/` (8 modules: the statement file, 5 proof
  modules, `Proof.lean` and `CheckA7.lean`). The statement file
  `Challenge.lean` takes Mathlib's `alternatingGroup (Fin 7)` and states
  `HasTerrace`: there is a bijection `a` from `{0, …, 2519}` onto the group
  with `a 0 = 1` such that, for every `g ≠ 1`, the number of `i` with
  `a_i^(−1) a_(i+1) = g` or `= g^(−1)` is 1 if `g = g^(−1)` and 2 otherwise.
  The statement does not contain the terrace. The proof checks a certificate
  (the rows, a matching of the quotients) with a checking program that is
  proved correct and evaluated by the Lean kernel (`decide +kernel` on 79
  blocks), and a counting lemma (Lemma 1 of the paper) turns the certificate
  into the statement. A newly started Codex agent that had taken no part in
  finding the terrace and had written neither the statement nor the proofs
  checked the reading of the sources and reviewed the statement file
  against Ollis's paper and survey, and it was frozen on 20 November 2026 at
  19:32:16 UTC; the development logs record only a compilation of the
  statement file itself before that time. OpenAI Codex found the terrace,
  wrote the statements, the encoder and the proofs, and checked the package
  in two new empty directories on the author's Mac
  (`certificates/a7-terrace/lean-package/`); the text was written by Claude
  Code. See the disclosure below for the reviews.

**Paper 23: [`papers/domination-root-radius`](papers/domination-root-radius/note.pdf).**
*The largest domination roots of friendship graphs and of joins with repeated petals.* 11 pages.

- The domination polynomial `D(G, x)` counts the dominating sets of a graph
  by size. The friendship graph `F_m = K_1 ∨ mK_2` consists of `m` triangles
  with a common vertex. Alikhani, Brown and Jahari (*On the domination
  polynomials of friendship graphs*, Filomat 30 (2016); Question 2 of §3 of
  arXiv:1401.2092v2) showed that the moduli of its domination roots are
  unbounded and asked (Question 3.2): what is a good upper bound on the
  modulus of the roots? Rather (arXiv:2604.08998v2) proved the explicit
  bound `1 + √(m/log 2)` and an implicit bound `R_m` with
  `(R_m − 1)² log R_m = m`, which he did not expect to be asymptotically
  sharp.
- **Theorems 1 and 2.** For a fixed graph `B` with at least one vertex and a
  fixed `a ≥ 1`, let `J_m = K_a ∨ mB`. The largest modulus `M_m` of a complex
  root of `D(J_m, x)` is attained, and `M_m/S_m → 1` as `m → ∞`, where
  `S_m = (c s m/(a log m))^(1/c)`, `c = 1 + δ(B)` and `s` is the number of
  distinct closed neighbourhoods of size `c` in `B`. **Corollary 1:** for
  friendship graphs `M_m/√(2m/log m) → 1`; so the moduli grow faster than
  the logarithm suggested by the numerical data of the source.
- Scope and earlier results: the friendship formula, the hyperbola of
  limits and the question are from Alikhani, Brown and Jahari; the formula
  for `D(J_m, x)` follows from standard facts on domination polynomials of
  disjoint unions and joins (Alikhani and Peng; Kotek, Preen, Simon,
  Tittmann and Trinks). For friendship graphs the upper half of Corollary 1
  already follows from Rather's implicit bound, since `R_m ∼ √(2m/log m)`
  (Remark 1, a short computation not in Lean); what is new there is the
  matching lower bound, which shows that Rather's implicit bound is
  asymptotically sharp and his explicit bound is not. The general family is
  new as far as the searches show. A similar phenomenon is known for
  chromatic roots of generalized theta graphs (Brown, Hickman, Sokal and
  Wagner). The results are limits: no explicit bound for a fixed `m` is
  given, and for those Rather's bounds remain the available ones. The
  convergence is slow; the numerical values of the paper are not in Lean.
- Lean: `lean/Research/TaskP/RootRadius/` (14 modules: the statement file,
  11 proof modules, `Proof.lean` and `CheckRootRadius.lean`; namespace
  `TaskP.GraphRootRadius`). The statement file `Challenge.lean` defines
  dominating sets, the domination polynomial over `ℂ` as a sum over the
  dominating sets of the actual graph, the join `petalJoin a m B`, the
  numbers `c` and `s` (`s` counts distinct closed neighbourhoods), the
  largest modulus `rootRadius` as a supremum over all complex roots, and the
  scale `S_m`; it states `Attainment` (the supremum is a maximum, for all
  `a, m ≥ 1` and every `B`), `GeneralAsymptotic` (Theorem 2, for every
  finite nonempty `B` and every `a ≥ 1`) and `FriendshipAsymptotic`
  (Corollary 1). Its only proofs are the two short checks that the
  adjacency of `petalJoin` is symmetric and irreflexive. One Codex agent,
  which had taken part neither in the proof nor in drafting the statement,
  checked the reading of the source and reviewed the statement file against
  it, and it was frozen on 20 November 2026 at 18:06:37 UTC; the file times
  and the development logs show no proof file before that time. OpenAI
  Codex wrote the statements and the proofs and checked the package in two
  new empty directories on the author's Mac
  (`certificates/domination-root-radius/lean-package/`); the text was
  written by Claude Code. See the disclosure below for the reviews.

**Paper 24: [`papers/bar-tiling-defect`](papers/bar-tiling-defect/note.pdf).**
*Multisets of bars that do not tile a `2 × n` rectangle: the optimal growth order.* 10 pages.

- Gajdzica, Visser and Zakarczemny (*Rectangle partitions generalizing
  integer partitions*, Ann. Comb., published online 28 April 2026;
  arXiv:2509.20495v2) count partitions of a rectangle into blocks. Let
  `D_k(n) = p_k(2n) − p_{k,1}(2, n)` be the number of multisets of bars
  `1 × ℓ`, `ℓ ≤ k`, of total area `2n` that cannot be arranged to tile the
  `2 × n` rectangle. In Remark 5.11, from conjectured formulas for
  `4 ≤ k ≤ 8`, they observe that this difference is `O(1)` for `k ≤ 5`,
  `O(n)` for `k = 6, 7` and `O(n²)` for `k = 8`, and they ask for a tight
  upper bound for all `k`.
- **Theorem 1.** With `e_k = max(0, ⌊k/2⌋ − 2)`: (a) `D_k(n) = 0` for
  `k ≤ 2`; (b) for every `k ≥ 3`, `D_k(n) ≤ C (n + 1)^(e_k)` for all
  `n ≥ 1`; (c) for every `k ≥ 3`, `(n + 1)^(e_k) ≤ C D_k(n)` for arbitrarily
  large `n`; (d) for `k ≥ 6`, the same for every large odd `n`. **Corollary
  1:** the three observations of Remark 5.11 hold unconditionally and are
  sharp. The proof uses a two-row criterion for tileability, a bounded
  Bézout argument and families of bars of even length.
- Scope and earlier results: the counts, the explicit formulas for
  `k, l ≤ 3` and the conjectured formulas of Table 2 are those of the
  source; Shaikh (arXiv:2609.13305) proved the neighbouring Conjecture 5.10
  and does not address Remark 5.11; three other 2026 papers on rectangle
  partitions (Gajdzica and Zakarczemny, twice; Shukla) treat different
  questions. The answer is in the sense of the optimal polynomial order; the
  matching lower bound is claimed only along subsequences (every large odd
  `n` for `k ≥ 6`, every `n ≡ 2 (mod 3)` for `3 ≤ k ≤ 5`), nothing is
  claimed about the lower limit, and the constants are not explicit. The
  two-row criterion is proved in Lean on the way but is not a frozen
  statement; the specialization of Corollary 1 and the computed values are
  not in Lean.
- Lean: `lean/Research/TaskP/RectangleDefect/` (18 modules: the statement
  file, 15 proof modules, `Proof.lean` and `CheckRectangle.lean`). The
  statement file `Challenge.lean` describes a multiset of bars by its vector
  of counts and defines `tiles m n` geometrically, as in Definition 1.2 of
  the source: every bar occurrence gets its own real anchor and direction,
  the closed bars cover exactly `[0, 2] × [0, n]` and distinct occurrences
  have disjoint interiors; `defect k n` is `D_k(n)`, and `SharpBound` states
  the finiteness of the sets counted (so the counts are true cardinalities)
  and parts (a)–(d) of Theorem 1, for `n > 0` as in the source. **An earlier
  draft** of the statement (`candidate-01`) used cells with natural-number
  anchors; its reviewer returned it, asking that the real-coordinate
  definition of the source be covered. The revised file was reviewed against
  the source by a Codex agent that had written neither the statement nor the
  proofs, and frozen on 20 November 2026 at 18:06:09 UTC; the file times and
  the development logs show no proof file before that time. OpenAI Codex
  wrote the statements and the proofs and checked the package in two new
  empty directories on the author's Mac
  (`certificates/bar-tiling-defect/lean-package/`); the text was written by
  Claude Code. See the disclosure below for the reviews.

**Paper 25: [`papers/minkowski-length-simplices`](papers/minkowski-length-simplices/note.pdf).**
*Lattice simplices whose Minkowski length exceeds the lattice diameter, and dilates whose Minkowski length is not quasi-linear.* 11 pages.

- The Minkowski length `L(P)` of a lattice polytope is the largest number of
  lattice polytopes of positive dimension whose Minkowski sum is contained
  in `P`; the lattice diameter `ℓ(P)` is one less than the largest number of
  collinear lattice points in `P`. Soprunov and Soprunova (*Eventual
  quasi-linearity of the Minkowski length*, European J. Combin. 58 (2016);
  arXiv:1412.4404v2) proved that `L(tP)` is eventually quasi-linear and
  asked whether it is always quasi-linear (Problem 2) and whether `L = ℓ`
  for every lattice simplex (Problem 3).
- **Theorem 1.** `T = conv{(1,0,1), (3,3,1), (2,0,3), (0,3,3)}` has
  `ℓ(T) = 1` and `L(T) = 2`, and in every dimension `d ≥ 3` there is a lattice
  simplex with `ℓ = 1` and `L = 2`. **Theorem 2.** The empty tetrahedron
  `U = conv{0, (1,0,0), (0,0,1), (13,18,1)}` has `L(U) = 1` and `L(tU) = 3t`
  for every `t ≥ 2`, so `L(tU)` is not quasi-linear; the same holds in every
  dimension `d ≥ 3`. Lattice pyramids carry both examples to higher
  dimensions. **Corollary 1:** with the source's result for triangles,
  Problem 3 is true for `d ≤ 2` and false for every `d ≥ 3`.
- Scope and earlier results: both tetrahedra are known objects: `T` is one
  of the tetrahedra with eight lattice points enumerated by Blanco and
  Santos (its entry in their database was not identified), and `U` is an
  empty tetrahedron (White's classification); Meyer, Soprunov and Soprunova
  (2022) give `L(2U) ≥ 3`, without discussing the whole sequence or the
  problems. The sequence `L(tU)` is linear from `t = 2` on, in agreement with
  the eventual quasi-linearity of the source; only its first term breaks
  quasi-linearity. Problem 1 of the source is not addressed. The paper notes
  that the identity `L_1(P) = ⌊λ_1(P)⌋` used in Remark 2.21 of the source
  fails for `U`, so that the conclusion of that remark is not supported in
  general (it is not shown to be false); the main theorem of the source is
  not affected. This remark, Corollary 1 for `d ≤ 2` and the periodicity
  remark are not formalized.
- Lean: `lean/Research/TaskP/GeomSimplex/` (16 modules: the statement file,
  13 proof modules, `Proof.lean` and `CheckSimplex.lean`). The statement file
  `Challenge.lean` defines lattice polytopes and simplices in `ℝ^d` as real
  convex hulls of lattice points, full-dimensionality by affine
  independence, dilates, `packs P k` (`P` contains the Minkowski sum of `k`
  lattice polytopes with at least two lattice points each), `lengthIs P n`
  (`L(P) = n`), `diameterOne P` (`ℓ(P) = 1`) and `quasiLinearLengths P`
  (Definition 1.3 of the source), and states `TetrahedronDiameter`,
  `TetrahedronDilations`, `EveryDimensionDiameter` and
  `EveryDimensionDilations`. A Codex agent that had written neither the
  statement nor the proofs reviewed the statement file against the source,
  and it was frozen on 20 November 2026 at 18:06:09 UTC; the development logs
  record no compilation of a proof file before that time. OpenAI Codex wrote
  the statements and the proofs and checked the package in two new empty
  directories on the author's Mac
  (`certificates/minkowski-length-simplices/lean-package/`); the text was
  written by Claude Code. See the disclosure below for the reviews.

**Paper 26: [`papers/css-covering-minima`](papers/css-covering-minima/note.pdf).**
*Covering minima of the standard terminal simplex and a discrete surface area bound for the covering radius of simplices.* 13 pages.

- The covering radius `μ(K, Λ)` of a convex body is the least `μ ≥ 0` such
  that `μK + Λ` is the whole space, and the `i`-th covering minimum `μ_i(K)`
  (Kannan and Lovász) is the largest covering radius of a linear projection
  of `K` to dimension `i` under which `Z^n` is mapped onto a lattice.
  González Merino and Schymura (*On densities of lattice arrangements
  intersecting every i-dimensional affine subspace*, Discrete Comput. Geom.
  58 (2017); arXiv:1605.00443v1, Remark 4.9) conjectured that the standard
  terminal simplex `T_n = conv{−1, e_1, …, e_n}` satisfies `μ_i(T_n) = i/2`
  for `1 ≤ i ≤ n`. Codenotti, Santos and Schymura (*The covering radius and
  a discrete surface area for non-hollow simplices*, Discrete Comput. Geom.
  67 (2022); arXiv:1903.02866v2) stated this as their Conjecture B, showed
  that it is equivalent to the inequality part of their Conjecture A
  (`μ(P) ≤ d/2` for non-hollow lattice `d`-polytopes), proved it for
  `i ≤ 3`, and proposed Conjecture C, a discrete analogue of Hadwiger's
  inequality: `μ(S) ≤ (1/2) Surf(S)/Vol(S)` for every `d`-simplex with the
  origin in its interior and rational vertex directions, where `Surf` is a
  discrete surface area obtained by projecting along the vertex directions.
  Conjecture C was known for `d ≤ 2`, for some families, and in general up
  to a constant factor; Krivokuća (arXiv:2601.15173, 2026) proved weaker
  general bounds for Conjecture B and listed it as open.
- **Theorem 1** (Conjecture B). For all `1 ≤ i ≤ n`: every projection
  `p` with `p(Z^n)` a lattice satisfies `p(Z^n) + (i/2) p(T_n) = R^i`, and
  for the coordinate projection `i/2` is the least such scale; so
  `μ_i(T_n) = i/2`. **Theorem 2** (Conjecture C). For primitive integer
  vectors `u_0, …, u_d`, positive reals `ω_i` and `S = conv{ω_i u_i}` with
  the origin in its interior, `Z^d + rS = R^d` with
  `r = (D_0 + … + D_d)/(2V)`, where `V` and `D_i` are explicit determinants
  equal to the normalized volume of `S` and of its projections along the
  vertex directions. **Theorem 2′** gives the same with the volumes taken as
  Lebesgue measures of actual projected sets. Both proofs average sawtooth
  functions over their jump points (Lemma 5, elementary, for which no
  novelty is claimed); for Theorem 1 this is combined with an induction that
  splits a rational kernel along the support of a nonnegative vector, for
  Theorem 2 with determinant identities for the barycentric coordinates of
  the origin.
- **Corollary 3** (not formalized). Every non-hollow lattice `d`-polytope
  satisfies `μ(P) ≤ d/2`: this is the d/2 bound of Conjecture A, and it
  follows from either theorem by published arguments of Codenotti, Santos
  and Schymura (the proof of their Theorem 1.2, or of their Corollary 4.3,
  with their reduction to simplices). The equality clause of Conjecture A
  does not follow, and it fails in dimension 4 (Paper 21); Corollary 3 is
  not a proof of Conjecture A. Conjecture D of the same paper and the case
  of simplices with the origin on the boundary are not addressed.
- Scope and earlier results: Conjecture B was known for `i = n` (González
  Merino and Schymura), `i = 1` and `i ≤ 3`; the primitive integer relation
  among the vertex directions and the chord form of the bound are in
  Codenotti, Santos and Schymura. The paper records that the search for
  problems in which the conjectures were selected had already produced
  written arguments: for Conjecture B by a different route, and for
  Conjecture C the argument of the paper in chord form (see the disclosure
  below); these notes are not claims of the paper. Section 5 (Corollary 3,
  the remarks on equality and the other written arguments) is not
  formalized, and neither is the independence of the projected volumes from
  the choice of projection (Lemma 11).
- Lean: `lean/Research/TaskS/` (25 modules: `B/` with the statement file,
  8 proof modules, `Proof.lean` and `CheckB.lean`; `C/` with the statement
  file, 9 proof modules, `Proof.lean`, `CheckC.lean` and
  `MeasureAudit/CheckC.lean`; and `Shared/Sawtooth.lean`, the averaging
  lemma, used by both). `B/Challenge.lean` defines `T_n` as a real convex
  hull, `LatticeProjection p` (a linear surjection mapping `Z^n` onto the
  integer combinations of some real basis of `R^i`, that is, onto a
  lattice) and `Covers p r` (`p(Z^n) + r p(T_n) = R^i`), and states
  `ConjectureB`: for all `0 < i ≤ n`, every admissible `p` covers at scale
  `i/2`, and for some admissible `p`, `i/2` is the least such scale.
  `C/Challenge.lean` defines primitive vectors, the simplex with vertices
  `ω_i u_i`, the determinants `V` (`volume`, the file's own definition) and
  `D_i` (`projectedVolume`) and `Covers`, and states `conjectureC` for every
  dimension `d = n + 1 ≥ 1`. The reading of the sources was checked by a
  Codex agent that had written neither statement and had not taken part in
  the earlier search for problems; the same agent reviewed both statement
  files, after checking that each compiled without diagnostics, and both
  were frozen on 20 November 2026 at 22:30:34 UTC; according to the
  development logs no proof file was compiled before 22:30:49 UTC. An
  earlier draft of the statement for Conjecture B had failed to compile
  before the review. OpenAI Codex wrote the statements and the proofs and
  checked them in two new empty directories on the author's Mac
  (`certificates/css-covering-minima/lean-package/`); the text was written
  by Claude Code. See the disclosure below for the reviews.

**Paper 27: [`papers/heisenberg-125-determinants`](papers/heisenberg-125-determinants/note.pdf).**
*The integer group determinants of the Heisenberg group of order 125.* 13 pages.

- For a finite group `G` and an integer-valued function `f` on `G`, the
  group determinant is `det(f(g h⁻¹))` with rows `g` and columns `h`, and
  `S(G)` is the set of its values. Olga Taussky-Todd asked in 1977 which
  integers are circulant determinants with integer entries; the same
  question is asked for every finite group. Complete answers are known for
  all groups of order at most 14 (Pinner and Smyth, Ramanujan J. 51 (2020))
  and, according to Panraksa, for all groups of order less than 20 and both
  groups of order 25. Mossinghoff and Pinner (*The integer group
  determinants for the Heisenberg group of order p³*, Michigan Math. J. 74
  (2024); arXiv:2108.04870v1, whose numbering the paper cites) determined
  `S(H_3)`; for `p = 5` they showed that the values prime to 5 are the
  integers `m` with `m^4 ≡ 1 (mod 125)` (Corollary 3.2) and that every
  nonzero value divisible by 5 is divisible by `5^28`, with `5^28` exactly
  dividing some value (Theorem 3.4). The multiples of 5 in `S(H_5)` were
  left undetermined; their example for `p = 5` has a cofactor of about
  `2.3·10^69`.
- A prime `ℓ` is *visible* if `ℓ ≡ 1 (mod 5)` and some element of
  `Z[ζ_5]` of norm `ℓ` is not congruent modulo 5 to a unit of `Z[ζ_5]`
  (Definition 1; by Lemma 2, "some" can be replaced by "every"). Below 600
  the primes `ℓ ≡ 1 (mod 5)` that are not visible are 211, 281, 421, 461
  and 521.
- **Theorem 1.** `S(H_5)` consists of the integers `m` with
  `m^4 ≡ 1 (mod 125)`, all multiples of `5^33` (0 included), and the
  integers `5^28·n` with `n ≠ 0` divisible by a visible prime.
  Equivalently, for `m ≠ 0` with `v = v_5(m)`: if `v = 0`, `m` is a value
  if and only if `m^4 ≡ 1 (mod 125)`; if `1 ≤ v ≤ 27`, it is not; if
  `28 ≤ v ≤ 32`, it is if and only if `m` has a visible prime factor; if
  `v ≥ 33`, it is. **Corollary 1.** The least positive value divisible by 5
  is `11·5^28 = 409781932830810546875`, the group determinant of
  `1 + x + y + y² + xy²`. **Corollary 2.** `5^32` is not a value, so 33 is
  the least `k` with `5^k Z ⊆ S(H_5)`. For example `11·5^28`, `31·5^30` and
  `211·11·5^28` are values, while `211·5^28`, `3·5^29` and `5^28` are not.
- The proofs use the factorization of Mossinghoff and Pinner into the
  augmentation, the norms of six "ray" values and the fifth power of the
  norm of a five-dimensional factor `D`, and their congruence for `D`. For
  necessity, a phase argument shows that if every ray value is `π = 1 − ζ`
  times an element congruent modulo 5 to a unit, then the valuation is at
  least 33; a visible prime is what breaks this balance. For sufficiency,
  three elements of `Z[C_5 × C_5]` found by Panraksa serve as seeds; a row
  shift inserts an element of `Z[ζ_5]` into one ray, and an exact lift
  fixes `D` by explicit cofactor certificates.
- Scope and earlier results: the factorization, the congruence, both
  directions of the description of the values prime to 5 and the bound
  `5^28` are due to Mossinghoff and Pinner; the seeds are from Panraksa
  (arXiv:2608.04267v1, Proposition 3.1), who used them to prove
  `S(C_5^2) ∩ 5Z = 5^8 Z`; his description of the two lowest valuations for
  `C_7 × C_7` by conditions on ideals of `Z[ζ_7]` (arXiv:2609.09542v1) is a
  precedent for a criterion of this kind; and membership of a given integer
  in `S(G)` can in principle be decided by the lattice isomorphism
  algorithms of Bley, Hofmann and Johnston, which give no explicit
  description. What is new is the description of the multiples of 5: the
  inclusion `5^33 Z ⊆ S(H_5)`, the visible-prime criterion at the
  valuations 28 to 32, and the minimum. Corollary 1 is a special case of
  Theorem 1, but it was stated and verified separately, before Theorem 1.
  Corollary 2 is not a separate Lean statement. Remark 1 (by class field
  theory the visible primes have density 4/5 among the primes
  `ℓ ≡ 1 (mod 5)`, and, as a numerical observation for the primes below
  20,000, `ℓ` is visible exactly when the golden-ratio unit is not a fifth
  power modulo a prime above `ℓ`) is not formalized and not used. Lemma 2
  is proved in the text but not in Lean; Theorem 1 does not need it, since
  visibility is defined with "some".
- Lean: `lean/Research/TaskU/` (63 modules: `H5/` with the 37 files of the
  minimum, that is, the statement file `Challenge.lean`, 33 proof modules,
  the audit file `Audit.lean` and the check files `CheckWitness.lean` and
  `Check.lean`; `H5B/` with the 26 further files of the classification, that
  is, the statement file `ChallengeB.lean`, 23 proof modules, `ProofB.lean`
  and `CheckB.lean`). `Challenge.lean` defines `H` as triples `⟨a, b, c⟩`
  over `ZMod 5`, standing for `x^a y^b z^c`, with the product
  `⟨a + a′, b + b′, c + c′ + b·a′⟩`, the witness, and
  `groupDet f = det(f(g * h⁻¹))` for every `f : H → ℤ`, and states
  `witnessValue` (`groupDet witness = 11 * 5 ^ 28`) and
  `leastPositiveMultiple` (`11 * 5 ^ 28` is the least element of the set of
  positive values divisible by 5). `ChallengeB.lean` uses `H` and
  `groupDet` and, from `Cyc5.lean`, the arithmetic of `Z[ζ_5]` in the basis
  `1, ζ, ζ², ζ³` (`Cyc5.mul` and `Cyc5.norm`, the full field norm); it
  defines `congrFive` (congruence modulo `5Z[ζ_5]`), `unitImage` (the residue
  is that of an element with an inverse) and `visible q`, and states
  `fullSpectrum`: for every integer `m`, `m` is a value if and only if
  `m^4 ≡ 1 (mod 125)`, `5^33 ∣ m`, or `m = 5^28·n` with `n ≠ 0` and a
  visible prime dividing `n`. Each statement file was checked against the
  source by a Codex agent that had not written it and frozen on 21 November
  2026, `Challenge.lean` at 01:32:25 UTC and `ChallengeB.lean` at 03:22:48
  UTC; according to the development logs no proof file was compiled before
  these times, and the 37 files of the minimum were not changed when the
  classification was added. The witness value is computed by the kernel
  through a proved triangular certificate. OpenAI Codex wrote the
  statements and the proofs and checked them in two new empty directories
  on the author's Mac (`certificates/heisenberg-125-determinants/lean-package/`);
  the text was written by Claude Code. See the disclosure below for the
  reviews.

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
entry's indexing and initial coefficients. With these normalizations each of
the thirteen series entries has exactly one solution in `ℤ[[x]]` (for A273958
one pair `(C, A)`, and for A338633 and A338634 one series admitting the tails
of the continued fraction); this and the first terms are proved in Lean in
version 2, so the theorems are not vacuous.

| Entry | Defining equation | Theorem |
| --- | --- | --- |
| A389472 | `A(x² + x³) = x²(1 + A(x))` | `3 ∣ a(3n − 1)` for `n > 1` |
| A240998 | `A(x)² = x + A(x + 2x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 |
| A295762 | `A(x − 2A(x²)) = x + A(x²)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 (the entry conjectures one direction) |
| A273958 | `xA + x²A² = C²`, with `C = x + C²` | `a(n)` is odd iff `n = 2·4^k − 1` |
| A301933 | `A = x(1 + 4AA′)/(1 + AA′)` | for `n ≥ 1`, `a(n)` is odd iff `n` is a power of 2 |
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

## Known issues

Problems found after publication by our own re-checks, including an
independent check of Papers 1–8 by a second AI system (OpenAI Codex),
completed on 27 September 2026. That check found no error that affects a
main result; it found the problems below. The papers have since been
corrected in their versions 2: version 1.9.0 corrected Paper 4, version
1.10.0 corrected Paper 3, version 1.11.0 corrected Paper 8, version 1.12.0
corrected Paper 5, version 1.13.0 corrected Paper 6, version 1.14.0 corrected
Paper 7, version 1.15.0 corrected Paper 2, and version 1.16.0 corrected Paper 1.
Version 1.17.0 adds version 3 of Paper 1, which extends Theorem 5 and corrects
no error of version 2.

- **Paper 6, Theorem C is not new (corrected in version 2 of the paper, in
  version 1.13.0).** Lou and Wang proved it earlier, in Discrete Appl. Math.
  388 (2026) 142–145, Proposition 2 (see Prior work); version 2 attributes it
  to them. The determination of the spectrum in Theorem B, Proposition C′ and
  the extension of Theorem C rested on cited theorems of Kasami and Tokura
  (1970) and of Kasami, Tokura and Azumi (1976) that we could not consult and
  have not formalized; version 2 removes them (the title of version 1, "The
  weight spectrum of the Reed–Muller code RM(7,14) up to four weights", is
  changed). Theorems A and B (its explicit codewords), the Corollary and
  Propositions D, E and F are unchanged.
- **Paper 6, the four values left open (later work, not a correction).** The
  paper (version 2) still describes 322, 326, 330 and 334 as open. According
  to later work of Lou and Wang (arXiv:2610.36687v1), whose abstract excludes
  the eight conjectured weights without listing them, they are not weights;
  we have not reviewed that proof. See the section on Paper 6.
- **Paper 5, a definition (corrected in version 2 of the paper, in version
  1.12.0).** In Section 3 of version 1, `top(x)` and `bot(x)` include the
  singleton blocks of partial Brauer diagrams, which contradicts the
  definition of a half-diagram, so Proposition 3.1(a) is not well defined as
  literally stated (PB₁ is the smallest example). The proofs use the intended
  reading, with only the 2-element blocks, which version 2 states. Version 2
  also removes the claims of version 1 for which we have no formal proof:
  the results of the computer checks of its Section 8, Remark 4.5(4) (a
  comparison of Lemma 4.4 with a criterion of Araújo et al.), and several
  side statements, among them the identifications with Green's relations
  (listed under "Changes in version 2" at the end of Section 9 of the
  paper). The theorems are unchanged.
- **Paper 1, computer-assisted results withdrawn (version 2 of the paper,
  in version 1.16.0).** Version 1.5 claimed Theorem 5 for
  `3 ≤ min(a, b) ≤ 8`, and Proposition 15 for eleven exponent pairs, on the
  strength of exact certificates computed by programs; these were not
  formalized. Version 2 withdraws both claims, the certificates of
  Section 12 with their counts, programs and negative controls, and the list
  of computational cross-checks, because they have no formal proof; the
  withdrawal does not
  report an error in those computations. Section 1 no longer says that the
  conjecture is open for `min(a, b) ≥ 9`. Version 2 also removes the
  restatement of the general results of Le and Sander in Remark 16, and the
  opening and last sentence of Remark 30, which compared two differences with
  `Θ` without a precise bound. Theorems 1–4 are unchanged, and Theorem 5 is
  kept for `min(a, b) ≤ 2`. Earlier, the README had said until version 1.7.1
  that Proposition 15 covered "every shape with `(a+1)(b+1) ≤ 27`"; it
  covered exactly the eleven exponent pairs listed in the paper. Version 3 of
  the paper (in version 1.17.0) proves, by a new argument with a Lean proof,
  Theorem 5 for every order of equal parity in which one of the primes is 3;
  this includes the orders with a prime 3 among those that version 1.5 had
  claimed with computer assistance. The orders with `p, q ≥ 5` and
  `min(a, b) ≥ 3` remain withdrawn and are not claimed.
- **Paper 4, three missing hypotheses (corrected in version 2 of the
  paper, in version 1.9.0).** Lemma 1 needs `S` to be nonempty: for
  `S = ∅` conditions (a) and (b) hold, but the empty graph is not connected
  (the convention we follow with Mathlib). Adding a false twin preserves
  distance-heredity only if the result is connected (a single vertex with a
  false twin gives two isolated vertices). A connected graph has a vertex
  whose removal leaves it connected only if it has at least two vertices.
  The proofs use these statements only where the extra hypotheses hold, so
  Theorems A, B and C are not affected. Version 2 also removes three claims
  of version 1 that are not formally verified: the numbers of connected
  labelled graphs in Section 4, the last sentence of Remark 5 (a uniqueness
  statement for `H₁₁`), and Section 6 of version 1 (computations on
  distance-hereditary graphs), apart from its last sentence, which now ends
  Section 5.
- **Paper 8 (corrected in version 2 of the paper, in version 1.11.0).**
  Version 2 removes the computational claims of version 1 that are not
  formally verified: that every tree with 3 to 24 vertices, and every tree of
  diameter at most 4 with at most 44 vertices, has such a switching; the
  counts of non-even pairs and of good switchings in Section 6; and the
  computed values in Remark 8.1. It states and proves the bound
  `t_r ≤ b* + k`, which version 1 used without proof, and it speaks of
  13,376 branch multisets rather than trees (for example `(2,0,0,0)` and
  `(3,0,0)` both give the double star D(2,3)). The theorems are unchanged.
- **Paper 3 (corrected in version 2 of the paper, in version 1.10.0).**
  Version 2 removes two claims of version 1 for which we have no formal
  proof: the normal approximation `i_{1/8}(G) = (1/2 + O(n^{-1/4})) 2^n` in
  Remark 10, with reading R6 at `γ = 1/8`, and the count of 19,355 labelled
  4-regular graphs on eight vertices in Section 8. It also removes three
  unformalized side remarks (on Mantel's theorem, on an explicit `n₀` in
  Theorem D, and on where the infimum defining `ρ(d, γ)` is attained). In
  version 1 the table of readings called the minimality of `(6,3,1/18)`
  "formally verified", although only the counterexample itself was; in
  version 2 both are. The theorems are unchanged.
- **Paper 6, property (P2) (corrected in version 2)** divides by `r`, so it
  needs `r ≥ 1`, while the introduction of version 1 allows `r = 0`. The
  paper uses (P2) only with `r = 6`.
- **Paper 7 (corrected in version 2).** Version 1 omitted the offsets
  `P − |K_p|` and `Q − |K_q|` from the bounds of program D at 0 and ±1. It
  said that the families `C_{6,1}(0,a,a,2a,a,a)` and `C_{4,1}(0,a,2a,a)` start
  at 42 and 68 vertices, which needs `a ≥ 1`: for `a = 0` they are the cycles
  `C_6` and `C_4`. Corollary 3.1 is superseded by later work of Braga, Moraes
  and Santos (see the section on Paper 7). The theorems are unchanged.
- **Paper 2, implicit normalizations (stated in version 2 of the paper).** For
  A240998, "minus 1" refers to the solution with constant term 1, as in the
  OEIS entry; the equation forces the constant term to be 0 or 1. This README
  said until version 1.14.0 that a solution with constant term 0 exists; we
  state nothing on that, and it is not in Lean. The equation `F = x/(1+FF′)` determines
  `F` only when read with `F(0) = 0`: cleared of denominators, it has a
  second solution modulo 2, one plus the Catalan series. The equation of
  A389472 does not determine `a(2)`; the entry has `a(2) = 1`. The theorems
  hold as stated for these normalizations.
- **README wording corrected in version 1.8.0:** what Lean covers for
  Papers 3 and 4 (above; for both now superseded by their versions 2), and the count of new weights in Paper 6
  (Theorem A gives 17 weights, 14 of them among the 22 open values).

## What is verified, and how

| Claim | Lean 4 declarations | Independent computation |
| --- | --- | --- |
| Paper 1 (version 3): Theorem 5 when one of the primes is 3 and `min(a,b) ≥ 3` (every exponent, every other odd prime), and the steps of its proof in Section 13: conditions (S_a) on both regions, (C_a) at `(3, q)` for real `q ≥ 5`, (F_a) at `(3, q)` for `q = 5`, `q = 7` and real `q ≥ 8`, and the statements of Lemmas and Propositions 32–43 that Table 1 of the paper lists; with the row below, every result of version 3 | `CodexPaper1.TaskE.check_SameParityThree` (in `lean/Research/TaskE/Main.lean`) for the main statement `SameParityThree` of the frozen statement file `lean/Research/TaskE/Challenge.lean` (SHA-256 `24b59fb5…e009f`), and the theorems restated in `lean/Research/TaskE/FinalTaskEAudit.lean`; the 20 auxiliary statements of six further frozen statement files in the same directory (`ChallengeS.lean`, `ChallengeF.lean`, `ChallengeFC.lean`, `ChallengeC0.lean`, `ChallengeC1.lean`, `ChallengeC1Alt.lean`) are proved in its proof modules | the 115 modules of the package (the 70 of version 2, unchanged, and 45 new) built and checked with `leanchecker` in two new empty directories, and again in a clean rebuild of the whole project (`certificates/icg-q3-general/lean-package-v3/`); 273 axiom listings in each build, covering 210 declarations, of which 209 use exactly the three standard axioms and one uses none; seven tests of the statement file; not checked with comparator or nanoda (see below). `UniformConditionsBothRegions` (the three conditions at every point of both regions for every `a ≥ 3`) is only a definition and is not proved; (F_a) and (C_a) are not claimed at any point of the region `p ≥ 5, q ≥ 3`, so nothing here concerns `p, q ≥ 5` with `min(a,b) ≥ 3`. No Lean statement depends on Jiang–Yang |
| Paper 1 (version 2): every result, the 51 statements of the frozen statement files (31 main and 20 supplementary): Theorems 1–4, Theorem 5 for `min(a,b) ≤ 2`, the summaries for opposite parity and for `min(a,b) ≤ 2`, Proposition 6, Lemmas 7, 8, 10, 11, 18–24 and 26–29, Remarks 9 (with the closed forms of `d_k` and `δ_k`), 13, 16, 17 and 30, Theorems 12 and 25 (the sign-matrix inequalities), Proposition 31 as an implication, and the facts of the text listed in Table 1 of the paper (Ramanujan sums, the path and the potential, the parameter regions, the cell values and matrix bounds, the graphs for `n = pq`, multiplicative sets) | `CodexPaper1.check_*` in `lean/Research/Backfill/Paper1/FinalContractAudit.lean`, one theorem for each of the 51 statements of the frozen statement files `Challenge.lean` (SHA-256 `e2823ed9…bff1`) and `SupplementStatements.lean` (SHA-256 `6cb1815c…a4da`) in `lean/Research/Backfill/Paper1/`; the version-1.5 declarations in the rows below remain | the 70 modules built and checked with `leanchecker` in two new empty directories, and again in a clean rebuild of the whole project (`certificates/icg-q3-general/lean-package-v2/`); only the three standard axioms; 84 known-answer tests and 10 regression tests of the statement files; not checked with comparator or nanoda (see below). No Lean statement of version 2 says that the conditions of Proposition 31 hold for any `a` (version 3 proves them at the points of the row above); Conjecture 14 is only a definition, and nothing proves or assumes it. The programs of version 1.5 are no longer used |
| Paper 1 (version 1.5): unique maximiser for `p^(2r)·3^(2s+1)`, `p ≥ 5`; value of the maximum, expressed through the norms `d_k(x) = ‖T_k(x) s_k‖₁` (their closed form was not formalized in version 1.5; it is in version 2); the sign-matrix inequality (all real `p ≥ 5`, `q ≥ 3`, all exponents); energy formula for all `p^a q^b`; Jiang–Yang Theorem A for all distinct odd primes | `ICGGeneral.jiang_yang_q3`, `jiang_yang_q3_value`, `energy_DstarPQ`, `thm5_le`, `thm5_eq`, `energy_icgAdj_pq`, `jiang_yang_thmA`, `checkerboard_unique_max_odd` | exhaustive exact searches over all divisor sets (shapes and primes listed in the paper); sign-matrix enumeration for `(a+1)(b+1) ≤ 25`; floating-point spectra of the actual graphs (`certificates/icg-q3-general/`) |
| Paper 1 (version 1.5), Theorem 3: maximal energy for `pq^m` and `p^m q`, `m` odd; both maximisers; uniqueness | `ICGEqualParity.corollaryA` | exact arithmetic for every step (`verify_1m.py`); graph spectra by FFT and dense eigenvalues (`certificates/icg-equal-parity/`) |
| Paper 1 (version 1.5), Theorem 4: maximal energy for `p²q^b` and `p^b q²`, `b` even; both maximisers; uniqueness; the sign-matrix inequality for the exponent 2 (Theorem 25) | `ICGEqualParityB.theoremB`, `theoremB_swap`, `corollaryB`, `thmB'`; the 325 inequalities of a first proof, not needed for the paper's proof, in `ICGEqualParityBCert1`–`6` | exhaustive searches over all divisor sets of 21 orders `p²q^b`, `b ∈ {2, 4, 6}`, up to `n = 1 058 841`, with exact eigenvalues from Ramanujan sums (`review/rv_graph.py`); exact replays of the steps of the proof (`paper-checks/`); both in `certificates/icg-equal-parity/theorems-b-c/` |
| Paper 1, version 1.5 only (withdrawn in version 2): Theorem 5 for `3 ≤ min(a,b) ≤ 8`, and Proposition 15 (Proposition 13 in version 1.2) for the eleven exponent pairs with `min(a, b) ≥ 2` and `(a+1)(b+1) ≤ 27` | not formalized; withdrawn in version 2 because they have no formal proof (not because an error was found) | the certification programs and logs of version 1.5 remain as its records: for Theorem 5, `generic_prover.py`, `generic_fast2.py` and the certifiers of two referee agents (`review2/c3_certify.py`, `review3/rv3_certify.py`) in `certificates/icg-equal-parity/theorems-b-c/`; for Proposition 15, `cert22.py`, `cert_fast.py`, a SymPy rebuild and a negative control in `certificates/icg-equal-parity/`. No result of version 2 rests on them |
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
| Paper 2 (version 2): every mathematical result, the 84 statements of the frozen statement file: Theorems 4–10, 12 and 13, Lemmas 1–3 and the other tools of Section 2, the remarks on classical results (the reductions modulo 2, the Catalan parity, the correspondence for linearised polynomials), the remarks after Theorems 6, 8 and 9, Remark 11, the remark on additive series in Section 6, the stronger readings that fail (A184894 at index 365, A107099 at `x^729`), and, new in version 2, existence and uniqueness for thirteen entries and the first terms for fourteen | `BackfillPaper2.Check.check_*`, one theorem for each of the 84 statements of the frozen statement file `lean/Research/Backfill/Paper2/Challenge.lean` (SHA-256 `9ee68640…8caf`), whose comments are frozen with it, date from version 1.2.1 and are not statements (see `certificates/oeis-hanna/lean-package-v2/README.md`); the version-1 declarations in the rows above remain | the 59 modules other than `Check.lean` built and checked with `leanchecker` in two new empty directories, and all 60 in a clean rebuild of the whole project (`certificates/oeis-hanna/lean-package-v2/`); only the three standard axioms; 43 tests and 7 regression tests of the statement file; not checked with comparator or nanoda (see below). No Lean statement mentions the OEIS, the literature or the numerical checks |
| Paper 3 (version 2): every result, the 60 statements of the frozen statement file: Theorems A, B, B′ and D, Proposition C, Corollary 5, Lemmas 1, 3, 6, 7 and 8, Proposition 2, Remarks 4 and 9–12, the smallest counterexample `(6,3,1/18)` and its minimality, Tables 1, 3 and 4, the readings of Section 2, the case of the theorem of Sah, Sawhney, Stoner and Zhao used in the paper, the Kahn–Zhao theorem and the 2-switch theorem | `BackfillPaper3.Check.check_*`, one theorem for each of the 60 statements of the frozen statement file `lean/Research/Backfill/Paper3/Challenge.lean` (SHA-256 `846efb56…8777`); the version-1 declarations `Carenini.not_careniniQuestion_*` remain | for version 1, exact edge-count distributions by two independent methods and exhaustive checks over all `d`-regular graphs on `2d` vertices for `d = 3, 4, 5` (`certificates/carenini/`); in version 2 all finite checks are carried out by the Lean kernel, and the data of the class counts and of the six-vertex cubic graphs come from two programs (`lean/Research/Backfill/Paper3/Proof/TS/gen/`, `Proof/Small/gen/`) whose output the kernel checks |
| A184894, A107099, A361047 (resolved) | `HannaA184894.zero_part`, `value_at_pow`, `counterexample`; `HannaA107099.hanna_a107099`, `hanna_a107099_counterexample`; `HannaA361047.hanna_a361047_pow`, `hanna_a361047_nonpow` | A184894: exact recomputation vs. the b-file; A107099: b-file substituted into the defining equation modulo two primes; A361047: the same, plus the first 60 terms recomputed independently (`batch2/`) |
| Paper 4 (version 2): every result, the 50 statements of the frozen statement file: Theorems A, B and C, including the minimality and uniqueness statements; Lemmas 1 and 2, Proposition 3, Remarks 4 and 5; the counts of Section 4 (59 connected triangle-free graphs with 7 vertices, 1,857 candidates, 1, 1, 1, 3, 4, 11, 23, 69 median graphs, 1,008,904 labelled median graphs with 8 vertices, 20,160 lacking (Q3′), 20,160 lacking (Q4), two automorphisms of `G1` and of `G2`); the two facts from Bandelt and Mulder used in the proofs | `BackfillPaper4.Check.check_*`, one theorem for each of the 50 statements of the frozen statement file `lean/Research/Backfill/Paper4/Challenge.lean` (SHA-256 `9f1b0c95…0785`); the version-1 declarations `HKOTriameter.not_problem1Claim`, `not_problem2Claim`, `problem3ClaimFP` and others remain | for version 1, two independent exhaustive enumerations of the median graphs with at most 8 vertices (`median_enum.c`, `median8_second_impl.py`) and a check over all 8! bijections (`iso_check.py`) (`certificates/hko-triameter/`); the computations on distance-hereditary graphs of version 1 (`dh_exhaustive.py`) are kept there but are no longer claimed |
| Paper 5 (version 2): every result, the 45 statements of the frozen statement files: Theorem 1.1 (a)–(c), and (c) also for `n = 0`; Proposition 3.1 (a)–(d) and the isomorphism of the principal factors with Rees 0-matrix semigroups; the facts on ranks, `J`-classes, the ranks that occur and the group of units (Section 2); Lemmas 4.1–4.4, 5.1–5.4 and 6.1; Proposition 6.2; Remark 4.5 (1)–(3); the special cases (R1) and (R2) of results of Araújo et al. ((R3) and (R4) are proved inside the proof of Theorem 1.1(c)); the number of half-diagrams and the idempotents `e_λ` (Section 3); the closure of `B_n` and `PB_n` under the product, with the identity diagram as identity; the fibres and the triangle product (Section 5); and the 12 supplementary statements (associativity of the product of diagrams and of Rees 0-matrix multiplication, the monoid structure of `B_n` and `PB_n`, the groups `{(λ, g, λ)}` and `S_r`, Cayley tables, the counts 45 and 105, and two auxiliary statements about reachability) | `CodexPaper5.*Check.check_*` in `lean/Research/Backfill/Paper5/Check.lean`, one theorem for each of the 45 statements: the 33 of the frozen statement file `lean/Research/Backfill/Paper5/Challenge.lean` (SHA-256 `ca2ff711…c373`) and the 12 of three supplementary statement files (`lean/Research/Backfill/Paper5/Supplement/`); the version-1 file `BrauerCMCore.lean` remains | the programs and certificates of version 1 (`certificates/brauer-complete/`) remain independent cross-checks; version 2 does not rely on them |
| Paper 6 (version 2): every result, the 35 statements of the frozen statement files: Theorem A and Table 1; the 7901 explicit codewords of Theorem B, and the size 7901 of S₀; the Corollary (in the middle-interval reading, Carlet's question for (7,14) is equivalent to 322, 326, 330, 334 being weights); Theorem C; Propositions D, E and F; Lemmas 2.1, 2.2 and 5.1; Remark 3.1; the remark after Proposition E; (P1), (P2), (P3), the minimum distance, flats and affine invariance; the other facts the proofs use (the 14 elements of M \ U, S₀ and Proposition 4 of Leuenberger and Albrizzio, Construction 2 of Lou and Wang for m = 6 and the concatenations, transversal flats, the example 162); the weights 162, 166, 170, 174 of RM(6,12); the identity of the weight predicate of version 1 with the one defined here; the fact (∗) of version 1, kept and proved although no proof of version 2 uses it | `Paper6FinalPackageV4.check_*` in `lean/Research/Backfill/Paper6/CheckPaper6.lean`, one theorem for each of the 35 statements of `lean/Research/Backfill/Paper6/ChallengeV3.lean` (SHA-256 `83ea2291…b6d78`) and `BridgeChallenge.lean`; the version-1 module `RM714Weights.lean` remains | the programs of version 1 (`certificates/rm714/`) remain independent cross-checks; version 2 does not rely on them |
| Paper 7 (version 2): every result, the 58 statements of the frozen statement files: Theorems 1 and 2 (minimum order 42, uniqueness; classification up to 41 vertices), orders and spectra of the graphs of Theorem 2 and that they are pairwise non-isomorphic; Proposition 3; Corollaries 3.1 and 4.3; Remark 3.2; Lemmas 2.1–2.4, 4.1, 4.2, 4.4 and 5.1–5.4; equations (1) and (2); Propositions 5.5–5.9 and 6.1–6.3; the bound of Section 7; the classification of the integral unicyclic graphs with at most 21 vertices; Theorem 2.1 and Proposition 3.2 of Braga, Moraes and Santos; the infinite families of the introduction | `Paper7FinalPackage.final_*`, one theorem for each of the 58 statements of `lean/Research/Backfill/Paper7/`, whose types are the frozen statements (`ClaudePaper7FinalPackage.lean`) | every module built and checked with `leanchecker` in two new empty directories and again in a clean rebuild of the whole project (`certificates/sun-graphs/lean-package-v2/`); only the three standard axioms; 120 known-answer tests of the statement files; not checked with comparator or nanoda (see below). The programs of version 1 are no longer used |
| Paper 9: Theorem A (the algebra `S`), Theorem B (`E`), Theorem C (`D`), Corollary 1.1 (the general forms (R1)–(R5) are false when arbitrary finite symmetric fusion laws are allowed), Proposition 4.1 (non-symmetric dominance in the algebra of Peng and of Kaygorodov, Martín González and Páez-Guillán), the facts about the fusion laws, and the two statements about `D` in Remark 5.1 | `AxialMSZ.Check.check_TheoremA`, `check_TheoremB`, `check_TheoremC`, `check_Corollary`, `check_not_MS_Conjecture_3_16`, `check_not_FinestSumDecomposition_connected`, `check_not_Indecomposable_connected`, `check_not_Simple_connected`, `check_RemarkP`, `check_Dominance_nonsymmetric`, `check_Laws_facts`, `check_ExD_axes_in_block`, `check_ExD_block_not_axial_on_contained_axes` (and the aliases `check_ExS_Statement`, `check_ExE_Statement`, `check_ExD_Statement`, `check_ExP_Statement`) | exact rational arithmetic by two separately written programs, recomputation by a reviewing agent and by Codex, and a check of every structure constant and displayed number in the paper against the statement file (`certificates/axial/`) |
| Paper 8 (version 2): every result, the 38 statements of the frozen statement file: Theorem 1 (also with Mathlib's definitions only) and its signature version, Lemmas 2.1–2.2, 3.1–3.4, 4.1–4.3, 5.2 and 5.4, Corollary 4.4, Propositions 5.1, 5.3, 5.5 and 5.6, the bound `t_r ≤ b* + k`, the criterion for a single secular eigenvalue, the structure of the trees of diameter at most 4 and their radius, the sharpness examples `T(15)` and `T(18,0,0)`, and Remarks 8.2 and 8.3 | `BackfillPaper8.Check.check_*`, one theorem for each of the 38 statements of the frozen statement file `lean/Research/Backfill/Paper8/Challenge.lean` (SHA-256 `69332eca…c715`); the version-1 files `SwitchingThmH.lean`, `SwitchingRowCount.lean` and `SwitchingWalkProfile.lean` remain and are used by the proofs, and `SwitchingDiam4Cubic.lean` remains | the finite search and the enumeration of the region (13,376 multisets) are checked by the Lean kernel; the programs of version 1 (`certificates/switching/`) remain independent cross-checks |
| Paper 10 (version 2): Theorem 3 (both products, all `1 ≤ n < m`) | `WordRepTensor.TaskF.Proof.check_Problem5_2`, `check_Problem5_3`, whose types are the frozen statements `WordRepTensor.TaskF.Challenge.Problem5_2`, `Problem5_3` (`lean/Research/WordRepTensor/TaskF/Challenge.lean`, SHA-256 `aef837f3…c0b5`); the internal statements of the proof (`TaskF/RouteContract.lean`, SHA-256 `f3e39eff…9553`) are frozen with them and are not results | the finite check of the seven-vertex windows is carried out by the Lean kernel; the 17 modules of the paper built and checked with `leanchecker` in two new empty directories and again in a clean rebuild of the whole project (`certificates/wordrep-tensor/lean-package-v2/`); not checked with comparator or nanoda |
| Paper 10: Theorem 1 (both products, all `n ≥ 1`, `m ≥ 2`); Theorem 2 in its word-representability form (`μ(C_{2t+1})` and `μ′(C_{2t+1})` are not word-representable, `t ≥ 1`); Lemmas 2.1, 2.2, 3.1 and 3.2 | `WordRepTensor.Check.check_Problem1Mu`, `check_Problem1MuExt`, `check_Problem5_1`, `check_MycielskiOddCycleNotWR`, `check_ExtMycielskiOddCycleNotWR`, `check_WordRepresentableOfEmbedding`, `check_EmbeddingOfHom`, `check_Lemma1Mu`, `check_Lemma1MuExt`, `check_Lemma2Mu`, `check_Lemma2MuExt` | no published programs: the finite checks of the proof are carried out by the Lean kernel (small cases were also checked with unpublished programs before the formalization) |
| Paper 11: Theorem 1 (for every `m ≥ 1`, `G_m = K_1 ∨ (K_1 ∪ mK_2)` is a connected cograph with a distance eigenvalue in `(−2 − 1/(2m), −2)`; hence the answer no to part (i) of the open problem of arXiv:2611.06981), with the steps of its proof (Lemma 1, the root of `p_m`, the eigenvector) | `CographDist.Audit.check_OpenProblemI_negative` for the statement `OpenProblemI_negative` of the frozen statement file `lean/Research/CographDist/Challenge.lean` (SHA-256 `960a24b9…0e569`), and `CographDist.Audit.check_family` (Theorem 1 for each `G_m`), in `lean/Research/CographDist/Audit.lean` | the 6 modules built and checked with `leanchecker` in two new empty directories (24 commands, identical `.olean` files) and again in the whole-project rebuild of version 1.18.0 (`certificates/cograph-distance/lean-package/`); 7 axiom lists, each exactly the three standard axioms; five tests of the statement file; no published programs (the family was checked numerically and symbolically before the formalization, by computations that are not published); not checked with comparator or nanoda (see below). Remark 1 (the derivation from the lemma of Conde, Dratman and Grippo) and the numerical values of the eigenvalues are not formalized |
| Paper 12: Theorem 1 (the algebra `A` over `F_11` is a primitive axial algebra for the stated fusion law, every bilinear form associating with its product is a multiple of `β`, the automorphism `g` multiplies `β` by `−1`, and `A` is simple without identity; hence a positive answer to Shpectorov's question in arXiv:2606.30048, with a 1-dimensional space of Frobenius forms) | `TaskG.Check.check_ShpectorovAnswer` and `check_StrongShpectorovAnswer`, whose types are the frozen statements `TaskG.Challenge.ShpectorovAnswer` and `StrongShpectorovAnswer` (`lean/Research/TaskG/Challenge.lean`, SHA-256 `05448636…09bb8`), in `lean/Research/TaskG/Check.lean`; the parts of Theorem 1 about this algebra are `TaskG.Proof.primitive_axial`, `primitive_basis_axis`, `fusion_finite_symmetric`, `fusion_grading`, `beta_symmetric`, `beta_frobenius`, `beta_nondegenerate`, `beta_form_space`, `g_mul`, `g_involutive`, `g_scales`, `simple`, `directlyIndecomposable` and `hasNoIdentity` | the 10 modules (the 8 of `TaskG/` and the statement file of Paper 9 with its tests) built and checked with `leanchecker` in two new empty directories (40 commands, identical `.olean` files) and again in the whole-project rebuild of version 1.20.0 (`certificates/axial-frobenius/lean-package/`); the axiom lists of these theorems and of the two checks are exactly the three standard axioms; no separate tests of the statement file; the finite computations over `ZMod 11` use `decide +kernel` and `ring`, no `native_decide`; the example was also recomputed independently, by programs that are not published; not checked with comparator or nanoda (see below). The frozen statements only say that some example exists; simplicity, the non-degeneracy of `β` and the `C_2`-grading are proved about the algebra of `Data.lean` but are not part of them. Not formalized: the full automorphism group of `A`, the remark on the Miyamoto group, and what the paper says about the literature |
| Paper 13 (version 2): Theorem 2 for every `k ≥ 4` (a `(k+1)`-critical graph with exactly `(k+1)!/(2k)` cycles of length 0 modulo `k` is `K_{k+1}`), with the lemmas of Sections 2–7 of the paper, including Theorem 3.1 of Gao, Huo, Liu and Ma | `TaskH.original_question_two_all_k` (`lean/Research/TaskH/OriginalQuestionTwoAssembly.lean`), whose type is the frozen statement `TaskH.Challenge.Question2` (`Challenge.lean` SHA-256 `a139c7e6…22a3b`), restated in `OriginalQuestionTwoTests.lean`, which also proves that the frozen counterexample statement is false; the theorems of version 1, `TaskH.case_four`, `case_five`, `case_six`, `case_seven` (types `CaseFour`, …, `CaseSeven`; `CaseFive.lean` `640313d2…9495e`, `CaseSix.lean` `68ec2193…61d3f`, `CaseSeven.lean` `d982be01…4691b`), restated in `ExactTests.lean` … `ExactTestsSeven.lean`; `TaskH.lower_bound_seven` (Theorem 3 of Choi and Sieniawski for `k = 7` and 8-critical graphs) | version 1: for each `k` the modules of that case (49, 120, 236, 240) built and checked with `leanchecker` in two new empty directories (identical `.olean` files; for `k = 6`, 13 attempts without a Lean verdict were run again by the driver and passed); all `k`: the 717 files of Codex's package built and checked in two new empty directories on the author's Mac (2868 commands with exit code 0, identical `.olean` files); all 716 files together in the whole-project rebuild of version 1.22.0 (`certificates/critical-cycles-mod-k/lean-package/`); the axiom lists of the main theorems are exactly the three standard axioms; tests of `K_{k+1}` for `k = 4, …, 7`; not checked with comparator or nanoda (see below). Not formalized: that `K_{k+1}` has exactly `(k+1)!/(2k)` such cycles for `k ≥ 8` (that it is `(k+1)`-critical is formalized for every `k`), the remark citing Bai, Grzesik, Li and Prorok, Proposition 1 of the paper for `k ≥ 6` and Lemmas 7 and 8 for `k ≥ 6` (they are used, and formalized, only for `k = 4, 5` and for `k = 5`), and what the paper says about the literature |
| Paper 14: Theorems 1, 2 and 3 (for the two-point and the five-point action of `C_2`: the parameters of the source, the rank of the equivariant group, the failure of the bound of Theorem 4 for the first, and for the second the rank below both packet expressions; for every `n ≥ 3`: a faithful action of a cyclic group with `r = κ = n`, `Λ = 0`, rank 2 and `n` packets for every valid choice of generating sets) | `TaskJ.Rank.check_TwoPointParameters`, `check_FivePointParameters`, `check_TwoPointRank`, `check_FivePointRank`, `check_TwoPointCounterexample`, `check_FivePointCounterexample` (`lean/Research/TaskJ/Rank/CheckRank.lean`) and `TaskJ.Rank.Extension.check_UnboundedGap` (`lean/Research/TaskJ/Rank/Extension/CheckExtension.lean`), whose types are the frozen statements of `Challenge.lean` (SHA-256 `5ebdebf7…21e5`) and `Extension/Challenge.lean` (`efa3009d…ad72`); proved by the theorems of the same names in `TaskJ.Rank.Proof` and `TaskJ.Rank.Extension.Proof` | the 5 and the 10 modules built and checked with `leanchecker` by Codex in two new empty directories each (22 and 42 commands with exit code 0, identical `.olean` files), the repository versions again by Claude Code in two new empty directories on the author's Mac (18 November 2026, 19:12–19:21 UTC), and all 15 in the whole-project rebuild of version 1.23.0 (`certificates/equivariant-rank/lean-package/`); the axiom lists of the seven checks are exactly the three standard axioms; the parameter values are computed with `decide +kernel`, no `native_decide`; the parameters of the examples were also recomputed by the final reviewer, and the 21-point example of the source by a Codex program, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: the four remarks marked as written arguments (transitive actions, the corrected bound, the second reading of `δ` in the preprint, the smaller variant of the family), the isomorphism types `C_2 × S_3` and `Z/M × Z/M` named in the written proofs, the 21-point example of the source, and what the paper says about the literature |
| Paper 15: Theorem 1 (for every finite list of positive side lengths: every ordering of the points of the box has length at most `U_r(D) − κ(D)`, some ordering attains it, and every longest ordering has gap exactly `κ(D)` to the bound `U_r(D)` printed in (6) of Yuan's paper), with the steps of its proof (Propositions 1 and 2, the constructions of Section 3) | `check_LengthUpperBound`, `check_LengthAttained`, `check_YuanGapAtLongest` (root namespace, `lean/Research/TaskJ/Grid/CheckGrid.lean`), whose types are the frozen statements `Challenge.LengthUpperBound`, `Challenge.LengthAttained` and `Challenge.YuanGapAtLongest` (`Challenge.lean` SHA-256 `6b0ad9f9…5e07`); proved by `Proof.LengthUpperBound`, `Proof.LengthAttained` and `Proof.YuanGapAtLongest` in `Proof.lean` | the 28 modules built and checked with `leanchecker` by Codex in two new empty directories (114 commands with exit code 0, identical `.olean` files), the repository versions again by Claude Code in two new empty directories on the author's Mac (18 November 2026, 19:12–19:21 UTC), and all 28 in the whole-project rebuild of version 1.23.0 (`certificates/lattice-box-paths/lean-package/`); the axiom lists of the three checks are exactly the three standard axioms; `decide` is used for the fixed seeds and finite case splits, no `native_decide`; the formula was also checked by the final reviewer by exhaustive search on small boxes (all 67 boxes with at most 8 points and at most three sides, all 40 boxes with sides at least 2 and at most 20 points, and further boxes including `2 × 3 × 4`, `2 × 2 × 2 × 3` and `3 × 3 × 3`), with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: Corollary 2 and the comparison with Jiang's conjecture (they also use Yuan's formula for a single coordinate, Theorem 2.3 of his paper), the closed forms of Corollary 1 as separate statements (they are rewritings of the formula of Theorem 1), the particular ordering printed in Remark 3 (the instance of `LengthAttained` for `2 × 3 × 4` gives some ordering of length 101), and what the paper says about the literature |
| Paper 16: Theorem 1 (for every numerical semigroup `S`, the set of lengths of its decompositions into irreducible numerical semigroups is nonempty and contains every integer between two of its elements; the same for positive lengths) and Corollary 1 in the form of Conjecture 3.9 (multiplicity `2k`: a length `j` with `k < j < 2k` gives the length `j − 1`), with the steps of the proof (the cover criterion, the exchange of Lemma 4, the step of Lemma 5 and its termination, Lemma 7) and Theorem 2 | `TaskL.Semigroup.check_LengthsExist`, `check_LengthsInterval`, `check_PositiveLengthsInterval`, `check_EvenMultiplicityDescent` (`lean/Research/TaskL/Semigroup/CheckSemigroup.lean`), whose types are the frozen statements of `Challenge.lean` (SHA-256 `a0269ad5…6662`); proved by the theorems of the same names in `TaskL.Semigroup.Proof`; Theorem 2 is `short_even_decomposition` and Lemma 7 is `terminal_card` | the 12 modules built and checked with `leanchecker` by Codex in two new empty directories (18 November 2026, 23:55–23:59 UTC; 50 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory, with warnings treated as errors (19 November 2026, 01:36–01:41 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (19 November 2026, 02:11–02:17 UTC), and all 12 in the whole-project rebuild of version 1.24.0 (`certificates/numerical-semigroup-lengths/lean-package/`); the axiom lists of the four checks are exactly the three standard axioms; `decide` is used only for three numerical side facts, no `native_decide`; the statements were also checked by Codex by exact computation for all 1249 numerical semigroups other than `ℕ` with Frobenius number at most 17, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: the assertion `r(S) ∈ L(S)` (Remark 2), the finiteness of `L(S)` (at most `m − 1` components, Remark 3), the stronger form of Corollary 1 for every `j > k` (it follows at once from Theorems 1 and 2, but is not stated in Lean), the examples of Remarks 1 and 3, and what the paper says about the literature |
| Paper 17: Theorem 1 without its last sentence (for every `n ≥ 11`, `⌊n/11⌋ + 1` trees on `n` vertices, each with a largest real independence root, pairwise incomparable under `⪯`) and Corollary 1 (Question 6 of Beaton and Cameron: for every `k`, some order has `k` pairwise incomparable trees), with the steps of the proof (the gadget polynomials and their difference, the transfer recursion, the site bounds and the zero-free interval `[−1/6, 0]`, the existence of the largest real root for the trees used, the exchange, and the strict monotonicity at `−1/10` and `−1/6`) | `TaskN.Antichain.check_WidthLowerBound`, `check_ArbitrarilyLarge` (`lean/Research/TaskN/Antichain/CheckAntichain.lean`), whose types are the frozen statements of `Challenge.lean` (SHA-256 `fb8861ac…5d58`); proved by `TaskN.Antichain.Proof.WidthLowerBound` and `Proof.ArbitrarilyLarge` | the 11 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 14:33–14:40 UTC; 46 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory, with warnings treated as errors (17:17–17:27 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (17:42–17:52 UTC), and all 11 in the whole-project rebuild of version 1.25.0 (`certificates/tree-antichains/lean-package/`); the axiom lists of the two checks are exactly the three standard axioms; `decide` is used only twice, on the one-element type `Unit`, no `native_decide`; the construction was also checked by Codex by exact computation at both test points for every order from 11 to 88, and the final reviewer recomputed the polynomials, the test values and the largest roots in Python for six orders, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: the bound 5 on the maximum degree (Remark 1), the last sentence of Theorem 1 as a separate statement (the paper derives it from the formal statement), and what the paper says about the literature |
| Paper 18: Theorem 1 (for every nonempty list of positive car lengths, `W(y)` has at most `2^(n−1)` elements, with equality if and only if `n = 1` or conditions (i)–(iii) hold) and Theorem 2 (for a fixed superdecreasing tail, the number of first-car lengths in `[b, b + D]` that attain equality is `1 + Σ(2^(L_i) − 1)`), with the steps of the proof (the gap reduction, the properties of the residual and of subset sums, the bound, the criterion for equality, the necessity of a superdecreasing tail, the reduction to the first two positions, the symmetry condition, the ruler word and its palindromic prefixes) | `TaskN.Parking.check_ExtremalClassification`, `check_FirstLengthCount` (`lean/Research/TaskN/Parking/CheckParking.lean`), whose types are the frozen statements of `Challenge.lean` (SHA-256 `7f0d8043…e46e`); proved by `TaskN.Parking.Proof.ExtremalClassification` and `Proof.FirstLengthCount`; the gap reduction is `allPositions_iff` | the 12 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 14:35–14:44 UTC; 50 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory, with warnings treated as errors (17:19–17:26 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (17:42–17:52 UTC), and all 12 in the whole-project rebuild of version 1.25.0 (`certificates/variable-length-parking/lean-package/`); the axiom lists of the two checks are exactly the three standard axioms; no `decide` and no `native_decide`; Theorem 1 was also compared by Codex with a simulation of the parking rule for all 37,440 length vectors with 2 to 5 cars of lengths at most 8, and the final reviewer compared a computable copy of the statement file's parking model with its own simulation of Chen's rule, Theorem 1 with the simulation on 4,679 length vectors and Theorem 2 on 411 fixed tails, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: the three remarks of Section 5, the argument that a run on the street of the statement file (finite gaps and a frontier, infinite to the right) succeeds on Chen's finite street exactly when the final frontier is at most its length (given in the paper), the statements about `a < b` and `a > b + D` in Theorem 2 as separate statements (they follow from Theorem 1), and what the paper says about the literature |
| Paper 19: Theorem 1 (for every prime `p`, the number of isomorphism classes of medial racks of order `p` equals that of 2-reductive racks plus `p − 2`; the same for quandles; every medial rack of order `p` that is not 2-reductive is a quandle), with the steps of the proof (invariance under isomorphism, the displacement group and its properties, the stabilizers and the divisibility argument, transitivity and regularity in prime order, the affine coordinates, the affine models and their uniqueness, the counting of classes) and Theorem 2 | `TaskP.PrimeMedialRacks.check_RackCount`, `check_QuandleCount`, `check_AutomaticIdempotence` (`lean/Research/TaskP/PrimeMedialRacks/CheckRack.lean`), whose types are the frozen statements of `Challenge.lean` (SHA-256 `36167e3c…c0d5`); proved by the theorems of the same names in `TaskP.PrimeMedialRacks.Proof`; Theorem 2 is `Proof.classified` with `affine_parameter_unique` | the 13 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 18:16–18:21 UTC; 54 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory, with warnings treated as errors (18:32–18:35 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (19:55–20:07 UTC), and all 13 in the whole-project rebuild of version 1.25.0 (`certificates/prime-medial-racks/lean-package/`); the axiom lists of the three checks are exactly the three standard axioms; no `decide` and no `native_decide`; the final reviewer also recomputed all racks and quandles of order at most 5 by brute force in Python, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: the values of the tables of the source, and what the paper says about the literature |
| Paper 20: Theorem 1 (for every `d ≥ 1` and all coprime `2 ≤ a < b`, for `S = {x ∈ N^d : x_1 + … + x_d ∈ ⟨a, b⟩}`: the set `C` of points below a gap and the set `A` of atoms are finite, `A` generates `S`, every generating set contains `A`, and `d` times the number of elements of `C` is at most the number of elements of `A` times that of `C ∩ S`), with the steps of the proof (the reflection in the Frobenius number, the layers and their sizes, `C` as the points of degree at most `F`, the formula for `n(S)`, the atoms as two layers, the high-dimensional and the low-dimensional inequalities) | `TaskP.GradedWilf.check_Wilf` (`lean/Research/TaskP/GradedWilf/CheckWilf.lean`), whose type is the frozen statement of `Challenge.lean` (SHA-256 `b7db38db…83e6`); proved by `TaskP.GradedWilf.Proof.Wilf` | the 9 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 18:21–18:24 UTC; 38 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory, with warnings treated as errors (18:31–18:34 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (19:55–20:07 UTC), and all 9 in the whole-project rebuild of version 1.25.0 (`certificates/graded-wilf/lean-package/`); the axiom lists are exactly the three standard axioms; no `decide` and no `native_decide`; the inequality was also checked by Codex by exact computation for 6,204 parameter triples and by the final reviewer for 18,096, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: the deduction of Corollary 1 as a separate statement (a few lines), and what the paper says about the literature |
| Paper 21: Theorem 1 (for `P = conv{e_1, e_2, e_3, e_4, −(2,1,1,1)}`: the origin is interior, the covering radius is exactly 2, the normalized volume is 6, and `P` is not in the family `Generated`), with the steps of the proof (coordinates and the lattice points of `P`, the residue certificate for `μ(P) ≤ 2` over 1296 residue vectors, the lower bound, the determinant, the centroid argument for the exclusion) | `TaskR.CSS.check_NonHollow`, `check_Radius`, `check_Volume`, `check_OutsideList` (`lean/Research/TaskR/CSS/CheckCSS.lean`), whose types are the frozen statements of `Challenge.lean` (version 2, SHA-256 `1dbf0ce8…8161`); proved by the theorems of the same names in `TaskR.CSS.Proof` | the 9 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 19:35–19:41 UTC; 38 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory (19:48–19:52 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (19:55–20:07 UTC), and all 9 in the whole-project rebuild of version 1.25.0 (`certificates/css-covering-equality/lean-package/`); the axiom lists of the four checks are exactly the three standard axioms; two finite checks use `decide +kernel` (the 1296 residue vectors and 64 subsets of lattice points), no `native_decide`; the final reviewer also recomputed the lattice points, facet normals and determinant in Python and checked the covering radius numerically, and Claude Code repeated the finite computations, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: Lemma 4 (the family `Generated` contains every polytope of the equality list of Conjecture A and its unimodular images), hence the step from Theorem 1 to Corollary 1; the remarks of Section 5; and what the paper says about the literature |
| Paper 22: Theorem 1 (there is a bijection `a` from `{0, …, 2519}` onto `A_7` with `a_0 = e` such that every involution occurs exactly once among the quotients `a_i^(−1) a_(i+1)` and every other non-identity `g` occurs, with `g^(−1)`, exactly twice), with the steps of the proof (the tables, the kernel-evaluated checks of the rows and of a matching of the quotients, the bijection onto `A_7`, the counting lemma) | `TaskR.A7.check_HasTerrace` (`lean/Research/TaskR/A7/CheckA7.lean`), whose type is the frozen statement of `Challenge.lean` (SHA-256 `27895ac5…37bb`); proved by `TaskR.A7.Proof.HasTerrace` | the 8 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 19:36–19:40 UTC; 34 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory (19:43–19:45 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (19:55–20:07 UTC), and all 8 in the whole-project rebuild of version 1.25.0 (`certificates/a7-terrace/lean-package/`); the axiom lists are exactly the three standard axioms; the certificate is checked by 79 calls of `decide +kernel` in `Cert.lean`, no `native_decide`; the terrace was also checked by two Python programs of Codex, by the final reviewer and by Claude Code, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: that the terrace is not directed (Remark 1), the consequences for the conjectures of Bailey, Anderson and Keedwell (Section 4), and what the paper says about the literature |
| Paper 23: Theorem 1 (for every graph `B` with at least one vertex and all `a, m ≥ 1`, the moduli of the domination roots of `K_a ∨ mB` have a largest element), Theorem 2 (its ratio to `(c s m/(a log m))^(1/c)` tends to 1) and Corollary 1 (friendship graphs, `√(2m/log m)`), with the steps of the proof (the domination polynomial of the join, the leading missing term, the root equation, the upper bound, the disc and the maximum modulus principle for roots of the predicted size) | `TaskP.GraphRootRadius.check_Attainment`, `check_GeneralAsymptotic`, `check_FriendshipAsymptotic` (`lean/Research/TaskP/RootRadius/CheckRootRadius.lean`), whose types are the frozen statements of `Challenge.lean` (SHA-256 `d6663c9f…222d`); proved by the theorems of the same names in `TaskP.GraphRootRadius.Proof` | the 14 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 18:24–18:30 UTC; 58 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory (about 20:53–20:56 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (21:04–21:16 UTC), and all 14 in the whole-project rebuild of version 1.25.0 (`certificates/domination-root-radius/lean-package/`); the axiom lists of the three checks are exactly the three standard axioms; `decide` only for `0 < 1`, no `native_decide`; the leading term was also checked by Codex on all 1,099 labelled graphs with at most 5 vertices, and the final reviewer and Claude Code computed root moduli in Python, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: the comparison with Rather's bounds (Remark 1), the numerical values, the examples of `(c, s)` other than `K_2`, and what the paper says about the literature |
| Paper 24: Theorem 1 (for `D_k(n)`, the number of multisets of bars of lengths at most `k` and total area `2n` that do not tile the `2 × n` rectangle, with tiling defined by real positions: `D_k(n) = 0` for `k ≤ 2`; `D_k(n) ≤ C (n + 1)^(e_k)` for `k ≥ 3`; `(n + 1)^(e_k) ≤ C D_k(n)` for arbitrarily large `n`, and for every large odd `n` when `k ≥ 6`), with the steps of the proof (the two-row criterion, the cases `k ≤ 2`, the bounded Bézout argument and the counting for the upper bound, the families of even bars for the lower bounds) | `TaskP.RectangleDefect.check_SharpBound` (`lean/Research/TaskP/RectangleDefect/CheckRectangle.lean`), whose type is the frozen statement of `Challenge.lean` (SHA-256 `906da3fa…29d9`); proved by `TaskP.RectangleDefect.Proof.SharpBound` | the 18 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 18:35–18:42 UTC; 74 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory (about 20:55–20:58 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (21:04–21:16 UTC), and all 18 in the whole-project rebuild of version 1.25.0 (`certificates/bar-tiling-defect/lean-package/`); the axiom lists are exactly the three standard axioms; `decide` only for four closed numerical facts, no `native_decide`; the criterion was also compared with enumeration of tilings by Codex (4308 count vectors, `k ≤ 8`, `n ≤ 10`) and by the final reviewer (`k ≤ 11`, `n ≤ 18`), with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: Corollary 1 as a separate statement, the computed values (Remark 1 and Table 1), any statement about the lower limit of `D_k(n)/n^(e_k)`, and what the paper says about the literature |
| Paper 25: Theorem 1 (`T` is a lattice 3-simplex with lattice diameter 1 and Minkowski length 2; for every `d ≥ 3` such a `d`-simplex exists) and Theorem 2 (`U` has `L(U) = 1` and `L(tU) = 3t` for every `t ≥ 2`, so `L(tU)` is not quasi-linear; the same in every dimension `d ≥ 3`), with the steps of the proof (segments and corners, the lattice points and the absence of three-segment sums in `T`, the cost bound and the segments in `2U` and `3U`, lattice pyramids) | `TaskP.GeomSimplex.check_TetrahedronDiameter`, `check_TetrahedronDilations`, `check_EveryDimensionDiameter`, `check_EveryDimensionDilations` (`lean/Research/TaskP/GeomSimplex/CheckSimplex.lean`), whose types are the frozen statements of `Challenge.lean` (SHA-256 `98fdde38…80a4`); proved by the theorems of the same names in `TaskP.GeomSimplex.Proof` | the 16 modules built and checked with `leanchecker` by Codex in two new empty directories, with warnings treated as errors (20 November 2026, 18:25–18:31 UTC; 66 commands with exit code 0, identical `.olean` files), again by the final reviewer in a third new directory, with warnings treated as errors (20:57–21:00 UTC), the repository versions again by Claude Code in two new empty directories on the author's Mac (21:04–21:16 UTC), and all 16 in the whole-project rebuild of version 1.25.0 (`certificates/minkowski-length-simplices/lean-package/`); the axiom lists of the four checks are exactly the three standard axioms; the finite tables (triples and quadruples of lattice points) and the witness inequalities are checked by `decide` in the kernel, no `native_decide`; the final reviewer also recomputed the lattice points and segment sums in Python, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: Corollary 1 for `d ≤ 2` (a result of the source), the periodicity remark, the remarks of Section 6 (the identity `L_1(P) = ⌊λ_1(P)⌋` and Remark 2.21 of the source), and what the paper says about the literature |
| Paper 26: Theorem 1 (Conjecture B: for all `1 ≤ i ≤ n`, every linear surjection `p` with `p(Z^n)` a lattice satisfies `p(Z^n) + (i/2) p(T_n) = R^i`, and for some such `p` the scale `i/2` is the least one), Theorem 2 (Conjecture C: `Z^d + rS = R^d` with `r = (D_0 + … + D_d)/(2V)` for every simplex with primitive vertex directions and the origin in its interior, in every dimension `d ≥ 1`) and Theorem 2′ (the same with Lebesgue measures of projected sets), with the steps of the proofs (Hermite's identity and the averaging lemma, the kernel rounding by splitting, the upper and lower bounds for `T_n`, the integer relation and the determinant identities, the rounding and padding, the projections and their measures) | `TaskS.B.check_ConjectureB` (`lean/Research/TaskS/B/CheckB.lean`) and `TaskS.C.check_conjectureC` (`lean/Research/TaskS/C/CheckC.lean`) and `TaskS.C.MeasureAudit.check_conjectureC` (`lean/Research/TaskS/C/MeasureAudit/CheckC.lean`), whose types are the frozen statements of `B/Challenge.lean` (SHA-256 `458363b3…58b7`) and `C/Challenge.lean` (SHA-256 `607e2915…1a57e`); proved by `TaskS.B.Proof.ConjectureB` and `TaskS.C.Proof.conjectureC`; Theorem 2′ is `TaskS.C.MeasureModel.measured_conjectureC` | built and checked with `leanchecker` by Codex in two new empty directories each, with warnings treated as errors (20 November 2026: Theorem 1, 12 modules, 22:34–22:40 UTC, 50 commands; Theorem 2, 9 modules, 22:33–22:38 UTC, 38 commands; Theorem 2′, 14 modules, 22:38–22:44 UTC, 58 commands; all with exit code 0 and identical `.olean` files), again by each of the four final reviewers in a new directory (22:43–23:16 UTC), the 25 repository versions again by Claude Code in two new empty directories on the author's Mac (23:11–23:18 UTC), and all 25 in the whole-project rebuild of version 1.25.0 (`certificates/css-covering-minima/lean-package/`); the axiom lists are exactly the three standard axioms; no `decide`, no `native_decide`; the final reviewers also tested the averaging lemma, covering radii of more than 11,000 projections of `T_n` (`n ≤ 5`, `i ≤ 4`) and the bound of Conjecture C numerically, and Claude Code checked three lemmas numerically, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: Corollary 3 (the d/2 bound of Conjecture A), the remarks of Section 5, the independence of the projected volumes from the choice of projection (Lemma 11), and what the paper says about the literature |
| Paper 27: Theorem 1 (the value set `S(H_5)`: for every integer `m`, `m` is a group determinant of `H_5` with integer entries if and only if `m^4 ≡ 1 (mod 125)`, `5^33 ∣ m`, or `m = 5^28·n` with `n ≠ 0` divisible by a visible prime) and Corollary 1 (the least positive value divisible by 5 is `11·5^28`, attained by `1 + x + y + y² + xy²`), with the steps of the proofs (the factorization derived from the matrix itself, the normalization, the congruence for `D`, the bound `5^28`, the phases and the cancellation of the trace, the residues of the units, the prime extraction, both directions for the values prime to 5, the seeds, the exact lift and the constructions) | `TaskU.H5.Check.check_witnessValue` and `TaskU.H5.Check.check_leastPositiveMultiple` (`lean/Research/TaskU/H5/Check.lean`) and `TaskU.H5.check_fullSpectrum` (`lean/Research/TaskU/H5B/CheckB.lean`), whose types are the frozen statements of `H5/Challenge.lean` (SHA-256 `9a9a0e18…1343`) and `H5B/ChallengeB.lean` (frozen version SHA-256 `2a5066bf…9ea6`; the repository version differs only in its `import` lines); proved by `TaskU.H5.Proof.witnessValue`, `TaskU.H5.Proof.leastPositiveMultiple` and `TaskU.H5.ProofB.fullSpectrum`; the class number one of `Q(ζ_5)` is taken from Mathlib's proved theorem | built and checked with `leanchecker` by Codex in two new empty directories each, with warnings treated as errors (21 November 2026: the minimum, 37 modules, 01:42:55–01:56:09 UTC, 150 commands; the classification, all 63 modules, 03:33:17–03:55:22 UTC, 254 commands; all with exit code 0 and identical `.olean` files), again by each of the three final reviewers in a new directory (03:21–04:55 UTC), the 63 repository versions again by Claude Code in two new empty directories on the author's Mac (17:02–17:22 UTC), and all 63 in the whole-project rebuild of version 1.25.0 (`certificates/heisenberg-125-determinants/lean-package/`); the axiom lists are exactly the three standard axioms (two audit lemmas use fewer); all uses of `decide`, including the large tables, are checked by the kernel, and there is no `native_decide`; the final reviewers recomputed the witness determinant by exact elimination on the 125 × 125 matrix and tested the classification on random integer functions (4,650 exact determinants in one review; about 300,000 evaluations through the factorization, checked against 140 full determinants, in the other) without finding a counterexample, and Claude Code recomputed the determinants of the witness and of the example of Mossinghoff and Pinner, the group `U` and the visible primes below 6000, with programs that are not published; not checked with comparator or nanoda (see below). Not formalized: Corollary 2 (a two-line deduction from Theorem 1), Remark 1, Lemma 2 (not needed for Theorem 1), and what the paper says about the literature |

Each OEIS theorem is stated for every integer power series satisfying the
defining equation. The energy is `∑ |eigenvalues|`, using
`Matrix.IsHermitian.eigenvalues`.

All final theorems depend only on the axioms `propext`, `Classical.choice`
and `Quot.sound`. There is no `sorry` in any proof (the comparator challenge
files in `lean/Comparator/` state the checked theorems with `sorry` on
purpose and are not built by default), no custom axiom and no
`native_decide`. Version 1.7.1 moved the project from Lean 4.33.1 to Lean
4.34.1, which fixes three issues in the Lean runtime that could in principle
be used to derive `False` (see its release notes). Three files changed, in
13 lines, because `PowerSeries.derivative` now takes its ring implicitly
(`logs/lean-upgrade-v1.7.1.md`); comparing the elaborated statements on
both versions showed no change of meaning. For version 1.8.0, which adds
the 25 files of Paper 9 (`lean/Research/AxialMSZ/`), the whole project was
rebuilt from a clean directory (`lake build`, exit code 0;
`logs/clean-replay-v1.8.0-build.log`), the known-answer tests of Paper 9
were built, and the twelve audit files were run
(`logs/clean-replay-v1.8.0-audit-*.log`; the eleven older ones print the
same as for version 1.7.1). Every axiom list printed in these logs, 173 in
the build log, 392 in the older audit logs and 1 in the tests of Paper 9,
is a subset of these three axioms (`logs/clean-replay-v1.8.0-axiom-audit.log`).
All 87 modules, namely the 51 proof modules and 11 audit modules of earlier
versions and the 25 modules of Paper 9, were replayed through the Lean
kernel with `lake env leanchecker <Module>`, and all passed
(`logs/clean-replay-v1.8.0-leanchecker.log`). The source manifest of
version 1.8.0 had 91 files, and the procedure and its parameters are
recorded in `logs/clean-replay-v1.8.0-receipt.json`
(earlier rebuilds: `logs/clean-replay-v1.4.0-receipt.json`,
`logs/clean-replay-v1.7.0-receipt.json`,
`logs/clean-replay-v1.7.1-receipt.json`).

For version 1.9.0, which adds the 199 files of Paper 4, version 2
(`lean/Research/Backfill/Paper4/`; with the two version-1 modules
`HKOTriameter` and `HKOTriameterDH` that they import, the 201 modules of its
Lean package), and the 11 files of Paper 10
(`lean/Research/WordRepTensor/`), the whole project was again rebuilt from a
clean directory (`lake build`, exit code 0;
`logs/clean-replay-v1.9.0-build.log`), the known-answer tests of Papers 4, 9
and 10 were built (`logs/clean-replay-v1.9.0-build-challenge-tests.log`),
and the twelve audit files were run (`logs/clean-replay-v1.9.0-audit-*.log`;
they print the same as for version 1.8.0). Every axiom list printed in these
logs, 591 in the build logs, 392 in the audit logs and 1 in the tests (each
command counted once), is a subset of the three standard axioms, and each
matches one `#print axioms` command in the sources (`logs/clean-replay-v1.9.0-axiom-audit.log`). All 297
modules were replayed through the Lean kernel with
`lake env leanchecker <Module>`, and all passed
(`logs/clean-replay-v1.9.0-leanchecker.log`,
`logs/clean-replay-v1.9.0-leanchecker-circulantq3.log`). The source manifest
`logs/lean-sources-sha256.txt` then listed 304 files, and the procedure is recorded
in `logs/clean-replay-v1.9.0-receipt.json`. Before they were copied into the
release tree, the Lean packages of Papers 4 and 10 had each been built module
by module in an empty directory and checked with `leanchecker`, twice
(`certificates/hko-triameter/lean-package-v2/receipt.json`,
`certificates/wordrep-tensor/lean-package/receipt.json`).

For version 1.10.0, which adds the 94 Lean files of Paper 3, version 2
(`lean/Research/Backfill/Paper3/`: the statement file, its tests, the 91
proof modules and `Check.lean`), the whole project was again rebuilt from a
clean directory on 29 September 2026, 12:49–13:14 UTC (`lake build`, exit
code 0; `logs/clean-replay-v1.10.0-build.log`), the known-answer tests of
Papers 3, 4, 9 and 10 were built
(`logs/clean-replay-v1.10.0-build-challenge-tests.log`), and the twelve audit
files were run (`logs/clean-replay-v1.10.0-audit-*.log`). Every axiom list
printed in these logs, 711 in the build logs, 392 in the audit logs and 1 in
the tests (each command counted once), is a subset of the three standard
axioms, and each matches one `#print axioms` command in the sources
(`logs/clean-replay-v1.10.0-axiom-audit.log`). All 391 modules were replayed
through the Lean kernel with `lake env leanchecker <Module>`, and all passed
(`logs/clean-replay-v1.10.0-leanchecker.log`,
`logs/clean-replay-v1.10.0-leanchecker-circulantq3.log`). The source manifest
`logs/lean-sources-sha256.txt` then listed 399 files, and the procedure is
recorded in `logs/clean-replay-v1.10.0-receipt.json`. Before it was copied
into the release tree, the Lean package of Paper 3 had been built module by
module in an empty directory and checked with `leanchecker`, twice
(`certificates/carenini/lean-package-v2/receipt.json`).

For version 1.11.0, which adds the 80 Lean files of Paper 8, version 2
(`lean/Research/Backfill/Paper8/`: the statement file, its tests, the 69
proof modules, 8 modules of further tests and `Check.lean`) and the comparator
challenge `lean/Comparator/Paper8.lean`, the whole project was again rebuilt
from a clean directory on 29 September 2026, 19:06–19:36 UTC (`lake build`,
exit code 0; `logs/clean-replay-v1.11.0-build.log`), the known-answer tests of
Papers 3, 4, 8, 9 and 10 were built
(`logs/clean-replay-v1.11.0-build-challenge-tests.log`), as were the further
tests of Paper 8, which are not imported by `Research.lean`
(`logs/clean-replay-v1.11.0-build-other.log`), and the twelve audit files were
run (`logs/clean-replay-v1.11.0-audit-*.log`). Every axiom list printed in
these logs, 788 in the build logs, 392 in the audit logs, 1 in the tests of
the statement files and 158 in the further tests of Paper 8 (each command
counted once), is a subset of the three standard axioms, and each matches one
`#print axioms` command in the sources
(`logs/clean-replay-v1.11.0-axiom-audit.log`). All 471 modules were replayed
through the Lean kernel with `lake env leanchecker <Module>`, and all passed
(`logs/clean-replay-v1.11.0-leanchecker.log`,
`logs/clean-replay-v1.11.0-leanchecker-circulantq3.log`). The source manifest
`logs/lean-sources-sha256.txt` then listed 480 files, and the procedure is
recorded in `logs/clean-replay-v1.11.0-receipt.json`. Before it was copied
into the release tree, the Lean package of Paper 8 had been built module by
module in an empty directory and checked with `leanchecker`, twice
(`certificates/switching/lean-package-v2/receipt.json`).

For version 1.12.0, which adds the 70 Lean files of Paper 5, version 2
(`lean/Research/Backfill/Paper5/`: the statement file, its tests, the three
supplementary statement files, the 64 proof modules and `Check.lean`) and the
comparator challenge `lean/Comparator/Paper5.lean`, the whole project was
again rebuilt from a clean directory on 6 October 2026, 18:56–19:21 UTC (`lake build`,
exit code 0; `logs/clean-replay-v1.12.0-build.log`), the known-answer tests
of Papers 3, 4, 5, 8, 9 and 10 were built
(`logs/clean-replay-v1.12.0-build-challenge-tests.log`), as were the further
tests of Paper 8 (`logs/clean-replay-v1.12.0-build-other.log`), and the
twelve audit files were run (`logs/clean-replay-v1.12.0-audit-*.log`). Every
axiom list printed in these logs, 1495 in the build logs, 392 in the audit
logs, 78 in the tests of the statement files and 158 in the further tests
of Paper 8 (each command counted once), is a subset of the three standard
axioms, and each matches one `#print axioms` command in the sources
(`logs/clean-replay-v1.12.0-axiom-audit.log`). All 541 modules were replayed
through the Lean kernel with `lake env leanchecker <Module>`, and all passed
(`logs/clean-replay-v1.12.0-leanchecker.log`,
`logs/clean-replay-v1.12.0-leanchecker-circulantq3.log`). The source manifest
`logs/lean-sources-sha256.txt` then listed 551 files, and the procedure is
recorded in `logs/clean-replay-v1.12.0-receipt.json`. Before it was copied
into the release tree, the Lean package of Paper 5 had been built module by
module in two new empty directories, side by side, and every module checked
with `leanchecker` (`certificates/brauer-complete/lean-package-v2/receipt.json`).

For version 1.13.0, which adds the 374 Lean files of Paper 6, version 2
(`lean/Research/Backfill/Paper6/`: the two statement files, the tests, the
370 proof modules and `CheckPaper6.lean`) and the comparator challenge
`lean/Comparator/Paper6.lean`, the whole project was again rebuilt from a
clean directory on 9 October 2026, 00:02–01:35 UTC. Because one `lake build` of the
whole project now takes longer than the 30-minute limit per command set by
our resource guard (a first attempt was stopped by this limit), the modules
imported by `Research.lean` were built in dependency order by 112 `lake build`
commands of at most eight modules each, all with exit code 0
(`logs/clean-replay-v1.13.0-build.log.gz`, compressed with gzip; the batches
are listed in the receipt), and the known-answer tests of Papers 3,
4, 5, 6, 8, 9 and 10 were built
(`logs/clean-replay-v1.13.0-build-challenge-tests.log`; those of Paper 6 are
imported by its file of checks and were built with it), as were the further
tests of Paper 8 (`logs/clean-replay-v1.13.0-build-other.log`), and the
twelve audit files were run (`logs/clean-replay-v1.13.0-audit-*.log`). Every
axiom list printed in these logs, 25771 in the build logs, 392 in the audit
logs, 78 in the tests of the statement files and 158 in the further tests
of Paper 8 (each command counted once), is a subset of the three standard
axioms, and each matches one `#print axioms` command in the sources
(`logs/clean-replay-v1.13.0-axiom-audit.log`). All 915 modules were replayed
through the Lean kernel with `lake env leanchecker <Module>`, and all passed
(`logs/clean-replay-v1.13.0-leanchecker.log`,
`logs/clean-replay-v1.13.0-leanchecker-circulantq3.log`). The source manifest
of that version listed 926 files, and the procedure is
recorded in `logs/clean-replay-v1.13.0-receipt.json`. Before it was copied
into the release tree, the Lean package of Paper 6 had been built module by
module in two new empty directories, side by side, and every module checked
with `leanchecker`, twice: once with root-level module names and once in the
directory layout of the repository (`certificates/rm714/lean-package-v2/receipt.json`).

For version 1.14.0, which adds the 1925 Lean files of Paper 7, version 2
(`lean/Research/Backfill/Paper7/`), the whole project was rebuilt from a new
empty directory on the author's Windows computer (63 GB of memory), from
22:08 UTC on 4 November to 08:57 UTC on 5 November 2026, with `lean` and
`leanchecker` run on one module at a time rather than with `lake`. The rebuilt
sources agree byte for byte with `lean/Research.lean` and `lean/Research/`; the
directory `lean/Comparator/` was not rebuilt here. All 2841 modules compiled,
with 260 warning lines in 28 older modules (257 deprecations), no error and no
`sorry`. 2840 modules passed `leanchecker`. The remaining module is
`Research`, which consists of `import` lines and has no constants, so there is
nothing to replay in it; we read this from its compiled file. `leanchecker` on
this module was not completed: the first attempt ended when the computer
crashed, after about an hour and a half, and we stopped the second attempt at
69 GB of memory. We do not know the cause of the crash (Windows bug check
0x10E); memory is a likely one. All 112,106 printed axiom lists are subsets of
the three axioms above. Outside comments, the forbidden tokens occur only as the
intentional `sorry`s of the comparator challenge files
(`logs/clean-replay-v1.14.0-forbidden-tokens.log`). The rebuild did not run in
one piece: we stopped and restarted it, 2 modules twice failed to read a compiled
Mathlib file and passed at the third, automatic attempt, and 7 modules ran out
of memory (and 16 dependent modules were skipped) and were built again; no Lean
check rejected a module. `logs/lean-sources-sha256.txt` listed 2851 files. The full record is in
`logs/clean-replay-v1.14.0-receipt.json`, and the logs of every module are in
`logs/clean-replay-v1.14.0-logs.tar.gz`.

For version 1.15.0, which adds the 60 Lean files of Paper 2, version 2
(`lean/Research/Backfill/Paper2/`), the whole project was rebuilt from a new
empty directory on the author's Windows computer (63 GB of memory), from
15:15 UTC on 6 November to 02:31 UTC on 7 November 2026, again with `lean` and
`leanchecker` run on one module at a time rather than with `lake`. The rebuilt
sources agree byte for byte with `lean/Research.lean` and `lean/Research/`; the
directory `lean/Comparator/` was not rebuilt here. All 2901 modules compiled,
with the same 260 warning lines in 28 older modules as for version 1.14.0, none
in Paper 2, no error and no `sorry`. 2900 modules passed `leanchecker`. The
remaining module is `Research`, which consists of `import` lines and has no
constants, so there is nothing to replay in it; we read this from its compiled
file and did not run `leanchecker` on it. All 112,522 printed axiom lists are
subsets of the three axioms above, and the 84 lists printed by
`Research.Backfill.Paper2.Check` consist of exactly these three. Outside
comments, the forbidden tokens occur only as the intentional `sorry`s of the
comparator challenge files (`logs/clean-replay-v1.15.0-forbidden-tokens.log`).
The rebuild was not stopped by hand. In 10 attempts, 7 modules of Papers 6 and 7
failed to read a compiled file or ran out of memory, and passed when the driver
ran them again automatically; no Lean check rejected a module.
`logs/lean-sources-sha256.txt` listed 2911 files. The full record is in
`logs/clean-replay-v1.15.0-receipt.json`, and the logs of every module are in
`logs/clean-replay-v1.15.0-logs.tar.gz`.

For version 1.16.0, which adds the 53 Lean files of Paper 1, version 2
(`lean/Research/Backfill/Paper1/`), and replaces 13 older modules
`lean/Research/ICG*.lean` by versions that differ only in the names of three
Mathlib lemmas (`if_pos`, `if_neg`, `if_true` replaced by `ite_eq_left`,
`ite_eq_right`, `ite_true`), the whole project was rebuilt from a new empty
directory on the author's Windows computer (63 GB of memory), from 06:10 to
17:27 UTC on 7 November 2026, again with `lean` and `leanchecker` run on one
module at a time rather than with `lake`. The rebuilt sources agree byte for
byte with `lean/Research.lean` and `lean/Research/`; the directory
`lean/Comparator/` was not rebuilt here. All 2954 modules compiled, with 97
warning lines in 15 older modules, none in Paper 1, no error and no `sorry`;
there are fewer warnings than for version 1.15.0 because of the renamed
lemmas. 2953 modules passed `leanchecker`. The remaining module is
`Research`, which consists of `import` lines and has no constants, so there is
nothing to replay in it; we read this from its compiled file and did not run
`leanchecker` on it. All 112,694 printed axiom lists are subsets of the three
axioms above, and the 56 lists printed by
`Research.Backfill.Paper1.FinalContractAudit` (the 51 statements, one
calibration and four internal lemmas) consist of exactly these three. Outside
comments, the forbidden tokens occur only as the intentional `sorry`s of the
comparator challenge files (`logs/clean-replay-v1.16.0-forbidden-tokens.log`).
The rebuild took three runs. In the first, with up to 16 Lean processes at a
time, the computer ran out of memory: 4 modules failed to compile (3 could not
read a compiled Mathlib file, and 1 stopped with Windows exit code
0xC0000005), the 102 modules that import them were skipped, and 14
`leanchecker` runs failed to read a compiled file. The second run, with up to
8 processes, ran only the failed and skipped modules: all of them compiled,
and 16 `leanchecker` runs, of modules that import many large modules of
Paper 7, still failed to read a compiled file. The third run, with 2
processes, ran `leanchecker` on these 16 modules, and all passed. The failed
attempts are kept as 174 logs in 39 modules of Paper 7; none ended in a Lean
error, and the same modules passed at the first attempt in the rebuild of
version 1.15.0. No module of Paper 1 had to be run again.
`logs/lean-sources-sha256.txt` listed 2964 files. The full record is in
`logs/clean-replay-v1.16.0-receipt.json`, and the logs of every module are in
`logs/clean-replay-v1.16.0-logs.tar.gz`.

For version 1.17.0, which adds the 45 Lean files of Paper 1, version 3
(`lean/Research/TaskE/`), and two `import` lines in `lean/Research.lean`
(`Research.TaskE.FinalTaskEAudit` and `Research.TaskE.C1High`), the whole
project was rebuilt from a new empty directory on the author's Windows computer
(63 GB of memory), from 21:09 UTC on 8 November 2026 to 08:20 UTC on 9 November
2026, again with `lean` and `leanchecker` run on one module at a time, with up
to 14 jobs at a time, rather than with `lake`. The rebuilt sources agree byte for
byte with `lean/Research.lean` and `lean/Research/`; the directory
`lean/Comparator/` was not rebuilt here. All 2999 modules (the 2954 of version
1.16.0 and the 45 new ones) compiled, with 97 warning lines in 15 older modules,
none in Paper 1, no error and no `sorry`. 2998 modules passed `leanchecker`; the
remaining one is the module `Research`, which has only imports and no constants
and was exempted, as before. All 112767 printed axiom lists are subsets of the
three axioms above, and the 7 lists printed by
`Research.TaskE.FinalTaskEAudit` consist of exactly these three. Outside
comments, the forbidden tokens occur only as the intentional `sorry`s of the
comparator challenge files (`logs/clean-replay-v1.17.0-forbidden-tokens.log`).
This time the computer did not run out of memory: every module passed at the
first attempt, in one run, and no module was run again.
`logs/lean-sources-sha256.txt` listed 3009 files. The full record is in
`logs/clean-replay-v1.17.0-receipt.json`, and the logs of every module are in
`logs/clean-replay-v1.17.0-logs.tar.gz`.

For version 1.18.0, which adds the 6 Lean files of Paper 11
(`lean/Research/CographDist/`) and one `import` line in `lean/Research.lean`
(`Research.CographDist.Audit`), the whole project was rebuilt from a new empty
directory on the author's Windows computer (63 GB of memory), from 23:49 UTC on
9 November 2026 to 11:04 UTC on 10 November 2026, again with `lean` and `leanchecker`
run on one module at a time, with up to 12 jobs at a time, rather than with
`lake`. The rebuilt sources agree byte for byte with `lean/Research.lean` and
`lean/Research/`; the directory `lean/Comparator/` was not rebuilt here. All 3005
modules (the 2999 of version 1.17.0 and the 6 new ones) compiled, with
the same 97 warning lines in 15 older modules as for version 1.17.0, none in
Paper 11, no error and no `sorry`. 3004 modules passed `leanchecker`; the remaining one is
the module `Research`, which has only imports and no constants and was
exempted, as before. All 112,774 printed axiom lists are subsets of the three
axioms above, and the 7 lists printed by `Research.CographDist.Audit` consist
of exactly these three. Outside comments, the forbidden tokens occur only as
the intentional `sorry`s of the comparator challenge files
(`logs/clean-replay-v1.18.0-forbidden-tokens.log`). Every module passed at the
first attempt, in one run, and no module was run again.
`logs/lean-sources-sha256.txt` listed 3015 files. The full
record is in `logs/clean-replay-v1.18.0-receipt.json`, and the logs of every
module are in `logs/clean-replay-v1.18.0-logs.tar.gz`. Before it was copied
into the release tree, the Lean package of Paper 11 had been built module by
module from two new empty directories on the author's Mac and checked with
`leanchecker` (`certificates/cograph-distance/lean-package/receipt.json`).

For version 1.19.0, which adds the 6 Lean files of version 2 of Paper 10
(`lean/Research/WordRepTensor/TaskF/`) and one `import` line in
`lean/Research.lean` (`Research.WordRepTensor.TaskF.FinalAudit`), the whole
project was rebuilt from a new empty directory on the author's Windows computer
(63 GB of memory), from 17:34 UTC on 10 November to 06:13 UTC on 11 November
2026, again with `lean` and `leanchecker` run on one module at a time rather
than with `lake`. The rebuilt sources agree byte for byte with
`lean/Research.lean` and `lean/Research/`; the directory `lean/Comparator/` was
not rebuilt here. It took two passes. In the first, with up to 14 jobs at a
time, 14 attempts in 10 modules of Paper 7 ended without a Lean verdict (5 could
not read a compiled file, 4 ran out of memory with `std::bad_alloc`, 3 with an
"out of memory" panic, 1 left an empty log and 1 a log cut off); 8 of these
modules passed when the driver ran them again automatically, 2 did not, and the
84 modules depending on them were skipped. The second pass, with up to 6 jobs,
compiled these 86 modules and replayed with `leanchecker` all of them except
the exempt module `Research`, each at the first attempt. In the end all 3011 modules (the 3005 of version 1.18.0 and the 6 new
ones) compiled, with the same 97 warning lines in 15 older modules as for
version 1.18.0, none in Paper 10, no error and no `sorry`, and 3010 modules
passed `leanchecker`; the remaining one is the module `Research`, which has
only imports and no constants and was exempted, as before. No Lean check
rejected a module. All 112,783 printed axiom lists are subsets of the three
axioms above, and the lists printed for `check_Problem5_2` and
`check_Problem5_3` by `Research.WordRepTensor.TaskF.FinalAudit` consist of
exactly these three. Outside comments, the forbidden tokens occur only as the
intentional `sorry`s of the comparator challenge files
(`logs/clean-replay-v1.19.0-forbidden-tokens.log`).
`logs/lean-sources-sha256.txt` listed 3021 files. The full record, with both
passes, is in `logs/clean-replay-v1.19.0-receipt.json`, and the logs of every
module, including those of the failed attempts (suffix `.attemptN`), are in
`logs/clean-replay-v1.19.0-logs.tar.gz`.

For version 1.20.0, which adds the 8 Lean files of Paper 12
(`lean/Research/TaskG/`) and one `import` line in `lean/Research.lean`
(`Research.TaskG.Check`), the whole project was rebuilt from a new empty
directory on the author's Windows computer (63 GB of memory), from 23:49 UTC on
12 November 2026 to 13:36 UTC on 13 November 2026, again with `lean` and
`leanchecker` run on one module at a time rather than with `lake`. The rebuilt
sources agree byte for byte with `lean/Research.lean` and `lean/Research/`; the
directory `lean/Comparator/` was not rebuilt here. It took two passes. In the
first, with up to 14 jobs at a time, 20 compile attempts in 15 modules of
Paper 7 ended without a Lean verdict (7 ran out of memory with
`std::bad_alloc`, 6 with an "out of memory" error, 3 could not read a compiled
file, 3 left empty logs and 1 a log cut off); 13 of these modules passed when
the driver ran them again automatically, 2 did not, and the 83 modules
depending on them were skipped. A watcher script with a 10-hour limit started
the second pass at 09:47 UTC, while the first was still replaying modules with
`leanchecker`; the two drivers ran at the same time for about 15 minutes, until
the driver of the first pass stopped with a Python error at about 10:02 UTC,
because both wrote the same status file. The second pass, with up to 6 jobs,
reran every module not recorded as passed when it started: it compiled the 85
failed or skipped modules and the module `Research`, and replayed 1477 modules
with `leanchecker`, each at the first attempt; the 1541 modules that had
passed `leanchecker` in the first pass were not rerun. The empty logs of the
`leanchecker` runs that the first pass started or still had going after the
second pass began are kept (suffix `.attempt1`); `leanchecker` prints nothing
when it succeeds, and their results are not used. In the end all 3019 modules (the
3011 of version 1.19.0 and the 8 new ones) compiled, with the same 97 warning
lines in 15 older modules as for version 1.19.0, none in Paper 12, no error and
no `sorry`, and 3018 modules passed `leanchecker`; the remaining one is the
module `Research`, which has only imports and no constants and was exempted, as
before. No Lean check rejected a module. All 112,810 printed axiom lists are
subsets of the three axioms above, and the two lists printed by
`Research.TaskG.Check` consist of exactly these three. Outside comments, the
forbidden tokens occur only as the intentional `sorry`s of the comparator
challenge files (`logs/clean-replay-v1.20.0-forbidden-tokens.log`).
`logs/lean-sources-sha256.txt` listed 3029 files. The full record, with both
passes, is in `logs/clean-replay-v1.20.0-receipt.json`, and the logs of every
module, including those of the failed attempts (suffix `.attemptN`) and the
traceback of the first driver (`run.log`), are in
`logs/clean-replay-v1.20.0-logs.tar.gz`.

For version 1.21.0, which adds the 447 Lean files of Paper 13
(`lean/Research/TaskH/`) and five `import` lines in `lean/Research.lean`
(`Research.TaskH.ExactTests`, `ExactTestsFive`, `ExactTestsSix`,
`Seven.SevenCheck` and `Six.CaseSixElaboration`), the whole project was
rebuilt from a new empty directory on the author's Windows computer (63 GB of
memory), from 19:26 UTC on 16 November 2026 to 09:17 UTC on 17 November 2026,
with `lean` and `leanchecker` run on one module at a time rather than with
`lake`, while OpenAI Codex was also using the computer. The 447 files had
never been built together before. The rebuilt sources agree byte for byte
with `lean/Research.lean` and `lean/Research/`; the directory
`lean/Comparator/` was not rebuilt here. It took two passes. In the first,
the driver was restarted twice (at 19:29 and 20:03 UTC) to run more modules at
once, up to 16; it keeps every result already recorded as passed, and reran
the runs it stopped. With the computer's reserved memory near its limit,
1112 attempts failed for lack of memory or file access, not because of a
proof: 1080 could not read a compiled file, 31 ran out of memory, and in one
the Lean kernel could not create a
thread (Windows error 1455, the memory limit), so a `decide` step of a module
of Paper 4 failed with a Lean error and Lean listed `sorryAx` for its theorem,
as it does after an error; the source file has no `sorry`. One further
attempt left an empty log, and so did the 10 runs stopped at the restarts.
Most of these
modules passed when the driver ran them again automatically; at the end of
the first pass 87 modules had not compiled and the 627 modules depending on
them were skipped; in the `leanchecker` phase 29 modules failed and the 713
modules that had not compiled were skipped. The second pass,
started only after the first had ended, with up to 6 jobs, reran every module
not recorded as passed: it compiled 714 modules and replayed 742 with
`leanchecker`, each at the first attempt, including the module of Paper 4,
whose theorems then use only the three axioms above. All 3466 modules (the
3019 of version 1.20.0 and the 447 new ones) compiled, with the same 97
warning lines in 15 older modules as for version 1.20.0, none in Paper 13, and,
in their final runs, no error and no `sorry`, and 3465 modules passed `leanchecker`; the remaining one
is the module `Research`, which has only imports and no constants and was
exempted, as before. All 115,582 printed axiom lists are subsets of the three
axioms above, and the lists printed for `case_four`, `case_five`, `case_six`
and `case_seven` consist of exactly these three. Outside comments, the
forbidden tokens occur only as the intentional `sorry`s of the comparator
challenge files (`logs/clean-replay-v1.21.0-forbidden-tokens.log`).
`logs/lean-sources-sha256.txt` listed 3476 files. The full record, with both
passes, is in `logs/clean-replay-v1.21.0-receipt.json`, and the logs of every
module, including those of the failed attempts (suffix `.attemptN`), are in
`logs/clean-replay-v1.21.0-logs.tar.gz`.

For version 1.22.0, which adds the 269 Lean files of version 2 of Paper 13
(in `lean/Research/TaskH/`) and three `import` lines in `lean/Research.lean`
(`Research.TaskH.OriginalQuestionTwoTests`, `Fan.Tests` and `Gao.Tests`), the
whole project was rebuilt from a new empty directory on the author's Windows
computer (63 GB of memory), from 17:50 UTC on 17 November 2026 to 07:27 UTC on
18 November 2026, with `lean` and `leanchecker` run on one module at a time
rather than with `lake`; OpenAI Codex did not use the computer during the
rebuild. The rebuilt sources agree byte for byte with `lean/Research.lean` and
`lean/Research/`; the directory `lean/Comparator/` was not rebuilt here. It
took two passes. In the first, with up to 16 jobs, every module compiled; 5
compile attempts in 4 modules failed for lack of memory or file access (3 could
not read a compiled file, 2 ran out of memory with `std::bad_alloc`), and these
modules compiled when the driver ran them again automatically. In the
`leanchecker` phase 626 attempts in 237 modules failed in the same way (624
could not read a compiled file, 2 ran out of memory); 198 of these modules
passed when run again automatically, and 39 still could not read a compiled
file at their sixth attempt. No attempt ended with a Lean error. The second
pass, started only after the first had ended, with up to 6 jobs, replayed these
39 modules with `leanchecker`, each at the first attempt; nothing was compiled
again. All 3735 modules (the 3466 of version 1.21.0 and the 269 new ones)
compiled, with the same 97 warning lines in 15 older modules as for version
1.21.0, none in Paper 13, and, in their final runs, no error and no `sorry`,
and 3734 modules passed `leanchecker`; the remaining one is the module
`Research`, which has only imports and no constants and was exempted, as
before. All 116,770 printed axiom lists are subsets of the three axioms above,
and the lists printed for `TaskH.original_question_two_all_k`, for the proof
`TaskH.OriginalTests.exact_frozen_question_two` of the frozen statement
`Question2`, and for `case_four`, `case_five`, `case_six` and `case_seven`
consist of exactly these three. Outside comments, the forbidden tokens occur
only as the intentional `sorry`s of the comparator challenge files
(`logs/clean-replay-v1.22.0-forbidden-tokens.log`).
`logs/lean-sources-sha256.txt` listed 3745 files. The full record, with both
passes, is in `logs/clean-replay-v1.22.0-receipt.json`, and the logs of every
module, including those of the failed attempts (suffix `.attemptN`), are in
`logs/clean-replay-v1.22.0-logs.tar.gz`.

For version 1.23.0, which adds the 43 Lean files of Papers 14 and 15 (in
`lean/Research/TaskJ/`) and three `import` lines in `lean/Research.lean`
(`Research.TaskJ.Rank.CheckRank`, `Research.TaskJ.Rank.Extension.CheckExtension`
and `Research.TaskJ.Grid.CheckGrid`), the whole project was rebuilt from a new
empty directory on the author's Windows computer (63 GB of memory), from 23:37
UTC on 18 November 2026 to 12:32 UTC on 19 November 2026, with `lean` and
`leanchecker` run on one module at a time rather than with `lake`; OpenAI Codex did not use the computer during the rebuild (no file in its directories there was written after 23:35 UTC on 18 November, according to a recursive file listing taken after the rebuild). A first start, at 19:23 UTC on 18
November with up to 16 jobs, was lost about three minutes later, when the computer stopped with a Windows system error (bugcheck 0xEF, recorded in the Windows event log); its directory was set aside, and the rebuild was started again from the
same sources in a new empty directory with up to 12 jobs. The rebuilt sources
agree byte for byte with `lean/Research.lean` and `lean/Research/`; the
directory `lean/Comparator/` was not rebuilt here. It took one pass: every
compile and every `leanchecker` run passed at its first attempt. All 3778
modules (the 3735 of version 1.22.0 and the 43 new ones) compiled, with the
same 97 warning lines in 15 older modules as for version 1.22.0, none in Papers
14 and 15, and with no error and no `sorry`, and 3777 modules passed
`leanchecker`; the remaining one is the module `Research`, which has only
imports and no constants and was exempted, as before. All 116,793 printed axiom
lists are subsets of the three axioms above, and the lists printed for the ten
check theorems of Papers 14 and 15 consist of exactly these three. Outside
comments, the forbidden tokens occur only as the intentional `sorry`s of the
comparator challenge files (`logs/clean-replay-v1.23.0-forbidden-tokens.log`).
`logs/lean-sources-sha256.txt` listed 3788 files. The full record is in
`logs/clean-replay-v1.23.0-receipt.json`, and the logs of every module are in
`logs/clean-replay-v1.23.0-logs.tar.gz`.

For version 1.24.0, which adds the 12 Lean files of Paper 16 (in
`lean/Research/TaskL/Semigroup/`) and one `import` line in `lean/Research.lean`
(`Research.TaskL.Semigroup.CheckSemigroup`), the whole project was rebuilt from a new
empty directory on the author's Windows computer (63 GB of memory), from 12:40
UTC on 19 November 2026 to 01:27 UTC on 20 November 2026, with `lean` and
`leanchecker` run on one module at a time rather than with `lake`; OpenAI Codex
did not use the computer during the rebuild (no file in its directories there
was written after 23:35 UTC on 18 November, according to a recursive file
listing taken after the rebuild). The sources were archived before the release
commit; they agree byte for byte with `lean/Research.lean` and
`lean/Research/`; the directory `lean/Comparator/` was not rebuilt here. It
took two passes. In the first, with up to 12 jobs, 26 compile attempts in 5
modules of Paper 7 failed for lack of memory or file access (5 ran out of
memory with `std::bad_alloc`, 21 could not read a compiled file); two of these
modules compiled when the driver ran them again automatically, three still
failed at their sixth attempt, and the 11 modules that depend on them were
skipped. Every module that had compiled passed `leanchecker` at its first
attempt. No attempt ended with a Lean error. The second pass, started only
after the first had ended, with up to 5 jobs, compiled the 14 remaining modules
and replayed 13 of them with `leanchecker`, each at the first attempt. All 3790
modules (the 3778 of version 1.23.0 and the 12 new ones) compiled, with the
same 97 warning lines in 15 older modules as for version 1.23.0, none in Paper
16, and, in their final runs, no error and no `sorry`, and 3789 modules passed
`leanchecker`; the remaining one is the module `Research`, which has only
imports and no constants and was exempted, as before. All 116,801 printed
axiom lists are subsets of the three axioms above, and the lists printed for
the four check theorems of Paper 16 consist of exactly these three. Outside
comments, the forbidden tokens occur only as the intentional `sorry`s of the
comparator challenge files (`logs/clean-replay-v1.24.0-forbidden-tokens.log`).
`logs/lean-sources-sha256.txt` listed 3800 files. The full record, with both
passes, is in `logs/clean-replay-v1.24.0-receipt.json`, and the logs of every
module, including those of the failed attempts (suffix `.attemptN`), are in
`logs/clean-replay-v1.24.0-logs.tar.gz`.

For version 1.25.0, which adds the 198 Lean files of Papers 17 to 27 (in
`lean/Research/TaskN/`, `lean/Research/TaskP/`, `lean/Research/TaskR/`,
`lean/Research/TaskS/` and `lean/Research/TaskU/`) and fourteen `import`
lines in `lean/Research.lean`
(`Research.TaskN.Antichain.CheckAntichain`,
`Research.TaskN.Parking.CheckParking`,
`Research.TaskP.PrimeMedialRacks.CheckRack`,
`Research.TaskP.GradedWilf.CheckWilf`, `Research.TaskR.CSS.CheckCSS`,
`Research.TaskR.A7.CheckA7`, `Research.TaskP.RootRadius.CheckRootRadius`,
`Research.TaskP.RectangleDefect.CheckRectangle`,
`Research.TaskP.GeomSimplex.CheckSimplex`, `Research.TaskS.B.CheckB`,
`Research.TaskS.C.CheckC`, `Research.TaskS.C.MeasureAudit.CheckC`,
`Research.TaskU.H5.Check` and `Research.TaskU.H5B.CheckB`), the whole
project, 3988 modules (the 3790 of version 1.24.0 and the 198 new ones),
was rebuilt from a new empty directory on the author's Windows computer (63 GB of memory),
with `lean` and `leanchecker` run on one module at a time rather than with
`lake`, in two passes in the same output directory. Pass 1, from 17:44
UTC on 20 November 2026 to 06:32 UTC on 21 November 2026, with up to 12 jobs,
built the 3813 modules of version 1.24.0 and of Papers 17 and 18 (compilation
until 01:20 UTC, then `leanchecker`). For pass 2 the 175 Lean files of
Papers 19 to 27 and the final `lean/Research.lean` were added to the same
source directory, and the same driver, started only after pass 1 had ended, built and checked the 175 new modules and the module `Research` from
17:23 to 17:49 UTC on 21 November 2026, skipping the modules that had passed in pass 1. In both passes every module compiled and passed `leanchecker` without a second attempt; no attempt ended with a Lean error or for lack of memory
or file access. OpenAI Codex used the same computer during pass 1, for two development
compiles of Paper 24 after that paper's statement had been frozen (18:06:09
UTC on 20 November), from 18:27:02 to 18:29:13 and from 18:33:52 to 18:44:09
UTC, in its own directory (`ai4math-lean-worker\taskP`); according to a
recursive file listing taken after the rebuild, the 72 files there were
created between 18:27:03 and 18:44:07 UTC (the unpacked sources keep their
earlier modification times, from 18:05:14 UTC). They did not touch the
rebuild directory, and no file in Codex's directories there was written
during pass 2. After pass 2 the SHA-256 hashes of all 3988 rebuilt sources
were compared with `lean/Research.lean` and `lean/Research/`: no difference;
the directory `lean/Comparator/` was not rebuilt here (it is unchanged since
version 1.13.0, and the CI workflow checks it). All 3988 modules compiled, with
the same 97 warning lines in 15 older modules as for versions 1.21.0 to
1.24.0, none in Papers 17 to 27, and with no error and no `sorry`, and 3987
modules passed `leanchecker`; the remaining one is the module `Research`,
which has only imports and no constants and was exempted, as before. All
116,874 printed axiom lists are subsets of the three axioms above, and the
lists printed for the check theorems of Papers 17 to 27 consist of exactly
these three. Outside comments, the forbidden tokens occur only as the
intentional `sorry`s of the comparator challenge files
(`logs/clean-replay-v1.25.0-forbidden-tokens.log`).
`logs/lean-sources-sha256.txt` lists 3998 files. The full record, with both
passes, is in `logs/clean-replay-v1.25.0-receipt.json`, and the logs of every
module are in `logs/clean-replay-v1.25.0-logs.tar.gz`.

### Comparator check of the completely formalized papers

The completely formalized papers other than Papers 1, 2, 7 and 11 to 27 are also checked with
[comparator](https://github.com/leanprover/comparator). For each such paper,
a challenge file in `lean/Comparator/` states the
checked theorems with `sorry` proofs and imports only the paper's frozen
statement files, and `ci/comparator/` lists the theorems and the permitted
axioms (`propext`, `Quot.sound`, `Classical.choice`). comparator builds the
proofs (the `Check` modules) inside the
[landrun](https://github.com/Zouuup/landrun) sandbox, checks that every listed
theorem has exactly the statement of the challenge file and uses only the
permitted axioms, and replays the proofs in the Lean kernel and in the
independent kernel [nanoda](https://github.com/ammkrn/nanoda_lib). The files
in `lean/Comparator/` contain `sorry` on purpose and are not part of the
default build. The challenge file of Paper 5 differs in form from the others:
its `Check.lean` states each theorem with the statement written out in full,
so `lean/Comparator/Paper5.lean` is that file with each proof replaced by
`sorry` and its imports replaced by the four statement files (generated by a
script that checks that nothing else differs). The challenge file of Paper 6
imports its two frozen statement files, one of which imports the published
module `lean/Research/RM714Weights.lean` of version 1, whose weight predicate
the statement `Sec7Bridge` compares with the one of version 2.

The GitHub Actions workflow `.github/workflows/comparator.yml`, which runs at
every push to `main`, checks Papers 3, 4, 5 and 8 (versions 2), 9 and 10; the
versions of the tools are pinned in the workflow. For version 1.9.0 the
check passed on GitHub for Papers 4, 9 and 10
([run 36505842920](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/36505842920)),
for version 1.10.0 for Papers 3, 4, 9 and 10
([run 36606648581](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/36606648581)),
for version 1.11.0 for Papers 3, 4, 8, 9 and 10
([run 36777454459](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/36777454459)),
for version 1.12.0 for Papers 3, 4, 5, 8, 9 and 10
([run 37558138194](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/37558138194)),
for version 1.13.0 for the same papers
([run 38003526255](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/38003526255)),
for version 1.14.0 for the same papers
([run 42103194322](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/42103194322)),
for version 1.15.0 for the same papers
([run 42344646991](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/42344646991)),
for version 1.16.0 for the same papers
([run 42454366396](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/42454366396)),
for version 1.17.0 for the same papers
([run 42637962692](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/42637962692)),
for version 1.18.0 for the same papers
([run 42863985711](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/42863985711)),
for version 1.19.0 for the same papers
([run 43149518924](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/43149518924)),
for version 1.20.0 for the same papers
([run 43452408163](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/43452408163)),
for version 1.21.0 for the same papers
([run 44136540421](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/44136540421)),
for version 1.22.0 for the same papers
([run 44371642744](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/44371642744)),
for version 1.23.0 for the same papers
([run 44530821691](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/44530821691)),
and for version 1.24.0 for the same papers
([run 44671967866](https://github.com/Horace-Maxwell/ai4math-results/actions/runs/44671967866)).
Paper 6 is not in the workflow: a comparator run of its 35 theorems takes much
longer than those of the other papers (more than 30 minutes on the computer
used for version 1.13.0), and we have not tried it on GitHub's machines. It was
checked locally, as described next.

**Paper 7 has not been checked with comparator or nanoda.** Its package has
1925 modules, a run would take far longer than those of the other papers, and
we have not attempted one. Its proofs have been replayed by the Lean kernel
with `leanchecker` in the three builds described above, but not by an
independent kernel, and no comparator run has compared its theorems with a
challenge file; instead, `ClaudePaper7FinalPackage.lean` restates each of the
58 statements with its frozen type.

**Paper 2 has not been checked with comparator or nanoda.** It has no challenge
file in `lean/Comparator/` and no configuration in `ci/comparator/`. Its proofs
have been replayed by the Lean kernel with `leanchecker` in the builds
described above, but not by an independent kernel; `Check.lean` restates each
of the 84 statements with its frozen type.

**Paper 1 has not been checked with comparator or nanoda.** It has no challenge
file in `lean/Comparator/` and no configuration in `ci/comparator/`. Its proofs
have been replayed by the Lean kernel with `leanchecker` in the builds
described above, but not by an independent kernel; `FinalContractAudit.lean`
restates each of the 51 statements of version 2 with its frozen type, and
`lean/Research/TaskE/FinalTaskEAudit.lean` restates the main statement of
version 3, `SameParityThree`, and the conditions proved for it.

**Theorem 3 of Paper 10 (version 2) has not been checked with comparator or
nanoda.** The comparator configuration of Paper 10 lists the 11 statements of
version 1 only. The proofs of `check_Problem5_2` and `check_Problem5_3` have been
replayed by the Lean kernel with `leanchecker` in the two builds of the package
and in the rebuild of the whole project described above, but not by an
independent kernel.

**Paper 11 has not been checked with comparator or nanoda.** It has no
challenge file in `lean/Comparator/` and no configuration in `ci/comparator/`.
Its proofs have been replayed by the Lean kernel with `leanchecker` in the two
builds of its package and in the rebuild of the whole project described above,
but not by an independent kernel; `lean/Research/CographDist/Audit.lean`
restates the frozen statement `OpenProblemI_negative` and Theorem 1.

**Paper 12 has not been checked with comparator or nanoda.** It has no
challenge file in `lean/Comparator/` and no configuration in `ci/comparator/`.
Its proofs have been replayed by the Lean kernel with `leanchecker` in the two
builds of its package and in the rebuild of the whole project described above,
but not by an independent kernel; `lean/Research/TaskG/Check.lean` restates the
frozen statements `ShpectorovAnswer` and `StrongShpectorovAnswer`.

**Paper 13 has not been checked with comparator or nanoda.** It has no
challenge file in `lean/Comparator/` and no configuration in `ci/comparator/`.
Its proofs have been replayed by the Lean kernel with `leanchecker` in the two
builds of each of its packages and in the rebuild of the whole project
described above, but not by an independent kernel; the files
`lean/Research/TaskH/OriginalQuestionTwoTests.lean` and
`lean/Research/TaskH/ExactTests*.lean` restate the frozen statements.

**Papers 14 and 15 have not been checked with comparator or nanoda.** They
have no challenge files in `lean/Comparator/` and no configuration in
`ci/comparator/`. Their proofs have been replayed by the Lean kernel with
`leanchecker` in Codex's two builds of each package, in the two builds of the
repository versions on the author's Mac and in the rebuild of the whole
project described above, but not by an independent kernel; the files
`lean/Research/TaskJ/Rank/CheckRank.lean`,
`lean/Research/TaskJ/Rank/Extension/CheckExtension.lean` and
`lean/Research/TaskJ/Grid/CheckGrid.lean` restate the frozen statements.

**Paper 16 has not been checked with comparator or nanoda.** It has no
challenge file in `lean/Comparator/` and no configuration in `ci/comparator/`.
Its proofs have been replayed by the Lean kernel with `leanchecker` in Codex's
two builds of its package, in the build of the final reviewer, in the two
builds of the repository versions on the author's Mac and in the rebuild of
the whole project described above, but not by an independent kernel;
`lean/Research/TaskL/Semigroup/CheckSemigroup.lean` restates the frozen
statements.

**Papers 17 to 27 have not been checked with comparator or nanoda.** They
have no challenge files in `lean/Comparator/` and no configuration in
`ci/comparator/`. Their proofs have been replayed by the Lean kernel with
`leanchecker` in Codex's two builds of each package, in the build of each
final reviewer, in the two builds of the repository versions on the
author's Mac and in the rebuild of the whole project described above, but
not by an independent kernel; the files
`lean/Research/TaskN/Antichain/CheckAntichain.lean`,
`lean/Research/TaskN/Parking/CheckParking.lean`,
`lean/Research/TaskP/PrimeMedialRacks/CheckRack.lean`,
`lean/Research/TaskP/GradedWilf/CheckWilf.lean`,
`lean/Research/TaskR/CSS/CheckCSS.lean`,
`lean/Research/TaskR/A7/CheckA7.lean`,
`lean/Research/TaskP/RootRadius/CheckRootRadius.lean`,
`lean/Research/TaskP/RectangleDefect/CheckRectangle.lean`,
`lean/Research/TaskP/GeomSimplex/CheckSimplex.lean`,
`lean/Research/TaskS/B/CheckB.lean`, `lean/Research/TaskS/C/CheckC.lean`,
`lean/Research/TaskS/C/MeasureAudit/CheckC.lean`,
`lean/Research/TaskU/H5/Check.lean` and `lean/Research/TaskU/H5B/CheckB.lean`
restate the frozen statements.

For version 1.13.0, the same comparator, lean4export and nanoda versions were
run locally by OpenAI Codex on 9 October 2026, on macOS, where the landrun
sandbox is not available (comparator's `scripts/fake-landrun.sh` was used
instead), in the directory of the clean rebuild for that version described
above, with a limit of 30 minutes per command. For each of Papers 3, 4, 5, 8,
9 and 10, nanoda and the Lean kernel accepted the solution
(`logs/comparator-local-v1.13.0-paper3.log`,
`logs/comparator-local-v1.13.0-paper4.log`,
`logs/comparator-local-v1.13.0-paper5.log`,
`logs/comparator-local-v1.13.0-paper8.log`,
`logs/comparator-local-v1.13.0-paper9.log`,
`logs/comparator-local-v1.13.0-wordrep.log`). For Paper 6, one run of all 35
theorems took longer than this limit, so comparator was run once for each
theorem, with `ci/comparator/paper6.json` restricted to that theorem: for 32
theorems nanoda and the Lean kernel accepted the solution within the limit
(`logs/comparator-local-v1.13.0-paper6.log`). For the other three, the
statements on Proposition E (`PropE`, `PropE_mathlib` and
`PropE_remark_2mod4`; a run for `PropE_remark_2mod4` alone was stopped at
the limit, and `PropE_mathlib` alone was not run), Codex ran the steps of
comparator separately, with a
version of comparator that it modified to keep one export of the three
theorems between the steps: the comparison with the challenge file and the
axiom check passed, nanoda accepted the export, and the Lean kernel accepted
it, replayed in 47 steps of less than 30 minutes each, its state being saved
and checked between steps (`logs/comparator-local-v1.13.0-paper6-prope.log`;
the modified tools are not published). An unmodified comparator run for
`PropE` alone also accepted the solution; it took 42 minutes, longer than the
limit, and is reported in the same log but not counted. All modules of Paper 6,
including those of these three theorems, also passed `leanchecker` in the clean
rebuild. A Codex agent that had written none of the proofs or tools reviewed
this evidence and approved it. The receipts are in
`logs/comparator-local-v1.13.0-receipts.json`; the logs of versions 1.9.0 to
1.12.0 are kept. The Lean sources of these papers are unchanged in versions
1.14.0 to 1.18.0, and comparator was not run locally for them. The run on GitHub
for version 1.18.0 takes place after it is pushed; its result is shown on the
repository's Actions page.

### Reproduce the Lean checks

Each code block in this and the following sections starts from the repository
root.

Requirements: [elan](https://github.com/leanprover/elan), about 30 GB of free
RAM for `CirculantQ3.lean` (with Lean 4.34.1 its build peaked at 18–28 GB and
its `leanchecker` run at 21–25 GB), and, without Paper 7, about an hour and a
half (the clean rebuilds took about 46 minutes for version 1.9.0, about 24
minutes for version 1.10.0 and, with Paper 6, about 92 minutes for version
1.13.0, with at most two build jobs at a time). With Paper 7 a plain `lake
build` takes far longer: our module-by-module build took about 11 hours with 3 to 12 Lean processes at a
time, each of which commits 8 to 12 GB of memory on Windows, and the
most demanding modules ran out of memory with too many running together. To skip Paper 7, remove its `import` line from
`lean/Research.lean`. The commands below were last run with `lake` for version
1.13.0; for versions 1.14.0 to 1.18.0 the same modules were compiled directly with `lean`
(see above).

```sh
cd lean
lake exe cache get                               # prebuilt mathlib, pinned in lake-manifest.json
lake build                                       # builds everything imported by Research.lean; BrauerCMCore (Paper 5, version 1), RM714Weights (Paper 6, version 1) and the Check files of Papers 3, 4, 5, 6 and 8 (versions 2), 9 and 10 print their own axiom audits
lake env lean Research/ICGGeneralAudit.lean      # Paper 1, version 1.5: prints the final statements, definitions and axioms
lake env lean Research/ICGEqualParityBAudit.lean # Paper 1, version 1.5, Theorem 4: the same
lake env lean Research/ICGEqualParityBCertAudit.lean # Paper 1, version 1.5, Theorem 4: axioms of the 325 certificate lemmas
lake env lean Research/ICGBridgeAudit.lean       # Roldán q = 3: the same
lake env lean Research/CareniniAudit.lean        # Paper 3, version 1: the same
lake env lean Research/HKOTriameterAudit.lean    # Paper 4: the same
lake env lean Research/RM714WeightsAudit.lean    # Paper 6: the same
lake env lean Research/SwitchingThmHAudit.lean        # Paper 8: restates the main statements, prints their axioms
lake env lean Research/SwitchingRowCountAudit.lean    # Paper 8: prints the statements and axioms, checks a small instance
lake env lean Research/SwitchingDiam4CubicAudit.lean  # Paper 8: the same, with small instances
lake env lean Research/SwitchingWalkProfileAudit.lean # Paper 8, Remark 8.3 (not used for Theorem 1): the same
lake build Research.AxialMSZ.ChallengeTests      # Paper 9: known-answer tests of the statement file
lake env lean Research/AxialMSZ/Audit.lean       # Paper 9: prints the definitions, the frozen statements and the types of the 17 checks
lake build Research.Backfill.Paper3.ChallengeTests  # Paper 3 (version 2): known-answer tests of the statement file
lake build Research.Backfill.Paper4.ChallengeTests  # Paper 4 (version 2): known-answer tests of the statement file
lake build Research.Backfill.Paper1.FinalContractAudit  # Paper 1 (version 2): the 51 statements, printing the axioms
lake build Research.Backfill.Paper1.ChallengeTests Research.Backfill.Paper1.NarrowContractTests  # Paper 1 (version 2): tests of the statement files
lake build Research.TaskE.FinalTaskEAudit  # Paper 1 (version 3): restates SameParityThree and the conditions, checks two instances and the seven tests, printing the axioms
lake build Research.Backfill.Paper2.Check  # Paper 2 (version 2): the 84 statements, printing the axioms
lake build Research.Backfill.Paper2.ChallengeTests  # Paper 2 (version 2): tests of the statement file
lake build Research.Backfill.Paper5.ChallengeTests  # Paper 5 (version 2): known-answer tests of the statement file
lake build Research.Backfill.Paper6.ChallengeV3Tests  # Paper 6 (version 2): known-answer tests of the statement file
lake build Research.Backfill.Paper7.ClaudePaper7FinalPackage  # Paper 7 (version 2): the 58 statements; imports the statement files and their 120 known-answer tests, and prints the axioms
lake build Research.Backfill.Paper8.ChallengeTests  # Paper 8 (version 2): known-answer tests of the statement file
lake build Research.Backfill.Paper8.Proof.Tests.Main  # Paper 8 (version 2): further known-answer tests, written after the proofs
lake build Research.WordRepTensor.ChallengeTests  # Paper 10: known-answer tests of the statement file
lake build Research.WordRepTensor.TaskF.FinalAudit  # Paper 10 (version 2): restates Problem5_2 and Problem5_3 and two instances, printing the axioms
lake build Research.CographDist.Audit  # Paper 11: restates OpenProblemI_negative and Theorem 1, imports the five tests, printing the axioms
lake build Research.TaskG.Check  # Paper 12: restates ShpectorovAnswer and StrongShpectorovAnswer, printing the axioms
lake build Research.TaskH.OriginalQuestionTwoTests  # Paper 13: restates Question2 (all k), printing the axioms
lake build Research.TaskH.ExactTests Research.TaskH.ExactTestsFive Research.TaskH.ExactTestsSix Research.TaskH.Seven.SevenCheck  # Paper 13, version 1: restate CaseFour..CaseSeven, test K_5..K_8
lake build Research.TaskJ.Rank.CheckRank Research.TaskJ.Rank.Extension.CheckExtension  # Paper 14: restate the seven frozen statements, printing the axioms
lake build Research.TaskJ.Grid.CheckGrid  # Paper 15: restates the three frozen statements, printing the axioms
lake build Research.TaskL.Semigroup.CheckSemigroup  # Paper 16: restates the four frozen statements, printing the axioms
lake build Research.TaskN.Antichain.CheckAntichain  # Paper 17: restates the two frozen statements, printing the axioms
lake build Research.TaskN.Parking.CheckParking  # Paper 18: restates the two frozen statements, printing the axioms
lake build Research.TaskP.PrimeMedialRacks.CheckRack  # Paper 19: restates the three frozen statements, printing the axioms
lake build Research.TaskP.GradedWilf.CheckWilf  # Paper 20: restates the frozen statement, printing the axioms
lake build Research.TaskR.CSS.CheckCSS  # Paper 21: restates the four frozen statements, printing the axioms
lake build Research.TaskR.A7.CheckA7  # Paper 22: restates the frozen statement, printing the axioms (the kernel evaluates the certificate)
lake build Research.TaskP.RootRadius.CheckRootRadius  # Paper 23: restates the three frozen statements, printing the axioms
lake build Research.TaskP.RectangleDefect.CheckRectangle  # Paper 24: restates the frozen statement, printing the axioms
lake build Research.TaskP.GeomSimplex.CheckSimplex  # Paper 25: restates the four frozen statements, printing the axioms
lake build Research.TaskS.B.CheckB  # Paper 26, Theorem 1: restates the frozen statement ConjectureB, printing the axioms
lake build Research.TaskS.C.CheckC  # Paper 26, Theorem 2: restates the frozen statement conjectureC, printing the axioms
lake build Research.TaskS.C.MeasureAudit.CheckC  # Paper 26, Theorem 2′: the measured form and conjectureC, printing the axioms
lake build Research.TaskU.H5.Check  # Paper 27, Corollary 1: restates the two frozen statements witnessValue and leastPositiveMultiple, printing the axioms
lake build Research.TaskU.H5B.CheckB  # Paper 27, Theorem 1: restates the frozen statement fullSpectrum, printing the axioms
```

Toolchain: Lean 4.34.1, mathlib v4.34.1 (commit `d13f23b723b8a846827a245b89c10fc7d3f11612`).

The comparator check can be reproduced on Linux with the commands of
`.github/workflows/comparator.yml`: build landrun, nanoda, and comparator
with lean4export (after copying `lean/lean-toolchain` into the comparator
checkout), then run, in `lean/`, `lake env <comparator>
../ci/comparator/<paper>.json` with `COMPARATOR_LANDRUN`,
`COMPARATOR_LEAN4EXPORT` and `COMPARATOR_NANODA` pointing to the three
binaries.

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

Paper 9 (Python 3; SymPy only for `verify_independent.py`):

```sh
cd certificates/axial/code
python3 verify_simple.py && python3 verify_example.py && python3 verify_block.py   # S, E and D in exact arithmetic
cd ../code2 && python3 verify_independent.py   # a second program, written separately
cd ../paper-check && python3 check_paper.py    # every structure constant and displayed computation of the paper
```


### Reproduce the computations of Paper 1

These programs belong to versions 1.1 to 1.5 of Paper 1. Version 2 withdraws
the results that rested on them (Theorem 5 for `3 ≤ min(a, b) ≤ 8` and
Proposition 15) and deletes the cross-checks; no result of versions 2 and 3 uses them.
They are kept as the records of version 1.5. Requires a C compiler and Python 3
with SymPy and NumPy.

```sh
cd certificates/icg-q3-general
cc -O2 -o icg_search icg_search.c              # exhaustive search over all divisor sets
cc -O2 -DSIGNMODE=1 -o icg_sign icg_search.c   # enumeration of sign matrices
python3 run_search.py 4 1 3 5,7,11             # example: n = p^4·3 for p = 5, 7, 11 (compare logs/search_small.log)
```

Equal-parity results of version 1.5 (Theorem 3 and Proposition 15):

```sh
cd certificates/icg-equal-parity
python3 verify_1m.py              # every step of Theorem 3 in exact arithmetic
python3 cert22.py 2 2 5 3         # certificate for the shape (2,2), region p >= 5, q >= 3
python3 cert_fast.py 4 4 5 3      # the same for (4,4), vectorised (about 4 minutes)
python3 cert_sympy_check.py 2 2 5 3
```

Theorems 4 and 5 (versions 1.4 and 1.5; version 2 withdraws Theorem 5 for `3 ≤ min(a, b) ≤ 8`). `theorems-b-c/README.md` lists the expected
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

Paper 3, version 1 (requires Python 3 with NumPy, NetworkX and SymPy; in version 2 the finite checks are done by the Lean kernel):

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
python3 verify_paper_claims.py   # every concrete graph claim of version 1 of the paper
cc -O2 -o median_enum median_enum.c && ./median_enum 8 1   # all graphs with at most 8 vertices (about 30 seconds; compare ../logs/median_enum_le8.log)
python3 median8_second_impl.py   # the second enumeration of the median graphs with at most 8 vertices
python3 iso_check.py             # the two violators with 8 vertices are G1 and G2 (all 8! bijections)
python3 dh_exhaustive.py 11      # version 1 only: all connected distance-hereditary graphs with at most 11 vertices (about 4 minutes); version 2 no longer claims these counts
```

Paper 5, the programs of version 1 (requires zsh, and Python 3 with NetworkX); version 2 of the paper does not rely on them:

```sh
cd certificates/brauer-complete/code
python3 verify_cm.py ../certificates/cm_B7_rank3.txt B 7 3   # the second implementation checks one certificate
zsh run_all.sh                   # all checks of Section 8 of version 1: rebuilds every certificate, checks it, and rewrites ../logs/ (a few minutes)
```

Paper 6, the programs of version 1 (requires a C compiler and Python 3); version 2 of the paper does not rely on them:

```sh
cd certificates/rm714
cc -O2 -o verify_witnesses code/verify_witnesses.c && ./verify_witnesses < data/rm714_all_witnesses.txt   # the 7901 codewords of Theorem B (Möbius transform)
python3 code/verify_all_py.py    # the same codewords with big-integer truth tables, and their coverage of the spectrum
python3 code/cert_arith.py > arith_py.txt && cc -O2 -o cert_arith code/cert_arith.c && ./cert_arith > arith_c.txt && diff arith_py.txt arith_c.txt   # Lemma 4.1, Propositions C′, D and F: the same 38 lines
cc -O2 -o venn_enum_fast code/venn_enum_fast.c && ./venn_enum_fast 4   # Proposition E for up to four monomials (five monomials took 23 minutes)
```

Paper 7, the programs of version 1 (requires a C compiler; `sunB2` needs LAPACK, e.g. `-framework Accelerate` on macOS); version 2 of the paper does not rely on them:

```sh
cd certificates/sun-graphs
cc -O2 -o sunsearch_v4 code/sunsearch_v4_f5a38c28.c -lm && ./sunsearch_v4 4 41   # b = 4 up to 41 vertices: the 3 graphs of Theorem 2 (compare logs/A_b4_N41.out)
cc -O2 -o sunB_v1 code/sunB_v1_4d92eb48.c && ./sunB_v1 4 41                    # the same with the second program
cc -O2 -o sunB2 code/sunB2.c -framework Accelerate && ./sunB2 6 42              # b = 6 at 42 vertices: the counterexample is unique (about 3 minutes)
cc -O2 -o sunC review/code/sunC.c && ./sunC 4 41 noprune 1 0 1                 # the first referee agent's program (implementation C), without pruning (about a minute)
```

`certificates/sun-graphs/PACKAGING-NOTES.md` maps each claim of version 1 of the
paper to its programs and logs.

Paper 8 (requires Python 3 with SymPy):

```sh
cd certificates/switching
python3 diam4/code/final_region.py      # the finite set: 13,376 branch multisets; 3 fail both criteria, the trees of Proposition 5.6 (under a second)
```

`certificates/switching/PACKAGING-NOTES.md` lists the other programs and logs.

Formalizations of the known results A246056 and A376230:

```sh
python3 certificates/oeis-hanna/round5/a246056/check.py
python3 certificates/oeis-hanna/round5/a376230/check.py
```

The logs of all runs cited in version 1.5 of the paper are in `certificates/icg-q3-general/logs/`,
`certificates/icg-equal-parity/logs/` and
`certificates/icg-equal-parity/theorems-b-c/` (in `logs/` and in the `logs/`
folders of its subdirectories).
The Lean comments and the scripts in `certificates/icg-q3-general/review/`
use the numbering of the first draft. Draft Lemmas 1–4 and Theorem 5 are
Lemmas 7, 8, 10, 11 and Theorem 12 of Paper 1 (versions 1.4, 1.5 and 2). The "Lemma 3 as
stated" counterexample printed by `review/test_e_misc.py` concerns a
superseded hypothesis (`P > 0`); Lemma 10 of the paper assumes `P ≥ μ`.

## Layout

- `papers/`: LaTeX sources and PDFs of the twenty-seven papers.
- `ATTEMPTS.md`: every problem we worked on, and what became of it.
- `certificates/icg-q3-general/`: programs, logs and reviews for versions 1.1 to 1.5 of Paper 1, kept as records and not used by versions 2 and 3; `certificates/icg-q3-general/lean-package-v2/`: the manifest, receipt and build logs of the Lean package of Paper 1, version 2; `certificates/icg-q3-general/lean-package-v3/`: the same for version 3 (115 modules: the 70 of version 2 and the 45 of `lean/Research/TaskE/`).
- `certificates/icg-equal-parity/`: programs, logs and a negative control for Theorem 3 and Proposition 15 of Paper 1, version 1.5 (Proposition 15 is withdrawn in version 2); `PROOF-working-note.md` is the working note.
- `certificates/icg-equal-parity/theorems-b-c/`: programs and logs for Theorems 4 and 5 of Paper 1, version 1.5 (Theorem 5 for `3 ≤ min(a, b) ≤ 8` is withdrawn in version 2), including those of the three referee agents (`review/`, `review2/`, `review3/`); its `README.md` lists the commands.
- `certificates/oeis-hanna/round5/`: checks for A246056 and A376230.
- `certificates/carenini/`: programs and logs for version 1 of Paper 3, and the manifest and acceptance receipt of the Lean package of version 2 (`lean-package-v2/`).
- `certificates/hko-triameter/`: programs (`code/`) and logs (`logs/`) for version 1 of Paper 4, and the manifest and acceptance receipt of the Lean package of version 2 (`lean-package-v2/`).
- `certificates/brauer-complete/`: programs, certificates and logs for version 1 of Paper 5; `review/REVIEW.md` is the referee agent's report; `certificates/brauer-complete/lean-package-v2/`: the manifest and acceptance receipt of the Lean package of version 2 of Paper 5.
- `certificates/rm714/`: programs, data and logs for version 1 of Paper 6; `certificates/rm714/lean-package-v2/`: the manifest and acceptance receipt of the Lean package of version 2 of Paper 6.
- `certificates/sun-graphs/`: programs, logs and the referee agents' code and reports for version 1 of Paper 7; `certificates/sun-graphs/lean-package-v2/`: the manifest, acceptance receipt and build logs of the Lean package of version 2 of Paper 7.
- `certificates/switching/`: programs and logs for Paper 8, and the referee agent's report and programs (`review/`); `certificates/switching/lean-package-v2/`: the manifest and acceptance receipt of the Lean package of version 2 of Paper 8.
- `certificates/axial/`: the statement contract, the reviews of the statement file, the programs and logs for Paper 9, and the receipt of the acceptance run of its Lean package (`lean-package/`).
- `certificates/wordrep-tensor/lean-package/`: the manifest and acceptance receipt of the Lean package of Paper 10.
- `certificates/wordrep-tensor/lean-package-v2/`: the manifest, receipt and build logs of the Lean package of Paper 10, version 2.
- `certificates/cograph-distance/lean-package/`: the manifest, receipt and build logs of the Lean package of Paper 11.
- `certificates/axial-frobenius/lean-package/`: the manifest, receipt and build logs of the Lean package of Paper 12.
- `certificates/critical-cycles-mod-k/lean-package/`: the manifest, receipt and build logs of the Lean packages of Paper 13 (the four packages for `k = 4, 5, 6, 7` and the package for all `k`).
- `certificates/equivariant-rank/lean-package/`: the manifest, Codex's acceptance logs, and the receipt and logs of the recheck of the repository versions, for the Lean files of Paper 14.
- `certificates/lattice-box-paths/lean-package/`: the same for the Lean files of Paper 15.
- `certificates/numerical-semigroup-lengths/lean-package/`: the same for the Lean files of Paper 16.
- `certificates/tree-antichains/lean-package/`: the same for the Lean files of Paper 17.
- `certificates/variable-length-parking/lean-package/`: the same for the Lean files of Paper 18.
- `certificates/prime-medial-racks/lean-package/`: the same for the Lean files of Paper 19.
- `certificates/graded-wilf/lean-package/`: the same for the Lean files of Paper 20.
- `certificates/css-covering-equality/lean-package/`: the same for the Lean files of Paper 21, with both versions of its statement file.
- `certificates/a7-terrace/lean-package/`: the same for the Lean files of Paper 22, with the encoder that writes the terrace into `Data.lean`.
- `certificates/domination-root-radius/lean-package/`: the same for the Lean files of Paper 23.
- `certificates/bar-tiling-defect/lean-package/`: the same for the Lean files of Paper 24, with an erratum to its final review.
- `certificates/minkowski-length-simplices/lean-package/`: the same for the Lean files of Paper 25.
- `certificates/css-covering-minima/lean-package/`: the same for the Lean files of Paper 26 (both statements, three acceptance receipts and the four final reviews).
- `certificates/heisenberg-125-determinants/lean-package/`: the same for the Lean files of Paper 27 (both statement files, the acceptance receipts, among them that of an earlier attempt that was stopped, and the three final reviews).
- `certificates/oeis-hanna/lean-package-v2/`: the manifest, receipt and build logs of the Lean package of Paper 2, version 2.
- The files `PROOF-working-note.md` and `CONTRACT.md` in these folders are the agents' working records; they may refer to files that are not included here.
- `lean/`: Lake project with all Lean 4 proofs (`Research.lean` imports all of them). The completely formalized papers each have a folder with the frozen statement file `Challenge.lean`, its known-answer tests, the proof modules (`Proof/`) and `Check.lean`: `lean/Research/Backfill/Paper1/` (Paper 1, version 2; statement files `Challenge.lean` and `SupplementStatements.lean`, tests `ChallengeTests.lean` and `NarrowContractTests.lean`, the proof modules in the same directory, with no `Proof/` folder, and the check file `FinalContractAudit.lean`; the proofs also use the older modules `lean/Research/ICG*.lean`), `lean/Research/TaskE/` (Paper 1, version 3; the main statement file `Challenge.lean`, six auxiliary statement files `Challenge*.lean`, the tests `StatementTests.lean`, the proof modules in the same directory, with no `Proof/` folder, `Main.lean` with the main theorem, and the check file `FinalTaskEAudit.lean`; the proofs also use the modules of version 2), `lean/Research/Backfill/Paper2/` (Paper 2, version 2; the proof modules are in the same directory, with no `Proof/` folder), `lean/Research/Backfill/Paper3/` (Paper 3, version 2; with the two data generators in `Proof/TS/gen/` and `Proof/Small/gen/`), `lean/Research/Backfill/Paper4/` (Paper 4, version 2), `lean/Research/Backfill/Paper5/` (Paper 5, version 2; the three supplementary statement files are in `Supplement/`), `lean/Research/Backfill/Paper6/` (Paper 6, version 2; statement files `ChallengeV3.lean` and `BridgeChallenge.lean`, tests `ChallengeV3Tests.lean`, check file `CheckPaper6.lean`, and the proof modules in the same directory), `lean/Research/Backfill/Paper7/` (Paper 7, version 2; the 31 statement and test files, the proof modules and the check file `ClaudePaper7FinalPackage.lean` are all in this directory, with no `Proof/` folder and no `Check.lean`), `lean/Research/Backfill/Paper8/` (Paper 8, version 2; further known-answer tests in `Proof/Tests/`), `lean/Research/AxialMSZ/` (Paper 9), `lean/Research/WordRepTensor/` (Paper 10; version 2 adds `TaskF/`) and `lean/Research/CographDist/` (Paper 11; the statement file `Challenge.lean`, the tests `ChallengeTests.lean`, the proof modules `Family.lean`, `Eigen.lean` and `Main.lean` in the same directory, with no `Proof/` folder, and the check file `Audit.lean`) and `lean/Research/TaskG/` (Paper 12; the statement file `Challenge.lean`, which reuses the definitions of `lean/Research/AxialMSZ/Challenge.lean`, the proof modules `Data.lean`, `Axes.lean`, `Forms.lean`, `Automorphism.lean`, `Simplicity.lean` and `Main.lean` in the same directory, with no `Proof/` folder and no separate tests, and the check file `Check.lean`) and `lean/Research/TaskH/` (Paper 13; the statement files `Challenge.lean`, `CaseFive.lean`, `CaseSix.lean` and `CaseSeven.lean`, the tests `ExactTests.lean`, `ExactTestsFive.lean`, `ExactTestsSix.lean` and `ExactTestsSeven.lean`, the main files `MainFour.lean` to `MainSeven.lean`, the proof modules in the same directory and in `Five/`, `Six/` and `Seven/`; `Seven/SevenCheck.lean` restates the case `k = 7`; for all `k` (version 2), the assembly `OriginalQuestionTwoAssembly.lean`, the tests `OriginalQuestionTwoTests.lean`, and the proof modules in `General/`, `Gao/`, `Fan/` and `Bai/`), `lean/Research/TaskJ/Rank/` (Paper 14; the statement file `Challenge.lean` for Theorems 1 and 2, the proof modules `Parameters.lean`, `RankValues.lean` and `Proof.lean` and the check file `CheckRank.lean`, and in `Extension/` the statement file `Challenge.lean` for Theorem 3, eight proof modules and the check file `CheckExtension.lean`; no separate tests), `lean/Research/TaskJ/Grid/` (Paper 15; the statement file `Challenge.lean`, the 25 proof modules `Grid*.lean`, `Proof.lean` and the check file `CheckGrid.lean`; no separate tests), `lean/Research/TaskL/Semigroup/` (Paper 16; the statement file `Challenge.lean`, the 9 proof modules `Foundations.lean`, `FBase.lean`, `AlgebraCore.lean`, `AlgebraSwap.lean`, `Algebra.lean`, `CoverStep.lean`, `Terminal.lean`, `Interval.lean` and `Even.lean`, `Proof.lean` and the check file `CheckSemigroup.lean`; no separate tests), `lean/Research/TaskN/Antichain/` (Paper 17; the statement file `Challenge.lean`, the 8 proof modules `Numeric.lean`, `TreeCode.lean`, `GraphTransport.lean`, `TreeRoot.lean`, `BridgeWeights.lean`, `SequenceGraph.lean`, `TreePolynomial.lean` and `CompareCore.lean`, `Proof.lean` and the check file `CheckAntichain.lean`; no separate tests), `lean/Research/TaskN/Parking/` (Paper 18; the statement file `Challenge.lean`, the 9 proof modules `ParkGaps.lean`, `ParkSums.lean`, `ParkClassification.lean`, `SpacingWord.lean`, `SpacingPalCount.lean`, `ParkWalk.lean`, `ParkPrefix.lean`, `ParkBand.lean` and `SpacingCount.lean`, `Proof.lean` and the check file `CheckParking.lean`; no separate tests), `lean/Research/TaskP/PrimeMedialRacks/` (Paper 19; the statement file `Challenge.lean`, the 10 proof modules `IsoTransfer.lean`, `DisplacementData.lean`, `DisplacementGroup.lean`, `PrimeOrbits.lean`, `PrimeAction.lean`, `Coordinates.lean`, `CoordinatesCore.lean`, `Affine.lean`, `ClassCount.lean` and `Enumeration.lean`, `Proof.lean` and the check file `CheckRack.lean`; no separate tests), `lean/Research/TaskP/GradedWilf/` (Paper 20; the statement file `Challenge.lean`, the 6 proof modules `WilfScalar.lean`, `WilfLayers.lean`, `WilfAtoms.lean`, `WilfBasis.lean`, `WilfLow.lean` and `WilfHigh.lean`, `Proof.lean` and the check file `CheckWilf.lean`; no separate tests), `lean/Research/TaskR/CSS/` (Paper 21; the statement file `Challenge.lean`, the 6 proof modules `Geometry.lean`, `Residues.lean`, `Radius.lean`, `Volume.lean`, `ExclusionFinite.lean` and `Exclusion.lean`, `Proof.lean` and the check file `CheckCSS.lean`; no separate tests), `lean/Research/TaskR/A7/` (Paper 22; the statement file `Challenge.lean`, the 5 proof modules `Data.lean` (the terrace and its tables), `Kernel.lean`, `Cert.lean`, `Interpret.lean` and `Counting.lean`, `Proof.lean` and the check file `CheckA7.lean`; no separate tests), `lean/Research/TaskP/RootRadius/` (Paper 23, namespace `TaskP.GraphRootRadius`; the statement file `Challenge.lean`, the 11 proof modules `JoinDecomposition.lean`, `JoinPolynomial.lean`, `PetalCoefficient.lean`, `PetalEvaluation.lean`, `RootData.lean`, `Scale.lean`, `LogLimit.lean`, `UpperEstimate.lean`, `DiskZero.lean`, `RootDisk.lean` and `LowerBound.lean`, `Proof.lean` and the check file `CheckRootRadius.lean`; no separate tests), `lean/Research/TaskP/RectangleDefect/` (Paper 24; the statement file `Challenge.lean`, the 15 proof modules `RectCounts.lean`, `RowPlacement.lean`, `RowSplit.lean`, `StripLayout.lean`, `SmallRows.lean`, `BoundaryRows.lean`, `BoundaryWidths.lean`, `IntervalPacking.lean`, `BoundedBezout.lean`, `BalanceCases.lean`, `BalanceConstruction.lean`, `UpperCount.lean`, `UpperSparse.lean`, `LowerFamily.lean` and `MatchingLower.lean`, `Proof.lean` and the check file `CheckRectangle.lean`; no separate tests), `lean/Research/TaskP/GeomSimplex/` (Paper 25; the statement file `Challenge.lean`, the 13 proof modules `Packing.lean`, `TCoordinates.lean`, `TDiameter.lean`, `TLength.lean`, `TTetrahedron.lean`, `UCoordinates.lean`, `ULower.lean`, `UUpper.lean`, `UTetrahedron.lean`, `PyramidGeometry.lean`, `PyramidCorners.lean`, `PyramidDiameter.lean` and `PyramidTransport.lean`, `Proof.lean` and the check file `CheckSimplex.lean`; no separate tests), `lean/Research/TaskS/` (Paper 26; in `B/` the statement file `Challenge.lean`, the 8 proof modules `RationalLine.lean`, `Split.lean`, `KernelRounding.lean`, `BasisCoordinates.lean`, `Balanced.lean`, `Hull.lean`, `Upper.lean` and `Lower.lean`, `Proof.lean` and the check file `CheckB.lean`; in `C/` the statement file `Challenge.lean`, the 9 proof modules `Coordinates.lean`, `Frequencies.lean`, `Projected.lean`, `Lift.lean`, `Geometry.lean`, `ProjectionLattice.lean`, `ProjectionBody.lean`, `SimplexMeasure.lean` and `ProjectionModel.lean`, `Proof.lean` and the check files `CheckC.lean` and `MeasureAudit/CheckC.lean`; and `Shared/Sawtooth.lean`, used by both; no separate tests) and `lean/Research/TaskU/` (Paper 27; in `H5/` the statement file `Challenge.lean` of the minimum, the 33 proof modules `Fourier.lean`, `Blocks.lean`, `WitnessRows.lean`, `WitnessBase.lean`, `WitnessEval.lean`, `Witness.lean`, `Cyc5.lean`, `CycEval.lean`, `CycPos.lean`, `CycNorm.lean`, `CycPhase.lean`, `CycMoments.lean`, `Profile.lean`, `Normalize.lean`, `Phase.lean`, `RayMoments.lean`, `Factors.lean`, `ProfileEval.lean`, `TraceWords.lean`, `TraceProfile.lean`, `IntegerFactors.lean`, `CycRoots.lean`, `RayCancellation.lean`, `TraceLower.lean`, `TraceOrbit.lean`, `TraceCongruence.lean`, `TraceIntegral.lean`, `SmallMultiples.lean`, `Quotient.lean`, `Divisibility.lean`, `TraceFinal.lean`, `TraceAugment.lean` and `Minimum.lean` (`Witness.lean` and `Minimum.lean` contain the theorems `Proof.witnessValue` and `Proof.leastPositiveMultiple`; there is no `Proof.lean`), the audit file `Audit.lean` and the check files `CheckWitness.lean` and `Check.lean`; in `H5B/` the statement file `ChallengeB.lean` of the classification, the 23 proof modules `LiftRing.lean`, `BTrace.lean`, `Residues.lean`, `UnitTable.lean`, `UnitResidues.lean`, `BTraceImage.lean`, `Seeds.lean`, `SeedMarginals.lean`, `Insert.lean`, `RowsValue.lean`, `LiftBlock.lean`, `LiftData.lean`, `LiftColumns.lean`, `LiftCorrection.lean`, `LiftShift.lean`, `Construct.lean`, `PrimeOrbit.lean`, `PrimeBasis.lean`, `PrimeRing.lean`, `PrimeExtract.lean`, `Necessity.lean`, `CoprimeCongruence.lean` and `CoprimeSeeds.lean`, `ProofB.lean` and the check file `CheckB.lean`; no separate tests). `lean/Comparator/` holds the challenge files for the comparator check below.
- `.github/workflows/comparator.yml` and `ci/comparator/`: the comparator check of the completely formalized papers (see below; the workflow does not include Paper 6, whose configuration `ci/comparator/paper6.json` was used locally, and Papers 1, 2, 7 and 11 to 27 have no configuration).
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
  - when Theorem 2 (`q = 3` for general `r, s`) was released in v1.1.0 (26 September 2026), we
    were not aware of any earlier treatment;
  - equal parity: the case `n = pq` follows from formulas of Ilić (Linear
    Algebra Appl. 431, 2009) and Ilić–Bašić (Appl. Math. Comput. 218, 2011);
    Le and Sander (Linear Algebra Appl. 437, 2012) study the maximum over
    multiplicative divisor sets; for `pq` it equals the maximal energy, but for
    `pq³` it does not (e.g. 584 > 512 for `5·3³`, proved in Lean in version 2);
    on 26 September 2026 we found no earlier treatment of `pq^m` with
    `m ≥ 3`, or of any other equal-parity shape (deep search on 26 September 2026, 03:37–04:32 UTC, incremental
    search at 05:53–05:58 UTC, and a final check of the arXiv, GitHub, MathDB
    and MathOverflow at 15:49–15:52 UTC);
  - later work: Jiang and Yang (arXiv:2610.36883v1, 27 October 2026) state the
    equal-parity formula and the two maximisers for all distinct primes `p, q ≥ 5`,
    which contains Theorem 5 for those primes; their statement does not include the
    prime 3. A Lean proof of Roldán's conjecture for the exponents (2,3), including
    `q = 3`, was merged in trureturing on 20 October 2026
    ([PR #19390](https://github.com/the-omega-institute/trureturing/pull/19390)).
    A search on 7 November 2026 (06:11–06:43 UTC), for version 2, found no other
    work on this problem since 25 September, and in particular no treatment of the
    equal-parity orders with `min(a, b) ≥ 3` involving the prime 3;
  - version 3 (equal parity, one of the primes equal to 3, `min(a, b) ≥ 3`): a
    Codex agent searched the literature on 8 November 2026 (17:17 UTC), before the
    proofs, and a Claude Code agent searched again on
    8 November 2026, 21:07–21:22 UTC: the arXiv (API, the versions of
    arXiv:2608.29523 and arXiv:2610.36883, and the listings of math.CO, math.NT
    and math.SP up to those of 6 November 2026), Semantic Scholar, OpenAlex,
    DataCite, zbMATH Open, MathDB, MathOverflow and Mathematics Stack Exchange,
    GitHub (commits, issues, pull requests, repositories and code, and the commits
    since 6 November 2026 of 27 repositories of AI-assisted mathematics, including
    trureturing), and web search. Apart from version 1.5 of Paper 1, we found no
    proof, claim or announcement for these orders, and no announcement that the
    whole of Conjecture 14 is proved. arXiv:2610.36883 still had only version 1,
    which requires `p, q ≥ 5`, and arXiv:2608.29523 still had version 2 as its
    latest version. On 9 November 2026, 08:24–08:35 UTC, a Claude Code agent
    repeated the parts of this search that could have changed (the arXiv, with
    the listings of math.CO, math.NT and math.SP of 9 November 2026, Semantic
    Scholar, OpenAlex, GitHub and web search) and found nothing new; the versions
    of the two arXiv papers had not changed.
  This reports the coverage of our searches, not a guarantee of priority or that
  they were complete.
- Paper 3: Carenini's question was posted on 22 September 2026. We found no
  earlier answer to it or discussion of it (arXiv listing and API, Semantic
  Scholar, MathDB, GitHub code, commits, issues, pull requests and
  repositories, the AI-assisted repositories listed below, and web search;
  26 September 2026, 05:12–05:23 and 06:39–06:42 UTC, and again at 13:41 UTC
  before release). For version 2 we repeated the searches on 29 September
  2026, 12:55–13:35 UTC, also on MathOverflow and zbMATH; Carenini's paper
  still had only version 1, and we found no answer to the question other
  than version 1 of Paper 3. This reports the coverage of our searches, not a
  guarantee of priority.
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
    at 15:49–15:52 UTC found nothing new. For version 2 of the paper we
    repeated the final check between 23:38 UTC on 28 September and 00:17 UTC
    on 29 September 2026 and found nothing new.
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
  0-matrix semigroups and the lifting lemma, of which we use special cases,
  are theirs; version 1 derived Proposition 6.2 from their non-existence
  theorem, for which version 2 substitutes a direct parity argument; and the
  treatment of `B_n` follows their proof for the partition monoid, including
  the triangle of half-diagrams. A final check of the arXiv (still only
  version 1 of arXiv:2608.25092), GitHub, MathDB and MathOverflow at
  15:49–15:52 UTC found nothing new. For version 2 we repeated the searches
  on 6 October 2026, 17:25–19:18 UTC (arXiv:2608.25092 still had only
  version 1; Semantic Scholar, OpenAlex and DataCite list no work citing it;
  zbMATH Open was searched through its OAI-PMH interface, for the records in
  Mathematics Subject Classification classes 05 and 20 added or changed since
  25 August 2026), and again found
  no solution of Problem 15.11 and no announced progress on it. A last check
  of the arXiv and GitHub on 7 October 2026, 01:31–01:34 UTC, found nothing
  new. This reports the coverage of our searches, not a guarantee of
  priority.
- Paper 6:
  - M. Leuenberger and M. Albrizzio (arXiv:2606.21425v1, 19 June 2026)
    reduced the open cases to 22 values. Three of our 17 weights, 4378, 4380
    and 4382, are weights by their Proposition 4 and are not new.
  - The question is C. Carlet's (IEEE Trans. Inf. Theory 70 (2024)); we
    paraphrase the wording of his extended abstract, as the full text was not
    accessible to us. Conjecture 2 is from Y. Lou and Q. Wang (Des. Codes
    Cryptogr. 93 (2025)), quoted from arXiv:2406.03803v1. The paper of
    Kasami, Tokura and Azumi (1976) was not accessible either; the page
    reference we give is the one given by Carlet. Version 1 used that theorem
    to determine the whole spectrum, by excluding the weights below 320 other
    than the known list; version 2 deletes this determination, and none of its
    results rests on the theorems of Kasami and Tokura (1970) or of Kasami,
    Tokura and Azumi.
  - Correction (version 1.7.1): we have since read the note of Lou and Wang,
    *A note on two conjectures about the weight spectra of the Reed–Muller
    codes*, Discrete Appl. Math. 388 (2026) 142–145 (online 4 April 2026).
    Its Proposition 2 is Theorem C of Paper 6 (the same construction and the
    same weight 322), so Theorem C is not new. Its Open problem 1 asks whether
    322 is a weight of RM(7,14), one of the four values left open by Paper 6.
    Version 2 attributes Theorem C to Lou and Wang.
  - Apart from this note, we found no earlier claim that one of the 14 new
    values is a weight and no determination of the spectrum. We searched on 26 September 2026, 06:41–07:15 and
    13:43–14:03 UTC: the arXiv, citing works in Semantic Scholar, Crossref,
    zbMATH Open, the MathSciNet reference lookup, MathDB, MathOverflow and
    Mathematics Stack Exchange, the IACR ePrint archive, HAL, GitHub
    including trureturing, and web search. Citation queries to OpenAlex and
    keyword searches of Semantic Scholar hit rate limits; we did not search
    Google Scholar, and Scopus was not accessible. A final check of the arXiv,
    GitHub, MathDB and MathOverflow at 15:49–15:52 UTC found nothing new.
    Before the release of version 2 we repeated the searches on 9 October
    2026, 00:37–01:17 UTC: the arXiv (arXiv:2606.21425 and arXiv:2406.03803
    still had only version 1; new submissions and replacements in cs.IT and
    math.CO announced up to 8 October 2026), the works citing the papers of
    Leuenberger and Albrizzio, Lou and Wang, and Carlet in Semantic Scholar,
    OpenAlex and zbMATH Open, Crossref, DataCite, MathDB (its entries on
    Carlet's question and on Conjecture 2 of Lou and Wang were still open,
    without solutions or comments), MathOverflow, Mathematics Stack Exchange,
    GitHub including trureturing and other repositories of AI-assisted work
    on open problems, Zenodo, HAL, the IACR ePrint archive and web search
    (keyword searches of Semantic Scholar again hit rate limits). We found no
    claim by others that 322, 326, 330 or 334 is, or is not, a weight of
    RM(7,14), and no other new work on the weight spectrum of RM(7,14). A
    last check of the arXiv (including the announcement of 9 October 2026 in
    cs.IT and math.CO), GitHub and MathDB on 9 October 2026, 14:51–14:53 UTC,
    found nothing new.
  - Later work: Lou and Wang (arXiv:2610.36687v1, 27 October 2026) and Wei,
    Zhou, Zhang and Chen (arXiv:2610.29807v1, 21 October 2026); see the
    section on Paper 6 above. We found them on 8 November 2026 and checked
    their arXiv abstract pages (only version 1 of each) on that day.
  This reports the coverage of our searches, not a guarantee of priority.
- Paper 7: the question is from Braga, Moraes and Santos (arXiv:2609.28754v1,
  23 September 2026, still the only version on 27 September 2026). The three
  graphs of Theorem 2 are not new: Braga, Rodrigues and Trevisan (2017) found
  them in a search of the unicyclic graphs with at most 21 vertices; Theorem 2
  adds that there are no others up to 41 vertices (a search by Veras does not
  state its range). We found no earlier answer to the minimum-order question,
  and no earlier statement of Proposition 3 (which the paper presents as an
  observation whose novelty is uncertain), in our searches of 26 September
  2026 (the arXiv, GitHub including trureturing, MathDB, MathOverflow and web
  search), the last between 23:15 and 23:17 UTC; the searches for works
  citing the source paper in OpenAlex failed (HTTP 429), some papers on
  integral unicyclic graphs were not accessible to us, and we did not search
  Google Scholar, zbMATH or MathSciNet. The arXiv, GitHub,
  MathDB and MathOverflow searches were repeated on 27 September 2026,
  06:01–06:04 UTC, with the same result. After version 1 was made public,
  Braga, Moraes and Santos (arXiv:2610.22773v1, 16 October 2026) proved that
  `C_3` is the only integral unicyclic graph with a cycle of odd length,
  which supersedes Corollary 3.1, and that `(g − 1)!` divides `2c_g`, which
  implies the first part of Proposition 3. Searches for version 2 on 4
  November 2026, 12:00–12:17 UTC (the arXiv API, Semantic Scholar, OpenAlex,
  Crossref, DataCite, zbMATH Open, MathDB, MathOverflow, Mathematics Stack
  Exchange, web search and public GitHub repositories of AI-assisted
  mathematics) found no other work on these questions. Web search did not
  find that paper by its exact title, so web search misses recent work.
  A last check of arXiv and of GitHub on 5 November 2026 found nothing new. This reports the coverage of our searches, not a guarantee of
  priority.
- Paper 8: the problem is Problem 1.6 of Akbari, Kumar, Mohar and Pragada
  (arXiv:2609.27046v1, still the only version on 27 September 2026); the
  conjecture is from Linear Algebra Appl. 614 (2021), whose full text was not
  accessible to us. Stars, double stars, paths, harmonic trees and all
  connected graphs with at most nine vertices were known before. We found no
  proof or claim of the conjecture for all trees of diameter at most 4, or
  for a class of trees containing them (arXiv, MathDB, GitHub including
  trureturing, MathOverflow and the other sources listed in the paper; we did
  not search Google Scholar or MathSciNet, and dblp could not be queried;
  last check 27 September 2026, 06:01–06:04 UTC). For version 2 we repeated
  the searches on 29 September 2026, 18:35–19:35 UTC (arXiv:2609.27046 still
  had only version 1, and the MathDB entry for the conjecture was still
  open), and again found no proof or claim of the conjecture for the trees of
  diameter at most 4 or for a class of trees containing them. This reports the
  coverage of our searches, not a guarantee of priority.
- Paper 9: the questions are Problems 3.8, 3.9 and 3.11 of Gorshkov and
  Shpectorov (arXiv:2606.30048v1), Questions 9.2, 9.3 and 9.5 of Mamontov,
  Shpectorov and Zhelyabin (arXiv:2602.11984v1) and Conjecture 3.16 of
  McInroy and Shpectorov (arXiv:2209.08043v1); no newer versions existed on
  28 September 2026. For Jordan-type laws the conjecture holds (Hall, Segev
  and Shpectorov), and for Seress laws it holds when all but one component
  subalgebra are slender (Khasraw, McInroy and Shpectorov); these results do
  not apply to our laws. Non-symmetric dominance was already present,
  unremarked, in the algebras of Peng (arXiv:2608.28653) and of Kaygorodov,
  Martín González and Páez-Guillán (arXiv:2211.00334). We found no earlier
  example answering Problem 3.11 or Problem 3.8 for any fusion law (arXiv,
  GitHub including trureturing and other repositories of AI-assisted
  results, MathDB, MathOverflow and Mathematics Stack Exchange, OpenAlex,
  zbMATH Open, Semantic Scholar's citation lists, authors' pages and the
  page of a seminar on axial algebras, 27 September 2026, 17:56–18:31 and
  22:59–23:23 UTC, and the arXiv again on 28 September, 00:30 UTC). We did
  not search Google Scholar or MathSciNet, and could not read the published
  versions of the papers of Khasraw, McInroy and Shpectorov and of McInroy
  and Shpectorov. This reports the coverage of our searches, not a guarantee
  of priority.
- Paper 10: the question is Problem 5.1 of Alshammari (arXiv:2609.20881,
  posted on 16 September 2026). Choi, Kim and Kim had shown that a tensor
  product of two graphs with semi-transitive orientations need not have one
  (the first part of Problem 7.2.5 of Kitaev and Lozin). We found no
  earlier answer to Problem 5.1. We searched on 27 September 2026 between
  18:06 and 19:02 UTC: the arXiv (its API, for the topic and the author);
  the works citing the paper in OpenAlex (there were none); MathDB;
  MathOverflow and Mathematics Stack Exchange, through the Stack Exchange
  API; GitHub (code, commits, issues, pull requests and repositories),
  including the repositories trureturing and SCOPE2026; Wikipedia; and web
  search. OpenAI Codex repeated a smaller search later that day, and a
  final check between 23:38 UTC on 28 September and 00:17 UTC on
  29 September 2026 found nothing new. We did not search
  Google Scholar, Scopus or Web of Science, and we did not consult the book
  of Kitaev and Lozin itself. This reports the coverage of our searches,
  not a guarantee of priority. For Problems 5.2 and 5.3 (version 2) we found
  no earlier answer, claim or announced work in a search on 9 November 2026
  between 22:11 and 22:27 UTC: the arXiv (only version 1 of the paper); the
  works citing it in OpenAlex and Semantic Scholar (there were none); Crossref
  and Zenodo; GitHub, including trureturing, where an issue opened on
  27 October 2026 concerns only Problem 5.4 and calls Problems 5.2 and 5.3
  open; MathDB; MathOverflow and Mathematics Stack Exchange; and web search.
  Google Scholar could not be searched. A further search on 11 November 2026 (14:36–14:46 UTC) found nothing new; Semantic Scholar and Google Scholar could not be searched then.
- Paper 11: the question is part (i) of the open problem "Distance
  eigenvalues of cographs below −2 and sharpness" in the survey of Manna,
  Mandal and Tura (arXiv:2611.06981v1, 4 November 2026). Lu, Huang and Lou
  (Linear Algebra Appl. 553 (2018)) showed that connected threshold graphs
  have no distance eigenvalue in `(−2, −1)`, Lou and Lin (Linear Algebra Appl.
  608 (2021)) extended this to all connected cographs, and Alazemi, Anđelić,
  Koledin and Stanić (Linear Multilinear Algebra 69 (2021)) found a larger
  such interval for threshold graphs. The graphs `G_m` of the paper were used
  by Conde, Dratman and Grippo (arXiv:2606.06052v1, 4 June 2026, Lemma 6 and
  its proof) for the adjacency matrix. Their paper does not discuss the
  distance matrix, but our answer follows from their lemma in a few lines
  (Remark 1 of the paper); the survey cites their paper. A Claude Code agent
  searched on 9 November 2026 between 22:49 and 23:17 UTC: the arXiv (its
  API, and the versions of the survey), OpenAlex (including the works citing
  the survey, the paper of Conde, Dratman and Grippo and the papers above),
  Crossref, zbMATH Open, MathDB, MathOverflow and Mathematics Stack Exchange
  through the Stack Exchange API, GitHub, including trureturing and other
  repositories of AI-assisted results, and web search. It found no paper that
  states the answer for the distance matrix, and no announcement or claim of
  it; the survey still had only version 1 and no citing works. Google Scholar
  (it returned a verification page) and Semantic Scholar (HTTP 429, for the
  survey and the paper of Conde, Dratman and Grippo) could not be searched,
  and of the papers of Lou and Lin and of Alazemi, Anđelić, Koledin and
  Stanić, which are behind paywalls, we read only the abstracts or the survey's account of them. This reports
  the coverage of our searches, not a guarantee of priority.
- Paper 12: the question is Shpectorov's, Problem 3.3 of the survey of
  Gorshkov and Shpectorov, *Axial algebras: questions and conjectures*
  (arXiv:2606.30048v1; Problem 2.3 of the journal version, Commun. Math. 35
  (2027), no. 2, Paper no. 5, published on 11 November 2026, with the same
  wording), which also gives the definitions used. Neither version marks the
  question as answered; the journal version does mark another of its
  questions as answered by later work. A Claude Code agent searched on
  12 November 2026 between 23:30 and 23:42 UTC: the arXiv (the versions of
  the survey, and its listings on axial algebras since June 2026, of which
  five recent papers were checked, two of them by their abstracts only), the journal version, OpenAlex and Semantic
  Scholar (the works citing the survey: two and one, none on this question;
  OpenAlex counts three but lists two), MathDB, web search, and GitHub,
  including trureturing (its issues and pull requests, and a truncated file
  listing), astrafala/Conjectures, OEIS-Settled and the names of the
  repositories of vibemathing. It found no answer to the question and no
  axial algebra whose full automorphism group is known not to preserve a
  Frobenius form in a non-trivial way. A second search on 13 November 2026
  between 15:03 and 15:23 UTC covered what had appeared since: the arXiv
  listings in math.RA, math.GR and math.RT announced on 13 November, the new
  commits and the issues and pull requests of trureturing, new commits of the
  other repositories, GitHub-wide searches of issues, commits and code, the
  open-problem catalogue 10m-u/open-problems-catalog (which lists other
  questions of the survey, but not this one), the journal and Zenodo pages,
  OpenAlex, Crossref, and MathOverflow and Mathematics Stack Exchange searched
  directly. It found nothing new. Google Scholar and the keyword search of
  Semantic Scholar could not be used, and the example was not compared with
  classifications of small algebras. This reports the coverage of the search, not a guarantee
  that it was complete.
- Paper 13: the question is Question 8 of Choi and Sieniawski
  (arXiv:2611.13580v1, submitted on 10 November 2026). The lower bound was
  conjectured by Brewster, McGuinness, Moore and Noel (Theoret. Comput. Sci.
  639 (2016)); Kim and Picollelli proved the case `k = 3`, with equality only
  for `K_4`, and the bound for graphs of minimum degree `k` (Electron. J.
  Combin. 31(2) (2024), Theorem 2.4 and Corollary 2.5), without discussing
  equality for `k ≥ 4`. Claude Code searched before the work began
  (13 November 2026, up to 17:56 UTC) and before the release (16 November
  2026, 19:28–19:43 UTC): the arXiv (the versions of the paper, which had only
  version 1, and the math.CO listings since 9 November, with keyword and
  author searches), OpenAlex, Semantic Scholar, OpenCitations and Crossref
  (no citing works were listed), web search, MathDB (the conjecture is listed
  as open), MathOverflow, Mathematics Stack Exchange, Emergent Mind and
  alphaXiv, and GitHub, including the issues, pull requests and commits of
  trureturing since 10 November and other repositories of AI-assisted
  mathematics. A shorter check after the rebuild (17 November 2026, about
  09:27 UTC: the arXiv page of the paper, an arXiv search and web search)
  found nothing new. For version 2 (all `k`), Claude Code checked again on
  17 November 2026, 17:58–18:05 UTC (the arXiv page, which still had only
  version 1, web search, GitHub issues, pull requests, commits and
  repositories, trureturing since 09:00 UTC, and the November entries of
  SCOPE-Science/SCOPE2026) and again on 17 November 2026, 19:32–19:35 UTC (the arXiv page, GitHub
  issues, commits and repositories, trureturing, openai/math, vibemathing and
  astrafala), and on 18 November 2026, 07:35–07:37 and 18:17–18:18 UTC (the arXiv page, GitHub
  issues, commits and repositories, trureturing, openai/math and astrafala). No answer to the question for any
  `k ≥ 4` was found, apart from version 1 of Paper 13. The tools of version 2
  are published: Gao, Huo, Liu and Ma (arXiv:1904.08126, IMRN 2022), Fan
  (J. Combin. Theory Ser. B 84 (2002)) and, for the remark, Bai, Grzesik, Li
  and Prorok (arXiv:2511.03085, J. Combin. Theory Ser. B 180 (2026)); none of
  them treats this question. The
  repository graph-theory-AI/Graph-Theory-LLM-Proofs contains two AI-written
  notes (September 2026) on the lower bound itself, for joins, graphs of order
  at most `2k`, line graphs and Mycielski graphs; one notes that among
  `(k+1)`-critical line graphs only `K_{k+1}` attains the bound. They do not
  answer the question for general critical graphs. Google Scholar, zbMATH and
  the details pages of Semantic Scholar could not be used, the file tree of
  trureturing was searched only as far as the API returned it, and web search
  indexes November 2026 incompletely. This reports the coverage of the search,
  not a guarantee that it was complete.
- Paper 14: the bounds and the expectation of equality are those of
  Lara-Gómez, Romero-Rosales and Ruiz-Medina (*Semigroup Forum*, published
  online 2 November 2026, doi:10.1007/s00233-026-10690-y; preprint
  arXiv:2607.04053v1, submitted on 4 July 2026), and so are the generating
  sets that the paper uses. Their own 21-point example (Example 1 of the
  journal version, Example 20 of the preprint) already shows that the packet
  expression is not always the rank; the five-point example of Theorem 2 is a
  simpler instance. That `C_2 × S_3` has rank 2 follows from Theorem 1.1 and
  Lemma 3.10 of J. Lu (arXiv:2604.16141v1, April 2026). Encoding adjacency by
  common prime factors, the Chinese remainder theorem and the description of
  the equivariant permutations of `G/H` are classical, and the corrected bound
  of Remark 2 of the paper is a recount of the authors' own generating set. A
  Codex agent searched on 17 and 18 November 2026 (23:56–00:00 UTC, before the
  Lean work): the arXiv (the preprint had only version 1), the journal page,
  Crossref (no update, correction or citing work registered), OpenAlex (no
  citing works), zbMATH, MathDB, MathOverflow and Mathematics Stack Exchange,
  web search, and GitHub (issues, pull requests, commits and code), including
  trureturing (its issues, pull requests and commits, and the full text of its
  files at a fixed commit) and the lists of other repositories of AI-assisted
  mathematics. Claude Code checked again on 18 November 2026, 19:27–19:33 UTC
  (the arXiv API, Crossref, OpenAlex, GitHub searches of issues, commits and
  repositories, the issues and recent commits of trureturing, and the latest
  updates of openai/math and astrafala/Conjectures). Claude Code checked again on the day of the release, 19 November 2026, 12:37–12:38 UTC, in the same places, and found nothing new. No correction of Theorem 4 and no earlier statement of Theorems 1 or 3 was found. Google
  Scholar returned a verification page, the agents could not open the
  publisher's page (the journal version was read in an archived copy), and
  one GitHub search of Claude Code's first check was rate-limited, so that its
  positive control did not complete. This reports the coverage of the search,
  not a guarantee that it was complete.
- Paper 15: the question is the first open problem of §6.3 of J. Yuan
  (arXiv:2611.19908v1, submitted on 15 November 2026), who also computed the
  three-dimensional values and suggested the expression for boxes with even
  sides. The hypercube was treated by Kchikech, Khennoufa and Togni (Discuss.
  Math. Graph Theory 28 (2008), Lemma 2), the plane by Jiang (arXiv:1401.6583,
  Theorem 3.1, for sides larger than 2), Fried (Math. Commun. 31 (2026), up
  to an additive error of one) and Yuan (Theorem 1.1), and one dimension by
  Bulteau, Giraudo and Vialette (CPM 2021, Theorem 8); the term upper
  traceable number is from Okamoto, Zhang and Saenpholphat (Czechoslovak
  Math. J. 58 (2008)). G. J. Simmons (*An application of maximum-minimum
  distance circuits on hypercubes*, Lecture Notes in Math. 686, Springer,
  1978, 290–299) maximized the sum of the distances around closed circuits
  through the points of an equal-sided cube `[d]^n` and used the
  one-coordinate form of the centring identity of the paper; only pp. 290–291
  could be read, and we do not know whether the rest treats open paths or
  boxes with unequal sides. Jiang (§7) conjectured that on grids with an odd
  side the coordinatewise maxima can be attained together; Corollary 2 of the
  paper answers this with free endpoints. Barvinok, Fekete, Johnson, Tamir,
  Woeginger and Woodroofe (J. ACM 50 (2003)) give a polynomial-time algorithm
  for maximum tours in fixed dimension, not a formula for boxes. A Codex agent
  searched on 17 November 2026 (23:54–23:58 UTC, before the Lean work): the
  arXiv (Yuan's paper had only version 1), OpenAlex, Crossref and zbMATH,
  including works citing Jiang, Fried and the papers of 2008, MathDB,
  MathOverflow and Mathematics Stack Exchange, web search with several
  phrasings (upper traceable number, radio labelling, maximum travelling
  salesman), and GitHub as for Paper 14. That search missed the paper of
  Simmons and described the conjecture of Jiang only as a direction of
  research; the final review found both, and Codex added them on 18 November
  2026. Claude Code checked again on 18 November 2026, 19:27–19:33 UTC, as for
  Paper 14, and again on 19 November 2026, 12:37–12:38 UTC, finding nothing new. No earlier exact value of the open-path maximum for
  boxes with three or more sides larger than 1 was found, apart from the
  hypercubes. Google Scholar returned a verification page, OpenAlex had no
  record of Yuan's paper at the time of the first search, and the full text of
  the paper of Fried was not read by the agent that wrote the paper. This
  reports the coverage of the search, not a guarantee that it was complete.
- Paper 16: the conjectures are Conjectures 1.1 and 3.9 of P. A.
  García-Sánchez and C. O'Neill (*Lengths of irreducible decompositions of
  numerical semigroups*, arXiv:2602.00404v1, 2026), who proved them for
  multiplicity at most 6 (Section 3) and found large intervals of lengths for
  ordinary numerical semigroups (Section 4). The question was raised in §3 of
  P. A. García-Sánchez (*Factorizations into irreducible numerical
  semigroups*, Commun. Korean Math. Soc. 40 (2025), 587–592;
  arXiv:2410.13729v1), whose main result concerns the union of the sets of
  lengths of all numerical semigroups. The criterion by special gaps, the
  existence of decompositions and an algorithm for a decomposition of minimum
  length are in J. C. Rosales and P. A. García-Sánchez (*Numerical
  Semigroups*, Springer, 2009, Chapter 3, Section 4); the exchange that keeps
  the Frobenius number is a special case of Proposition 5 of V. Blanco and
  J. C. Rosales (Forum Math. 25 (2013); arXiv:1105.2147v1); the bound `r(S)`
  for the minimum length is from J. C. Rosales and M. B. Branco (Bull. Belg.
  Math. Soc. Simon Stevin 9 (2002), Corollaries 10 and 18), as quoted in
  Theorem 2.1 of T. Bogart and S. A. Seyed Fakhari (Comm. Algebra 53 (2025);
  arXiv:2405.11080), who also show that the minimum length is unbounded; and
  the pairing of residue classes for multiplicity 6 is in the proof of
  Theorem 3.5 of García-Sánchez and O'Neill. The full text of the paper of
  Rosales and Branco could not be read, so a decomposition of length exactly
  `r(S)` may already be there; Paper 16 does not claim it as new. Codex
  agents searched on 18 November 2026, during the search for problems
  (19:22–19:50 UTC) and again before the statement file was frozen: the
  arXiv (both preprints had only version 1), OpenAlex (one citing work each
  for the 2026 and the 2024 preprints; the first, a survey of Tringali, was
  checked), Crossref, DataCite, MathDB, MathOverflow and Mathematics Stack
  Exchange, web search, the research page
  of O'Neill (which lists the 2026 paper as submitted), the abstracts of the
  biennial congress of the Real Sociedad Matemática Española of January 2026,
  and GitHub (issues, commits, repositories and code), including trureturing
  (three of its issues ask other questions on numerical semigroups, among
  them lengths of factorizations of elements) and the lists of other
  repositories of AI-assisted mathematics. They also found an undergraduate
  project of 2025/26 at the University of Granada supervised by
  García-Sánchez, whose public proposal asks for a survey of known results;
  no final report of it was found. Claude Code checked again on 19 November
  2026, 12:42–12:43 UTC (the arXiv API, OpenAlex, GitHub searches of issues,
  commits and repositories, the issues and recent commits of trureturing, and
  the latest updates of openai/math and astrafala/Conjectures), and found
  nothing new. Claude Code checked again on the day of the release, 20 November 2026, 01:30–01:31 UTC, in the same places, and found nothing new. No proof of either conjecture beyond multiplicity 6
  was found. The Crossref record of the 2025 journal paper could not be
  retrieved, OpenAlex does not record that the 2026 preprint cites it, so the
  citation data are incomplete, and work in progress of the authors and
  their students cannot be seen. This reports the coverage of the search,
  not a guarantee that it was complete.
- Paper 17: the question is Question 6 of I. Beaton and B. Cameron (*On the
  largest real root of the independence polynomial of a unicyclic graph*,
  Open J. Discrete Appl. Math. 5 (2022), no. 3, 30–46; Question 5.3 of
  arXiv:2006.05511, which has versions 1 and 2), who also found two
  incomparable trees of order 8 and a pair of incomparable trees at each
  order `2^(k+3)` (their Figure 16 and Theorem 16), disproving a conjecture
  of M. R. Oboudi (arXiv:1303.3222; Ars Combin. 137 (2018)). The relation
  `⪯`, its transitivity and the extremal trees are due to P. Csikvári (J.
  Graph Theory 74 (2013), Section 8), and that the independence root of
  smallest modulus is real to Csikvári (Combin. Probab. Comput. 22 (2013)).
  Codex agents searched on 20 November 2026, during the search for problems
  (04:04–04:25 UTC) and again before the statement file was frozen (from
  14:20 UTC): the arXiv, OpenAlex (one merged record for the journal paper
  and the preprint, with no citing works), Crossref (no citing works
  registered for the journal DOI), DataCite, the publication lists of both
  authors (in OpenAlex and on Cameron's web page), web search with several
  phrasings, MathDB, MathOverflow and Mathematics Stack Exchange, and GitHub
  (issues, pull requests, repositories and commits, with positive controls),
  including trureturing, vibemathing, astrafala/Conjectures, OEIS-Settled,
  openai/math, SCOPE, formal-conjectures and cmu-l3/reuF2F. MathDB lists two
  neighbouring problems from the same papers, a question on chain lengths
  (325170) and Oboudi's conjecture on starlike trees of fixed degree
  (325171), for which a ten-vertex counterexample had already been posted
  there (our agents found the same one independently; it is not claimed
  here); neither concerns antichains among trees of equal order. Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex list of citing works (still empty), and found no new related work.
  No answer to Question 6 and no construction of arbitrarily large
  antichains among trees of equal order was found. Citation databases record
  only what they index, and work in progress cannot be seen. This reports
  the coverage of the search, not a guarantee that it was complete.
- Paper 18: the question is the equality case of Theorem E(b) of D. M. Chen
  (*On the structure of permutation invariant parking*, arXiv:2311.15699v1,
  2023; only version 1 exists), whose sufficient condition E(c) and
  necessary condition E(d) differ, as his Remark 4.7 shows; Chen does not
  list the equality case among the open problems of his Section 5. The
  parking model, the reduction to one special preference and the minimally
  invariant length vectors are from D. M. Chen, P. E. Harris, J. C. Martínez
  Mori, E. J. Pabón-Cancel and G. Sargent (*Permutation invariant parking
  assortments*, Enumer. Combin. Appl. 4:1 (2024), Article S2R4;
  arXiv:2211.01063v2), whose Corollary 4.4 is essentially the gap reduction
  of the paper. Codex agents searched on 20 November 2026, during the search
  for problems (04:04–04:25 UTC) and again before the statement file was
  frozen (from 14:20 UTC): the arXiv, OpenAlex (the twelve works of Chen it
  lists; one work citing the 2023 preprint, J. Bown, P. Kagey, A. Kappler,
  M. E. Orrison and J. Thadani, *Preference-restricted parking functions*,
  arXiv:2507.11701, which studies a different question; and the 16 works it
  returns as citing the paper of 2024), Crossref and DataCite, web search
  with several phrasings, MathDB, MathOverflow and Mathematics Stack
  Exchange, the OEIS, and GitHub as for Paper 17. The repository
  cmu-l3/reuF2F, a benchmark for AI agents, contains at commit `230023d8` a
  Lean statement of the four-car Conjecture 6.1 of Chen, Harris, Martínez
  Mori, Pabón-Cancel and Sargent with an unfinished proof; MathDB 356727 is
  the same four-car question, and OEIS A355645 concerns classical parking
  functions; none of them treats the equality case of Theorem E(b).
  Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex lists of citing works, which could not be retrieved on 21 November, and found no new related work. No earlier statement of condition (iii) of Theorem 1 or of
  Theorem 2 was found. The Crossref record of Chen's preprint could not be
  retrieved, and work in progress cannot be seen. This reports the coverage
  of the search, not a guarantee that it was complete.
- Paper 19: the conjecture is Conjecture 6.5 of P. Vojtěchovský and S. Y.
  Yang (*Enumeration of racks and quandles up to isomorphism*, Math. Comp.
  88 (2019), 2523–2540; arXiv:1911.04991v1), whose enumeration relies in part
  on counts of 2-reductive racks and quandles of P. Jedlička, A. Pilitowska,
  D. Stanovský and A. Zamojska-Dzienio (J. Algebra 443 (2015)). That a rack
  is medial if and only if its displacement group is abelian is Proposition
  2.4 of A. Hulpke, D. Stanovský and P. Vojtěchovský (J. Pure Appl. Algebra
  220 (2016)); that every connected quandle of prime order is affine is due
  to P. Etingof, A. Soloviev and R. Guralnick (J. Algebra 242 (2001)), as
  stated in Theorem 9.3 of Hulpke, Stanovský and Vojtěchovský, who also give
  the isomorphism criterion for connected affine quandles; the corollaries
  of Jedlička et al. on orbit sizes concern quandles and do not give
  2-reductivity directly. Codex agents searched on 20 November 2026, during
  the search for problems (17:23–17:53 UTC) and again before the statement
  file was frozen (until 18:04 UTC): the arXiv, OpenAlex (14 works citing the
  paper), Crossref, MathDB, MathOverflow and Mathematics Stack Exchange, and
  GitHub (issues, pull requests, repositories and commits, with a positive
  control), including trureturing, vibemathing, astrafala/Conjectures,
  SCOPE, OEIS-Settled, openai/math, formal-conjectures, Epoch and
  cmu-l3/reuF2F. MathDB lists the conjecture as open (problem 344474, with
  no solution), and trureturing issue 27945 cites the same paper for a
  different question. Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex list of citing works (which names 14 of the 16 works it counts), and found no new related work. No proof of Conjecture 6.5 was found. This
  reports the coverage of the search, not a guarantee that it was complete.
- Paper 20: the conjecture is the generalized Wilf conjecture of C. Cisto,
  M. DiPasquale, G. Failla, Z. Flores, C. Peterson and R. Utano (Semigroup
  Forum 101 (2020)), and the class is the one left open in §6 of C. Cisto
  and F. Navarra (*On some classes of generalized numerical semigroups*, An.
  Ştiinţ. Univ. Ovidius Constanţa Ser. Mat. 33 (2025); arXiv:2212.12467v1),
  who also determined the minimal generators and `n(S)`. O. P. Bhardwaj, C.
  Cisto and P. Deshpande (*Structure of gaps and generalized Wilf's
  conjecture*, arXiv:2611.20086v1, November 2026) proved the case `d = 2`
  and the case `d ≥ 3` under a condition, with a single-layer bound of the
  same kind. Codex agents searched on 20 November 2026, during the search for
  problems (17:23–17:53 UTC) and again before the statement file was frozen
  (until 18:04 UTC): the arXiv, OpenAlex (4 works citing the preprint of
  2022, none citing that of 2026), Crossref, DataCite, MathDB, MathOverflow
  and Mathematics Stack Exchange, and GitHub as for Paper 19. Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex lists of citing works, and found no new related work and no new version of arXiv:2611.20086. No
  proof of the inequality for the parameters left open by Bhardwaj, Cisto
  and Deshpande was found; work in progress of these authors, who published
  their partial result five days before the search, cannot be seen. This
  reports the coverage of the search, not a guarantee that it was complete.
- Paper 21: the conjecture is Conjecture A of G. Codenotti, F. Santos and
  M. Schymura (*The covering radius and a discrete surface area for
  non-hollow simplices*, Discrete Comput. Geom. 67 (2022), 65–111;
  arXiv:1903.02866, versions 1 and 2), restated by K. Krivokuća
  (arXiv:2601.15173v1, Conjecture 4.1). The simplex is in A. M. Kasprzyk's
  thesis (University of Bath, 2006, Proposition 9.7.10, as the simplex of
  `P(1,1,1,1,2)`) and in Appendix C of T.-J. Lee (arXiv:2610.26186), who
  notes its normalized volume; Appendix B of Codenotti, Santos and Schymura
  computes covering radii of lattice simplices from the diameter of a Cayley
  digraph. Recent related work includes G. Codenotti, A. Freyer and K.
  Krivokuća (arXiv:2606.14442). Codex agents searched on 20 November 2026,
  during the search for problems (18:36–18:54 UTC) and again before the
  statement file was frozen (19:32 UTC): the arXiv (with queries for the last
  six months), bibliographic records, MathDB (the problem pages of
  Conjectures A, B and C list no solutions), GitHub (issues, pull requests,
  commits and repositories) and seven repositories of AI-assisted or formal
  mathematics, openai/math, astrafala/Conjectures and recent repositories of
  vibemathing; the final reviewer searched again. Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places; on 22 November the OpenAlex list of works citing the paper of Codenotti, Santos and Schymura, refused on 21 November (rate limit), was retrieved and contained the same ten works as before, and no new related work was found. No earlier
  statement of the covering radius of this simplex and no counterexample to
  the equality clause of Conjecture A was found. The citation search of
  OpenAlex was refused (rate limit) during the second search, and anonymous
  GitHub code search was not available. This reports the coverage of the
  search, not a guarantee that it was complete.
- Paper 22: the definitions and the context are from M. A. Ollis (*Terraces
  for small groups*, J. Combin. Math. Combin. Comput. 108 (2019);
  arXiv:1603.01496v1) and his dynamic survey (*Sequenceable groups and
  related topics*, Electron. J. Combin. DS10, version 3, 2025); Bailey's
  paper of 1984 and the papers of B. A. Anderson and E. C. Ihrig (1993) were
  not consulted and are cited after Ollis. The hill-climbing method is that
  of Ollis, building on Anderson; A. Müyesser and A. Pokrovskiy (Invent.
  Math. 240 (2025), Theorem 6.12 of arXiv:2204.09666v3) proved that every
  sufficiently large non-abelian group is sequenceable, without an explicit
  bound; a dataset of H. Yang (Zenodo 10.5281/zenodo.22785373, September
  2026) gives terraces for all non-abelian groups of orders 256 and 384, not
  for `A_7`. Codex agents searched on 20 November 2026, during the search for
  problems (from 18:39 UTC) and again before the statement file was frozen
  (19:32 UTC), as for Paper 21; the final reviewer searched again and asked
  for a further check of Yang's dataset and website before release.
  Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex lists of citing works, and found no new related work; the Zenodo dataset of Yang was unchanged (still version 1.0.0, for orders 256 and 384). No terrace, directed terrace or sequencing of `A_7` and no
  non-asymptotic theorem that covers it was found. The website with Ollis's
  search programs and the full text of the paper of Anderson and Ihrig could
  not be reached, and some search services refused or limited automated
  queries. This reports the coverage of the search, not a guarantee that it
  was complete.
- Paper 23: the question is Question 3.2 of S. Alikhani, J. I. Brown and S.
  Jahari (*On the domination polynomials of friendship graphs*, Filomat 30
  (2016), 169–178; Question 2 of §3 of arXiv:1401.2092v2). B. A. Rather (*On
  roots of domination polynomials for friendship and book graphs*,
  arXiv:2604.08998v2, 2026) proved the explicit bound `1 + √(m/log 2)` and an
  implicit bound `R_m`, and asked whether the bound is asymptotically
  optimal; the upper half of Corollary 1 follows from his implicit bound by a
  short computation, given in the paper. The formulas for domination
  polynomials of disjoint unions and joins are due to S. Alikhani and Y. H.
  Peng and appear also in T. Kotek, J. Preen, F. Simon, P. Tittmann and M.
  Trinks; the analogous result for chromatic roots of generalized theta
  graphs is due to J. I. Brown, C. Hickman, A. D. Sokal and D. G. Wagner.
  Codex agents searched on 20 November 2026, during the search for problems
  (17:23–17:53 UTC) and again before the statement file was frozen: the
  arXiv (both papers have two versions), OpenAlex (23 works citing the paper
  of Alikhani, Brown and Jahari, one citing Rather's), web search, MathDB,
  MathOverflow and Mathematics Stack Exchange, SCOPE, and GitHub as for Paper
  19 (trureturing issue 23025 concerns real domination roots of book graphs,
  a different question). Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex lists of citing works, and found no work on the largest domination roots of friendship graphs; the closest finds are still a Zenodo note on the real domination roots of book graphs and a general bound |z| ≤ n for all domination roots of graphs of order n, neither of which overlaps with the results here. No earlier sharp asymptotic for the
  largest domination roots of friendship graphs and no matching lower bound
  were found. Two OpenAlex queries were rate-limited. This reports the
  coverage of the search, not a guarantee that it was complete.
- Paper 24: the question is in Remark 5.11 of K. Gajdzica, R. Visser and M.
  Zakarczemny (*Rectangle partitions generalizing integer partitions*, Ann.
  Comb., published online 28 April 2026; arXiv:2509.20495v2). M. Shaikh
  (arXiv:2609.13305v1) proved their Conjecture 5.10 and does not address
  Remark 5.11; K. Gajdzica and M. Zakarczemny (arXiv:2608.08762 and
  arXiv:2608.22955) and C. K. Shukla (XSci Preprints, 14 November 2026)
  treat other questions on rectangle partitions. Codex agents searched on 20
  November 2026, during the search for problems (17:23–17:53 UTC) and again
  before the statement file was frozen: the arXiv, OpenAlex (4 works citing
  the preprint), web search, MathDB, MathOverflow and Mathematics
  Stack Exchange, and GitHub as for Paper 19 (a record of trureturing on
  column partitions of Li and Uncu concerns a different definition); the
  final reviewer made a spot check. Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex lists of citing works, and found no work on Remark 5.11 of the source; the closest find is still a result in the repository 1337isnot1337/solved-conjectures on a different question from a neighbouring paper (Remark 5.9 of Gajdzica and Zakarczemny, arXiv:2608.08762). No answer to the question of
  Remark 5.11 and no work on the order of `D_k(n)` were found. This reports
  the coverage of the search, not a guarantee that it was complete.
- Paper 25: the problems are Problems 2 and 3 of I. Soprunov and J.
  Soprunova (*Eventual quasi-linearity of the Minkowski length*, European J.
  Combin. 58 (2016), 107–117; arXiv:1412.4404v2), whose problem numbers and
  wording were checked in both arXiv versions (the journal text was checked
  by a Codex agent, not by the agent that wrote the paper). The tetrahedron
  `T` is one of the lattice 3-polytopes with eight lattice points enumerated
  by M. Blanco and F. Santos (Discrete Comput. Geom. 60 (2018)); `U` is an
  empty tetrahedron in the sense of G. K. White; K. Meyer, I. Soprunov and
  J. Soprunova (SIAM J. Appl. Algebra Geom. 6 (2022)) study maximal
  decompositions in 3-polytopes, and their Theorem 3.4 gives `L(2U) ≥ 3`;
  three-dimensional Minkowski lengths can be computed by the algorithm of
  Beckwith, Grimm, Soprunova and Weaver. Codex agents searched on 20 November
  2026, during the search for problems (17:23–17:53 UTC) and again before the
  statement file was frozen: the arXiv (the preprint has two versions),
  OpenAlex (8 citing works), web search with two phrasings of Problem 2, the
  authors' published code, MathDB, MathOverflow and Mathematics Stack
  Exchange, and GitHub as for Paper 19; the final reviewer read the closest
  later works. Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the works citing Meyer, Soprunov and Soprunova, their MAGMA repository and the OpenAlex list of works citing the source (which names 8 of the 9 works it counts), and found no new related work. No answer to Problems 2 or 3 was found. This
  reports the coverage of the search, not a guarantee that it was complete.
- Paper 26: Conjecture B is from B. González Merino and M. Schymura
  (Discrete Comput. Geom. 58 (2017), 663–685; arXiv:1605.00443v1, Remark
  4.9, where the second author is listed as Henze), with covering minima as
  defined by R. Kannan and L. Lovász (Ann. of Math. 128 (1988)), and
  Conjectures A, B and C are from G. Codenotti, F. Santos and M. Schymura
  (Discrete Comput. Geom. 67 (2022), 65–111; arXiv:1903.02866v2), who proved
  them in low dimensions, showed the equivalence of B with the inequality
  of A and the implication from C to that inequality, and proved C up to a
  constant factor. K. Krivokuća (arXiv:2601.15173, January 2026) proved
  weaker general bounds for Conjecture B and listed it as open; G.
  Codenotti, A. Freyer and K. Krivokuća (arXiv:2606.14442) treat related
  questions. Codex agents searched during the search for problems (18:36–18:54
  UTC on 20 November 2026) and again before the statement files were frozen,
  and the final reviewers searched again. A deeper search by a Claude Code
  agent (20 November 2026, 23:17–23:43 UTC) covered the works citing the two
  source papers and Krivokuća's paper (Semantic Scholar, scite,
  OpenCitations; 10, 16 and 1 citing works), whose arXiv full texts were
  downloaded and searched; arXiv searches for the main terms; web search;
  MathOverflow; the web pages and repositories of the authors and of
  Krivokuća, including her master's thesis; and GitHub (code, issue and
  commit search, and the trees of trureturing, openai/math,
  formal-conjectures, astrafala/Conjectures, OEIS-Settled, SCOPE and other
  repositories of AI-assisted mathematics). The repository chy4pro/automath
  listed the paper of Codenotti, Santos and Schymura as a candidate in a
  selection note of August 2026, with no further work on it in its public
  files. Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places; on 22 November the OpenAlex list of works citing the paper of Codenotti, Santos and Schymura, refused on 21 November (rate limit), was retrieved and contained the same ten works as before, the works citing González Merino and Schymura were unchanged, and no new related work was found. No earlier proof of Conjecture B for `4 ≤ i < n`, of
  Conjecture C for `d ≥ 3`, or of the d/2 bound of Conjecture A for `d ≥ 4`
  was found. The OpenAlex list of citing works (rate limit), Google Scholar
  (bot wall) and the full text of Codenotti's thesis of 2020 could not be
  retrieved; zbMATH and MathSciNet were not searched. This reports the
  coverage of the search, not a guarantee that it was complete.
- Paper 27: the problem is from M. J. Mossinghoff and C. Pinner (Michigan
  Math. J. 74 (2024), 551–569; arXiv:2108.04870v1, the only arXiv version;
  the paper cites its numbering, since the journal version could not be
  read), after the question of O. Taussky-Todd (1977) as described by C.
  Pinner and C. Smyth (Ramanujan J. 51 (2020)). C. Panraksa found the three
  elements of `Z[C_5 × C_5]` used as seeds and proved
  `S(C_5^2) ∩ 5Z = 5^8 Z` (arXiv:2608.04267v1); his papers on
  `C_7 × C_7` (arXiv:2609.09542v1) and on `C_p × C_p` for `p ≥ 7`
  (arXiv:2610.15262v1, whose Proposition 4.7 gives a structural
  obstruction at the lowest valuation) treat abelian groups. W. Bley, T.
  Hofmann and H. Johnston (Forum Math. Sigma 10 (2022)) give lattice
  isomorphism algorithms that decide membership in principle, without an
  explicit description; White (arXiv:2607.14379) treats the Davenport
  constant of the same group. Codex agents searched on 21 November 2026
  during the search for problems (01:00–01:22 UTC), again from 01:28 UTC
  before the statement of the minimum was frozen, with further searches
  for the classification at 01:39 and 01:42 UTC, and once more at
  03:28–03:31 UTC, after the statement of the classification had been
  frozen: the arXiv, OpenAlex (6 citing works of the source), Crossref,
  zbMATH, MathDB, MathOverflow and Mathematics Stack Exchange, web search,
  and GitHub (code, repository, commit, issue and pull request searches,
  the trees of 23 repositories, and the full text of 13 local checkouts,
  among them trureturing, astrafala/Conjectures, formal-conjectures and
  OEIS-Settled). The three final reviewers searched again (the arXiv,
  web search and DataCite, including the series of classifications of
  group determinants of small orders posted on Zenodo by A. Radolović,
  none of which concerns order 125). Claude Code searched again on 21 November 2026 (17:54–18:21 UTC) and on the day of the release, 22 November 2026 (05:39–05:51 UTC), in the same places, including the OpenAlex list of citing works and the Zenodo series of group-determinant classifications by Radolović (no new record since 13 September 2026), and found no new related work. No earlier determination
  of the multiples of 5 in `S(H_5)`, of its least positive multiple of 5,
  or of a prime-factor criterion of the kind in Theorem 1 for `H_5` was
  found (Panraksa gives a criterion of this kind for `C_7 × C_7`). The journal
  version of the source could not be read (access was blocked), Google
  Scholar returned nothing usable, and OpenAlex refused some queries of
  the reviewers (rate limit). This reports the coverage of the search, not
  a guarantee that it was complete.
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
  - Later, a Lean proof of the conjecture for all distinct odd primes,
    including `q = 3`, was merged in the trureturing repository
    ([pull request #19390](https://github.com/the-omega-institute/trureturing/pull/19390),
    2026-10-20); we read its description, not its Lean code.
- A389472, modulo 2: proved earlier by A. Perez Fontelles
  (astrafala/Conjectures, paper 1042, 2026-08-31) and in the trureturing
  repository. Neither of these two proofs addresses the modulo-three
  conjecture.
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
- Later work (found when we searched again on 6 November 2026): the following proofs
  appeared after version 1 of Paper 2 was released. In the trureturing repository, pull
  requests 19207 (A274479, A377100; merged 2026-10-19), 19258 (the vanishing
  part of A107099; merged 2026-10-19) and 26856 (A389472 modulo 3; merged
  2026-11-06), with Lean proofs; ProveIt (A338634, without Lean); and
  Y. Su (Zenodo 10.5281/zenodo.23520531; A338633 and A338634, without Lean). The
  paper lists them in its section on the relation to other work.

## Tool and computational resource disclosure

This work was carried out from 25 September 2026 to 22 November 2026 (UTC) in a
workflow directed by the author, using two AI coding agents:

- OpenAI Codex (desktop app; models `gpt-6-astra`, `gpt-6-sol`, `gpt-6.1-sol`,
  `gpt-6.2-astra`);
- Anthropic Claude Code (model Claude Opus 5.5; some referee agents used
  Claude Fable 5.1, which from 7 October 2026 also drafted text).

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
Version 2 of Paper 3 was produced from 27 to 29 September 2026. A Claude
Code agent wrote version 1 of its statement file, which an independent
Claude Code agent reviewed and OpenAI Codex (desktop application; models
gpt-6-astra and gpt-6-sol) audited; Codex also checked version 1 of the
paper, recomputing most of its numbers with its own programs. When Codex's
usage quota ran out, Claude Code wrote version 2 of the statement file,
which an independent Claude Code agent reviewed; on 29 September 2026 Claude
Code agents wrote the Lean proofs, working in parallel, and Claude Code ran
the checks. Independent Claude Code agents reviewed the Lean package and
refereed a draft of the paper. Codex has not reviewed version 2 of the paper,
version 2 of the statement file or the Lean proofs. The author
has read version 2 of Paper 3 and, using a side-by-side table, compared its
Lean statements with the results in the paper.

The material new in version 1.4.0, namely Theorems 4 and 5 of Paper 1
(version 1.4) and Papers 4, 5 and 6, was found, formalized in Lean (to the
extent stated above) and drafted by Claude Code agents (model Claude Opus
5.5). The agents also selected the problems of Papers 4, 5 and 6 and carried
out the literature searches described in the papers. Independent Claude
referee agents checked each paper; for Paper 1, two referee agents checked
earlier write-ups of the proofs of Theorems 4 and 5, and one of them wrote
the second certification program for Theorem 5. The author has also read the
new material of version 1.4.0 and, using the same kind of side-by-side
table, compared its Lean statements with the results in the papers. In
version 1.5.0 the
extension of Theorem 5 to exponents 5 to 8 was checked by a third independent
Claude referee agent, which reran both certification programs and certified
the same inequalities with its own program.
The author has also read the changes of version 1.5. Version 2 of Paper 1
withdraws this extension and Proposition 15 (see below).

Version 2 of Paper 5 was produced from 27 September to 7 October 2026. On
27 September a Claude Code agent (model Claude Opus 5.5) wrote its
statement file, which an independent Claude Code agent reviewed, and OpenAI
Codex (desktop application; model gpt-6-astra) checked version 1 of the
paper independently: it re-derived the proofs, checked the certificates with
programs of its own, and found the error in the definition of `top(x)` and
`bot(x)` that version 2 corrects. From 29 September to 1 October 2026 Codex
(its main session used gpt-6-astra and, from 30 September, gpt-6.1-sol)
wrote the Lean proofs of the 33 statements, reusing for Lemmas 4.3 and 4.4 a
copy of the Lean code of version 1; each group of proofs was accepted
after two builds from empty directories and a review of the evidence by a
Codex agent that had not written it. On 1 October Codex checked a draft of
version 2 paragraph by paragraph against the formal statements, wrote the
three supplementary statement files, which Codex agents that had not written
them reviewed before they were frozen, and proved their statements. On
6 October Codex (model gpt-6-astra) built and checked the assembled Lean
package in two new empty directories, and a Codex agent that had written none
of the proofs reviewed the evidence. Claude Code (model Claude Opus 5.5) drafted the text of
version 2, and an independent Claude Code agent (model Claude Fable 5.1),
which had written neither the paper nor any Lean file, refereed the draft on
2 October. The author has read version 2 of Paper 5 and, using a
side-by-side table, compared its Lean statements with the results in the
paper.

Version 2 of Paper 6 was produced from 27 September to 9 October 2026. On
27 September 2026 a Claude Code agent (model Claude Opus 5.5) wrote a first
statement file, which an independent Claude Code agent reviewed, and OpenAI
Codex (desktop application; its main session used the model gpt-6-astra)
checked version 1 of the paper independently: it found that the determination of the weight spectrum
rested on the theorem of Kasami, Tokura and Azumi, which we had not verified,
that (P2) lacked the hypothesis `r ≥ 1`, and that the example after
Proposition D was stated without its membership in RM(6,12); the same day we
read the note of Lou and Wang. On 6 October 2026 Codex wrote the present
statement file, following the author's decision of
27 September that claims which cannot be formalized completely are deleted;
a Codex agent that had not written it reviewed it before it was frozen. On
7 October the author had one statement deleted (the five numbers of the
enumeration of version 1, whose kernel certificates would have taken about a
week), and the file was reviewed and frozen again. From 6 to 8 October 2026
Codex wrote the Lean proofs (the retained records of its main session show
the model gpt-6-astra); each group of proofs was
accepted after two builds from empty directories and a review of the
evidence by a Codex agent that had not written it, and on 8 October the
assembled package was built and checked in two new empty directories, twice
(in an isolated layout and in the layout of this repository), and reviewed
in the same way. On 8 October Codex also checked the draft of version 2
paragraph by paragraph against the statement files, the file of checks and
the package receipts, and on 9 October the revised passages; the text was
revised accordingly. Claude Code drafted and revised the text of version 2
(models Claude Opus 5.5 and, from 7 October, Claude Fable 5.1), and an
independent Claude Code agent (model Claude Fable 5.1), which had written
neither the paper nor any Lean file, refereed the draft on 7 October 2026,
recomputing the finite checks and the 7901 codewords with programs of its
own. The author has read version 2 of Paper 6 and, using a side-by-side
table, compared its Lean statements with the results in the paper.

Paper 7 (version 1.6.0) was selected, proved and drafted by Claude Code
agents (model Claude Opus 5.5). An independent Claude referee agent refereed
the proofs line by line, contributed the bound of Lemma 4.4 and reran the
searches with a program it wrote from scratch (implementation C); a second
one later checked Lemma 4.2, Corollary 4.3 and the later program versions
and recomputed the cases with its own program (implementation D). The author
has also read Paper 7.

Version 2 of Paper 7 (version 1.14.0): on 27 September 2026 a Claude Code
agent (model Claude Opus 5.5) wrote a first statement file, and an independent
Claude Code agent reviewed it. OpenAI Codex (its main session used the model
gpt-6-astra) wrote the present statement files, which a Codex agent that had
not written them reviewed before they were frozen on 8 October 2026 and again
on 18 October 2026, and from 8 to 18 October it wrote the Lean proofs of 57
statements; each group of proofs was accepted after two builds from empty
directories and a review of the evidence by a Codex agent that had not
written it. Until 3 November Codex also wrote part of the proof of the last
statement. On 3 and 4 November 2026 Claude Code (model Claude Opus 5.5) wrote
the rest of that proof, of which 190 modules were generated by a script, and
the final package, and on 4 and 5 November built and checked the package and
the whole project on the author's Windows computer. Claude Code (model Claude Opus 5.5) compared
version 1 claim by claim with the statement files and drafted version 2. An
independent Claude Code agent (model Claude Fable 5.1), which had written
none of the files, reviewed the draft against the statement files and the
evidence of the first build on 4 November 2026. On 5 November 2026 a second independent Claude Code
agent (model Claude Fable 5.1), which had written none of the files, compared
the final package with the frozen statements, read the proof of
`LegacyMomentCounts` for steps that avoid the kernel, recounted the evidence of
the three builds and reviewed the paper; it did not run Lean. The corrections of
both reviews were applied.
The author has read version 2 of Paper 7, but did not check its proofs and did
not compare its Lean statements with the paper.

Version 2 of Paper 2 (version 1.15.0): on 27 September 2026 a Claude Code agent
(model Claude Opus 5.5) wrote the statements from version 1.2.1, an independent
Claude Code agent reviewed them, and Codex reviewed them on the same day. On
5 November 2026 OpenAI Codex (its main session used the model gpt-6.1-sol)
ported them to Lean 4.34.1 and changed one statement, a Codex agent that had not
written the files reviewed them, and they were frozen; on 5 and 6 November Codex
wrote all the proofs, in ten groups, each accepted after two builds from empty
directories and a review by a Codex agent that had not written it. Claude Code
(model Claude Opus 5.5) compared version 1.2.1 claim by claim with the statements,
drafted version 2, wrote `Check.lean`, integrated the package into the project
and on 6 and 7 November rebuilt the whole project on the author's Windows computer. Claude Code agents searched the
literature again on 6 November 2026. An independent Claude Code agent (model Claude Fable 5.1), which had written none
of the files, reviewed a draft of the paper against the statements and the
evidence on 6 November 2026, and before the release a second such agent (same
model) reviewed the paper, the Lean package and the receipts; neither ran Lean.
The corrections of both reviews were applied.
The author has read version 2 of Paper 2, but did not check its proofs and did
not compare its Lean statements with the paper.

Version 2 of Paper 1 (version 1.16.0): on 27 September 2026 a Claude Code agent
(model Claude Opus 5.5) wrote a first statement file from version 1.5, and an
independent Claude Code agent (same model) reviewed it. OpenAI Codex (desktop
application) reviewed its second version, which was frozen on 27 September,
and on 27 and 28 September wrote the Lean proofs of 29 of its 33 statements; its
session records name the model gpt-6-astra for this work. On 6 November 2026 the
author decided to narrow the paper to `min(a, b) ≤ 2` rather than formalize the
certificates. On 6 and 7 November Codex (model gpt-6.1-sol in its session
records) wrote the statement files of version 2, which Codex agents that had not
written them reviewed before they were frozen on 7 November; moved the earlier
proofs into the package; proved the remaining statements, including
`Proposition31` and `Theorem5MinTwo`; and built the package twice from empty
directories. Two Codex agents that had not written the package reviewed the
build evidence and the mathematics; they had taken part in read-only reviews of
earlier stages, so these are not reviews by another model family. The older
modules `lean/Research/ICG*.lean` go back to the Lean formalization of the
earlier versions, written by Claude Code agents according to the disclosure of
those versions. Claude Code (model Claude Opus 5.5) compared version 1.5
claim by claim with the statements, drafted version 2, integrated the package
into the project and on 7 November rebuilt the whole project on the author's
Windows computer. Claude Code searched the literature again on 7 November 2026.
An independent Claude Code agent (model Claude Fable 5.1), which had written
none of the files, reviewed a draft of the paper against the statements and the
evidence on 7 November 2026, and before the release a second such agent (same
model) reviewed the paper, the Lean package and the receipts; neither ran Lean.
The corrections of both reviews were applied.
The author has read version 2 of Paper 1 and, using a side-by-side table,
compared the statements of the Lean theorems with the results stated there.

Version 3 of Paper 1 (version 1.17.0) was produced on 8 November 2026. OpenAI
Codex (desktop application; its session records name the model gpt-6.1-sol)
found the proofs of the conditions of Proposition 31 for the prime 3, wrote the
statement files and the Lean proofs of version 3, and built the package twice
from empty directories. A Codex agent that had not written the statement files
reviewed them before they were frozen. After both builds had ended, a Codex
agent that had written no statement, proof or build script of version 3
reviewed the sources, the logs of both builds and the mathematics of the 45 new
modules, and approved the package (20:58:51 UTC); it did not run Lean. These
are reviews by Codex agents, not by another model family. Codex also searched
the literature (17:17 UTC). Claude Code (model Claude Opus 5.5) drafted the
text of version 3, including the written proofs of Section 13, from the Lean
proofs and Codex's notes on them, rebuilt the whole Lean project of the
repository on the author's Windows computer (8 November 2026, 21:09 UTC, to
9 November, 08:20 UTC), and searched
the literature again (8 November, 21:07–21:22 UTC, and 9 November, 08:24–08:35
UTC). An independent Claude Code agent (model
Claude Fable 5.1), which had written none of the files, reviewed a draft of the
paper against the statements and the evidence on 8 November 2026; it did not
run Lean. Five of its seven minor remarks were applied and one needed no
change; the remaining one asked for a further literature check if the release
came after the arXiv announcement of 9 November 2026, and that check was done. Before
the release a second such agent (same model) reviewed the paper, the Lean
package and the receipts on 9 November 2026; it did not run Lean, and its
corrections were applied. The author has read version 3 of Paper 1 and,
using a side-by-side table, compared the statements of its new Lean theorems
with the results stated in it.

Paper 8 (version 1.7.0) was selected, proved, partly formalized in Lean and
drafted by Claude Code agents (model Claude Opus 5.5); an adversarial
checking agent and two independent Claude referee agents checked the proof,
and the referees recomputed the finite part with programs they wrote
themselves. The first referee agent also checked the correspondence between
the Lean statements and the paper. The author has also read Paper 8.

Version 2 of Paper 8 was produced from 27 to 29 September 2026. A Claude
Code agent wrote version 1 of its statement file, which an independent
Claude Code agent reviewed; OpenAI Codex (desktop application; models
gpt-6-astra and gpt-6-sol) checked version 1 of the paper, recomputing the
finite region, the exceptions and the sharpness examples with its own
programs. When Codex's usage quota ran out, Claude Code wrote version 2 of
the statement file, which an independent Claude Code agent reviewed; on
29 September 2026 nine Claude Code agents wrote the Lean proofs, working in
parallel, and Claude Code ran the checks. Independent Claude Code agents
reviewed the Lean package and refereed a draft of the paper (the referee
used the model Claude Fable 5.1). Later on 29 September, after Claude's usage
credits ran out, OpenAI Codex reviewed version 2 of the paper and statement
file, examined the Lean proof routes, and checked the saved validation
evidence against the current sources. Codex did not rerun the Lean checks. The author has
read version 2 of Paper 8 and, using a side-by-side table, compared its Lean
statements with the results in the paper.

Paper 9 (version 1.8.0) was selected, found and drafted by Claude Code
agents (model Claude Opus 5.5), which checked the examples with two
separately written programs and wrote the statement file; an independent
Claude agent reviewed version 1 of the statement file and recomputed the
examples. OpenAI Codex (desktop app) then reviewed the mathematics and
version 2 of the statement file, recomputed the examples with its own
program, wrote and froze, after an independent review, the two
supplementary statements, wrote all the Lean proofs and ran their
acceptance checks, and reviewed the paper. The author has also read
Paper 9 and, using the same kind of side-by-side table, compared its Lean
statements with the results in the paper.

Version 2 of Paper 4 (version 1.9.0) was prepared from 27 to 29 September
2026. A Claude Code agent (model Claude Opus 5.5) wrote the statement file,
and an independent Claude agent reviewed version 1 of it and recomputed the
enumeration with its own programs. OpenAI Codex (desktop application;
models gpt-6-astra and gpt-6-sol) then checked version 1 of the paper
independently, recomputing the enumeration with its own program, reviewed
version 2 of the statement file and froze it, and wrote the Lean proofs of 46 of the 50
statements, 44 of which it also checked. When Codex's usage quota ran out,
Claude Code compiled and checked Codex's proofs of the two minimality
statements, wrote and checked the proofs of the other four statements, and
assembled and checked the Lean package; independent Claude agents reviewed
these six proofs and refereed a draft of version 2. Claude Code drafted the
corrections. The author has also read version 2 of Paper 4 and, using the
same kind of side-by-side table, compared its Lean statements with the
results in the paper.

Paper 10 (version 1.9.0) was produced from 27 to 29 September 2026 by Claude
Code agents (model Claude Opus 5.5), which selected the question, found the
proof, checked it with two separately written programs for small
parameters, wrote the statement file, carried out the main literature
search and drafted the text. An independent Claude Code agent reviewed
version 1 of the statement file. OpenAI Codex (desktop application; models
gpt-6-astra and gpt-6-sol) checked the mathematics independently,
recomputing the embeddings with its own program, reviewed version 2 of the
statement file and froze it. When Codex's usage quota ran out, Claude Code
wrote the Lean proofs and ran the checks; an independent Claude Code agent
reviewed the proofs, and another refereed a draft of the paper.
The author has also read Paper 10 and, using the same kind of side-by-side
table, compared its Lean statements with the results in the paper.

Version 2 of Paper 10 (version 1.19.0) was produced on 9 and 10 November
2026. A Claude Code agent (model Claude Opus 5.5) searched the literature for
Problems 5.2 and 5.3. OpenAI Codex (desktop application; model gpt-6.1-sol)
chose the approach, wrote the second statement file and the file of internal
statements, which a Codex agent that had not written them reviewed before they
were frozen, then wrote the proof of Theorem 3 and the Lean proofs and ran the
two builds; a Codex agent that had not written the proofs reviewed the result.
Claude Code (model Claude Opus 5.5) wrote Section 4 of the paper from Codex's
notes and the Lean files and drafted the other changes. An independent Claude
Code agent (model Claude Fable 5.1), which had written none of the files,
reviewed the draft against the Lean files, Codex's records and the source on
10 November 2026, without running Lean; it found no error in the mathematics,
and its corrections were applied. The author has read version 2 of Paper 10 and, using a side-by-side table,
compared the statements of its new Lean theorems with Theorem 3.

Paper 11 (version 1.18.0) was produced on 9 November 2026 by agents of
Anthropic Claude Code with the model Claude Opus 5.5, unless stated otherwise;
the author approved the work and chose to publish it as a short note. A Claude
Code agent scouting for open problems found the question, noticed that the
family `G_m` answers it, and checked this numerically and symbolically.
Another Claude Code agent searched the literature (22:49–23:17 UTC) and found
the lemma of Conde, Dratman and Grippo and the derivation of Remark 1. Claude
Code wrote the statement file, the Lean proofs and the text, and ran the two
builds of the package. An independent Claude Code agent (model Claude Fable
5.1), which had written none of the files, reviewed the statement file and
its tests against the question of the survey, approved them with three minor
suggestions (a comment and three more tests), which were applied, and
compiled them; the statement file was then frozen (22:56 UTC). Before the
release a second such agent (same model) reviewed the paper, the Lean files
and the records of the builds; it did not run Lean, and its seven minor
corrections were applied. OpenAI Codex was not involved in Paper 11.
The author has read Paper 11 and, using the same kind of side-by-side table,
compared its Lean statement with the theorem in the paper.

Paper 12 (version 1.20.0) was produced on 12 and 13 November 2026. Scouting agents
of Claude Code (model Claude Opus 5.5) proposed the question (on 30 September
and again on 12 November 2026), and Claude Code selected it and assigned it to
OpenAI Codex (model GPT-6.1 Sol), at
the author's request that the mathematics go to Codex. Codex agents found the
example by a computer search over a family of 4-dimensional algebras over
`F_5`, `F_7` and `F_11`, wrote the statement file, the proofs and the Lean
files, and built the package on the author's Windows computer. A Codex agent
that had written none of the files reviewed the statement file before it was
frozen, and another one gave the final review of the mathematics, the Lean
files and the records of the builds, recomputing the example independently.
Claude Code recomputed the example by an independent program, searched the
literature, rebuilt the whole Lean project and wrote the paper. An independent
Claude Code agent (model Claude Opus 5.5; Claude Fable 5.1 was not available
because its usage limit had been reached), which had written none of the
files, reviewed the paper and the release before publication; its corrections
were applied. The author has read Paper 12 and, using the same kind of
side-by-side table, compared its Lean statement with Theorem 1 of the paper.

Paper 13 (version 1.21.0) was produced from 13 to 17 November 2026. Scouting
agents of Claude Code (model Claude Opus 5.5) proposed the question; the
author chose it, and Claude Code assigned it to OpenAI Codex (model GPT-6.1
Sol). Codex agents found the proofs, wrote the statement files, the
mathematical manuscripts and the Lean files, and built the packages on the
author's Windows computer. For each `k`, a Codex agent that had not written
the statement reviewed it before it was frozen, and after the builds another
Codex agent that was not among the recorded authors of the proofs gave the
final review. These
reviews did not each read every file. For `k = 5` the final reviewer read 44
of the 120 files itself and relied for the others on a sub-agent it started
(27 files) and on its own earlier review for `k = 4` (49 files), for `k = 6` the final reviewer read the main
files (249 lines) and relied for the others on a chain of earlier reviews, and
for `k = 7` the final reviewer read 16 main files in full, three earlier
reviewers read 80 files each, and the records do not identify the authors of
40 of the 240 files, so that the independence of the final reviewer from those
authors is not documented. Some agents served as reviewers for more than one
`k`. All reviewers are agents of the same model family; there was no
cross-model or human review of the proofs. The author decided to publish the
cases `k = 4, 5, 6, 7` while Codex continued to work on the general case.
Claude Code searched the literature, wrote the paper from Codex's manuscripts
and the Lean files, and rebuilt the whole Lean project. An independent Claude
Code agent (model Claude Opus 5.5), which had written none of the files,
reviewed the paper and the release before publication; its corrections were
applied. The author has read Paper 13 and, using the same kind of
side-by-side table, compared its Lean statements with Theorem 2 of the paper.

Version 2 of Paper 13 (version 1.22.0) was produced from 14 to 18
November 2026. Codex agents found the proof for all `k`, wrote its
mathematical manuscripts and the Lean files (717 files, of which 269 are new in
the repository) and built them in two new empty directories on the author's
Mac (17 November 2026, 04:08–07:14 UTC). The statement `Question2` had been
reviewed and frozen with `Challenge.lean` on 13 November. After the checks, an
independent Claude Code agent (model Claude Opus 5.5) that had written none of
the files gave the final review of the formal proof: it reread the raw logs and
the source hashes, read the statement file, the main proof files, Codex's
written proof of the minimum-degree step in full and the parts of its written
proof of the long-cycle step that derive it from Theorem 3.1 of Gao, Huo, Liu
and Ma, and approved, with 3 minor remarks (that `K_{k+1}` attains the bound
is formalized only for `k ≤ 7`; stale comments in two files; its own reading
did not cover the deeper Lean lemmas on Gao, Huo, Liu and Ma and on Fan's
theorem, nor the deeper counting lemmas, which rest on the Lean check). Its
model family differs from Codex's; the reviews within Codex were by agents of
the same model family. Claude Code searched the
literature again, wrote version 2 of the paper from Codex's manuscripts and
the Lean files, and rebuilt the whole Lean project. A further independent
Claude Code agent (model Claude Opus 5.5), which had written none of the files,
reviewed the paper, and another reviewed the release (the README, the
certificates, the receipts and the release notes; it reran the audit of the
logs of the rebuild, but not Lean); their corrections were applied. The author
has read version 2 of Paper 13 and, using the same kind of side-by-side table,
compared its Lean statements with Theorem 2 of the paper.

Papers 14 and 15 (version 1.23.0) were produced from 17 to 19 November 2026.
The author asked for a search for open problems with the newest Codex model,
and Claude Code passed this request to OpenAI Codex (model GPT-6.2-Astra,
reasoning level ultra). Between 19:34 and 20:23 UTC on 17 November, Codex
screened 45 problems and sub-questions from the recent literature, wrote proof
sketches for three of them and proposed them; the author chose two of them,
the questions of Papers 14 and 15. From 23:49 UTC on 17 November, Codex agents
(same model) checked the reading of the sources, searched for prior work,
wrote the statement files, the written proofs and the Lean files, and checked
the packages in two new empty directories on the author's Mac; the checks
ended at 00:32 UTC on 18 November. For each paper one Codex agent, which wrote
neither the statements nor the proofs, checked the reading of the source and
then reviewed the statement files before they were frozen; these checks were
done by a single agent and are not independent of each other. After the
checks, independent Claude Code agents (model Claude Opus 5.5), which had
written none of the files, gave the final reviews, one for each paper; their
model family differs from Codex's. The reviewer of Paper 14 read the preprint
itself and the journal version in an archived copy (it could not open the
publisher's page), the statement files, the check files and the main proof
files, read the receipts and the raw logs, recomputed the parameters of the
examples with its own programs, and did not read `OrbitStructure.lean` and
`FiberAutomorphisms.lean` line by line; it approved the formal results with
five minor remarks on wording and attribution, which were applied. The
reviewer of Paper 15 read the source itself, compared the statement file with
it, read the written proof, the main proof files and the raw logs, checked the
formula by exhaustive search on small boxes, and did not read every Lean
module line by line; it approved the formal result unchanged and required
changes to the attribution, in particular adding the paper of Simmons and the
conjecture of Jiang, which the earlier searches had missed or understated;
these changes were applied. Claude Code checked the cited passages of the
sources, searched the literature again, wrote both papers from Codex's
manuscripts and the Lean files, moved the Lean files into the repository
(changing only their `import` lines), compiled the repository versions again
and checked them with `leanchecker` on the author's Mac, and rebuilt the whole
Lean project. An independent Claude Code agent (model Claude Opus 5.5), which had written none of the files, reviewed both papers, and another reviewed the release (the README, the certificates, the receipts and the release notes); their corrections were applied. The author has read Papers 14 and 15 and, using the same kind of
side-by-side table, compared their Lean statements with the theorems of the
papers.

Paper 16 (version 1.24.0) was produced from 18 to 20 November 2026. The
author asked for a search for substantial open problems, and Claude Code
passed this request to OpenAI Codex (model GPT-6.2-Astra, reasoning level
ultra). Between 19:22 and 19:50 UTC on 18 November, Codex screened 50
problems from the literature, wrote proof sketches for three of them, had
the proofs for the question of Paper 16 read by two other Codex agents (same
model) and checked its statements by exact computation for all 1249
numerical semigroups other than `ℕ` with Frobenius number at most 17; the
author chose two of the three problems, the question of Paper 16 and a
question on two-dimensional subtraction games, which the author later set
aside (see ATTEMPTS.md). From 23:38 UTC on 18 November, Codex agents (same
model) checked the reading of the sources, searched again for prior work,
wrote the statement file, the written proof and the Lean files, and checked
the package in two new empty directories on the author's Mac; the checks
ended at 23:59 UTC. One Codex agent, which had not taken part in the search
for problems and had not written the statement file, checked the reading of
the sources and then reviewed the statement file before it was frozen;
after the freeze, this agent also wrote four of the proof files
(`AlgebraCore.lean`, `AlgebraSwap.lean`, `Algebra.lean` and
`Interval.lean`); the reading of the sources and the review of the
statement file were done by this single agent and are not independent of
each other. According to the session records, the proof
files were written after the freeze by several Codex agents working in
parallel; their compilation logs cover 23:49–23:55 UTC, and the written
proof they follow had been prepared before, in the search for problems.
After the checks, an independent Claude Code agent (model Claude Opus 5.5),
which had written none of the files, gave the final review; its model
family differs from Codex's. It read the sources itself, compared the
statement file with them, read the written proof, every Lean module and the
raw logs, verified the example of Remark 1 by hand, and compiled the 12
files again in a new directory, with warnings treated as errors, replaying
every module with `leanchecker`; it approved the formal result with six
minor remarks on the written account, which were applied. Claude Code
checked the cited passages of the sources, searched the literature again,
wrote the paper from Codex's manuscript and the Lean files, moved the Lean
files into the repository (changing only their `import` lines), compiled
the repository versions again and checked them with `leanchecker` on the
author's Mac, and rebuilt the whole Lean project. An independent Claude Code agent (model Claude Opus 5.5), which had written none of the files, reviewed the paper, and another reviewed the release (the README, the certificates, the receipts and the release notes); their corrections were applied. The author has
read Paper 16 and, using a side-by-side table, compared its Lean statements
with Theorems 1 and 2 and Corollary 1 of the paper.

Papers 17 and 18 (version 1.25.0) were produced from 19 to 22 November 2026.
The author asked for a further search for open problems, and Claude Code
passed this request to OpenAI Codex (model GPT-6.2-Astra, reasoning level
ultra) on 19 November at 17:58 UTC. Codex's records of the search are dated
20 November, 04:04–04:25 UTC: it screened 42 problems and wrote proofs or
proof attempts for three groups of candidates. For the question of Paper 17
it checked the construction by exact computation at both test points for
every order from 11 to 88, and another Codex agent (same model) that had not
taken part in it recomputed the gadget polynomials and both test values by
enumerating vertex subsets; for the question of Paper 18 its proofs covered
both theorems, other Codex agents (same model) read them, and it compared
Theorem 1 with a simulation of the parking rule for all 37,440 length
vectors with 2 to 5 cars of lengths at most 8. The third group, on the
parity of the stable exceptional sets for sums of positive powers, was
dropped because the same target had been registered publicly before (see
ATTEMPTS.md). The author chose the problems of Papers 17 and 18. From 14:20
UTC on 20 November, Codex agents (same model) checked the reading of the
sources, searched again for prior work, wrote the statement files, the
written proofs and the Lean files, and checked the packages in two new empty
directories on the author's Mac; the checks ended at 14:44 UTC. For each
paper one Codex agent, which had not worked on that problem in the search
for problems and had written neither the statement file nor the proofs,
checked the reading of the source and then reviewed the statement file
before it was frozen; for each paper these two checks were done by a single
agent and are not independent of each other. According to the file times
and the development logs, the proof files of Paper 17 were created after the
freeze and compiled between 14:27 and 14:33 UTC. According to the session
records, the statement file and the proof files of Paper 18 were written
between 14:23 and 14:34 UTC by the main Codex agent and by the Codex agent
that had worked on this problem in the search, and the development logs
record no compilation of a proof file before the freeze (14:25:56 UTC). Both
formalizations follow written proofs prepared in the search for problems.
During development, Codex also compiled the files of both papers on the
author's Windows computer (20 November 2026, 14:32–14:41 UTC); these runs
are not counted among the checks. After the checks, independent Claude Code
agents (model Claude Opus 5.5), which had written none of the files, gave
the final reviews, one for each paper, from 17:16 UTC; their model family
differs from Codex's. Each read the source itself (the reviewer of Paper 17
the journal version and arXiv version 2), compared the statement file with
it, read the written proof, the proof files and the raw logs, and compiled
the files again in a new directory, with warnings treated as errors,
replaying every module with `leanchecker`. The reviewer of Paper 17
recomputed the polynomials, the test values and the largest roots in
Python; the reviewer of Paper 18 compared a computable copy of the statement
file's parking model with its own simulation of Chen's rule and checked both
theorems against the simulation. Both approved the formal results, each with
five minor remarks on the written account, which were applied (the reviewer
of Paper 18 added a sixth, on contacting the author of the source). The
reviewer of Paper 18 asked that the public text say that the paper closes
the gap between Chen's conditions E(c) and E(d), not that it solves an open
problem of Chen. Claude Code checked the cited passages of the sources,
searched the literature again, wrote both papers from Codex's manuscripts
and the Lean files, moved the Lean files into the repository (changing only
their `import` lines), compiled the repository versions again and checked
them with `leanchecker` on the author's Mac, and rebuilt the whole Lean
project.

Papers 19 and 20 (version 1.25.0) were produced from 20 to 22 November 2026. The author asked for a further search for substantial open
problems, and Claude Code passed this request to OpenAI Codex (model
GPT-6.2-Astra, reasoning level ultra) at 17:23 UTC on 20 November. Between
17:23 and 17:53 UTC Codex recorded 111 problems from the literature and wrote
complete proofs for the five top-ranked candidates, each read by another
Codex agent (same model) that had not taken part in it; for the question of
Paper 20 it also checked the inequality by exact computation for 6,204
parameter triples. While the search was still running, the author asked that
the five most important candidates be formalized at once, without waiting
for the author's choice, and Claude Code passed this request to Codex at
17:48 UTC; at 18:00 UTC Codex ranked the candidates, and the questions of
Papers 19 and 20 were among the five; the other three are those of Papers
23, 24 and 25, described below. From 18:00 UTC, Codex agents (same model) checked
the reading of the sources, searched again for prior work, wrote the
statement files, the written proofs and the Lean files, and checked the
packages in two new empty directories on the author's Mac (18:16–18:25 UTC).
For each paper the reading of the sources was checked by a Codex agent that
had taken part neither in the proof nor in drafting the statement, and the
statement file was reviewed before it was frozen by a Codex agent that had
written neither the proofs nor the statement; both statement files were
frozen at 18:04:44 UTC. According to the file times and the development
logs, the proof files were created after the freeze and compiled between
18:05 and 18:18 UTC; they follow written proofs prepared in the search for
problems. After the checks, independent Claude Code agents (model Claude
Opus 5.5), which had written none of the files, gave the final reviews, one
for each paper, from 18:28 UTC; their model family differs from Codex's.
Each read the sources itself, compared the statement file with them, read
the written proof, the proof files and the raw logs, and compiled the files
again in a new directory, with warnings treated as errors, replaying every
module with `leanchecker`. The reviewer of Paper 19 recomputed by brute force
all racks and quandles of order at most 5 up to isomorphism, reproducing the
corresponding entries of the tables of Vojtěchovský and Yang; the reviewer
of Paper 20 checked the invariants by enumeration and the inequality on
18,096 parameter triples in Python. Both approved the formal results, each
with five minor remarks on the written account, which were applied; the
reviewer of Paper 20 asked in particular that the known cases (`a = 2`,
`d ≤ 2`, and Theorem 5.6 of Bhardwaj, Cisto and Deshpande) be credited and
the novelty be limited to the remaining parameters. Claude Code checked the
cited passages of the sources, searched the literature again, wrote both
papers from Codex's manuscripts and the Lean files, moved the Lean files
into the repository (changing only their `import` lines), compiled the
repository versions again and checked them with `leanchecker` on the
author's Mac, and rebuilt the whole Lean project.

Papers 21 and 22 (version 1.25.0) were produced from 20 to 22 November 2026. The author asked for a search for hard and substantial open
problems; Claude Code wrote this request for Codex at about 18:04 UTC, and
from about 18:36 UTC it was carried out in a Codex session separate from the
main one (model GPT-6.2-Astra, reasoning level ultra), in which Codex
screened 78 candidate problems by 18:54 UTC and prepared detailed notes on
eight of them. The example of Paper 21 was found and written up in this
search, checked by exact computation, and read by another Codex agent (same
model) of a parallel lane of the search, which gave an independent written
proof of the upper bound. The terrace of Paper 22 was found in this search
by a hill-climbing program written by Codex (the witness file is dated 18:38
UTC) and checked with two separately written Python programs. After reading
the report, the author chose these two problems. In a second separate Codex
session, from 19:29 UTC, Codex agents (same model) checked the reading of
the sources, searched again for prior work, wrote the statement files, the
written proofs, the Lean files and, for Paper 22, a deterministic encoder
that writes the terrace into `Data.lean`, and checked the packages in two new
empty directories on the author's Mac (19:35–19:41 UTC). For Paper 22, one
newly started Codex agent, which had taken no part in finding the terrace and
had written neither the statement nor the proofs, checked the reading of the
sources and reviewed the statement file before it was frozen (19:32:16 UTC);
the proof files were compiled between 19:32 and 19:36 UTC, after the freeze.
For Paper 21, the statement file went through two versions, as described in
the section on Paper 21 above: version 1 was approved, before it had been
compiled, by a Codex agent that had written neither the statement nor any
proof and had also checked the reading of the source; it failed to compile
because a notation scope was not opened; version 2, which differs only in
that line, was approved by a second Codex agent and frozen at 19:33:34 UTC.
Two proof files were created between the first approval and the freeze, one
of them (`Residues.lean`, which uses no definition of the statement file) in
its final form; no proof file was compiled before the freeze. A rule was
recorded for later tasks that a statement file must compile without
diagnostics before it is approved. Both formalizations follow proofs or
certificates prepared in the search for problems. After the checks,
independent Claude Code agents (model Claude Opus 5.5), which had written
none of the files and had taken no part in the search, gave the final
reviews, one for each paper, from 19:42 UTC; their model family differs from
Codex's. Each read the sources itself, compared the statement file with
them, read the written proof, the proof files and the raw logs, and compiled
the files again in a new directory, replaying every module with
`leanchecker`. The reviewer of Paper 21 also read the freeze records,
diffed the two versions of the statement file and judged the difference
immaterial, recomputed the lattice points, the facet normals and the
determinant in Python and checked the covering radius numerically; the
reviewer of Paper 22 checked the terrace in Python from `Data.lean` and
against Codex's witness file. Both approved the formal results: the reviewer
of Paper 21 with four minor remarks on the written account, the reviewer of
Paper 22 with six (five on the written account and one asking for a further
priority check before release); the remarks on the written account were
applied. The reviewer of Paper 22 asked in particular that the paper say
that the terrace is not directed and present it as a further verified case
of Bailey's conjecture as well as the `A_7` case of the reduction of
Anderson and Ihrig. Claude Code
checked the cited passages of the sources, repeated the finite computations
of Paper 21 and decoded the terrace of Paper 22 with its own Python
programs, searched the literature again, wrote both papers from Codex's
manuscripts and the Lean files, moved the Lean files into the repository
(changing only their `import` lines), compiled the repository versions again
and checked them with `leanchecker` on the author's Mac, and rebuilt the
whole Lean project.

Papers 23, 24 and 25 (version 1.25.0) were produced from 20 to 22 November 2026. They come from the same search for problems (17:23–17:53 UTC on 20
November) and the same request to formalize the five most important
candidates at once as Papers 19 and 20. In the search, Codex checked the
leading term of Paper 23 by exact computation on all 1,099 labelled graphs
with at most 5 vertices and certified roots in small discs for three
friendship graphs, compared the two-row criterion of Paper 24 with an
enumeration of tilings for 4308 count vectors, and checked the finite facts
of Paper 25 by exact computation; each written proof was read by another
Codex agent (same model) that had not taken part in it. From 18:00 UTC,
Codex agents (same model) checked the reading of the sources, searched again
for prior work, wrote the statement files, the written proofs and the Lean
files, and checked the packages in two new empty directories on the author's
Mac (18:24–18:42 UTC). For Paper 23, one Codex agent that had taken part
neither in the proof nor in drafting the statement checked the reading of
the source and reviewed the statement file; for Papers 24 and 25 the reading
of the source was checked by a Codex agent that had not written the proof,
and the statement file was reviewed by a Codex agent that had written
neither the statement nor the proofs. For Paper 24 an earlier draft of the
statement file, with natural-number positions, was returned by its reviewer
and replaced by the real-coordinate version. The statement files were frozen
at 18:06:37 UTC (Paper 23) and 18:06:09 UTC (Papers 24 and 25). According to
the file times and the development logs, the proof files were created after
the freeze and compiled between 18:06 and 18:44 UTC; for Paper 24 two development jobs also compiled files on the author's Windows
computer (18:27–18:29 and 18:33–18:44 UTC), while the rebuild of the whole
project for this version was running there (see the rebuild section); they are
not counted among the checks. The formalizations follow the written proofs prepared in the
search, except that Paper 23 obtains roots of the predicted size from the
maximum modulus principle instead of a contraction argument and Paper 24
uses a different family for its lower bound when `k ≥ 6`. After the checks,
independent Claude Code agents (model Claude Opus 5.5), which had written
none of the files, gave the final reviews, one for each paper, from 20:52
UTC; their model family differs from Codex's. Each read the sources itself,
compared the statement file with them, read the written proof, the proof
files and the raw logs, and compiled the files again in a new directory,
replaying every module with `leanchecker`. The reviewer of Paper 23 checked
the join formula against enumeration of dominating sets for nine small
petals and computed root moduli in Python; the reviewer of Paper 24 compared
exhaustive tilings with the two-row criterion for `k ≤ 11` and `n ≤ 18`; the
reviewer of Paper 25 recomputed the lattice points, the segment sums and the
cost bound in Python. All three approved the formal results, with six, four
and five minor remarks on the written account, which were applied (one
remark on Paper 25 concerns an internal record of Codex). The reviewer of
Paper 24 later issued an erratum to one sentence of its report, about the
rejected draft of the statement, after the independent review of the paper
found the error; it does not affect the frozen statement, the Lean proof or
the verdict (`certificates/bar-tiling-defect/lean-package/`). Claude Code
checked the cited passages of the sources, searched the literature again,
wrote Papers 23 to 25 from Codex's manuscripts and the Lean files, moved
the Lean files into the repository (changing only their `import` lines),
compiled the repository versions again and checked them with `leanchecker`
on the author's Mac, checked that the new entry points of this version can
be imported together, and rebuilt the whole Lean project.

Paper 26 (version 1.25.0) was produced from 20 to 22 November 2026.
Conjectures B and C were among the eight problems on which Codex prepared
detailed notes in the separate search session of Papers 21 and 22 (18:36–18:54
UTC on 20 November). According to the file times, that search had written
arguments by 18:41 UTC for Conjecture B (by averaging over the common zeros
of integer linear forms on a torus, a route that the Lean proof does not
use), by 18:46 UTC for Conjecture C (the weighted averaging used in the
paper, in chord form; a review note of the same time added an integral
version) and by 18:50 UTC (a second note with the integral version); they
were read by other Codex agents of that search. At about 22:27 UTC the
author asked for complete Lean proofs of Conjectures B and C, and Claude
Code passed this request to OpenAI Codex (model GPT-6.2-Astra, reasoning
level ultra), which carried it out in another separate session. Codex
agents (same model) wrote the two statement files, checked the reading of
the sources, searched again for prior work, wrote the Lean proofs and the
written proofs, and checked the packages in two new empty directories on the
author's Mac (22:33–22:44 UTC). The reading of the sources was checked
(22:29:40 UTC) by a Codex agent that had written neither statement and had
not taken part in the earlier search; the same agent reviewed both statement
files, after checking that each compiled without diagnostics, and approved
them at 22:30:07 UTC; both were frozen at 22:30:34 UTC. According to the
development logs and the file times, all proof files were created after the
freeze, and they were compiled during development between 22:30:49 and 22:39
UTC. For Conjecture B the Lean route, by kernel splitting, differs from the
earlier written proof; for Conjecture C it follows the earlier note, with the
volumes identified through determinants. Because of the significance of the
results, each of the two theorems was given two independent final reviews by
Claude Code agents (model Claude Opus 5.5), four reviewers in all, none of
which had written any of the files and each second reviewer reading the first
report only after writing its own analysis (22:43–23:16 UTC); their model
family differs from Codex's. Each reviewer read the sources itself, compared
the statement file with them, read the written proof, the proof files and
the raw logs, and rebuilt the formalization in a new directory, replaying
every module with `leanchecker`; between them they tested the averaging
lemma in exact rational arithmetic, the covering radii of more than 11,000
random and adversarially chosen projections of `T_n` with `n ≤ 5` and
`i ≤ 4`, and the bound of Conjecture C for random simplices in dimensions 2
to 4, and found no violation. All four decisions were APPROVE_FORMAL, with no
blocking or major remarks; their minor remarks on the written account (4 and
5 for Conjecture B, 5 and 7 for Conjecture C) were applied. Claude Code
checked the cited passages of the sources, checked three lemmas numerically
in Python, wrote the paper from Codex's manuscripts and the Lean files, had
a further Claude Code agent search the literature in depth (see the prior-work
section), moved the Lean files into the repository (changing only their
`import` lines), compiled the repository versions again and checked them
with `leanchecker` on the author's Mac, checked that the fourteen new entry
points of Papers 17 to 27 can be imported together, and rebuilt the whole
Lean project. No human mathematician has read the proofs of Paper 26.

Paper 27 (version 1.25.0) was produced on 21 and 22 November 2026.
The author asked for a new search for substantial open problems, and Claude
Code passed this request to OpenAI Codex (model GPT-6.2-Astra, reasoning
level ultra) at 01:00 UTC on 21 November. In that search Codex screened 72
problems not screened in earlier rounds and prepared notes on eight of
them, this one among them. According to the file times, by 01:12 UTC a
Codex agent had written the proof of the minimum (Corollary 1) and checked
the value of the witness by exact elimination on the full matrix, and
another Codex agent (same model) that had not derived it had read the
proof, recomputed the witness value and approved it; the search ended at
01:22 UTC. After reading its report, the author asked, at about 01:27 UTC,
that Codex take up this problem and one other, which is not part of this
version, each in its own Codex session, separate from the search. Codex
agents (same model) checked the reading of the source, searched again for
prior work, wrote the statement files, the written proofs and the Lean
files, and checked the packages in two new empty directories on the
author's Mac. The statement file of the minimum was reviewed against the
source by a Codex agent that had not written it (approved at 01:31:57 UTC)
and frozen at 01:32:25 UTC; according to the file times and the
development logs, its proof files were created after the freeze and
compiled during development between 01:32 and 01:42 UTC, and the package
of 37 files was checked at 01:42:55–01:56:09 UTC. An earlier attempt,
started 35 seconds before, had been stopped by the acceptance script, which
misread two informational messages of Lake; it is kept on record, and the
script was corrected only in this respect. In parallel, Codex wrote a
proof of the classification (file times 01:36 to 01:41 UTC), which was read by
Codex agents that had not derived it (reviews at 01:39, 01:42 and 01:44
UTC); one of them rebuilt the coefficients of 25 constructed elements and
recomputed their full 125 × 125 determinants. As the task description
allowed, Claude Code asked Codex at 03:20 UTC to formalize the
classification. Its statement file was reviewed against the source by a
Codex agent that had not written it (approved at 03:22:01 UTC) and frozen
at 03:22:48 UTC; its proof files were created after the freeze and
compiled during development between 03:23 and 03:34 UTC, and all 63 files
were checked at 03:33:17–03:55:22 UTC, the 37 files of the minimum
unchanged. The Lean route follows the written classification, except that
the exact lift (Lemma 8) uses explicit cofactor certificates in place of a
general lifting argument. The final reviews were done by Claude Code
agents (model Claude Opus 5.5) that had written none of the files: one for
the minimum (03:20–03:27 UTC) and, because of the significance of the
result, two independent ones for the classification (03:57–04:55 UTC),
neither of which read the other's report; their model family differs from
Codex's. Each reviewer read the source itself, compared the statement
files with it, read the written proofs, the proof files and the receipts,
and rebuilt the formalization in a new directory, replaying every module
with `leanchecker`; the reviewers of the classification tested it on
random integer functions (4,650 exact determinants in one review; about
300,000 evaluations through the factorization, checked against 140 full
determinants, in the other) and found no counterexample. All three
decisions were APPROVE_FORMAL, with no blocking or major remarks; their
minor remarks on the written account (6, 5 and 5) were taken into account
where they concern the paper; the others concern internal records of
Codex. The author decided to include Paper 27 in version 1.25.0. Claude
Code checked the cited passages of the source, recomputed in Python the
determinants of the witness and of the example of Mossinghoff and Pinner,
the group `U` and the visible primes below 6000, wrote the paper from
Codex's manuscripts and the Lean files, moved the Lean files into the
repository (changing only their `import` lines), compiled the repository
versions again and checked them with `leanchecker` on the author's Mac,
and rebuilt the whole Lean project. No human mathematician has read the
proofs of Paper 27. Eleven further independent Claude Code agents (model Claude Opus 5.5), which had written none of the files, reviewed the papers, one each, and another reviewed the release (the README, the certificates, the receipts and the release notes); their corrections were applied. The author has read Papers 17–27 and, using a
side-by-side table, compared their Lean statements with the main theorems
of each paper: Theorem 1 (apart from its last sentence) and Corollary 1 of Paper 17, Theorems 1 and 2 of
Paper 18, Theorem 1 of Papers 19, 20, 21 and 22, Theorems 1 and 2 and
Corollary 1 of Paper 23, Theorem 1 of Paper 24, Theorems 1 and 2 of Paper
25, Theorems 1, 2 and 2′ of Paper 26, and Theorem 1 and Corollary 1 of
Paper 27.

For versions 1.9.0 and 1.10.0 the final review before release was done by
an independent Claude Code agent instead of OpenAI Codex, whose usage quota
had run out (the author's decision; version 1.4.0 was handled the same way).
For version 1.11.0, Codex took over the final review and local release
preparation after Claude's usage credits ran out. Its Paper 8 review covered
the paper, the statement file, the proof routes and the saved validation
evidence; it did not rerun the Lean checks. Codex's re-review of version 2
of Papers 3 and 4, the text of Paper 10 and the Claude-written proofs for
those papers remains pending. For version 1.12.0, OpenAI Codex (model
gpt-6-astra) rebuilt the whole Lean project from a clean directory and ran
the local comparator check described above, and an independent Codex agent
reviewed the evidence. Before the release of version 1.12.0,
an independent Claude Code agent (model Claude Fable 5.1), which had written
none of the files, reviewed the changes to the README and ATTEMPTS.md, the
paper, the Lean package of Paper 5 against Codex's receipts, the comparator
files and the published logs of the clean rebuild (6 October 2026). For
version 1.13.0, OpenAI Codex (its main session used the model gpt-6-astra)
rebuilt the whole Lean project from a clean directory and ran the local
comparator check described above, and a Codex agent that had written none of
the proofs or tools reviewed the evidence (9 October 2026). Before the
release of version 1.13.0, an independent Claude Code agent (model Claude
Fable 5.1), which had written none of the files, reviewed the changes to the
README and ATTEMPTS.md, the paper, the Lean package of Paper 6 against
Codex's receipts, the comparator files, and the published logs and receipts
of the clean rebuild and of the local comparator check against their
originals (9 October 2026). For version 1.14.0, Claude Code (model Claude Opus
5.5) rebuilt the whole Lean project from a new empty directory, as described
above. Before the release of version 1.14.0, the second
independent agent named in the disclosure of Paper 7 reviewed the changes to the
README and ATTEMPTS.md, the certificates, the receipts and the release notes
(5 November 2026). OpenAI Codex took no part in the work on version 1.14.0 after
3 November 2026. For version 1.15.0, Claude Code (model Claude Opus
5.5) rebuilt the whole Lean project from a new empty directory, as described
above, and the second independent agent named in the disclosure of version 2 of
Paper 2 reviewed the changes to the README and ATTEMPTS.md, the certificates,
the receipts and the release notes (7 November 2026). OpenAI Codex read the
release of version 1.14.0 and reported one minor error in the package notes of
Paper 7, on the module `Research`, which is corrected. For version 1.16.0,
Claude Code (model Claude Opus 5.5) rebuilt the whole Lean project from a new
empty directory, as described above, and the second independent agent named in
the disclosure of version 2 of Paper 1 reviewed the changes to the README and
ATTEMPTS.md, the certificates, the receipts and the release notes (7 November
2026). OpenAI Codex wrote the statement files and the Lean proofs of version 2
of Paper 1, as described above. For version 1.17.0, Claude Code (model Claude
Opus 5.5) rebuilt the whole Lean project from a new empty directory, as
described above, and drafted the changes to the README and ATTEMPTS.md. OpenAI
Codex wrote the statement files and the Lean proofs of version 3 of Paper 1, as
described above. For version 1.18.0, Claude Code (model Claude Opus 5.5) rebuilt
the whole Lean project from a new empty directory, as described above, and
drafted the changes to the README and ATTEMPTS.md. A third independent Claude
Code agent (model Claude Fable 5.1), which had written none of these files,
reviewed these changes, the certificates, the receipts and the release notes on
10 November 2026, without running Lean; its corrections were applied. OpenAI
Codex took no part in Paper 11 or in this rebuild. For version 1.19.0, Claude Code (model Claude Opus
5.5) rebuilt the whole Lean project from a new empty directory, as described
above, and drafted the changes to the README and ATTEMPTS.md, and an independent
Claude Code agent (model Claude Fable 5.1), which had written none of these
files, reviewed them, the certificates, the receipts and the release notes on
11 November 2026, without running Lean; its corrections were applied. OpenAI
Codex wrote the statements and the Lean proofs of version 2 of Paper 10, as
described above, and took no part in this rebuild. For version 1.20.0, Claude
Code (model Claude Opus 5.5) rebuilt the whole Lean project from a new empty
directory, as described above, and drafted the changes to the README and
ATTEMPTS.md, which the independent agent named in the disclosure of Paper 12
reviewed with the certificates, the receipts and the release notes. OpenAI
Codex made Paper 12's example, statement file and Lean proofs, as described
above, and took no part in this rebuild. For version 1.21.0, Claude Code
(model Claude Opus 5.5) rebuilt the whole Lean project from a new empty
directory, as described above, and drafted the changes to the README and
ATTEMPTS.md, which the independent agent named in the disclosure of Paper 13
reviewed with the certificates, the receipts and the release notes. OpenAI
Codex made Paper 13's statement files and Lean proofs, as described above,
and took no part in this rebuild. For version 1.22.0, Claude Code (model
Claude Opus 5.5) rebuilt the whole Lean project from a new empty directory, as
described above, and drafted the changes to the README and ATTEMPTS.md, which
the second independent agent named in the disclosure of version 2 of Paper 13
reviewed with the certificates, the receipts and the release notes; OpenAI Codex made the all-`k` Lean proofs of Paper 13 and took
no part in this rebuild. For version 1.23.0, Claude Code (model Claude Opus
5.5) rechecked the Lean files of Papers 14 and 15 in their repository versions
and rebuilt the whole Lean project from a new empty directory, as described
above, and drafted the changes to the README and ATTEMPTS.md, which the second independent agent named in the disclosure of Papers 14 and 15 reviewed with the certificates, the receipts and the release notes;
OpenAI Codex made the statement files and the Lean proofs of Papers 14 and 15,
as described above, and took no part in this rebuild. For version 1.24.0,
Claude Code (model Claude Opus 5.5) rechecked the Lean files of Paper 16 in
their repository versions and rebuilt the whole Lean project from a new
empty directory, as described above, and drafted the changes to the README
and ATTEMPTS.md, which the second independent agent named in the disclosure of Paper 16 reviewed with the certificates, the receipts and the release notes; OpenAI Codex made the statement file and the
Lean proofs of Paper 16, as described above, and took no part in this
rebuild. For version 1.25.0,
Claude Code (model Claude Opus 5.5) rechecked the Lean files of Papers 17
to 27 in their repository versions and rebuilt the whole Lean project from
a new empty directory, as described above, and drafted the changes to the
README and ATTEMPTS.md, which the independent agent named in the disclosure of Papers 17 to 27 as the reviewer of the release reviewed with the certificates, the receipts and the release notes; OpenAI Codex made the statement files
and the Lean proofs of Papers 17 to 27, as described above, and took no
part in this rebuild.

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
v1.4.0 [10.5281/zenodo.22981669](https://doi.org/10.5281/zenodo.22981669),
v1.5.0 [10.5281/zenodo.22982516](https://doi.org/10.5281/zenodo.22982516),
v1.6.0 [10.5281/zenodo.23000177](https://doi.org/10.5281/zenodo.23000177),
v1.7.0 [10.5281/zenodo.23000178](https://doi.org/10.5281/zenodo.23000178),
v1.7.1 [10.5281/zenodo.23002935](https://doi.org/10.5281/zenodo.23002935),
v1.8.0 [10.5281/zenodo.23004801](https://doi.org/10.5281/zenodo.23004801),
v1.9.0 [10.5281/zenodo.23043604](https://doi.org/10.5281/zenodo.23043604),
v1.10.0 [10.5281/zenodo.23045882](https://doi.org/10.5281/zenodo.23045882),
v1.11.0 [10.5281/zenodo.23070713](https://doi.org/10.5281/zenodo.23070713); later
versions are listed on the Zenodo record.
