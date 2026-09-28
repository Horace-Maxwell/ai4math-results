# REVIEW-CHALLENGE — `Research/AxialMSZ/Challenge.lean` (round 7, axial)

Independent review. The reviewer (a Claude subagent) did not write or help write the challenge file, `CONTRACT.md`, `PROOF.md`, `STATEMENTS.md`, `LEAN-PLAN.md`, G1 or any code in this folder. Brief: `work/lean-backfill/REVIEW-BRIEF.md`, adapted to a research result. Work window 2026-09-27 18:46–19:16 UTC (`date -u`).

- **Reviewed file:** `work/research-lean/Research/AxialMSZ/Challenge.lean`, 452 lines,
  **SHA-256 `76caf8d5dbc90cf2b43d01a6c902dd4869b99e8129013b3f4b0b02c13bd30e5b`**
  (byte-identical copy: `work/round7/axial/lean/Challenge.lean`). Not edited.
- **Tests next to it:** none (no `ChallengeTests.lean` or other test file exists; see FIX-3).
- **Reviewer's own material:** `work/round7/axial/review-challenge/` (exact-arithmetic verifier `qla.py` + `verify_review.py` + `verify_proof_details.py` + `verify_partitions.py` with their `.out` files; Lean probe file `AxialReviewTests.lean`; elaboration check of the proposed fixes `FixCheck.lean`; compile logs). These files are outside the Lean tree and are not imported anywhere.

## 中文摘要（给用户）

- **结论：修改后冻结（FREEZE after listed fixes）。** 三个例子 S、E、D 以及 Peng 的例子，我用自己写的精确有理数程序全部重算，全部成立。Lean 陈述基本忠实，没有发现平凡真/平凡假的问题。
- **要改的三件小事：**
  1. 六个"一般性"命题要加上"融合律有限且对称"这个前提（MS 综述只讨论对称融合律）；
  2. 例 D 的注释把 MSZ 主定理的前提写错了：主定理只要求"有 Frobenius 形式"（可以是零），"(a,a)≠0" 是另一个附加条件；
  3. 缺少测试文件 `ChallengeTests.lean`。
- **对外能说什么：** 对"任意融合律"（本例用的融合律不是 Seress 的，也只有平凡分次），GS 问题 3.11 / MSZ 问题 9.5 / MS 猜想 3.16 的一般形式不成立，GS 问题 3.8 的答案是否定的。**不能说**推翻了 KMS 的 Monster 型猜想，也不能说涉及 Majorana 情形（问题 3.12）。问题 3.9 其实已被 KMP（2022）和 Peng（2026）的二维例子隐含回答，我们只是指出这一点，不能说"首次"。

## 0. Overall verdict

**FREEZE after listed fixes.** Item counts (table in §2): **ACCEPT 25, FIX 8, REJECT 0.** Six of the eight FIX are one mechanical change (FIX-1: add `F.IsFiniteSymmetric` to the six general propositions). The other two: one docstring (FIX-2) and the missing test file (FIX-3). There are also four prose fixes outside the Lean file (FIX-4), which must be made before any public text. No mathematical error was found: every conjunct of `TheoremA`, `TheoremB`, `TheoremC` and `RemarkP` was recomputed independently in exact rational arithmetic and is true (§3).

Most serious points:
- (a) The general propositions quantify over *all* fusion laws. [MS] works only with symmetric laws and [KMS] only with finite symmetric ones, so `¬ MS_Conjecture_3_16` as frozen is formally weaker than "MS Conjecture 3.16 is false" (FIX-1).
- (b) The public claims must say "for arbitrary (here non-Seress, only trivially graded) fusion laws" every time (§4).
- (c) Problem 3.9 is not new (§5).

## 1. Sources read by the reviewer

The LaTeX sources were downloaded with `curl -sL https://arxiv.org/e-print/<id>` (2026-09-27 18:46–18:47 UTC, no e-mail address or other personal data in any request). They are kept in the reviewer's scratch folder.

| ref | arXiv version read | what was checked |
|---|---|---|
| [GS] Gorshkov–Shpectorov, *Axial Algebras: Questions and Conjectures* | 2606.30048v1 | Defs. 2.1, 2.3–2.6; §3 "General axial algebras": Def. 3.7 (block), Problem 3.8, Problem 3.9 with its comment "No such examples are known at present", Def. 3.10 (Δ), Problem 3.11, Problem 3.12, Problem 3.13. The numbering was verified: `prob` and `defn` share the counter `thm`, so the order is Probs 3.1–3.3, Defs 3.4–3.5, Prob 3.6, Def 3.7, Probs 3.8–3.9, Def 3.10, Probs 3.11–3.14. There is no standing Seress, graded or Frobenius assumption in §3. |
| [MSZ] Mamontov–Shpectorov–Zhelyabin, *Radicals in primitive axial algebras* | 2602.11984v1 | Defs. 2.1–2.4, Def. 2.7 (Frobenius form, zero allowed; "always symmetric"), Lemma 2.12 (direct sums need 0 ∈ 0⋆0). §3: Def. 3.1, Lemma 3.2, Def. 3.3, Lemma 3.4, Cor. 3.5, the warning at l. 373–375, Def. 3.6. **Theorem 1.1** (main theorem) and l. 103–107. §9: Qs 9.1–9.3, Def. 9.4, Q 9.5 with the reformulation at l. 850–853, Q 9.6. Numbering verified: `question` shares the section counter, and §9 is the ninth section. |
| [MS] McInroy–Shpectorov, *Axial algebras of Jordan and Monster type* (survey) | 2209.08043v1 | Defs. 2.1–2.4; the standing assumption "From now on, we will consider only symmetric fusion laws" (background.tex l. 65); Def. 3.9 (Seress); Def. 3.11 (sum decomposition); Def. 3.15 (Δ); **Conjecture 3.16** and its operational form (l. 164); Theorem 3.20. Numbering verified: shared counter, `structure_theory` is §3, and Conj. 3.16 is the 16th environment. The published CUP chapter was not seen. |
| [KMS] Khasraw–McInroy–Shpectorov, *On the structure of axial algebras* | 1809.10132v2 | Def. 2.1 (a fusion law is a *finite* set with a *symmetric* ⋆); Def. 5.1 (sum of subalgebras); Def. 6.1 (Δ); **Conjecture 6.2 (Monster type only)** and l. 1111 ("While we do not have any examples to the contrary"); Theorem 6.14 (Seress laws with slender components). The TAMS text was not seen. |
| Peng, *A two-dimensional counterexample to radical equality…* | 2608.28653v1 | Whole paper (Thm 2.1, Prop. 3.1, §4). |
| [KMP] Kaygorodov–Martín González–Páez-Guillán, *Central extensions of axial algebras* | 2211.00334v1 (J. Algebra 662 (2025) 797–831 per Peng's bibliography) | The table "Complex axial algebras of dimension 2" (label `t:ax2`), the fusion-law table `t:flax2`, and the paragraph after them (primitivity and radicals). |

The numbering in `CONTRACT.md` §0/§1 (Problems 3.8/3.9/3.11/3.12, Questions 9.2/9.3/9.5/9.6, Conj. 3.16, Conj. 6.2) is **correct**. The line references I spot-checked also match.

## 2. Item table (coverage and faithfulness)

The list below is my own, made from `CONTRACT.md` §5, `PROOF.md` and the sources, not taken from `STATEMENTS.md`. Every claimed result has a `def … : Prop`, except the side facts listed in §8.

| # | Source statement (short) | Challenge `def` | Verdict | Notes |
|---|---|---|---|---|
| 1 | commutative algebra ([GS] 2.5, [MSZ] 2.4, [MS] 2.4, [KMS] 2.4) | `IsCommutative` | ACCEPT | Bilinearity is built into `V →ₗ[K] V →ₗ[K] V`. No associativity and no unit are assumed, as in all sources. |
| 2 | fusion law (F,⋆), F ⊆ 𝔽 ([GS] 2.1, [MSZ] 2.1, [MS] 2.1) | `FusionLaw` | ACCEPT | Only values on `carrier × carrier` enter `IsAxis`. |
| 3 | finite and symmetric ([KMS] 2.1; symmetric: [MS] §2.1) | `FusionLaw.IsFiniteSymmetric` | ACCEPT | The symmetry clause quantifies over all of `K`. It still holds for the three `if` cascades (checked by hand). |
| 4 | Seress: 0 ∈ F and 0⋆λ ⊆ {λ} ([MS] 3.9, [KMS] §6.3) | `FusionLaw.IsSeress` | ACCEPT | Verbatim. |
| 5 | A_λ(a), A_Λ(a) = ⊕ A_λ(a) | `eigsp`, `eigspSet` | ACCEPT | Mathlib `Module.End.eigenspace` = ker(ad_a − λ). The sum is direct automatically, and Λ = ∅ gives 0 (blank table cell). |
| 6 | F-axis: nonzero idempotent, A = A_F(a), A_λA_μ ⊆ A_{λ⋆μ} ([GS] 2.3, [MSZ] 2.2, [MS] 2.2, [KMS] 2.2) | `IsAxis` | ACCEPT | `eigspSet μ a F.carrier = ⊤` means ad_a is semisimple with all eigenvalues in F. `a ≠ 0` is as in [GS]/[MSZ]. |
| 7 | primitive: A_1(a) = ⟨a⟩ | `IsPrimitiveAxis` | ACCEPT | |
| 8 | ⟨⟨X⟩⟩ | `IsSubalgebra`, `gen` (sInf) | ACCEPT | Non-unital, non-associative closure. |
| 9 | primitive F-axial algebra (A, X) | `IsPrimitiveAxialAlgebra` | ACCEPT | X is part of the data, as all four sources stress. |
| 10 | ideal; block I_a = smallest ideal ∋ a ([GS] 3.7, [MSZ] 3.1) | `IsIdeal`, `IsIdealIn`, `block` | ACCEPT | Ideals are K-subspaces, the right notion for non-unital algebras. Mathlib's `TwoSidedIdeal` would allow non-subspaces and must not be used here. |
| 11 | decomposable = sum of its proper ideals ([MSZ] 3.3, [GS] l. 591); for a block, the ideals *of the block* ([MSZ] l. 373–375) | `IsDecomposableSub`, `IsDecomposable` | ACCEPT | This is the only reading under which [GS] 3.8 is non-trivial: if the ideals had to be ideals of A, [MSZ] Lemma 3.4 would make every block indecomposable. See §4 for the "axial block" caveat. |
| 12 | simple | `IsSimpleAlg` | ACCEPT | Standard: A² ≠ 0 and only the trivial ideals. |
| 13 | Δ(X): vertices X; distinct a, b adjacent iff ab ≠ 0 ([GS] 3.10, [MSZ] 9.4, [MS] 3.15, [KMS] 6.1) | `nonAnnGraph` (Mathlib `SimpleGraph.fromRel`) | ACCEPT | `fromRel` symmetrises, which is harmless because commutativity is assumed. `Connected` needs a non-empty X. The degenerate case V = 0, X = ∅ makes rows 18/19 vacuous, not false (checked; see row 17 note). |
| 14 | Frobenius form: (uv, w) = (u, vw) ([GS] 2.6, [MSZ] 2.7) | `IsFrobeniusForm` | ACCEPT | The form may be zero here, as in [MSZ]. It is used only in `ExD`, together with `β a a ≠ 0`, which forces it to be non-zero ([GS]/[KMS] require non-zero). Symmetry is not required. [MSZ] says it is automatic, and both basis forms of D are symmetric (§3). |
| 15 | sum decomposition ([MS] 3.11, [KMS] 5.1); the finest one is trivial | `IsSumDecomposition`, `OnlyTrivialSumDecompositions` | ACCEPT | The set version is at least as strong as the family version, as `STATEMENTS.md` §2(a) argues correctly. |
| 16 | operational form of [MS] Conj. 3.16: ⟨⟨X_i⟩⟩⟨⟨X_j⟩⟩ = 0 for distinct components ([MS] l. 164; [KMS] after Conj. 6.2) | `ComponentsAnnihilate` | ACCEPT | Uses Mathlib `ConnectedComponent.supp`. |
| 17 | [MS] Conj. 3.16, general law, reading (R1) | `MS_Conjecture_3_16` | **FIX** (required) | [MS] §2.1 restricts to symmetric laws, but the def quantifies over all `FusionLaw K`. So `¬MS_Conjecture_3_16` could in principle be witnessed by a non-symmetric law and would then not refute [MS]. Add `F.IsFiniteSymmetric →` (FIX-1). Degenerate check: for V = 0, X = ∅ the conclusion holds vacuously, so the statement is not trivially false. |
| 18 | [GS] 3.11 = [MSZ] 9.5, reading (R2): the finest sum decomposition is trivial ⇒ Δ connected | `FinestSumDecomposition_connected` | **FIX** (required, same) | This is a consequence of the literal question, so refuting it gives a "no". The sum-decomposition notion is [MS]'s, so the symmetric-law restriction applies. Degenerate check: for V = 0, S = ∅ is a sum decomposition without ⊤, so the hypothesis fails and the case is vacuous. |
| 19 | [MSZ] l. 850–853, reading (R3): indecomposable ⇒ Δ connected | `Indecomposable_connected` | **FIX** (recommended, uniformity) | This is literal-faithful to [MSZ], whose laws are arbitrary. Add `F.IsFiniteSymmetric →` so that the Corollary is uniformly at least as strong as every source. Degenerate check: V = 0 is "decomposable" (empty sum), so the case is vacuous. |
| 20 | general-law analogue of [GS] 3.12 (simple ⇒ Δ connected), reading (R4) | `Simple_connected` | **FIX** (recommended, same) | The docstring correctly says that 3.12 itself (Majorana) is not addressed. (R4) is the weakest reading: (R1) ⇒ (R2) ⇒ (R4) and (R1) ⇒ (R3) ⇒ (R4), which I checked. |
| 21 | [GS] 3.8 = [MSZ] 9.2: every axial block is indecomposable | `Blocks_indecomposable` | **FIX** (recommended, same; plus docstring note O-4) | Faithful under the reading "block of a primitive axial algebra, with the ideals of the block". Degenerate check: a 1-dimensional or 𝔽⊕𝔽 algebra satisfies it, so the statement is not trivially false. |
| 22 | [GS] 3.9 = [MSZ] 9.3: can dominance be non-symmetric? | `Dominance_nonsymmetric` | **FIX** (recommended, same: add the `F.IsFiniteSymmetric ∧` conjunct) | Strict `<`, so it cannot be met by a = b (probe in §6). |
| 23 | J⁺(η) | `JPlus` | ACCEPT | All 9 carrier entries were evaluated from the literal `if` cascade (Python and Lean probes). They are exactly the table in the docstring and in `CONTRACT.md` §3; the cascade needs η ∉ {0,1}, which holds for ½ and ⅓. |
| 24 | J°(η) | `JMild` | ACCEPT | As in row 23: 0⋆0 = 0⋆η = {0,η}, η⋆η = {1,0}. |
| 25 | F_{D3} at β = −1 ([Peng] Table 1, [KMP] `t:flax2`) | `FD3` | ACCEPT | This is Peng's table verbatim: 0⋆0 = {0,1}, 1⋆1 = {1}, 1⋆2 = 2⋆2 = {2}, other entries ∅. |
| 26 | laws are finite, symmetric, not Seress | `Laws_facts` | ACCEPT | True (§3). |
| 27 | structure constants → product | `structProduct`, `e` | ACCEPT | The only proofs in the file are the four bilinearity obligations. `#print axioms structProduct` gives [propext, Classical.choice, Quot.sound]. |
| 28 | Theorem A (S) | `ExS.T`, `ExS.μ`, `ExS.X`, `ExS.Statement` = `TheoremA` | ACCEPT | The table equals the verbal description (my parser read it from the Lean file). All five conjuncts are true (§3). |
| 29 | Theorem B (E) | `ExE.Statement` = `TheoremB` | ACCEPT | All seven conjuncts are true. Optional O-1: the text also claims I_a = ⟨a,b,x⟩, which is not stated in the def. |
| 30 | Theorem C (D) | `ExD.Statement` = `TheoremC` | **FIX** (docstring only; semantics ACCEPT) | The docstring calls "a Frobenius form non-zero on every generating axis" "the hypothesis of the main theorem of [MSZ]". That is wrong: [MSZ] Thm 1.1 assumes only a Frobenius form, explicitly possibly zero (l. 107). (a,a) ≠ 0 is the extra condition under which R = J = A^⊥ (FIX-2). All seven conjuncts are true. |
| 31 | Remark P (Peng/KMP) | `ExP.Statement` = `RemarkP` | ACCEPT | True. The credit wording in the docstring is correct. |
| 32 | Corollary | `Corollary` | ACCEPT | Follows from rows 28–31. After FIX-1 it also needs `Laws_facts`, which is already planned. The docstring tweak is in FIX-1. |
| 33 | known-answer tests (brief item 4) | — | **FIX** (missing) | No test file exists. Add `Research/AxialMSZ/ChallengeTests.lean` (FIX-3). |

## 3. Independent recomputation (exact rational arithmetic)

Method: my own code, `review-challenge/qla.py` and `verify_review.py`, uses `fractions.Fraction` only. It **parses the `![…]` tables directly from the frozen Lean file** and separately rebuilds them from the verbal description in `CONTRACT.md` §5. **The two agree for S, E, D and P.** For each algebra and each axis it computes the kernel of ad_a − λ for each λ in the carrier and checks that the dimensions sum to n (so ad_a is diagonalizable with eigenvalues in F) and that A_1(a) = ⟨a⟩. It then decomposes the product of every pair of eigenbasis vectors in the eigenbasis and records the realised law. Other outputs: generation (closure), Δ and its components, the blocks (ideal closure), the dimension of the associative multiplication algebra M(A) generated by all ad_{e_i}, the space of all associating bilinear forms, a unit element and the annihilator. `verify_proof_details.py` re-checks the hand computations in `PROOF.md`. `verify_partitions.py` tests every partition of X into mutually annihilating generated subalgebras; by [KMS] Theorem 5.11 (`sumaxial`, arXiv v2 numbering) every sum decomposition induces such a partition.

**Fusion laws** (literal `if` cascades): all four are symmetric with values in the carrier. J⁺(½), J⁺(⅓) and J°(½) are not Seress; FD3 is not Seress either. J⁺ and J° admit only the trivial grading: 0 ∈ 0⋆0 forces 0 ∈ F_1, and then 0⋆0 ∋ η (and 1 for J⁺) forces everything into F_1. This last fact is a hand argument and is not in Lean.

**S (4-dim, J⁺(½)).**
- Axes: each of a, b, c has eigenvalue multiplicities 1:1, 0:2, ½:1 and is a primitive J⁺(½)-axis.
- Realised law: the union over X of the realised laws is exactly J⁺(½). In particular 1 ∈ 0⋆0 is realised: for a, the product c·(b+x−½a) has a-component −½. So the law cannot be weakened.
- ⟨⟨X⟩⟩ = S.
- Δ: the only edge is a–b, with components {a,b} and {c}. `ComponentsAnnihilate` fails with the witness x·c = (−½,−½,½,−¼).
- **Simplicity:** dim M(S) = 16 = dim End_ℚ(S), so S has no ideals other than 0 and S, and S² ≠ 0. This certificate is rigorous over ℚ and shows S stays simple over every extension field.
- The simplicity certificate in `PROOF.md` was re-verified: φ_c(u) = γ − ½ξ, the four forms have rank 4, and c, xc, a(xc), b(xc) span S.
- Only trivial sum decompositions: every member of a sum decomposition is an ideal (argument in `PROOF.md` 5), and S is simple. The partition test agrees.
- Associating bilinear forms: the space is **0**. S is not unital, and Ann(S) = 0.

**E (4-dim, J⁺(⅓)).**
- a, b, c are primitive; the realised union is exactly J⁺(⅓).
- Blocks: I_a = I_b = ⟨a,b,x⟩ (dimension 3), which is an ideal of E, and I_c = E.
- E is not decomposable: every proper ideal misses c and so lies in A_{0,⅓}(c), which has dimension 3.
- Δ has components {a,b} and {c}; `ComponentsAnnihilate` fails (x·c = ⅓(x−a−b)).
- Only trivial sum decompositions.
- dim M(E) = 13, so E is not simple, as expected. Frobenius forms: 1-dimensional, spanned by (c,c).
- `PROOF.md` identities checked: v = x−a−b gives cv = v/3 and v² = (4/3)(a+b); also (x−b)² = ⅔(b+x−a/3) + (5/9)a.

**D (5-dim, J°(½)).**
- a, b, c are primitive; the realised union is exactly J°(½). For c: A_0(c) = ⟨a, b, x−2d⟩ and A_½(c) = ⟨d⟩.
- Blocks: I_a = I_b = ⟨a,b,x,d⟩ and I_c = ⟨c,d⟩.
- ⟨a,b,x⟩ and ⟨d⟩ are ideals *of I_a*, they are proper, and their sum is I_a. ⟨a,b,x⟩ is not an ideal of D (cx = d).
- β (the 3C(½) form on a, b, x plus (c,c) = 1) is associating, with β(a,a) = β(b,b) = β(c,c) = 1 and radical ⟨d⟩. The space of associating forms is 2-dimensional, and both basis forms are symmetric.
- D = I_a + I_c is itself decomposable, which `PROOF.md` notes and nothing claims otherwise.
- **Also true (not claimed by the authors):** Δ(D) is disconnected, `ComponentsAnnihilate` fails (x·c = d), and D has only trivial sum decompositions. So D is a counterexample to readings (R1) and (R2), although it has a Frobenius form with all generating axes non-singular and its law has 1 ∉ 0⋆0 (optional O-3).

**P (Peng).** The eigenvalues are 1, 2 for a and 1, 0 for b. The realised law equals F_{D3} on the realised entries (0⋆2 is not realised, which the law allows). I_b = ⟨b⟩ ⊊ I_a = P.

This is a third independent computation, after `code/` and `code2/`. All results agree with `PROOF.md` "Checks".

## 4. Scope: does any claimed "answer" overstate what the sources ask?

| source item | as posed | what the examples show | not shown |
|---|---|---|---|
| [GS] 3.11 = [MSZ] 9.5 | "a primitive axial algebra", in [GS] §3 "General axial algebras", with any fusion law (Def. 2.1) | **Negative answer for general fusion laws** (S; also E for (R2)/(R3); D for (R1)/(R2)) | any restricted class |
| [MS] Conj. 3.16 | "an axial algebra" (primitive by the survey's convention), **symmetric** laws (§2.1). [GS] l. 615–616 confirms it was "repeated in a more general setting" than [KMS] | The general form is false. J⁺(½) is symmetric and finite, so the counterexample is admissible for [MS] and [KMS] alike. | — |
| [KMS] Conj. 6.2 | **Monster type only** (and [KMS] say explicitly they have no counterexamples) | **Nothing.** A non-Seress J⁺/J° example does not touch it. This includes MathDB #340561. | Monster type, and all Seress laws: [KMS] Thm 6.14 / [MS] Thm 3.20 say a Seress counterexample needs at least two non-slender components |
| [GS] 3.12 = [MSZ] 9.6 | simple **Majorana** algebras | **Nothing.** S only shows that the general-law analogue fails. | Majorana |
| [GS] 3.8 = [MSZ] 9.2 | blocks of axial algebras, general law | **Negative answer for general fusion laws** (D) | Algebras with a non-degenerate Frobenius form, where [MSZ] §6 shows all blocks are simple (so Majorana is settled positively), and Seress/Monster type |
| [GS] 3.9 = [MSZ] 9.3 | general | Positive answer, but already implicit in [KMP] and Peng (§5). E is a further example. | Settled symmetric for a non-degenerate Frobenius form ([MSZ] Lemma 6.1) |

Specific overstatements found in the prose (not in the Lean statements). These are covered by FIX-4.
- `PROOF.md` status table: "refutes general [MS] Conj. 3.16 / [GS] P3.11 / [MSZ] Q9.5 **in every reading**". The Monster-type and Seress readings are readings too. The correct wording is "in each of the readings (R1)–(R4) of the arbitrary-fusion-law statement".
- `PROOF.md` Thm C step 4 and the Lean docstring of `ExD.Statement` say that D "satisfies the hypothesis of the main theorem of [MSZ]". [MSZ] Theorem 1.1 assumes only "a primitive axial algebra with a Frobenius form", explicitly allowing the zero form (l. 107), so every primitive axial algebra satisfies it. What D has is the extra *non-singularity* condition (a,a) ≠ 0 for all a ∈ X ([MSZ] l. 103–105, 796–797), under which R = J = A^⊥.
- "(R4)" is not a reading of [MS] 3.16 but the weakest consequence of it. Public text should call it "even the weaker statement 'simple ⇒ Δ connected' fails".

**"Axial block" caveat, for [GS] 3.8.** The natural reading, adopted by the challenge and in my view correct, is "a block I_a of an axial algebra (A,X)". [MSZ] l. 373–375 warns separately that a block need not itself be an axial algebra. In D, I_a = ⟨a,b,x,d⟩ is **not** generated by X ∩ I_a = {a,b}, which generate ⟨a,b,x⟩. If the posers meant only blocks that are themselves axial algebras, D would not answer the question. Public text must describe D's block precisely (wording in §10).

**Caveat on significance** (the authors already state this honestly in `CONTRACT.md` §3). Specialists will likely read S, E and D as showing that the general statements need a hypothesis on the fusion law (Seress, graded, or a Frobenius form with non-singular axes), not as progress on the Monster or Majorana cases. S has no non-zero Frobenius form. D has one with non-singular axes, but it is degenerate, with radical ⟨d⟩.

## 5. Credit for non-symmetric dominance (task item 4): verified

- **Peng, arXiv:2608.28653v1.** Theorem 2.1 proves that the ideal lattice of A = 𝔽a ⊕ 𝔽b (a² = a, ab = 2b, b² = b; law F_{D3}; X = {a,b}) is 0 < 𝔽b < A. Hence I_b = 𝔽b ⊊ I_a = A. Proposition 3.1 identifies this, over ℂ, with (D(−1), {e₂, a₆}, F_{D3}) of [KMP]. I read the whole source: there is **no mention of blocks, dominance, Problem 3.9 or Question 9.3**.
- **[KMP], arXiv:2211.00334v1** (1 Nov 2022; J. Algebra 662 (2025) 797–831). The table "Complex axial algebras of dimension 2" lists D(β): e₁² = e₁, e₁e₂ = βe₂, e₂² = e₂. It has three generating sets:
  - {e₁,e₂} with law F_{D1} = {1, β, 0} (β⋆β = β, 0⋆0 = {1,0});
  - {e₁,a₆} with F_{D2};
  - {e₂,a₆} with F_{D3}.
  The paragraph after the table says that only (A,{e₁,a₃}) and (A,{e₂,a₃}) are non-primitive. ⟨e₂⟩ is an ideal of D(β). So with X = {e₁,e₂} (for β ≠ 0) we get I_{e₂} = ⟨e₂⟩ ⊊ I_{e₁} = D(β), and with X = {e₂,a₆} (for β ≠ 1; Peng's case is β = −1) we get I_{e₂} ⊊ I_{a₆}. Blocks and dominance are **not mentioned**; the notion was introduced by [MSZ] in 2026.
- [GS] (29 June 2026) write "No such examples are known at present."
- **Conclusion.** The statement in `CONTRACT.md` §4 and `PROOF.md` is correct: [GS] 3.9 has been answered *implicitly* by publicly available examples since 2022 (arXiv 2022; J. Algebra 2025; Peng 2026), and the answer has not been remarked on. E is only a further example. Its other features (indecomposable, Δ disconnected) are superseded by S. I suggest presenting E as a remark or second example rather than as "Theorem B". Following the project's outreach norms, avoid "first" wording ("first to observe" included).

## 6. Compilation and tests (task item 5)

- Toolchain `lean-4.33.1-darwin_aarch64` (Lean 4.33.1, commit 819816b2); run from `work/research-lean`.
- **`lake env lean Research/AxialMSZ/Challenge.lean`: exit 0, no messages** (`review-challenge/axial_challenge_compile.log`). This ran under **slot B**, held 18:57:21Z–18:58:09Z. The slot was taken with `mkdir` + `owner.txt` before the `leanlock.sh` rule was circulated. I released only my own lock and touched no other lock.
- **No tests exist next to the challenge.**
- Brief item 6 (Mathlib-only restatement): the challenge contains none, so there is nothing to check. Brief item 5 (triviality): see the degenerate checks in rows 13 and 17–22; no statement is trivially true or trivially false.
- Reviewer's probe file `review-challenge/AxialReviewTests.lean`, which imports the challenge and lives outside the Lean tree: **exit 0**, with linter warnings only (`axial_tests_compile.log`). It checks:
  - 12 fusion-table entries across `JPlus ½`, `JPlus ⅓`, `JMild ½` and `FD3`;
  - one case that must be false (`(JPlus ½).star 0 0 ≠ {0}`);
  - structure-constant spot checks: `ExS.μ (e 3) (e 2) = ![-1/2,-1/2,1/2,-1/4]`, `ExE.μ (e 0) (e 1) = ![1/6,1/6,-1/6,0]` and `ExD.μ (e 3) (e 2) = e 4`;
  - `¬ IsAxis (JPlus ½) ExS.μ 0`;
  - `¬ (block … < block …)` for equal axes;
  - `#print axioms structProduct`, which gives only the standard three axioms.
- The proposed replacement statements (FIX-1) and the optional conjuncts (O-1 to O-3) are in `review-challenge/FixCheck.lean`. It also contains two `example`s proving that each fixed statement relates to the frozen one in the stated direction. Its compile result is in `review-challenge/fixcheck_compile.log`; see the addendum at the end of this file.

## 7. Exact fixes

### FIX-1 (rows 17–22): restrict the general propositions to finite symmetric fusion laws

Replace the six definitions in §2 of the challenge with the following. The docstrings stay as they are, with the additions in square brackets.

```lean
/-- [MS, Conjecture 3.16] (general fusion law) … [restricted, as [MS, §2.1] and [KMS, Def. 2.1] do,
to finite symmetric fusion laws, so that its negation refutes every source's reading] -/
def MS_Conjecture_3_16 : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → ComponentsAnnihilate μ X

def FinestSumDecomposition_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → OnlyTrivialSumDecompositions μ →
      (nonAnnGraph μ X).Connected

def Indecomposable_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → ¬ IsDecomposable μ →
      (nonAnnGraph μ X).Connected

def Simple_connected : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X → IsSimpleAlg μ →
      (nonAnnGraph μ X).Connected

def Blocks_indecomposable : Prop :=
  ∀ (K : Type) [Field K] (V : Type) [AddCommGroup V] [Module K V]
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric → IsPrimitiveAxialAlgebra F μ X →
      ∀ a ∈ X, ¬ IsDecomposableSub μ (block μ a)

def Dominance_nonsymmetric : Prop :=
  ∃ (K : Type) (_ : Field K) (V : Type) (_ : AddCommGroup V) (_ : Module K V)
    (F : FusionLaw K) (μ : V →ₗ[K] V →ₗ[K] V) (X : Set V),
    F.IsFiniteSymmetric ∧ IsPrimitiveAxialAlgebra F μ X ∧
      ∃ a ∈ X, ∃ b ∈ X, block μ a < block μ b
```

Change the `Corollary` docstring to: "…the general forms (arbitrary finite symmetric fusion laws) of [MS, Conj. 3.16], [GS, Problem 3.11]/[MSZ, Q. 9.5] (readings (R1)–(R3)), the general-law analogue of [GS, Problem 3.12] (R4) are false, [GS, Problem 3.8] has a negative answer and [GS, Problem 3.9] a positive one (the latter already implicit in [KMP]/Peng)."

Proof impact: none beyond citing `Laws_facts` in the Corollary proof.

### FIX-2 (row 30): `ExD.Statement` docstring

Replace "and which admits a Frobenius form that is non-zero on every generating axis (the hypothesis of the main theorem of [MSZ])." with:

"and which admits a Frobenius form with `β a a ≠ 0` for every generating axis `a` (the non-singularity condition under which [MSZ, Thm. 1.1 and l. 103–105] give `R(A) = J(A) = A^⊥`; the hypothesis of [MSZ, Thm. 1.1] itself is only the existence of a Frobenius form, possibly zero). The block `I_a` is not generated by the axes `X ∩ I_a = {a, b}`."

### FIX-3 (row 33): add `Research/AxialMSZ/ChallengeTests.lean`

At least the probes of `review-challenge/AxialReviewTests.lean`, which compile against the frozen file:
- fusion-table evaluations, including the empty entries `1⋆0` and `FD3 0⋆2`;
- one must-be-false table test;
- three structure-constant spot checks;
- `¬ IsAxis _ _ 0`.

Recommended additions:
- a must-be-false test for `IsDecomposable` on a simple algebra, or `IsDecomposable` true on 𝔽⊕𝔽 (`e₀² = e₀`, `e₁² = e₁`, `e₀e₁ = 0`);
- `¬ OnlyTrivialSumDecompositions` for 𝔽⊕𝔽;
- the `FixCheck.lean` implications between the old and new forms.

### FIX-4 (prose outside the Lean file; required before any public text)

- (a) `PROOF.md` status table: replace "in every reading" with "in each of the readings (R1)–(R4) of the arbitrary-fusion-law statement".
- (b) `PROOF.md` Thm C step 4: replace "`D` satisfies the hypothesis of the main theorem of [MSZ] (then `R(D)=J(D)=D^⊥=⟨d⟩`)" with "every generating axis of `D` is non-singular for `β` (`β(a,a)=1`), the extra condition under which [MSZ] (Thm 1.1 with l. 103–105) give `R(D)=J(D)=D^⊥=⟨d⟩`. This is not Lean-checked."
- (c) `STATEMENTS.md` §2(h): "nothing about … Frobenius forms" contradicts Theorem C. Change it to "Frobenius forms occur only in the existence conjunct of Theorem C".
- (d) `STATEMENTS.md` §1, row `Dominance_nonsymmetric`: after "proved (also by Peng's algebra)" add "and by [KMP] `D(β)`, `X = {e₁,e₂}` (2022)".

## 8. Missing items and optional strengthening

These are not required for freezing. They are needed only if the corresponding sentence appears in public text.

- **O-1:** add `block μ (e 0) = Submodule.span ℚ {e 0, e 1, e 2}` to `ExE.Statement`, because the Theorem B text claims I_a = ⟨a,b,x⟩.
- **O-2:** if the public text says "S has no non-zero Frobenius form", either formalize `∀ β, IsFrobeniusForm ExS.μ β → β = 0` or mark the sentence as an exact computation that is not Lean-checked. The same applies to "R(D) = J(D) = ⟨d⟩", "the ideals of E are exactly 0, ⟨a,b,x⟩, E", and "J⁺/J° admit only trivial gradings".
- **O-3 (new claim, would need its own review):** add `¬ (nonAnnGraph μ X).Connected ∧ ¬ ComponentsAnnihilate μ X ∧ OnlyTrivialSumDecompositions μ` to `ExD.Statement`. These conjuncts are true (§3). They answer the obvious objection to S (no Frobenius form) for the [MS]/[KMS] sum-decomposition readings (R1)/(R2): D has a Frobenius form with all generating axes non-singular, and its law has 1 ∉ 0⋆0. D does not refute (R3)/(R4), because D is decomposable.
- **O-4:** in the `Blocks_indecomposable` docstring, add "the block need not itself be an axial algebra ([MSZ] l. 373–375)".
- Nothing about [GS] Problem 3.13 (simple ⇒ unital) should be claimed. S is simple and not unital, but [KMP]'s 2-dimensional algebra B (e₁e₂ = −e₁−e₂) is already simple and not unital.

## 9. Trust surface (what a reader must trust after phase C)

- **Custom definitions:**
  - `FusionLaw` (carrier and `star`), with the three concrete `if` cascades `JPlus`, `JMild` and `FD3`;
  - `eigspSet`, `IsAxis`, `IsPrimitiveAxis`, `IsSubalgebra`, `gen`, `IsPrimitiveAxialAlgebra`;
  - `IsIdeal`, `IsIdealIn`, `block`, `IsDecomposableSub`, `IsDecomposable`, `IsSimpleAlg`;
  - `IsFrobeniusForm`, `IsSumDecomposition`, `OnlyTrivialSumDecompositions`, `ComponentsAnnihilate`, `FusionLaw.IsFiniteSymmetric`, `FusionLaw.IsSeress`.
- **Mathlib notions used:** `Module.End.eigenspace`, `Submodule.span`, `SimpleGraph.fromRel`, `SimpleGraph.Connected`, `ConnectedComponent.supp`, `sInf`/`sSup` of submodules.
- **Data:** the four structure-constant tables `ExS.T`, `ExE.T`, `ExD.T` and `ExP.T`. A reader should compare them with the displayed multiplication rules; I did (§3).
- **Modelling choices:**
  - algebras are modelled as `V` with a bilinear `μ` rather than Mathlib's algebra classes;
  - sum decompositions are sets rather than families (stronger);
  - blocks are decomposed with the ideals *of the block*;
  - universe 0 (harmless);
  - the global propositions quantify over *all* fusion laws, which FIX-1 changes.

## 10. What exactly may be claimed publicly

Status first: until phase C passes (proofs, `#print axioms`, checker), say "statements formalized in Lean 4; proofs in progress", not "Lean-verified". The examples were found and checked by AI agents with exact computation: two programs by the authors plus this review's third. The author is not a specialist, so the disclosure should say exactly that. Cite the arXiv versions and numbering: [GS] 2606.30048v1, [MSZ] 2602.11984v1, [MS] 2209.08043v1 (Conj. 3.16), [KMS] 1809.10132v2 (Conj. 6.2).

**May be claimed** (precise, modest wording):

1. **Main example (S).** "Over ℚ, the 4-dimensional commutative algebra S with basis a, b, x, c has the products
   - a² = a, b² = b, x² = x;
   - ab = ¼(a+b−x), ax = ¼(a+x−b), bx = ¼(b+x−a);
   - c² = c, ca = cb = 0, cx = ½(x−a−b) − ¼c.

   It is generated by the primitive axes a, b, c for the fusion law J⁺(½) on {1, 0, ½}, which is the Jordan-type law J(½) with the entries 0⋆0 and 0⋆½ enlarged to {1, 0, ½}. S is simple, but its non-annihilation graph has two components, {a, b} and {c}. Hence, for arbitrary fusion laws, the answer to Gorshkov–Shpectorov Problem 3.11 (= Mamontov–Shpectorov–Zhelyabin Question 9.5) is negative, and the general-fusion-law form of McInroy–Shpectorov's Conjecture 3.16 fails:
   - ⟨⟨a,b⟩⟩ and ⟨⟨c⟩⟩ do not annihilate each other;
   - S has no non-trivial sum decomposition;
   - S is simple, hence indecomposable, although Δ is disconnected."

   The following must accompany it:
   - "The law J⁺(½) is not Seress and admits only the trivial grading, and S has no non-zero Frobenius form (exact linear-algebra computations; see O-2).
   - Nothing is claimed about the Monster-type conjecture of Khasraw–McInroy–Shpectorov (Conjecture 6.2), about Seress or graded fusion laws, or about simple Majorana algebras (GS Problem 3.12, MSZ Question 9.6).
   - For algebras of Jordan type η the statement holds by Hall–Segev–Shpectorov (Israel J. Math. 223 (2018), Theorem A), as cited in [KMS] and [MS]."

2. **Decomposable block (D).** "Over ℚ there is a 5-dimensional primitive axial algebra D for the law J°(½), which is J(½) with 0⋆0 = 0⋆½ = {0, ½}. D is generated by axes a, b, c and admits a Frobenius form with (a,a) = (b,b) = (c,c) = 1. In D, the block I_a (the ideal of D generated by a) is ⟨a,b,x⟩ ⊕ ⟨d⟩, a sum of two proper ideals of I_a. So, for arbitrary fusion laws, the answer to GS Problem 3.8 (= MSZ Question 9.2) is negative. The summand ⟨a,b,x⟩ is an ideal of I_a but not of D, which is the possibility pointed out by MSZ. I_a is not generated by the axes it contains."
   - Optional, only after O-3: "D also shows that (R1)/(R2) fail in the presence of a Frobenius form that is non-singular on all generating axes."

3. **Dominance (credit).** "Non-symmetric dominance (GS Problem 3.9 = MSZ Question 9.3) already occurs in known 2-dimensional axial algebras:
   - D(β) with generating axes {e₁, e₂}, from the classification of Kaygorodov, Martín González and Páez-Guillán (arXiv:2211.00334; J. Algebra 662 (2025));
   - Bo Peng's example (arXiv:2608.28653), which Peng identifies with their (D(−1), {e₂, a₆}).

   In both, ⟨e₂⟩ is an ideal, so I_{e₂} ⊊ I_{e₁} (respectively I_b ⊊ I_a). Neither paper discusses blocks (a notion of MSZ, 2026); we point out that their examples answer Problem 3.9. [E gives a further example.]"

**Must not be claimed:**
- "first";
- "solves/settles/refutes the non-annihilating graph conjecture" without "for arbitrary fusion laws";
- any claim of progress on (as opposed to the disclaimers above about) Monster type, Majorana algebras, MathDB #340561, or Seress/graded laws;
- "in every reading";
- "D satisfies the hypothesis of MSZ's main theorem";
- "new answer to Problem 3.9" or "we answer 3.9";
- "Lean-verified" before phase C;
- anything about GS Problem 3.13.

---

## Addendum: compile result of `FixCheck.lean`

`lake env lean <review-challenge>/FixCheck.lean` (run from `work/research-lean`, Lean 4.33.1): **exit 0, no messages** (`review-challenge/fixcheck_compile.log`). It ran under slot B, taken and released with `work/tools/leanlock.sh` (owner `axial-challenge-reviewer`, 19:15:39Z–19:15:43Z). So:
- the FIX-1 replacement text elaborates verbatim against the frozen file's definitions;
- the fixed `MS_Conjecture_3_16` is implied by the frozen one, so its negation is stronger;
- the fixed `Dominance_nonsymmetric` implies the frozen one;
- the optional statements O-1, O-2 and O-3 elaborate.

SHA-256 of the reviewer's files (in `work/round7/axial/review-challenge/`):

```
    6ae6b0eed626032918fced38a7ff9a9dbbc53a1437f736709ffa820d0b020ef4  FixCheck.lean
    25003605248709e6b4f8ee10b68a93f72df0f51e39b26b7882fe8fb6bfc6b7e3  AxialReviewTests.lean
    853d8ee511ce2a913fc4eae515fb745b76a0d380c53bdad1d251a504ffbc275b  qla.py
    6b821368e73e5ea75011b569ab0c690a7e3e77e6e730ec74616bd891012f7900  verify_review.py
    08cd10d939564f36c3d676e32ed89664c0dec6a9ef82b60290261da062de053b  verify_proof_details.py
    b2ea66192fc1c2c548ef3ae166763cb2c6f6f44269240f6baff8f01d44dea2f4  verify_partitions.py
```
