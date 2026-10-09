import Mathlib

/-!
# Paper 6 back-fill: V3 CANDIDATE (definitions and statements only; NOT FROZEN)

Paper: H. Dong, "The weight spectrum of the Reed–Muller code RM(7,14) up to four weights",
`papers/rm714-weights/note.tex` of the repository (version 1.4.0).

This file contains **only definitions and statements** (`def … : Prop`). It imports Mathlib and
nothing else. No statement is proved here. Each `def` quotes the paper item it formalizes.
These statements were written **after** the paper and its programs (back-fill), by an AI agent.

## Trust surface

Mathlib notions used directly: `ZMod 2`, functions `Fin m → ZMod 2` (points of `𝔽₂^m`),
`MvPolynomial` with `MvPolynomial.totalDegree`, `MvPolynomial.eval`, `MvPolynomial.support`;
`hammingNorm` (Hamming weight); `Function.support`; `Set.ncard`; `Set.indicator`; `AffineSubspace`,
`AffineSubspace.direction`, `Module.finrank`; `AffineEquiv` (`≃ᵃ[ZMod 2]`), `LinearEquiv`
(`≃ₗ[ZMod 2]`); `Fin.snoc`, `Fin.init`, `Fin.last`, `Fin.castAdd`, `Fin.natAdd`; `Finset`, `List`.
The old trust-surface table is `work/lean-backfill/paper6/STATEMENTS.md`.
V3 changes and exclusions are in the adjacent DIFF.md and MANIFEST.json.
ChallengeV3Tests.lean is candidate test source; it has NOT been compiled for V3.
Independent semantic review and compilation are required before any freeze.
No claim is certified by writing its definition; deletions earn no proof credit.

## Conventions

* A point of `𝔽₂^m` is `x : Fin m → ZMod 2`. The paper's variable `x_j` (`1 ≤ j ≤ m`) is the
  coordinate with index `j - 1 : Fin m`. So `x13`, `x14` of `𝔽₂^14` are `y 12`, `y 13`.
* `RM r m`: truth tables of polynomials over `𝔽₂` of total degree at most `r`. (As functions,
  `x_i^2 = x_i`; any polynomial of total degree `≤ r` has the same truth table as its multilinear
  reduction, which has degree `≤ r`, so this is the paper's `RM(r,m)`.)
* The weight of a truth table `f` is `hammingNorm f` = the number of points with `f x ≠ 0`
  (`= 1` in `ZMod 2`).
* "A sum of at most `k` monomials of degree at most `r`" = a polynomial `p` with
  `p.support.card ≤ k` and `p.totalDegree ≤ r` (as a function, each term `X^d` is the multilinear
  monomial on the variables occurring in `d`).
-/

set_option autoImplicit false

namespace BackfillPaper6.V3

/-! ## 1. Basic objects -/

/-- A point of `𝔽₂^m`. -/
abbrev Pt (m : ℕ) := Fin m → ZMod 2

/-- A Boolean function on `𝔽₂^m` (a truth table, i.e. a word of length `2^m`). -/
abbrev BFun (m : ℕ) := Pt m → ZMod 2

/-- The truth table of a polynomial `p` over `𝔽₂` in the variables `x_1, …, x_m`. -/
noncomputable def evalFun {m : ℕ} (p : MvPolynomial (Fin m) (ZMod 2)) : BFun m := fun x => MvPolynomial.eval x p

/-- The binary Reed–Muller code `RM(r,m)`: truth tables of polynomials of degree at most `r`. -/
def RM (r m : ℕ) : Set (BFun m) :=
  {f | ∃ p : MvPolynomial (Fin m) (ZMod 2), p.totalDegree ≤ r ∧ f = evalFun p}

/-- `w` is a weight of `RM(r,m)` (Hamming weight of a codeword). -/
def IsWeight (r m w : ℕ) : Prop := ∃ f ∈ RM r m, hammingNorm f = w

/-- The weight spectrum of `RM(r,m)`. -/
def spectrum (r m : ℕ) : Set ℕ := {w | IsWeight r m w}

/-- `k`-flat: a nonempty affine subspace of `𝔽₂^m` whose direction has dimension `k`. -/
def IsFlat {m : ℕ} (F : AffineSubspace (ZMod 2) (Pt m)) (k : ℕ) : Prop :=
  (F : Set (Pt m)).Nonempty ∧ Module.finrank (ZMod 2) F.direction = k

/-- The indicator `1_F` of a set of points (Mathlib's `Set.indicator`). -/
noncomputable def ind {m : ℕ} (F : Set (Pt m)) : BFun m := F.indicator 1

/-! ## 2. The sets of the paper -/

/-- `U₀ = {322, 326, 330, 334}`. -/
def U0 : Finset ℕ := {322, 326, 330, 334}

/-- `U = U₀ ∪ (2^14 − U₀)`. -/
def U : Finset ℕ := {322, 326, 330, 334, 16050, 16054, 16058, 16062}

/-- The explicit 18-element set `K` retained as data for `S0`.
V3 makes no claim that it exhausts the weights of `RM(7,14)` below `320`. -/
def K : Finset ℕ :=
  {0, 128, 192, 224, 240, 248, 252, 254, 256, 272, 288, 296, 304, 308, 312, 314, 316, 318}

/-- `S₀ = (K ∪ {320, 322, …, 16064} ∪ (2^14 − K)) \ U`. -/
def S0 : Finset ℕ :=
  ((K ∪ (Finset.range 16065).filter (fun w => 320 ≤ w ∧ Even w)) ∪ K.image (fun k => 16384 - k)) \ U

/-- The set `M` of the 22 possibly missing weights of Leuenberger–Albrizzio, Prop. 4. -/
def M : Finset ℕ :=
  {322, 326, 330, 334, 354, 8174, 8178, 8182, 8186, 8188, 8190,
   8194, 8196, 8198, 8202, 8206, 8210, 16030, 16050, 16054, 16058, 16062}

/-- `W₀` of Leuenberger–Albrizzio, Prop. 4. -/
def W0 : Finset ℕ := {0, 128, 192, 224, 240, 248, 252, 254, 256, 272, 288, 296, 304, 308}

/-- The 17 weights of Theorem A. -/
def thmAWeights : Finset ℕ :=
  {354, 4378, 4380, 4382, 8174, 8178, 8182, 8186, 8188, 8190, 8194, 8196, 8198, 8202, 8206,
   8210, 16030}

/-! ## 3. Independent preliminary targets and historical data
The KT/KTA classification targets have been removed. The `xs`/`ktFormI`/`ktFormII`
functions below remain historical data, with no adopted classification claim. -/

/-- (P1) "If `r < m`, every codeword of `RM(r,m)` has even weight, since `wt f mod 2` is the
coefficient of `x_1⋯x_m` in `f`. As `wt(f+1) = 2^m − wt f`, the weight spectrum is invariant
under `w ↦ 2^m − w`." The coefficient of `x_1⋯x_m` in the multilinear form of `p` is the sum of the
coefficients of the monomials of `p` in which every variable occurs. -/
def P1 : Prop :=
  (∀ r m : ℕ, r < m → ∀ f ∈ RM r m, Even (hammingNorm f)) ∧
  (∀ m : ℕ, ∀ p : MvPolynomial (Fin m) (ZMod 2),
    ((hammingNorm (evalFun p) : ℕ) : ZMod 2) =
      ∑ d ∈ p.support.filter (fun d => ∀ i, d i ≠ 0), p.coeff d) ∧
  (∀ r m : ℕ, ∀ f ∈ RM r m, (f + 1) ∈ RM r m ∧ hammingNorm (f + 1) = 2 ^ m - hammingNorm f) ∧
  (∀ r m w : ℕ, IsWeight r m w → w ≤ 2 ^ m ∧ IsWeight r m (2 ^ m - w))

/-- (P2) McEliece: "The weights of `RM(r,m)` are divisible by `2^⌊(m−1)/r⌋`. In particular the
weights of `RM(6,13)` are divisible by `4`." (For `r ≥ 1`; `/` is floor division.) -/
def P2 : Prop :=
  (∀ r m : ℕ, 1 ≤ r → ∀ f ∈ RM r m, 2 ^ ((m - 1) / r) ∣ hammingNorm f) ∧
  (∀ h ∈ RM 6 13, 4 ∣ hammingNorm h)

/-- (P3), first sentence: "The codewords of weight `d` are the indicators of `(m−r)`-flats"
(`d = 2^(m−r)`, `r ≤ m`). -/
def P3_minWeight : Prop :=
  ∀ r m : ℕ, r ≤ m → ∀ f : BFun m,
    (f ∈ RM r m ∧ hammingNorm f = 2 ^ (m - r)) ↔
      ∃ F : AffineSubspace (ZMod 2) (Pt m), IsFlat F (m - r) ∧ f = ind (F : Set (Pt m))

/-- Product `x_a x_{a+1} ⋯ x_b` of the variables with (1-based) indices in `[a, b]`
(empty product `= 1` if `b < a`). -/
def xs {m : ℕ} (a b : ℕ) : BFun m :=
  fun x => ∏ j : Fin m, if a ≤ j.val + 1 ∧ j.val + 1 ≤ b then x j else 1

/-- Kasami–Tokura normal form I:
`x_1⋯x_{r−2}(x_{r−1}x_r + x_{r+1}x_{r+2} + ⋯ + x_{r+2l−3}x_{r+2l−2})`. -/
def ktFormI (m r l : ℕ) : BFun m :=
  xs 1 (r - 2) * ∑ j ∈ Finset.Icc 1 l, xs (r + 2 * j - 3) (r + 2 * j - 2)

/-- Kasami–Tokura normal form II: `x_1⋯x_{r−l}(x_{r−l+1}⋯x_r + x_{r+1}⋯x_{r+l})`. -/
def ktFormII (m r l : ℕ) : BFun m :=
  xs 1 (r - l) * (xs (r - l + 1) r + xs (r + 1) (r + l))


/-- Historical 15-element data list from (P4b), retained for semantic tests only.
V3 adopts neither the low-weight classification nor its upper-bound assertion. -/
def L4b : Finset ℕ := {0, 64, 96, 112, 120, 124, 126, 128, 136, 144, 148, 152, 154, 156, 158}


/-! ## 4. Section 2: Lemmas 2.1 and 2.2 -/

/-- Lemma 2.1 (first part): for `S_1, …, S_k ⊆ {1, …, m}`,
`wt(∑ x_{S_i}) = ∑_{∅ ≠ T ⊆ {1..k}} (−2)^{|T|−1} 2^{m − |⋃_{i∈T} S_i|}`, where
`x_S = ∏_{j ∈ S} x_j`. -/
def Lem21 : Prop :=
  ∀ (m k : ℕ) (S : Fin k → Finset (Fin m)),
    (hammingNorm (fun x : Pt m => ∑ i, ∏ j ∈ S i, x j) : ℤ) =
      ∑ T ∈ (Finset.univ : Finset (Finset (Fin k))).filter (fun T => T.Nonempty),
        (-2 : ℤ) ^ (T.card - 1) * (2 : ℤ) ^ (m - (T.biUnion S).card)

/-- The Venn region of `T ⊆ {1..k}`: the variables lying in `S_i` exactly for `i ∈ T`. -/
def venn {m k : ℕ} (S : Fin k → Finset (Fin m)) (T : Finset (Fin k)) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∀ i, j ∈ S i ↔ i ∈ T

/-- Lemma 2.1 (second part): "the weight depends only on the sizes of the `2^k − 1` Venn regions
of `S_1, …, S_k`". -/
def Lem21_venn : Prop :=
  ∀ (m k : ℕ) (S S' : Fin k → Finset (Fin m)),
    (∀ T : Finset (Fin k), T.Nonempty → (venn S T).card = (venn S' T).card) →
      hammingNorm (fun x : Pt m => ∑ i, ∏ j ∈ S i, x j) =
        hammingNorm (fun x : Pt m => ∑ i, ∏ j ∈ S' i, x j)

/-- `g(x) = f(x, 0)` for `f` on `𝔽₂^{m+1}` (the last coordinate is `x_{m+1}`). -/
def half0 {m : ℕ} (f : BFun (m + 1)) : BFun m :=
  fun x => f (Fin.snoc (α := fun _ => ZMod 2) x 0)

/-- `g'(x) = f(x, 1)`. -/
def half1 {m : ℕ} (f : BFun (m + 1)) : BFun m :=
  fun x => f (Fin.snoc (α := fun _ => ZMod 2) x 1)

/-- Lemma 2.2: "Let `f : 𝔽₂^{m+1} → 𝔽₂`, and put `g(x) = f(x,0)` and `g'(x) = f(x,1)`. Then
`f = g + x_{m+1}(g + g')`, and `f ∈ RM(r+1,m+1)` iff `g ∈ RM(r+1,m)` and `g + g' ∈ RM(r,m)`.
Moreover `wt f = wt g + wt g' = wt(g+g') + 2|supp g ∩ supp g'|`, and
`supp g ∩ supp g' = supp g \ supp(g+g')`." -/
def Lem22 : Prop :=
  ∀ (m r : ℕ) (f : BFun (m + 1)),
    (∀ y : Pt (m + 1), f y =
        half0 f (Fin.init y) + y (Fin.last m) * (half0 f (Fin.init y) + half1 f (Fin.init y))) ∧
    (f ∈ RM (r + 1) (m + 1) ↔ (half0 f ∈ RM (r + 1) m ∧ (half0 f + half1 f) ∈ RM r m)) ∧
    hammingNorm f = hammingNorm (half0 f) + hammingNorm (half1 f) ∧
    hammingNorm f = hammingNorm (half0 f + half1 f) +
      2 * (Function.support (half0 f) ∩ Function.support (half1 f)).ncard ∧
    Function.support (half0 f) ∩ Function.support (half1 f) =
      Function.support (half0 f) \ Function.support (half0 f + half1 f)

/-! ## 5. Section 3: Theorems A and B -/

/-- Theorem A: "The following 17 numbers are weights of `RM(7,14)`: 354, 4378, 4380, 4382, 8174,
8178, 8182, 8186, 8188, 8190, 8194, 8196, 8198, 8202, 8206, 8210 and 16030. Table 1 gives
codewords with at most seven monomials." -/
def ThmA : Prop :=
  ∀ w ∈ thmAWeights, ∃ p : MvPolynomial (Fin 14) (ZMod 2),
    p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧ hammingNorm (evalFun p) = w

/-- The (1-based) variable index `j ∈ [1, 14]` as an element of `Fin 14` (index `j - 1`). -/
def fin14 (j : ℕ) : Fin 14 := ⟨(j - 1) % 14, Nat.mod_lt _ (by norm_num)⟩

/-- The variable set of a monomial of `𝔽₂^14`, given by its (1-based) variable indices. -/
def ms (l : List ℕ) : Finset (Fin 14) := (l.map fin14).toFinset

/-- `𝖺 = x_1⋯x_7`. -/
def sa : Finset (Fin 14) := ms [1, 2, 3, 4, 5, 6, 7]

/-- `𝖻 = x_8⋯x_14`. -/
def sb : Finset (Fin 14) := ms [8, 9, 10, 11, 12, 13, 14]

/-- The polynomial `∑_{S ∈ Ls} ∏_{j ∈ S} x_j` of a list of variable sets. -/
noncomputable def polyOf {m : ℕ} (Ls : List (Finset (Fin m))) : MvPolynomial (Fin m) (ZMod 2) :=
  (Ls.map fun S => ∏ j ∈ S, MvPolynomial.X j).sum

/-- The codewords `f_w` of Table 1, as printed (each monomial as its set of variables). -/
def table1 : List (ℕ × List (Finset (Fin 14))) :=
  [(354, [sa, sb, ms [1, 2, 3, 5, 6, 7, 11], ms [1, 3, 6, 7, 10, 12, 13],
      ms [3, 4, 6, 7, 10, 12, 13]]),
   (4378, [sa, sb, ms [3, 4, 6], ms [1, 5, 7, 11, 13], ms [6, 14]]),
   (4380, [ms [2, 6, 7, 9, 12], ms [3, 4, 5, 8, 9, 10, 13], ms [8, 14],
      ms [1, 3, 5, 9, 10, 11, 14]]),
   (4382, [sa, sb, ms [1, 2, 5, 6, 7], ms [4, 9], ms [3, 4, 6, 8, 12]]),
   (8174, [sa, sb, ms [7], ms [5, 10], ms [2, 3, 4, 5, 8, 10, 11], ms [1, 2, 4, 6, 13, 14]]),
   (8178, [sa, sb, ms [7], ms [2, 5, 6, 13], ms [2, 5, 8, 10, 13, 14]]),
   (8182, [sa, sb, ms [8], ms [1, 2, 3, 4, 6, 11, 13], ms [1, 14], ms [2, 7, 8, 10, 11, 12, 14]]),
   (8186, [sa, sb, ms [11], ms [4, 12], ms [1, 2, 8, 10, 11, 12, 13]]),
   (8188, [ms [1], ms [2, 5, 6, 8, 9, 10, 13], ms [2, 14], ms [1, 4, 6, 7, 11, 12, 14]]),
   (8190, [sa, sb, ms [2], ms [1, 7, 8]])]

/-- The column `(σ_1, …, σ_k)` of Table 1. -/
def table1Sigma : List (ℕ × List ℕ) :=
  [(354, [640, 203, 50, 12, 1]), (4378, [6912, 1537, 173, 21, 1]), (4380, [4864, 288, 25, 1]),
   (4382, [5376, 725, 150, 20, 1]), (8174, [12928, 2825, 314, 59, 9, 1]),
   (8178, [9728, 1081, 187, 19, 1]), (8182, [12800, 2765, 304, 50, 8, 1]),
   (8186, [12672, 2597, 219, 23, 1]), (8188, [12544, 2370, 100, 2]), (8190, [10496, 1313, 82, 1])]

/-- `σ_j = ∑_{|T| = j} 2^{14 − |⋃_{i∈T} S_i|}` for `f = ∑_{i=1}^k x_{S_i}` (`S = Ls.get`). -/
def sigma (Ls : List (Finset (Fin 14))) (j : ℕ) : ℕ :=
  ∑ T ∈ (Finset.univ : Finset (Finset (Fin Ls.length))).filter (fun T => T.card = j),
    2 ^ (14 - (T.biUnion fun i => Ls.get i).card)

/-- Table 1 and its caption: each `f_w` is a sum of distinct monomials of degree at most 7 with
weight `w`; its `σ`-column is as printed and `wt f_w = ∑_j (−2)^{j−1} σ_j`; the complements
`1 + f_w` for `w = 354, 8190, 8188, 8186, 8182, 8178, 8174` have the weights
`16030, 8194, 8196, 8198, 8202, 8206, 8210`. -/
def Table1 : Prop :=
  (∀ w Ls, (w, Ls) ∈ table1 →
      Ls.Nodup ∧ (∀ S ∈ Ls, S.card ≤ 7) ∧ hammingNorm (evalFun (polyOf Ls)) = w ∧
      (∀ σ, (w, σ) ∈ table1Sigma →
        σ.length = Ls.length ∧ (∀ j : Fin σ.length, σ.get j = sigma Ls (j.val + 1)) ∧
        (w : ℤ) = ∑ j : Fin σ.length, (-2 : ℤ) ^ j.val * (σ.get j : ℤ))) ∧
  (∀ w w' Ls, (w, w') ∈ [(354, 16030), (8190, 8194), (8188, 8196), (8186, 8198), (8182, 8202),
        (8178, 8206), (8174, 8210)] → (w, Ls) ∈ table1 →
      hammingNorm (evalFun (1 + polyOf Ls)) = w')

/-- Remark 3.1 (direct sums): for `A` depending only on `x_1..x_7` and `B` only on `x_8..x_14`. -/
def dsum (A B : BFun 7) : BFun 14 :=
  fun y => A (fun i => y (Fin.castAdd 7 i)) + B (fun i => y (Fin.natAdd 7 i))

/-- Remark 3.1: "`deg(A+B) ≤ 7` and `wt(A+B) = 8192 − 2(64 − wt A)(64 − wt B)`. As `wt A` and
`wt B` can take any value from 0 to 128, taking `wt B = 63` and `wt A = 64 − n` shows that every
even number `8192 − 2n` with `|n| ≤ 64` is a weight." -/
def Rem31 : Prop :=
  (∀ A B : BFun 7, dsum A B ∈ RM 7 14 ∧
      (hammingNorm (dsum A B) : ℤ) =
        8192 - 2 * (64 - (hammingNorm A : ℤ)) * (64 - (hammingNorm B : ℤ))) ∧
  (∀ a : ℕ, a ≤ 128 → ∃ A : BFun 7, hammingNorm A = a) ∧
  (∀ n : ℤ, |n| ≤ 64 → IsWeight 7 14 (8192 - 2 * n).toNat)


/-- Theorem B, second sentence: "Every element of `S₀` is the weight of an explicit codeword with
at most eight monomials." -/
def ThmB_witnesses : Prop :=
  ∀ w ∈ S0, ∃ p : MvPolynomial (Fin 14) (ZMod 2),
    p.totalDegree ≤ 7 ∧ p.support.card ≤ 8 ∧ hammingNorm (evalFun p) = w


/-- Proof of Theorem B / Section 6: "the 7901 elements of `S₀`". -/
def S0_card : Prop := S0.card = 7901

/-- Carlet's question for `(c, m) = (7, 14)`, in the paper's reading (Section 1, after
Theorem B): every even number from `320` to `16064` is a weight of `RM(7,14)`. -/
def CarletQ714 : Prop := ∀ w : ℕ, Even w → 320 ≤ w → w ≤ 16064 → IsWeight 7 14 w

/-- Section 1 (after Theorem B, and abstract): "By the explicit codewords of Theorem B and by
(P1), it has a positive answer if and only if 322, 326, 330 and 334 are weights. This
equivalence does not depend on the theorem of Kasami, Tokura and Azumi." -/
def CarletEquiv : Prop := CarletQ714 ↔ ∀ w ∈ U0, IsWeight 7 14 w

/-- Section 1: "Fourteen of these numbers, the elements of `M \ U`, are listed as missing". -/
def IntroMU : Prop :=
  M \ U = {354, 8174, 8178, 8182, 8186, 8188, 8190, 8194, 8196, 8198, 8202, 8206, 8210, 16030} ∧
  (M \ U).card = 14 ∧ M \ U ⊆ thmAWeights

/-- Section 3 (after the proof of Theorem B): "the file also checks that proposition
[Leuenberger–Albrizzio, Prop. 4] independently", i.e. every element of
`(W₀ ∪ {312, 314, …, 2^14 − 312} ∪ (2^14 − W₀)) \ M` is a weight of `RM(7,14)`. -/
def LAProp4 : Prop :=
  ∀ w : ℕ, (w ∈ W0 ∨ (Even w ∧ 312 ≤ w ∧ w ≤ 16384 - 312) ∨ (w ≤ 16384 ∧ 16384 - w ∈ W0)) →
    w ∉ M → IsWeight 7 14 w

/-! ## 6. Section 4: Lou–Wang Construction 2 and independent targets -/

/-- The first 12 coordinates of a point of `𝔽₂^14`. -/
def lo12 (y : Pt 14) : Pt 12 := fun i => y (Fin.castAdd 2 i)

/-- `f₁ ‖ f₂ ‖ f₃ ‖ f₄`: equal to `f₁, f₂, f₃, f₄` on the cosets
`(x13, x14) = (0,0), (1,0), (0,1), (1,1)`. -/
def cat4 (f1 f2 f3 f4 : BFun 12) : BFun 14 := fun y =>
  if y 12 = 0 then (if y 13 = 0 then f1 (lo12 y) else f3 (lo12 y))
  else (if y 13 = 0 then f2 (lo12 y) else f4 (lo12 y))

/-- `x13·A + x14·B` for `A, B` on `𝔽₂^12`. -/
def xAB (A B : BFun 12) : BFun 14 := fun y => y 12 * A (lo12 y) + y 13 * B (lo12 y)

/-- `x_{i_1} x_{i_2} ⋯ x_{i_6}` for a sequence of indices `1 ≤ i_j ≤ 12` (repetitions allowed). -/
def prodSeq (i : Fin 6 → Fin 12) : BFun 12 := fun x => ∏ j, x (i j)

/-- `x_1 x_2 ⋯ x_6` on `𝔽₂^12`. -/
def x16 : BFun 12 := fun x => ∏ j ∈ ({0, 1, 2, 3, 4, 5} : Finset (Fin 12)), x j

/-- Construction 2 of Lou–Wang with `m = 6`:
`g₁ = x_1⋯x_6 + x_{i_1}⋯x_{i_6} + x_{i_7}⋯x_{i_12}`,
`g₂ = x_1⋯x_6 + x_{i_13}⋯x_{i_18} + x_{i_19}⋯x_{i_24}` (`1 ≤ i_j ≤ 12`), `a₁, a₂ ∈ 𝔽₂`,
`g = 0 ‖ (g₁ + a₁) ‖ g₂ ‖ (g₁ + g₂ + a₂)`. -/
def lwG (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2) : BFun 14 :=
  cat4 0 (x16 + prodSeq i1 + prodSeq i2 + fun _ => a1) (x16 + prodSeq i3 + prodSeq i4)
    ((x16 + prodSeq i1 + prodSeq i2) + (x16 + prodSeq i3 + prodSeq i4) + fun _ => a2)

/-- The set `S` of all weights generated by Construction 2 with `m = 6`. -/
def lwS : Set ℕ :=
  {w | ∃ (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2), hammingNorm (lwG i1 i2 i3 i4 a1 a2) = w}

/-- Conjecture 2 of Lou–Wang for `m = 6`: `S` contains `2^{m+2} + 2^m + 2i` and
`2^{2m} + 2^m + 2i` for `0 ≤ i < 2^m`. -/
def LWConj2_m6 : Prop :=
  (∀ i : ℕ, i < 2 ^ 6 → 2 ^ 8 + 2 ^ 6 + 2 * i ∈ lwS) ∧
  (∀ i : ℕ, i < 2 ^ 6 → 2 ^ 12 + 2 ^ 6 + 2 * i ∈ lwS)

/-- Section 1 (l. 147–148): Construction 2 produces codewords of `RM(m+1, 2m+2) = RM(7,14)`. -/
def LWConstrInRM : Prop :=
  ∀ (i1 i2 i3 i4 : Fin 6 → Fin 12) (a1 a2 : ZMod 2), lwG i1 i2 i3 i4 a1 a2 ∈ RM 7 14

/-- Section 1 (l. 100–102): Conjecture 2 of [lw] "would give 322, 326, 330, 334 and 354". Stated
by its content, without the hypothesis `LWConj2_m6` (false by the known literal refutation, which would make an
implication vacuous): each of these numbers lies in the family `2^8 + 2^6 + 2i`, `0 ≤ i < 64`,
asserted by the conjecture, and every weight of Construction 2 is a weight of `RM(7,14)`. -/
def LWConj2_gives : Prop :=
  (∀ w ∈ ({322, 326, 330, 334, 354} : Finset ℕ), ∃ i < 2 ^ 6, w = 2 ^ 8 + 2 ^ 6 + 2 * i) ∧
  lwS ⊆ spectrum 7 14


/-- Literal Construction 2 only. This refutation is already due to Lou and Wang,
DAM 388 (2026), Proposition 2; see paper6/LOUWANG-CHECK.md.
Retained for formal verification of a known result, without a novelty claim.
Proving this does not prove the removed, stronger `ThmC` target. -/
def ThmC_literal : Prop := ¬ LWConj2_m6 ∧ 322 ∉ lwS

/-- Section 4: "For `A, B ∈ RM(6,12)` we have `0 ‖ A ‖ B ‖ (A+B) = x13 A + x14 B ∈ RM(7,14)`." -/
def Sec4Concat : Prop :=
  ∀ A ∈ RM 6 12, ∀ B ∈ RM 6 12, cat4 0 A B (A + B) = xAB A B ∧ xAB A B ∈ RM 7 14


/-- Fact `(∗)` in the proof of Proposition C′: "if `G, E` are flats of `𝔽₂^12` and `q` is
quadratic, then `|G ∩ E ∩ supp q|` is even or at most 3". -/
def FactStar : Prop :=
  ∀ (G E : AffineSubspace (ZMod 2) (Pt 12)) (q : BFun 12), q ∈ RM 2 12 →
    Even (((G : Set (Pt 12)) ∩ E ∩ Function.support q).ncard) ∨
      ((G : Set (Pt 12)) ∩ E ∩ Function.support q).ncard ≤ 3


/-! ## 7. Section 5: Propositions D, E, F and Lemma 5.1 -/

/-- Section 5.1: "Two transversal flats of `𝔽₂^14` of dimension at least 7 both have
dimension 7" (transversal: meeting in exactly one point). -/
def TransversalDim : Prop :=
  ∀ F1 F2 : AffineSubspace (ZMod 2) (Pt 14),
    7 ≤ Module.finrank (ZMod 2) F1.direction → 7 ≤ Module.finrank (ZMod 2) F2.direction →
    ((F1 : Set (Pt 14)) ∩ F2).ncard = 1 →
    Module.finrank (ZMod 2) F1.direction = 7 ∧ Module.finrank (ZMod 2) F2.direction = 7

/-- Proposition D: "Let `F1, F2, F3` be flats of `𝔽₂^14` of dimension at least 7, not
necessarily distinct (the whole space is allowed). Then none of `wt 1_{F1}`,
`wt(1_{F1} + 1_{F2})` and `wt(1_{F1} + 1_{F2} + 1_{F3})` lies in `U`." -/
def PropD : Prop :=
  ∀ F1 F2 F3 : AffineSubspace (ZMod 2) (Pt 14),
    (F1 : Set (Pt 14)).Nonempty → (F2 : Set (Pt 14)).Nonempty → (F3 : Set (Pt 14)).Nonempty →
    7 ≤ Module.finrank (ZMod 2) F1.direction → 7 ≤ Module.finrank (ZMod 2) F2.direction →
    7 ≤ Module.finrank (ZMod 2) F3.direction →
    hammingNorm (ind (F1 : Set (Pt 14))) ∉ U ∧
    hammingNorm (ind (F1 : Set (Pt 14)) + ind (F2 : Set (Pt 14))) ∉ U ∧
    hammingNorm (ind (F1 : Set (Pt 14)) + ind (F2 : Set (Pt 14)) + ind (F3 : Set (Pt 14))) ∉ U

/-- The linear subspace of `𝔽₂^12` spanned by the unit vectors `e_j`, `j ∈ J` (1-based):
the points whose coordinates outside `J` vanish. -/
def coordSpan (J : Finset ℕ) : Set (Pt 12) := {x | ∀ i : Fin 12, i.val + 1 ∉ J → x i = 0}

/-- Remark after Proposition D, with "in RM(6,12)" (replacement of `RemD162`). -/
def RemD162 : Prop :=
  (ind (coordSpan {1, 2, 3, 4, 5, 6}) + ind (coordSpan {7, 8, 9, 10, 11, 12}) +
      ind (coordSpan {1, 2, 3, 7, 8, 9})) ∈ RM 6 12 ∧
  hammingNorm (ind (coordSpan {1, 2, 3, 4, 5, 6}) + ind (coordSpan {7, 8, 9, 10, 11, 12}) +
      ind (coordSpan {1, 2, 3, 7, 8, 9})) = 162

/-- Proposition E: "No sum of at most five monomials of degree at most 7 in `x_1, …, x_14` (the
constant 1 allowed) has weight in `U`. The same holds for `f ∘ φ` for every such sum `f` and every
affine bijection `φ` of `𝔽₂^14`." -/
def PropE : Prop :=
  (∀ p : MvPolynomial (Fin 14) (ZMod 2), p.support.card ≤ 5 → p.totalDegree ≤ 7 →
      hammingNorm (evalFun p) ∉ U) ∧
  (∀ p : MvPolynomial (Fin 14) (ZMod 2), p.support.card ≤ 5 → p.totalDegree ≤ 7 →
    ∀ φ : Pt 14 ≃ᵃ[ZMod 2] Pt 14, hammingNorm (fun x => evalFun p (φ x)) ∉ U)

/-- The weights of sums of at most five monomials of degree at most 7 in `x_1, …, x_14`. -/
def weightsLe5 : Set ℕ :=
  {w | ∃ p : MvPolynomial (Fin 14) (ZMod 2),
    p.support.card ≤ 5 ∧ p.totalDegree ≤ 7 ∧ hammingNorm (evalFun p) = w}

/-- Retained first conjunct of the old `PropE_remark`, under a new name.
The second conjunct (all weights below 320 equal K) is removed under the user directive.
This target does not assert or count as the complete old `PropE_remark`. -/
def PropE_remark_2mod4 : Prop :=
  {w | w ∈ weightsLe5 ∧ w % 4 = 2 ∧ 250 ≤ w ∧ w ≤ 400} =
    {w | w = 254 ∨ w = 314 ∨ w = 318 ∨ (w % 4 = 2 ∧ 338 ≤ w ∧ w ≤ 398)}

/-- The Venn vectors of the proof of Proposition E for `k` monomials: families `(n_T)` indexed
by the nonempty `T ⊆ {1..k}`, with `n_T ≤ 14`, `∑_T n_T ≤ 14` and `∑_{T ∋ i} n_T ≤ 7` for all `i`. -/
def vennVectors (k : ℕ) : Finset ({T : Finset (Fin k) // T.Nonempty} → Fin 15) :=
  Finset.univ.filter fun n =>
    (∑ T, (n T : ℕ)) ≤ 14 ∧
      ∀ i : Fin k, (∑ T ∈ Finset.univ.filter (fun T : {T : Finset (Fin k) // T.Nonempty} => i ∈ T.1),
        (n T : ℕ)) ≤ 7

/-- `n_a`: the number of pairs `{x, x + a}` contained in the support of `f` (`a ≠ 0`); the
ordered count is halved. -/
noncomputable def pairCount {m : ℕ} (f : BFun m) (a : Pt m) : ℕ :=
  (Function.support f ∩ {x | x + a ∈ Function.support f}).ncard / 2

/-- Lemma 5.1: "Let `f ∈ RM(7,14)` have support `S` and weight `w ≡ 2 (mod 4)`. For
`a ∈ 𝔽₂^14 \ {0}` let `n_a` be the number of pairs `{x, x+a}` contained in `S`. Then
`∑_{a≠0} n_a = C(w,2)`, every `n_a` is odd, and in coordinates in which `a` is the last unit vector
we have `f = g + x14 h` with `g ∈ RM(7,13)`, `h ∈ RM(6,13)`, `n_a = |supp g \ supp h|` and
`wt h = w − 2 n_a`." (Coordinates: any linear bijection `φ` with `φ e₁₄ = a`; `x = φ y`.) -/
def Lem51 : Prop :=
  ∀ f ∈ RM 7 14, hammingNorm f % 4 = 2 →
    (∑ a ∈ Finset.univ.erase (0 : Pt 14), pairCount f a) = (hammingNorm f).choose 2 ∧
    (∀ a : Pt 14, a ≠ 0 → Odd (pairCount f a)) ∧
    (∀ a : Pt 14, a ≠ 0 → ∀ φ : Pt 14 ≃ₗ[ZMod 2] Pt 14, φ (Pi.single 13 1) = a →
      ∃ g ∈ RM 7 13, ∃ h ∈ RM 6 13,
        (∀ y : Pt 14, f (φ y) = g (Fin.init y) + y (Fin.last 13) * h (Fin.init y)) ∧
        pairCount f a = (Function.support g \ Function.support h).ncard ∧
        hammingNorm h + 2 * pairCount f a = hammingNorm f)

/-- The decomposition of Proposition F in direction `a`, "as in Lemma 5.1". -/
def DecompAt (f : BFun 14) (a : Pt 14) (w : ℕ) : Prop :=
  ∀ φ : Pt 14 ≃ₗ[ZMod 2] Pt 14, φ (Pi.single 13 1) = a →
    ∃ g ∈ RM 7 13, ∃ h ∈ RM 6 13,
      (∀ y : Pt 14, f (φ y) = g (Fin.init y) + y (Fin.last 13) * h (Fin.init y)) ∧
      ((hammingNorm h = w - 2 ∧ (Function.support g \ Function.support h).ncard = 1) ∨
       (hammingNorm h = w - 6 ∧ (Function.support g \ Function.support h).ncard = 3))

/-- Proposition F: "Let `w ∈ U₀`. Then `w` is a weight of `RM(7,14)` if and only if there are
`h ∈ RM(6,13)` and `g ∈ RM(7,13)` with `(wt h, |supp g \ supp h|) = (w−2, 1)` or `(w−6, 3)`.
Moreover, a codeword of weight `w = 322, 326, 330, 334` has such a decomposition, as in
Lemma 5.1, in at least 7559, 7235, 6908, 6576 directions." -/
def PropF : Prop :=
  (∀ w ∈ U0, IsWeight 7 14 w ↔
    ∃ h ∈ RM 6 13, ∃ g ∈ RM 7 13,
      (hammingNorm h = w - 2 ∧ (Function.support g \ Function.support h).ncard = 1) ∨
      (hammingNorm h = w - 6 ∧ (Function.support g \ Function.support h).ncard = 3)) ∧
  (∀ f ∈ RM 7 14, ∀ w N : ℕ,
    (w, N) ∈ ([(322, 7559), (326, 7235), (330, 6908), (334, 6576)] : List (ℕ × ℕ)) →
    hammingNorm f = w → N ≤ Set.ncard {a : Pt 14 | a ≠ 0 ∧ DecompAt f a w})

/-! ## 8. Additional independent statement candidates
These declarations close review coverage gaps. They contain no proofs and are not frozen. -/


/-- Section 1: "The minimum distance of RM(r,m) is d = 2^{m−r}" (abstract: "RM(7,14) has minimum
distance d = 128"). Used in the proof of Proposition C′ (nonzero codewords of RM(2,6) have weight
≥ 16; of RM(6,12), ≥ 64). -/
def MinDist : Prop :=
  ∀ r m : ℕ, r ≤ m →
    (∀ f ∈ RM r m, f ≠ 0 → 2 ^ (m - r) ≤ hammingNorm f) ∧ IsWeight r m (2 ^ (m - r))

/-- Section 2: "A k-flat is an affine subspace of dimension k, with 2^k points; its indicator 1_F is
a product of m−k affine functions, so it lies in RM(m−k,m)." -/
def FlatBasics : Prop :=
  ∀ (m k : ℕ) (F : AffineSubspace (ZMod 2) (Pt m)), IsFlat F k →
    (F : Set (Pt m)).ncard = 2 ^ k ∧ ind (F : Set (Pt m)) ∈ RM (m - k) m

/-- Section 2: "Affine bijections preserve degrees, weights and flats." -/
def AffineInvariance : Prop :=
  ∀ (r m : ℕ) (φ : Pt m ≃ᵃ[ZMod 2] Pt m) (f : BFun m),
    (f ∈ RM r m → (fun x => f (φ x)) ∈ RM r m) ∧
    hammingNorm (fun x => f (φ x)) = hammingNorm f ∧
    ∀ (F : AffineSubspace (ZMod 2) (Pt m)) (k : ℕ), IsFlat F k → IsFlat (F.map φ.toAffineMap) k

/-- Section 4: "`f₁ ‖ f₂ ‖ f₃ ‖ f₄` … so that its weight is `∑ wt f_i`". -/
def Cat4Weight : Prop :=
  ∀ f1 f2 f3 f4 : BFun 12,
    hammingNorm (cat4 f1 f2 f3 f4) =
      hammingNorm f1 + hammingNorm f2 + hammingNorm f3 + hammingNorm f4

/-- Section 1 (l. 165–166) and Section 6.2 (l. 637): "on RM(6,12) they find the analogues
162, 166, 170, 174 of U₀". -/
def Calib612 : Prop := ∀ w ∈ ({162, 166, 170, 174} : Finset ℕ), IsWeight 6 12 w

/-- l. 328–330: "S₀ consists of the weights asserted in [la, Prop. 4] and the new weights of
Theorem A". -/
def S0_eq_LA : Prop :=
  (S0 : Set ℕ) =
    {w | (w ∈ W0 ∨ (Even w ∧ 312 ≤ w ∧ w ≤ 16384 - 312) ∨ (w ≤ 16384 ∧ 16384 - w ∈ W0)) ∧ w ∉ M} ∪
      ((M \ U : Finset ℕ) : Set ℕ)

/-- Mathlib-only restatement of Theorem A, a V3 candidate for independent review. -/
def ThmA_mathlib : Prop :=
  ∀ w ∈ ({354, 4378, 4380, 4382, 8174, 8178, 8182, 8186, 8188, 8190, 8194, 8196, 8198, 8202,
      8206, 8210, 16030} : Finset ℕ),
    ∃ p : MvPolynomial (Fin 14) (ZMod 2), p.totalDegree ≤ 7 ∧ p.support.card ≤ 7 ∧
      hammingNorm (fun x : Fin 14 → ZMod 2 => MvPolynomial.eval x p) = w

/-- Mathlib-only restatement of Proposition E (first sentence), a V3 candidate for independent review. -/
def PropE_mathlib : Prop :=
  ∀ p : MvPolynomial (Fin 14) (ZMod 2), p.support.card ≤ 5 → p.totalDegree ≤ 7 →
    hammingNorm (fun x : Fin 14 → ZMod 2 => MvPolynomial.eval x p) ∉
      ({322, 326, 330, 334, 16050, 16054, 16058, 16062} : Finset ℕ)

end BackfillPaper6.V3
