import Research.Backfill.Paper6.ChallengeV3

/-!
# Paper 6 V3 CANDIDATE known-answer tests — NOT COMPILED / NOT ACCEPTED

This candidate retains all 78 old examples; boundary examples are appended below.
The tests do not prove any full paper target. All tests must compile in the V3
environment before they earn test credit; no such run has occurred.
Custom definitions are exercised on small cases, by `decide` where the
definition is computable, otherwise by `simp`/`norm_num` plus `decide`. Each block says where the
expected value comes from (the paper, a cited source, or a hand count), and contains at least one
instance that must come out false. Truth tables on `𝔽₂^14` (16384 points) are too large for
`decide`; the same definitions are tested on `𝔽₂^m` for small `m` (they are uniform in `m`), and
the `𝔽₂^14` data (sets, variable sets, σ-values) are tested directly.
-/

set_option autoImplicit false

namespace BackfillPaper6.V3Tests

open BackfillPaper6.V3

/-! ### `hammingNorm` as the weight of a truth table (Mathlib; semantic check) -/

-- `x1 x2` on `𝔽₂^2` is 1 only at `(1,1)`.
theorem test_001 : hammingNorm (fun x : Pt 2 => x 0 * x 1) = 1 := by decide
-- `x1 + x2` on `𝔽₂^3`: balanced, weight 4.
theorem test_002 : hammingNorm (fun x : Pt 3 => x 0 + x 1) = 4 := by decide
-- Lemma 2.1 on a small case: `wt(x1x2 + x2x3) = 2^1 + 2^1 − 2·2^0 = 2` on `𝔽₂^3`.
theorem test_003 : hammingNorm (fun x : Pt 3 => x 0 * x 1 + x 1 * x 2) = 2 := by decide
-- [la, Lemma 2] scaled down (two monomials of degree `k` on `2k` variables meeting in `c`
-- variables have weight `2^{k+1} − 2^{c+1}`): `k = 2`, `c = 0`: `x1x2 + x3x4` on `𝔽₂^4` has weight 6.
theorem test_004 : hammingNorm (fun x : Pt 4 => x 0 * x 1 + x 2 * x 3) = 6 := by decide
-- false instance
theorem test_005 : hammingNorm (fun x : Pt 3 => x 0 * x 1) ≠ 3 := by decide

/-! ### `evalFun`, `polyOf` -/

theorem test_006 : evalFun (polyOf [({0, 1} : Finset (Fin 3))]) = fun x => x 0 * x 1 := by
  funext x; simp [evalFun, polyOf]

theorem test_007 : evalFun (polyOf [({0} : Finset (Fin 3)), {1}]) = fun x => x 0 + x 1 := by
  funext x; simp [evalFun, polyOf]

-- the empty variable set is the constant monomial 1
theorem test_008 : evalFun (polyOf [(∅ : Finset (Fin 3))]) = fun _ => 1 := by
  funext x; simp [evalFun, polyOf]

-- equal monomials cancel in pairs (x + x = 0 in `𝔽₂`)
theorem test_009 : evalFun (polyOf [({0} : Finset (Fin 3)), {0}]) = fun _ => 0 := by
  have h : ∀ a : ZMod 2, a + a = 0 := by decide
  funext x; simp [evalFun, polyOf, h]

-- `x_i^2 = x_i` as functions: `X 0 ^ 2` evaluates like `X 0`
theorem test_010 : evalFun (MvPolynomial.X 0 ^ 2 : MvPolynomial (Fin 3) (ZMod 2)) = evalFun (MvPolynomial.X 0) := by
  funext x; simp only [evalFun, map_pow, MvPolynomial.eval_X]; revert x; decide

-- false instance
theorem test_011 : evalFun (polyOf [({0, 1} : Finset (Fin 3))]) ≠ fun x => x 0 := by
  intro h
  have := congrFun h (fun i => if i = 0 then 1 else 0)
  simp [evalFun, polyOf] at this

/-! ### `RM`, `IsWeight` -/

-- `x1 x2 ∈ RM(2,3)`, weight 2 (a 1-flat of `𝔽₂^3`, `d = 2^{3−2} = 2`).
theorem test_012 : (fun x : Pt 3 => x 0 * x 1) ∈ RM 2 3 := by
  refine ⟨MvPolynomial.X 0 * MvPolynomial.X 1, ?_, ?_⟩
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X])
  · funext x; simp [evalFun]

theorem test_013 : IsWeight 2 3 2 := by
  refine ⟨fun x : Pt 3 => x 0 * x 1, ⟨MvPolynomial.X 0 * MvPolynomial.X 1, ?_, ?_⟩, by decide⟩
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X])
  · funext x; simp [evalFun]

-- false instances: `RM(0,1)` consists of the constants, so `x1 ∉ RM(0,1)` and 1 is not a weight.
theorem test_014 : (fun x : Pt 1 => x 0) ∉ RM 0 1 := by
  rintro ⟨p, hp, hf⟩
  have hc : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hp)
  have h0 := congrFun hf (fun _ => 0)
  have h1 := congrFun hf (fun _ => 1)
  rw [hc] at h0 h1
  simp only [evalFun, MvPolynomial.eval_C] at h0 h1
  exact absurd (h0.trans h1.symm) (by decide)

theorem test_015 : ¬ IsWeight 0 1 1 := by
  rintro ⟨f, ⟨p, hp, rfl⟩, hw⟩
  have hc : p = MvPolynomial.C (p.coeff 0) :=
    MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hp)
  have hconst : evalFun p = fun _ => p.coeff 0 := by
    funext x; conv_lhs => rw [hc]
    simp [evalFun]
  rw [hconst] at hw
  have : ∀ c : ZMod 2, hammingNorm (fun _ : Pt 1 => c) ≠ 1 := by decide
  exact this _ hw

/-! ### `IsFlat`, `ind` -/

theorem test_016 : IsFlat (⊤ : AffineSubspace (ZMod 2) (Pt 2)) 2 := by
  refine ⟨⟨0, trivial⟩, ?_⟩
  rw [AffineSubspace.direction_top]
  simp

-- false instance: the empty affine subspace is not a flat
theorem test_017 : ¬ IsFlat (⊥ : AffineSubspace (ZMod 2) (Pt 2)) 0 := by
  rintro ⟨⟨x, hx⟩, -⟩
  simp at hx

theorem test_018 : ind (Set.univ : Set (Pt 2)) = fun _ => 1 := by
  funext x; simp [ind]

theorem test_019 : ind (∅ : Set (Pt 2)) = fun _ => 0 := by
  funext x; simp [ind]

/-! ### Data sets (transcribed from the paper; hand counts) -/

theorem test_020 : U0.card = 4 ∧ U.card = 8 ∧ K.card = 18 ∧ M.card = 22 ∧ W0.card = 14 ∧
    thmAWeights.card = 17 ∧ L4b.card = 15 := by decide
theorem test_021 : U0 ⊆ U ∧ U ⊆ M ∧ W0 ⊆ K := by decide
-- `U = U₀ ∪ (2^14 − U₀)`
theorem test_022 : U = U0 ∪ U0.image (fun w => 16384 - w) := by decide
-- `S₀`: inside, outside, boundaries; `318 ∈ K`, `16066 = 2^14 − 318`
theorem test_023 : 318 ∈ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_024 : 320 ∈ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_025 : 16064 ∈ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_026 : 16066 ∈ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_027 : 354 ∈ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_028 : 16384 ∈ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_029 : 0 ∈ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
-- false instances
theorem test_030 : 322 ∉ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_031 : 334 ∉ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_032 : 16050 ∉ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_033 : 319 ∉ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_034 : 258 ∉ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide
theorem test_035 : 16065 ∉ S0 := by
  simp only [S0, Finset.mem_sdiff, Finset.mem_union, Finset.mem_filter, Finset.mem_range,
    Finset.mem_image]
  decide

/-! ### Table 1 data: `fin14`, `ms`, `sa`, `sb`, `table1`, `table1Sigma`, `sigma` -/

theorem test_036 : ms [1, 2, 3, 5, 6, 7, 11] = {0, 1, 2, 4, 5, 6, 10} := by decide
theorem test_037 : sa ∪ sb = Finset.univ ∧ Disjoint sa sb ∧ sa.card = 7 ∧ sb.card = 7 := by decide
theorem test_038 : ms [14] = {13} := by decide
-- false instance
theorem test_039 : ms [14] ≠ {0} := by decide
theorem test_040 : table1.map Prod.fst = [354, 4378, 4380, 4382, 8174, 8178, 8182, 8186, 8188, 8190] := by
  decide
theorem test_041 : table1.map (fun e => e.2.length) = [5, 5, 4, 5, 6, 5, 6, 5, 4, 4] := by decide
theorem test_042 : table1Sigma.map Prod.fst = table1.map Prod.fst := by decide
-- σ of the row 8190 (`𝖺 + 𝖻 + x2 + x1x7x8`), first and last entries of the printed column
-- `(10496, 1313, 82, 1)`: `σ₁ = 2^7 + 2^7 + 2^13 + 2^11`, `σ₄ = 2^0`.
theorem test_043 : sigma [sa, sb, ms [2], ms [1, 7, 8]] 1 = 10496 := by decide +kernel
theorem test_044 : sigma [sa, sb, ms [2], ms [1, 7, 8]] 4 = 1 := by decide +kernel
-- false instance
theorem test_045 : sigma [sa, sb, ms [2], ms [1, 7, 8]] 1 ≠ 10497 := by decide +kernel

/-! ### `xs`, `ktFormI`, `ktFormII` (Kasami–Tokura forms; weights from the paper's formula
`2d − 2^{m−r+1−l}`, `d = 2^{m−r}`) -/

theorem test_046 : (xs 2 3 : BFun 4) = fun x => x 1 * x 2 := by funext x; revert x; decide
-- form I, `m = 4, r = 2, l = 1`: `x1x2`, weight `8 − 4 = 4`
theorem test_047 : hammingNorm (ktFormI 4 2 1) = 4 := by decide
-- form I, `m = 4, r = 2, l = 2`: `x1x2 + x3x4`, weight `8 − 2 = 6`
theorem test_048 : hammingNorm (ktFormI 4 2 2) = 6 := by decide
-- form II, `m = 6, r = 3, l = 3`: `x1x2x3 + x4x5x6`, weight `16 − 2 = 14`
theorem test_049 : hammingNorm (ktFormII 6 3 3) = 14 := by decide +kernel
-- false instance
theorem test_050 : hammingNorm (ktFormI 4 2 2) ≠ 4 := by decide

/-! ### `venn` -/

theorem test_051 : venn (![{0, 1}, {1, 2}] : Fin 2 → Finset (Fin 3)) {0} = {0} := by decide
theorem test_052 : venn (![{0, 1}, {1, 2}] : Fin 2 → Finset (Fin 3)) {0, 1} = {1} := by decide
theorem test_053 : venn (![{0, 1}, {1, 2}] : Fin 2 → Finset (Fin 3)) {1} = {2} := by decide
-- false instance
theorem test_054 : venn (![{0, 1}, {1, 2}] : Fin 2 → Finset (Fin 3)) {0} ≠ {1} := by decide

/-! ### `half0`, `half1` (Lemma 2.2 on `f = x1 x2`, `m + 1 = 2`) -/

theorem test_055 : half0 (fun x : Pt 2 => x 0 * x 1) = fun _ => 0 := by
  funext x; revert x; decide
theorem test_056 : half1 (fun x : Pt 2 => x 0 * x 1) = fun x => x 0 := by
  funext x; revert x; decide
-- `wt f = wt g + wt g'`: `1 = 0 + 1`
theorem test_057 : hammingNorm (fun x : Pt 2 => x 0 * x 1) =
    hammingNorm (half0 (fun x : Pt 2 => x 0 * x 1)) + hammingNorm (half1 (fun x : Pt 2 => x 0 * x 1)) := by
  decide
-- false instance
theorem test_058 : half1 (fun x : Pt 2 => x 0 * x 1) ≠ fun _ => 0 := by
  intro h; have := congrFun h (fun _ => 1); revert this; decide

/-! ### `dsum`, `lo12`, `cat4`, `xAB`, `prodSeq`, `x16`, `lwG` (pointwise, on unit vectors) -/

/-- The unit vector `e_{i+1}` of `𝔽₂^n` (test helper). -/
def e {n : ℕ} (i : Fin n) : Pt n := fun j => if j = i then 1 else 0

-- `dsum A B` reads `A` on `x1..x7` and `B` on `x8..x14`
theorem test_059 : dsum (fun x => x 0) 0 (e 0) = 1 := by decide
theorem test_060 : dsum (fun x => x 0) 0 (e 7) = 0 := by decide
theorem test_061 : dsum 0 (fun x => x 0) (e 7) = 1 := by decide
-- `cat4` coset order `(x13, x14) = (0,0), (1,0), (0,1), (1,1)`
theorem test_062 : cat4 0 1 0 0 (e 12) = 1 ∧ cat4 0 1 0 0 (e 13) = 0 := by decide
theorem test_063 : cat4 0 0 1 0 (e 13) = 1 ∧ cat4 0 0 1 0 (e 12) = 0 := by decide
theorem test_064 : cat4 0 0 0 1 (e 12 + e 13) = 1 ∧ cat4 1 0 0 0 0 = 1 := by decide
-- `xAB A B = x13·A + x14·B`
theorem test_065 : xAB 1 0 (e 12) = 1 ∧ xAB 1 0 (e 13) = 0 ∧ xAB 0 1 (e 13) = 1 ∧ xAB 1 1 (e 12 + e 13) = 0 := by
  decide
-- `x_1^6 = x_1`; `x16 = x1⋯x6`
theorem test_066 : prodSeq (fun _ => 0) (e 0) = 1 ∧ prodSeq (fun _ => 0) (e 1) = 0 := by decide
theorem test_067 : x16 (fun i => if i.val < 6 then 1 else 0) = 1 ∧ x16 (e 0) = 0 := by decide
-- `lwG` with `i_j ≡ 1`: `g₁ = g₂ = x1⋯x6` (the two `x1` cancel); at `x1..x6 = 1`:
-- coset `(1,0)` gives `g₁ = 1`, coset `(1,1)` gives `g₁ + g₂ = 0`, coset `(0,0)` gives `0`
theorem test_068 : lwG (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0
      (fun i => if i.val < 6 ∨ i.val = 12 then 1 else 0) = 1 := by decide
theorem test_069 : lwG (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0
      (fun i => if i.val < 6 ∨ i.val = 12 ∨ i.val = 13 then 1 else 0) = 0 := by decide
-- with `a₂ = 1` the coset `(1,1)` gives `g₁ + g₂ + 1 = 1`
theorem test_070 : lwG (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 1
      (fun i => if i.val < 6 ∨ i.val = 12 ∨ i.val = 13 then 1 else 0) = 1 := by decide
-- false instance
theorem test_071 : lwG (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0 0 ≠ 1 := by decide

/-! ### `coordSpan` -/

theorem test_072 : e 0 ∈ coordSpan {1, 2, 3} := by simp only [coordSpan, Set.mem_ofPred_eq]; decide
theorem test_073 : e 2 ∈ coordSpan {1, 2, 3} := by simp only [coordSpan, Set.mem_ofPred_eq]; decide
-- false instance
theorem test_074 : e 6 ∉ coordSpan {1, 2, 3, 4, 5, 6} := by simp only [coordSpan, Set.mem_ofPred_eq]; decide

/-! ### `vennVectors` (the paper's counts for `k = 1, 2`) -/

theorem test_075 : (vennVectors 1).card = 8 := by decide +kernel
-- false instance
theorem test_076 : (vennVectors 1).card ≠ 7 := by decide +kernel

/-! ### `pairCount` on `𝔽₂^3` (hand count): `f = x1 x2` has support `{(1,1,0), (1,1,1)}`;
direction `e3` gives the single pair, direction `e1` none. -/

/-- The set counted by `pairCount`, as a `Finset` (test helper). -/
theorem pairSet_eq (f : BFun 3) (a : Pt 3) :
    Function.support f ∩ {x | x + a ∈ Function.support f} =
      ↑(Finset.univ.filter (fun x : Pt 3 => f x ≠ 0 ∧ f (x + a) ≠ 0)) := by
  ext x; simp

theorem test_077 : pairCount (fun x : Pt 3 => x 0 * x 1) (e 2) = 1 := by
  rw [pairCount, pairSet_eq, Set.ncard_coe_finset]; decide
theorem test_078 : pairCount (fun x : Pt 3 => x 0 * x 1) (e 0) = 0 := by
  rw [pairCount, pairSet_eq, Set.ncard_coe_finset]; decide

/-! ### V3 boundary tests (candidate source; not yet compiled)
Expected answers are hand counts or direct polynomial/affine definitions.
Historical KT data tests above assert only their small explicit values.
-/

-- A nonzero singleton is a proper affine 0-flat; the wrong dimension must fail.
theorem test_079 : IsFlat ({e (0 : Fin 2)} : AffineSubspace (ZMod 2) (Pt 2)) 0 := by
  constructor
  · exact ⟨e 0, by simp⟩
  · simp [AffineSubspace.direction_singleton]

theorem test_080 : ¬ IsFlat ({e (0 : Fin 2)} : AffineSubspace (ZMod 2) (Pt 2)) 1 := by
  rintro ⟨_, h⟩
  have h0 := test_079.2
  exact Nat.zero_ne_one (h0.symm.trans h)

-- Empty flat is excluded regardless of dimension.
theorem test_081 : ¬ IsFlat (⊥ : AffineSubspace (ZMod 2) (Pt 2)) 2 := by
  rintro ⟨⟨x, hx⟩, _⟩
  simp at hx

theorem test_082 : ¬ IsFlat (⊤ : AffineSubspace (ZMod 2) (Pt 2)) 1 := by
  rintro ⟨_, h⟩
  have hd : (⊤ : AffineSubspace (ZMod 2) (Pt 2)).direction =
      (⊤ : Submodule (ZMod 2) (Pt 2)) :=
    AffineSubspace.direction_top (ZMod 2) (Pt 2) (Pt 2)
  have he := congrArg (fun S : Submodule (ZMod 2) (Pt 2) =>
    Module.finrank (ZMod 2) S) hd
  have ht : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (Pt 2)) = 2 := by
    simp [Pt]
  have h2 := he.trans ht
  have hn : 2 = 1 := h2.symm.trans h
  omega

-- RM(0,m): constants are permitted, not just the zero word.
theorem test_083 : (1 : BFun 2) ∈ RM 0 2 := by
  refine ⟨(1 : MvPolynomial (Fin 2) (ZMod 2)), by simp, ?_⟩
  funext x
  simp [evalFun]

theorem test_084 : IsWeight 0 2 4 := by
  refine ⟨(1 : BFun 2), ⟨(1 : MvPolynomial (Fin 2) (ZMod 2)), by simp, ?_⟩, by decide⟩
  funext x
  simp [evalFun]

-- m=r=0: the domain has one point; the nonzero constant has weight one.
theorem test_085 : IsWeight 0 0 1 := by
  refine ⟨(1 : BFun 0), ⟨(1 : MvPolynomial (Fin 0) (ZMod 2)), by simp, ?_⟩, by decide⟩
  funext x
  simp [evalFun]

-- r=m=2 permits an odd weight: guards such as r<m in P1 are essential.
theorem test_086 : IsWeight 2 2 1 := by
  refine ⟨fun x : Pt 2 => x 0 * x 1, ⟨MvPolynomial.X 0 * MvPolynomial.X 1, ?_, ?_⟩, by decide⟩
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by simp [MvPolynomial.totalDegree_X])
  · funext x
    simp [evalFun]

theorem test_087 : ¬ Even (hammingNorm (fun x : Pt 2 => x 0 * x 1)) := by decide

-- The source polynomial has degree three, but its Boolean function has degree one.
theorem test_088 : (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) (ZMod 2)).totalDegree = 3 := by
  simp

theorem test_089 : evalFun (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) (ZMod 2)) =
    evalFun (MvPolynomial.X 0) := by
  funext x
  simp only [evalFun, map_pow, MvPolynomial.eval_X]
  revert x
  decide

theorem test_090 : evalFun (MvPolynomial.X (0 : Fin 2) ^ 3 : MvPolynomial (Fin 2) (ZMod 2)) ∈ RM 1 2 := by
  refine ⟨MvPolynomial.X 0, by simp, ?_⟩
  funext x
  simp only [evalFun, map_pow, MvPolynomial.eval_X]
  revert x
  decide

-- Each selector coset reads the corresponding original twelve-variable function.
theorem test_091 : cat4 (fun x => x 0) 0 0 0 (e 0) = 1 := by decide
theorem test_092 : cat4 0 (fun x => x 0) 0 0 (e 0 + e 12) = 1 := by decide
theorem test_093 : cat4 0 0 (fun x => x 0) 0 (e 0 + e 13) = 1 := by decide
theorem test_094 : cat4 0 0 0 (fun x => x 0) (e 0 + e 12 + e 13) = 1 := by decide
theorem test_095 : cat4 0 (fun x => x 0) 0 0 (e 0 + e 13) = 0 := by decide

-- The old reviewer explicitly requested these two known-answer checks.
theorem test_096 : (List.range 5).map (fun j => sigma [sa, sb, ms [1, 2, 3, 5, 6, 7, 11],
    ms [1, 3, 6, 7, 10, 12, 13], ms [3, 4, 6, 7, 10, 12, 13]] (j + 1)) =
    [640, 203, 50, 12, 1] := by decide +kernel

theorem test_097 : (vennVectors 2).card = 204 := by decide +kernel

-- Conversion boundary behavior is explicit: the valid paper indices are 1..14.
theorem test_098 : fin14 1 = 0 ∧ fin14 14 = 13 ∧ fin14 0 = 0 ∧ fin14 15 = 0 := by decide

end BackfillPaper6.V3Tests

-- Per-test audits; these are tests of definitions, not completed paper targets.
#print axioms BackfillPaper6.V3Tests.test_001
#print axioms BackfillPaper6.V3Tests.test_002
#print axioms BackfillPaper6.V3Tests.test_003
#print axioms BackfillPaper6.V3Tests.test_004
#print axioms BackfillPaper6.V3Tests.test_005
#print axioms BackfillPaper6.V3Tests.test_006
#print axioms BackfillPaper6.V3Tests.test_007
#print axioms BackfillPaper6.V3Tests.test_008
#print axioms BackfillPaper6.V3Tests.test_009
#print axioms BackfillPaper6.V3Tests.test_010
#print axioms BackfillPaper6.V3Tests.test_011
#print axioms BackfillPaper6.V3Tests.test_012
#print axioms BackfillPaper6.V3Tests.test_013
#print axioms BackfillPaper6.V3Tests.test_014
#print axioms BackfillPaper6.V3Tests.test_015
#print axioms BackfillPaper6.V3Tests.test_016
#print axioms BackfillPaper6.V3Tests.test_017
#print axioms BackfillPaper6.V3Tests.test_018
#print axioms BackfillPaper6.V3Tests.test_019
#print axioms BackfillPaper6.V3Tests.test_020
#print axioms BackfillPaper6.V3Tests.test_021
#print axioms BackfillPaper6.V3Tests.test_022
#print axioms BackfillPaper6.V3Tests.test_023
#print axioms BackfillPaper6.V3Tests.test_024
#print axioms BackfillPaper6.V3Tests.test_025
#print axioms BackfillPaper6.V3Tests.test_026
#print axioms BackfillPaper6.V3Tests.test_027
#print axioms BackfillPaper6.V3Tests.test_028
#print axioms BackfillPaper6.V3Tests.test_029
#print axioms BackfillPaper6.V3Tests.test_030
#print axioms BackfillPaper6.V3Tests.test_031
#print axioms BackfillPaper6.V3Tests.test_032
#print axioms BackfillPaper6.V3Tests.test_033
#print axioms BackfillPaper6.V3Tests.test_034
#print axioms BackfillPaper6.V3Tests.test_035
#print axioms BackfillPaper6.V3Tests.test_036
#print axioms BackfillPaper6.V3Tests.test_037
#print axioms BackfillPaper6.V3Tests.test_038
#print axioms BackfillPaper6.V3Tests.test_039
#print axioms BackfillPaper6.V3Tests.test_040
#print axioms BackfillPaper6.V3Tests.test_041
#print axioms BackfillPaper6.V3Tests.test_042
#print axioms BackfillPaper6.V3Tests.test_043
#print axioms BackfillPaper6.V3Tests.test_044
#print axioms BackfillPaper6.V3Tests.test_045
#print axioms BackfillPaper6.V3Tests.test_046
#print axioms BackfillPaper6.V3Tests.test_047
#print axioms BackfillPaper6.V3Tests.test_048
#print axioms BackfillPaper6.V3Tests.test_049
#print axioms BackfillPaper6.V3Tests.test_050
#print axioms BackfillPaper6.V3Tests.test_051
#print axioms BackfillPaper6.V3Tests.test_052
#print axioms BackfillPaper6.V3Tests.test_053
#print axioms BackfillPaper6.V3Tests.test_054
#print axioms BackfillPaper6.V3Tests.test_055
#print axioms BackfillPaper6.V3Tests.test_056
#print axioms BackfillPaper6.V3Tests.test_057
#print axioms BackfillPaper6.V3Tests.test_058
#print axioms BackfillPaper6.V3Tests.test_059
#print axioms BackfillPaper6.V3Tests.test_060
#print axioms BackfillPaper6.V3Tests.test_061
#print axioms BackfillPaper6.V3Tests.test_062
#print axioms BackfillPaper6.V3Tests.test_063
#print axioms BackfillPaper6.V3Tests.test_064
#print axioms BackfillPaper6.V3Tests.test_065
#print axioms BackfillPaper6.V3Tests.test_066
#print axioms BackfillPaper6.V3Tests.test_067
#print axioms BackfillPaper6.V3Tests.test_068
#print axioms BackfillPaper6.V3Tests.test_069
#print axioms BackfillPaper6.V3Tests.test_070
#print axioms BackfillPaper6.V3Tests.test_071
#print axioms BackfillPaper6.V3Tests.test_072
#print axioms BackfillPaper6.V3Tests.test_073
#print axioms BackfillPaper6.V3Tests.test_074
#print axioms BackfillPaper6.V3Tests.test_075
#print axioms BackfillPaper6.V3Tests.test_076
#print axioms BackfillPaper6.V3Tests.test_077
#print axioms BackfillPaper6.V3Tests.test_078
#print axioms BackfillPaper6.V3Tests.test_079
#print axioms BackfillPaper6.V3Tests.test_080
#print axioms BackfillPaper6.V3Tests.test_081
#print axioms BackfillPaper6.V3Tests.test_082
#print axioms BackfillPaper6.V3Tests.test_083
#print axioms BackfillPaper6.V3Tests.test_084
#print axioms BackfillPaper6.V3Tests.test_085
#print axioms BackfillPaper6.V3Tests.test_086
#print axioms BackfillPaper6.V3Tests.test_087
#print axioms BackfillPaper6.V3Tests.test_088
#print axioms BackfillPaper6.V3Tests.test_089
#print axioms BackfillPaper6.V3Tests.test_090
#print axioms BackfillPaper6.V3Tests.test_091
#print axioms BackfillPaper6.V3Tests.test_092
#print axioms BackfillPaper6.V3Tests.test_093
#print axioms BackfillPaper6.V3Tests.test_094
#print axioms BackfillPaper6.V3Tests.test_095
#print axioms BackfillPaper6.V3Tests.test_096
#print axioms BackfillPaper6.V3Tests.test_097
#print axioms BackfillPaper6.V3Tests.test_098
#print axioms BackfillPaper6.V3Tests.pairSet_eq
