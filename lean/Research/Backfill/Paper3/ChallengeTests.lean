import Research.Backfill.Paper3.Challenge

/-!
# Known-answer tests for the Paper 3 challenge definitions (addendum 1, item 2)

Every custom definition of `Challenge.lean` is tested here on small cases taken from the paper
(Table 1, Table 4, Remark 4, Theorems B and B′ at small `d`, the polynomials of §5), including
instances that must come out **false**. Not part of the frozen challenge file. No `sorry`.
-/

set_option autoImplicit false

namespace BackfillPaper3.Challenge

open SimpleGraph Finset

/-! ### `edgesIn` -/
example : edgesIn (Kdd 3) univ = 9 := by decide
example : edgesIn prism univ = 9 := by decide
example : edgesIn (Kdd 3) {.inl 0, .inl 1} = 0 := by decide          -- same side: no edge
example : ¬ edgesIn (Kdd 3) {.inl 0, .inl 1} = 1 := by decide        -- false instance

/-! ### `iCount`: Table 1 of the paper, both rows -/
example : (List.range 10).map (fun t => iCount (Kdd 3) t) =
    [15, 24, 42, 48, 57, 57, 63, 63, 63, 64] := by decide
example : (List.range 10).map (fun t => iCount prism t) =
    [13, 28, 40, 48, 57, 57, 63, 63, 63, 64] := by decide
example : ¬ iCount prism 1 = 24 := by decide                           -- false instance

/-! ### `NleZ` (integer threshold) -/
example : NleZ (Kdd 3) (-1) = 0 ∧ NleZ (Kdd 3) 0 = 15 ∧ NleZ (Kdd 3) 1 = 24 := by decide

/-! ### `iGamma` (real threshold): `i_{1/18}(K_{3,3}) = 24` (Table 1 at `t = ⌊18 γ⌋ = 1`) -/
example : iGamma (Kdd 3) 3 (1 / 18) = 24 := by
  have h : iCount (Kdd 3) 1 = 24 := by decide
  rw [← h]
  unfold iGamma iCount
  congr 1
  apply Finset.filter_congr
  intro A _
  have ht : (1 / 18 : ℝ) * ((3 : ℕ) : ℝ) * (Fintype.card (Fin 3 ⊕ Fin 3) : ℝ) = ((1 : ℕ) : ℝ) := by
    simp; norm_num
  rw [ht]
  exact Nat.cast_le

/-! ### `boundary` -/
example : boundary (Kdd 3) {.inl 0} = 3 := by decide
example : boundary (Kdd 3) {.inl 0, .inr 0} = 5 := by decide          -- 3 + 3 - 1
example : ¬ boundary (Kdd 3) {.inl 0, .inl 1} = 5 := by decide        -- it is 6

/-! ### `edgePoly`: `N_0(K_{3,3}) = 15`, `N_1(K_{3,3}) = 9` -/
example : (edgePoly (Kdd 3)).coeff 0 = 15 ∧ (edgePoly (Kdd 3)).coeff 1 = 9 := by
  simp only [edgePoly, Polynomial.finsetSum_coeff, Polynomial.coeff_X_pow]
  decide

/-! ### `triangles`, `Qcount` (Remark 4: `T(3K₄) = 12`, `Q(3K₄) = 3`; `K₅`: `Q = 5 + 1`) -/
example : triangles prism = 2 ∧ triangles (Kdd 3) = 0 := by decide
example : ¬ triangles prism = 0 := by decide                             -- false instance
set_option maxRecDepth 100000 in
example : triangles threeK4 = 12 := by decide +kernel
set_option maxRecDepth 100000 in
example : Qcount threeK4 3 = 3 := by decide +kernel
example : Qcount (⊤ : SimpleGraph (Fin 5)) 4 = 6 ∧ triangles (⊤ : SimpleGraph (Fin 5)) = 10 := by
  decide
example : Qcount (Kdd 3) 3 = 0 ∧ Qcount prism 3 = 0 := by decide

/-! ### `Kdd`, `copies`, `KddUnion`, `⊕g`, `□` -/
example : ¬ (KddUnion 2 3).Adj (0, .inl 0) (1, .inr 0) := by decide    -- different copies
example : (KddUnion 2 3).Adj (1, .inl 0) (1, .inr 2) := by decide
example : ¬ (KddUnion 2 3).Adj (1, .inl 0) (1, .inl 2) := by decide    -- same side
example : ¬ (Kdd 2 ⊕g Kdd 2).Adj (.inl (.inl 0)) (.inr (.inr 0)) := by decide
example : prism.Adj (0, 0) (1, 0) ∧ prism.Adj (0, 0) (0, 1) ∧ ¬ prism.Adj (0, 0) (1, 1) := by
  decide
example : prism.IsRegularOfDegree 3 ∧ (KddUnion 2 3).IsRegularOfDegree 3 := by
  constructor <;> (intro v; revert v; decide)
example : Fintype.card (GnV 2 5) = 20 := by decide                      -- k = 2, r = 1

/-! ### `twoSwitch`, `Sd` (x₁ = inl 0, x₂ = inl 1, y₁ = inr 0, y₂ = inr 1) -/
example : (Sd 3 0 1 0 1).Adj (.inl 0) (.inl 1) := by decide            -- x₁x₂ added
example : (Sd 3 0 1 0 1).Adj (.inr 0) (.inr 1) := by decide            -- y₁y₂ added
example : ¬ (Sd 3 0 1 0 1).Adj (.inl 0) (.inr 0) := by decide          -- x₁y₁ deleted
example : ¬ (Sd 3 0 1 0 1).Adj (.inl 1) (.inr 1) := by decide          -- x₂y₂ deleted
example : (Sd 3 0 1 0 1).Adj (.inl 0) (.inr 1) := by decide            -- x₁y₂ kept
example : ¬ (Sd 3 0 1 0 1).Adj (.inl 0) (.inl 2) := by decide          -- no other X–X edge
example : (Sd 3 0 1 0 1).IsRegularOfDegree 3 := by intro v; revert v; decide
-- Theorem B: `N_{≤1}(S_d) = 2^{d+1} + d² + 4d − 9` = 28 (d = 3), 55 (d = 4)
example : iCount (Sd 3 0 1 0 1) 1 = 28 := by decide
set_option maxRecDepth 100000 in
example : iCount (Sd 4 2 0 3 1) 1 = 55 := by decide +kernel             -- another labelling
-- Corollary 5 (proof): `i_0(S_3) = 3·2² + 1 = 13`
example : iCount (Sd 3 0 1 0 1) 0 = 13 := by decide

/-! ### `Hd` (u₁ = (0, inl 0), w₁ = (0, inr 0), u₂ = (1, inl 0), w₂ = (1, inr 0)) -/
example : (Hd 2 0 0 0 0).Adj (0, .inl 0) (1, .inr 0) := by decide      -- u₁w₂ added
example : (Hd 2 0 0 0 0).Adj (1, .inl 0) (0, .inr 0) := by decide      -- u₂w₁ added
example : ¬ (Hd 2 0 0 0 0).Adj (0, .inl 0) (0, .inr 0) := by decide    -- u₁w₁ deleted
example : ¬ (Hd 2 0 0 0 0).Adj (0, .inl 0) (1, .inr 1) := by decide    -- not an edge
example : (Hd 2 0 0 0 0).IsRegularOfDegree 2 := by intro v; revert v; decide
-- Theorem B′ at d = 2: `111 − 105 = 2(d−1)(2^d+d−3) = 6`, `i_0` difference `−2(2^{d−1}−1)² = −2`
set_option maxRecDepth 100000 in
example : iCount (Hd 2 0 0 0 0) 1 = 111 ∧ iCount (KddUnion 2 2) 1 = 105 := by decide +kernel
set_option maxRecDepth 100000 in
example : iCount (Hd 2 1 0 0 1) 0 = 47 ∧ iCount (KddUnion 2 2) 0 = 49 := by decide +kernel
set_option maxRecDepth 100000 in
example : iCount (cycleGraph 8) 1 = 111 := by decide +kernel            -- `H_2 = C_8`

/-! ### `TwoSwitchStep`: `S_3` is one 2-switch away from `K_{3,3}` -/
example : TwoSwitchStep (Kdd 3) (Sd 3 0 1 0 1) :=
  ⟨.inl 0, .inr 0, .inr 1, .inl 1, by decide, by decide, by decide, by decide, by decide,
    by decide, rfl⟩

/-! ### `tStar`, `gammaStar`, `Admissible` -/
example : tStar 6 3 = 1 ∧ tStar 12 3 = 10 ∧ tStar 8 2 = 3 := by decide
example : tStar 4 2 = -1 := by decide                 -- why `(n, d) = (4, 2)` is excluded
example : gammaStar 6 3 = 1 / 18 := by norm_num [gammaStar, tStar]
example : Admissible 6 3 ∧ ¬ Admissible 6 2 ∧ ¬ Admissible 0 1 := by unfold Admissible; decide

/-! ### `Pd`, `Wpoly` (§3 and §5): `P_2 = 7 + 4z + 4z² + z⁴`, `W₀₀ = 3 + z`, `W₁₁ = 1 + 2z + z³`
for `d = 2` -/
example : (Pd 2).coeff 0 = 7 ∧ (Pd 2).coeff 1 = 4 ∧ (Pd 2).coeff 2 = 4 ∧ (Pd 2).coeff 3 = 0 ∧
    (Pd 2).coeff 4 = 1 := by
  simp [Pd, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X, Finset.sum_range_succ]
example : (Wpoly 2 0 0).coeff 0 = 3 ∧ (Wpoly 2 1 1).coeff 3 = 1 ∧ (Wpoly 2 1 1).coeff 2 = 0 := by
  simp [Wpoly, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X, Finset.sum_range_succ]
example : evalR (Pd 1) 1 = 4 := by
  simp [evalR, Pd, Finset.sum_range_succ]; norm_num

/-! ### Version 2: tests suggested by the review of version 1 (items T1, T3) -/

-- `iGamma` just below the threshold `1/18`: `γ d n = 18/19 < 1`, so only independent sets count
example : iGamma (Kdd 3) 3 (1 / 19) = 15 := by
  have h : iCount (Kdd 3) 0 = 15 := by decide
  rw [← h]
  unfold iGamma iCount
  congr 1
  apply Finset.filter_congr
  intro A _
  have ht : (1 / 19 : ℝ) * ((3 : ℕ) : ℝ) * (Fintype.card (Fin 3 ⊕ Fin 3) : ℝ) = 18 / 19 := by
    simp; norm_num
  rw [ht]
  constructor
  · intro hle
    by_contra hne
    have h1 : (1 : ℝ) ≤ (edgesIn (Kdd 3) A : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
    linarith
  · intro hle
    have h0 : edgesIn (Kdd 3) A = 0 := by omega
    rw [h0]; norm_num

-- `D_2 = (z - 1)^3`: `D_2(0) = -1`, `D_2(2) = 1`, and a false instance
example : evalR (Dpoly 2) 0 = -1 ∧ evalR (Dpoly 2) 2 = 1 := by
  simp [evalR, Dpoly, Wpoly, Finset.sum_range_succ]; norm_num
example : ¬ evalR (Dpoly 2) 2 = 0 := by
  simp [evalR, Dpoly, Wpoly, Finset.sum_range_succ]; norm_num

-- `W₁₀ = 2 + z + z²` for `d = 2`
example : (Wpoly 2 1 0).coeff 0 = 2 ∧ (Wpoly 2 1 0).coeff 1 = 1 ∧ (Wpoly 2 1 0).coeff 2 = 1 := by
  simp [Wpoly, Polynomial.coeff_X_pow, Polynomial.coeff_one, Polynomial.coeff_X, Finset.sum_range_succ]

-- `G_n` with `m = 3` (`k = 1`, `r = 1`): `C_8 ∪ C_4`, `N_{≤1} = 47·11 + 64·7 = 965`
set_option maxRecDepth 200000 in
example : iCount (Gn 2 3 0 0 0 0) 1 = 965 := by decide +kernel

end BackfillPaper3.Challenge
