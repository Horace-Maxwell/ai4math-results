import Research.Backfill.Paper8.Challenge

/-!
# Known-answer tests for the custom definitions of `Challenge.lean` (paper 8)

Not part of the frozen challenge.  Small checks (`decide`, `norm_num`, short `simp`) that
reproduce cases stated in the paper, and instances that must come out FALSE.  Each block names
the paper sentence it reproduces.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge Polynomial Matrix

/-! ## `TV`, `parentB`, `treeT` -/

-- Prop 5.6: "the three trees have 7, 6 and 5 vertices"; Section 3: `n = 1 + k + ∑ a_i`
example : Fintype.card (TV (![2, 2] : Fin 2 → ℕ)) = 7 := by decide
example : Fintype.card (TV (![2, 0, 0] : Fin 3 → ℕ)) = 6 := by decide
example : Fintype.card (TV (![3] : Fin 1 → ℕ)) = 5 := by decide
example : Fintype.card (TV (![1, 1, 1, 0] : Fin 4 → ℕ)) = 8 := by decide
-- false instance
example : Fintype.card (TV (![3] : Fin 1 → ℕ)) ≠ 4 := by decide

-- Prop 5.6(c): "`T(3) = K_{1,4}`, rooted at a leaf `c`": `v_1` has degree 4, `c` degree 1
example : (treeT (![3] : Fin 1 → ℕ)).degree (some ⟨0, none⟩) = 4 := by decide
example : (treeT (![3] : Fin 1 → ℕ)).degree none = 1 := by decide
-- Prop 5.6(b): "`T(2,0,0) = D(2,2)`, the double star with two leaves at each of its two central
-- vertices": `c` and `v_1` have degree 3, the other vertices degree 1
example : (treeT (![2, 0, 0] : Fin 3 → ℕ)).degree none = 3 := by decide
example : (treeT (![2, 0, 0] : Fin 3 → ℕ)).degree (some ⟨0, none⟩) = 3 := by decide
example : (treeT (![2, 0, 0] : Fin 3 → ℕ)).degree (some ⟨1, none⟩) = 1 := by decide
-- Prop 5.1(a): `T(0^{k_0})` is the star `K_{1,k_0}`
example : (treeT (![0, 0, 0, 0] : Fin 4 → ℕ)).degree none = 4 := by decide
-- false instances
example : (treeT (![3] : Fin 1 → ℕ)).degree (some ⟨0, none⟩) ≠ 3 := by decide
example : ¬ (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj (some ⟨1, none⟩) (some ⟨2, none⟩) := by decide
example : ¬ (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj none (some ⟨0, some ⟨0, by decide⟩⟩) := by decide
example : ¬ (treeT (![2, 2] : Fin 2 → ℕ)).Adj (some ⟨0, none⟩) (some ⟨1, some ⟨0, by decide⟩⟩) := by
  decide
example : (treeT (![2, 0, 0] : Fin 3 → ℕ)).Adj (some ⟨0, some ⟨1, by decide⟩⟩) (some ⟨0, none⟩) := by
  decide

/-! ## Multiset data: `branchMS`, `Bset`, `kb`, `bstar`, `Ib` -/

example : branchMS (![2, 0, 0] : Fin 3 → ℕ) = {2, 0, 0} := by decide
example : Bset {3, 2, 2, 1, 0} = {0, 1, 2, 3} := by decide
example : kb {3, 2, 2, 1, 0} 2 = 2 := by decide
example : kb {3, 2, 2, 1, 0} 4 = 0 := by decide
example : bstar {2, 0, 0} = 2 := by decide
example : Ib (![2, 0, 0] : Fin 3 → ℕ) 0 = {1, 2} := by decide
-- false instances
example : branchMS (![2, 0, 0] : Fin 3 → ℕ) ≠ {2, 0} := by decide
example : bstar {12, 3} ≠ 3 := by decide

/-! ## `posIn`, `lamStd` (Section 4, "Standard leaf sums") -/

-- odd `b = 3`, `k_3 = 3`: the two smallest get `1, -3`, the rest `-1`
example : (lamStd (![3, 3, 3] : Fin 3 → ℕ) 0, lamStd (![3, 3, 3] : Fin 3 → ℕ) 1,
    lamStd (![3, 3, 3] : Fin 3 → ℕ) 2) = (1, -3, -1) := by decide
-- even `b = 2`: `0, -2, 0, …`
example : (lamStd (![2, 2, 2] : Fin 3 → ℕ) 0, lamStd (![2, 2, 2] : Fin 3 → ℕ) 1,
    lamStd (![2, 2, 2] : Fin 3 → ℕ) 2) = (0, -2, 0) := by decide
-- `b = 1`, `k_1 = 2`: `1` for the smallest, `-1` otherwise; bare branch `0`
example : (lamStd (![1, 0, 1] : Fin 3 → ℕ) 0, lamStd (![1, 0, 1] : Fin 3 → ℕ) 1,
    lamStd (![1, 0, 1] : Fin 3 → ℕ) 2) = (1, 0, -1) := by decide
-- `k_b = 1`: `-1` (odd `b`), and for `b = 1` alone also `-1` (Prop 5.1(e): `Λ°_1 = -1` if `k_1 = 1`)
example : lamStd (![3] : Fin 1 → ℕ) 0 = -1 := by decide
example : lamStd (![1] : Fin 1 → ℕ) 0 = -1 := by decide
-- Prop 5.1(e): `Λ°_1 = 2 - k_1` for `k_1 ≥ 2` (here `k_1 = 4`)
example : LamStdB (![1, 1, 1, 1] : Fin 4 → ℕ) 1 = -2 := by decide
example : posIn (![2, 0, 2] : Fin 3 → ℕ) 2 = 1 := by decide
-- false instance
example : lamStd (![3, 3] : Fin 2 → ℕ) 1 ≠ -1 := by decide

/-! ## `gapCount`, `sqCountB`, `nuB`, `MB` (Lemmas 5.2, 5.4) -/

-- `B = {0,1,2,3}`, `b* = 3`: no gap, `sq = 0` (only `q = 1`, and `1 ∈ B`), `ν = 1`, `M = 3`
example : gapCount {3, 2, 1, 0} = 0 := by decide
example : sqCountB {0, 1, 2, 3} 3 = 0 := by decide
example : nuB {0, 1, 2, 3} 3 = 1 := by decide
example : MB {0, 1, 2, 3} 3 = 3 := by decide
-- `B = {12}`: squares `1, 4, 9 ≤ 11` not in `B`, so `sq = 3`, `g = 12`, `ν = min(4, 1) = 1`
example : sqCountB {12} 12 = 3 := by decide
example : gapCount {12} = 12 := by decide
example : nuB {12} 12 = 1 := by decide
-- Prop 5.3: `sq ≤ ⌊√(b* - 1)⌋` is sharp at `b* = 17` (`sq = 4` for `B = {17}`)
example : sqCountB {17} 17 = 4 ∧ Nat.sqrt 16 = 4 := ⟨by decide, by simpa using Nat.sqrt_eq' 4⟩
-- false instance
example : sqCountB {0, 1, 4, 9} 12 ≠ 3 := by decide

/-! ## `Lset` (Lemma 4.1) -/

-- `ℒ_2(2) = {-2, 2}`: `2` is realized by `(2, 0)`
example : (2 : ℤ) ∈ Lset 2 2 :=
  ⟨![2, 0], by decide, by decide, fun _ => ⟨0, 1, by decide⟩, fun _ => ⟨1, by decide⟩⟩
-- `ℒ_1(1) = {±1}`
example : (-1 : ℤ) ∈ Lset 1 1 :=
  ⟨![-1], by decide, by decide, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
-- the exception of Lemma 4.1: `0 ∉ ℒ_2(2)` (FALSE instance of membership)
example : (0 : ℤ) ∉ Lset 2 2 := by
  rintro ⟨l, hl, hs, hne, hlt⟩
  simp only [Fin.sum_univ_two] at hs
  obtain ⟨i, i', hii⟩ := hne le_rfl
  obtain ⟨j, hj⟩ := hlt le_rfl
  have e : ∀ x : Fin 2, l x = -2 ∨ l x = 0 ∨ l x = 2 := by
    intro x
    obtain ⟨hb, r, hr⟩ := hl x
    rw [abs_le] at hb
    omega
  have hj' : l j = 0 := by
    rcases e j with h | h | h
    · rw [h] at hj; norm_num at hj
    · exact h
    · rw [h] at hj; norm_num at hj
  have h0 : l 0 = 0 ∧ l 1 = 0 := by
    fin_cases j <;> simp at hj' <;> omega
  apply hii
  fin_cases i <;> fin_cases i' <;> simp [h0.1, h0.2]

/-! ## `secular` (the polynomial `R`) -/

-- Prop 5.6(c): `R(t) = t - 4` for `T(3)`
example : secular {3} = X - C 4 := by
  have hB : Bset {3} = {3} := by decide
  have hk : kb {3} 3 = 1 := by decide
  apply Polynomial.funext
  intro r
  unfold secular
  rw [hB]
  simp [hk]
  ring
-- Prop 5.6(b): `R(t) = (t - 1)(t - 4)` for `T(2,0,0)`
example : secular {2, 0, 0} = (X - C 1) * (X - C 4) := by
  have hB : Bset {2, 0, 0} = {0, 2} := by decide
  have h0 : kb (2 ::ₘ 0 ::ₘ {0}) 0 = 2 := by decide
  have h2 : kb (2 ::ₘ 0 ::ₘ {0}) 2 = 1 := by decide
  have e2 : ({0, 2} : Finset ℕ).erase 2 = {0} := by decide
  have e0 : ({0, 2} : Finset ℕ).erase 0 = {2} := by decide
  apply Polynomial.funext
  intro r
  unfold secular
  rw [hB]
  simp [Finset.sum_insert, Finset.prod_insert, h0, h2, e0, e2]
  ring
-- false instance
example : secular {3} ≠ X - C 3 := by
  have hB : Bset {3} = {3} := by decide
  have hk : kb {3} 3 = 1 := by decide
  intro h
  have := congrArg (Polynomial.eval 3) h
  unfold secular at this
  rw [hB] at this
  simp [hk] at this

/-! ## `IsSwitching`, `switchMatrix`, `mkSw` -/

example : IsSwitching sw56c := by
  intro v
  rcases v with _ | ⟨i, _ | j⟩
  · simp [sw56c, mkSw]
  · simp [sw56c, mkSw]
  · by_cases h : j.val = 0 <;> simp [sw56c, mkSw, h]
-- `D_s A D_s` flips the sign of an edge at a switched vertex: triangle switched at `0`
example : switchMatrix (!![0, 1, 1; 1, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
    (fun i => if i = 0 then -1 else 1) 0 1 = -1 := by
  simp [switchMatrix, Matrix.mul_apply, diagonal]
example : switchMatrix (!![0, 1, 1; 1, 0, 1; 1, 1, 0] : Matrix (Fin 3) (Fin 3) ℝ)
    (fun i => if i = 0 then -1 else 1) 1 2 = 1 := by
  simp [switchMatrix, Matrix.mul_apply, diagonal]

/-! ## `IsMainEigenvalue`: `K_2` (the paper's exception) has a non-main eigenvalue -/

-- FALSE instance: for `K_2` (unswitched), the eigenvalue `-1` is not main (eigenvector `(1, -1)`)
example : ¬ IsMainEigenvalue (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (-1) := by
  rintro ⟨_, x, hx, hsum⟩
  rw [Module.End.mem_eigenspace_iff] at hx
  have h0 := congrFun hx 0
  simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0
  apply hsum
  simp [Fin.sum_univ_two]
  linarith

/-! ## Tests written by the independent reviewer of version 1

(`work/lean-backfill/paper8/review/ReviewTests.lean`, review item T2; added for version 2.) -/

-- R1. POSITIVE instance of `IsMainEigenvalue`: eigenvalue 1 of K_2, eigenvector (1,1).
example : IsMainEigenvalue (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) 1 := by
  have hmem : (![1, 1] : Fin 2 → ℝ) ∈
      Module.End.eigenspace (Matrix.toLin' (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) 1 := by
    rw [Module.End.mem_eigenspace_iff]
    ext i
    fin_cases i <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hne : (![1, 1] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    norm_num at this
  refine ⟨Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩, ![1, 1], hmem, ?_⟩
  norm_num [Fin.sum_univ_two]

-- R2. FALSE instance of `IsGood`: the all-ones switching of K_2 is not good
-- (P_{-1} (1,1) = 0).  Uses `ProjNe` through Mathlib's `starProjection`.
example : ¬ IsGood (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) ![1, 1] := by
  intro h
  have hmem : (![1, -1] : Fin 2 → ℝ) ∈
      Module.End.eigenspace (Matrix.toLin' (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) (-1) := by
    rw [Module.End.mem_eigenspace_iff]
    ext i
    fin_cases i <;> simp [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hne : (![1, -1] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    have := congrFun h0 0
    norm_num at this
  have hev : IsEigenvalue (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℝ) (-1) :=
    Module.End.hasEigenvalue_of_hasEigenvector ⟨hmem, hne⟩
  apply h (-1) hev
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.mem_orthogonal]
  intro u hu
  rw [Module.End.mem_eigenspace_iff] at hu
  have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) hu
  simp [Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two] at h0
  simp [PiLp.inner_apply, Fin.sum_univ_two]
  linarith

-- R4. FALSE instance of `IsSwitching`.
example : ¬ IsSwitching (fun _ : Fin 2 => (0 : ℝ)) := by
  intro h
  rcases h 0 with h | h <;> norm_num at h

-- R5. `IsEvenPoly` and `mirror` on small polynomials.
example : IsEvenPoly (X ^ 2 - C (2 : ℚ)) := by
  unfold IsEvenPoly
  simp
example : ¬ IsEvenPoly (X - C (2 : ℚ)) := by
  unfold IsEvenPoly
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  simp at this
  norm_num at this
-- R5b. `mirror` (the challenge's, not `Polynomial.mirror`).
example : BackfillPaper8.Challenge.mirror (X - C (2 : ℚ)) = X + C 2 := by
  unfold BackfillPaper8.Challenge.mirror
  rw [Polynomial.natDegree_X_sub_C]
  simp
  ring

theorem rv_secular3 : secular {3} = X - C 4 := by
  have hB : Bset {3} = {3} := by decide
  have hk : kb {3} 3 = 1 := by decide
  apply Polynomial.funext
  intro r
  unfold secular
  rw [hB]
  simp [hk]
  ring

-- R3. `IsSecular`: for T(3), R(t) = t - 4: θ = ±2 are secular, θ = 1 is not (false instance).
example : IsSecular {3} 2 := by
  unfold IsSecular
  rw [rv_secular3]
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  norm_num
example : IsSecular {3} (-2) := by
  unfold IsSecular
  rw [rv_secular3]
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  norm_num
example : ¬ IsSecular {3} 1 := by
  unfold IsSecular
  rw [rv_secular3]
  simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C]
  norm_num

-- R6. `R2 {3} = x² - 4`.
theorem rv_R2_3 : R2 {3} = X ^ 2 - C 4 := by
  unfold R2
  rw [rv_secular3]
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sub,
    Polynomial.expand_X, Polynomial.expand_C]
  norm_num

-- R7. `x - 2` is an orbit factor of T(3), and it is not even: an integer pair.
theorem rv_orbit3 : IsOrbitFactor {3} (X - C 2) := by
  refine ⟨Polynomial.monic_X_sub_C 2,
    Polynomial.irreducible_of_degree_eq_one (Polynomial.degree_X_sub_C 2), ?_⟩
  rw [rv_R2_3]
  refine ⟨X + C 2, ?_⟩
  rw [show (C 4 : ℚ[X]) = C 2 * C 2 by rw [← C_mul]; norm_num]
  ring
theorem rv_noneven3 : ¬ IsEvenPoly (X - C (2 : ℚ)) := by
  unfold IsEvenPoly
  intro h
  have := congrArg (Polynomial.eval (1 : ℚ)) h
  simp at this
  norm_num at this
-- R8. hence `{x - 2, x + 2}` is a non-even pair of T(3) (it has degree 1: counted by `NI`).
example : ({X - C 2, BackfillPaper8.Challenge.mirror (X - C 2)} : Set ℚ[X]) ∈ nonEvenPairs {3} :=
  ⟨X - C 2, rv_orbit3, rv_noneven3, rfl⟩
-- R9. FALSE instance: `x - 3` is not an orbit factor of T(3) (3 is not a root of x² - 4).
example : ¬ IsOrbitFactor {3} (X - C 3) := by
  rintro ⟨-, -, hd⟩
  rw [rv_R2_3] at hd
  have := Polynomial.eval_dvd (x := (3 : ℚ)) hd
  simp at this
  norm_num at this
