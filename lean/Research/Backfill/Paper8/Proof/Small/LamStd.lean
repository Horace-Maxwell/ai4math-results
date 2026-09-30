import Research.Backfill.Paper8.Proof.Small.Setup

/-!
# Paper 8, Proposition 5.1: the standard leaf sums on branches of size one

For `i ∈ I₁`, `posIn a i = 0` iff `i` is the minimum of `I₁`; hence, when `k₁ ≥ 2`, `λ°_i = 1`
for the minimum and `λ°_i = -1` for the other `i ∈ I₁`, and `λ°_i = -1` for all `i ∈ I₁` when
`k₁ ≤ 1`. Consequently `Λ°₁ = ∑_{i∈I₁} λ°_i` is `2 - k₁` if `k₁ ≥ 2` and `-k₁` otherwise.
-/

set_option autoImplicit false

open BackfillPaper8.Challenge

namespace P8Small

variable {k : ℕ} (a : Fin k → ℕ)

theorem lamStd_of_one {i : Fin k} (hi : a i = 1) :
    lamStd a i = if posIn a i = 0 ∧ 2 ≤ kb (branchMS a) 1 then 1 else -1 := by
  simp [lamStd, hi]

theorem posIn_eq_zero_iff (i : Fin k) : posIn a i = 0 ↔ ∀ j, a j = a i → i ≤ j := by
  rw [posIn, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h j hj
    by_contra hlt
    exact h (Finset.mem_univ j) ⟨lt_of_not_ge hlt, hj⟩
  · rintro h j - ⟨hlt, hj⟩
    exact absurd (h j hj) (not_le_of_gt hlt)

/-- In `I₁`, exactly the minimum has `posIn = 0`. -/
theorem posIn_eq_zero_iff_min (hne : (Ib a 1).Nonempty) {i : Fin k} (hi : i ∈ Ib a 1) :
    posIn a i = 0 ↔ i = (Ib a 1).min' hne := by
  rw [posIn_eq_zero_iff]
  have hai : a i = 1 := (mem_Ib a).1 hi
  constructor
  · intro h
    apply le_antisymm
    · apply h
      rw [hai]
      exact (mem_Ib a).1 (Finset.min'_mem _ hne)
    · exact Finset.min'_le _ _ hi
  · intro h j hj
    rw [h]
    rw [hai] at hj
    exact Finset.min'_le _ _ ((mem_Ib a).2 hj)

theorem lamStd_I1_big (hne : (Ib a 1).Nonempty) (h2 : 2 ≤ kb (branchMS a) 1) {i : Fin k}
    (hi : i ∈ Ib a 1) : (lamStd a i : ℝ) = if i = (Ib a 1).min' hne then 1 else -1 := by
  rw [lamStd_of_one a ((mem_Ib a).1 hi)]
  have key := posIn_eq_zero_iff_min a hne hi
  split_ifs with h1 h3 h3
  · simp
  · exact absurd (key.1 h1.1) h3
  · exact absurd ⟨key.2 h3, h2⟩ h1
  · simp

theorem lamStd_I1_small (h2 : kb (branchMS a) 1 < 2) {i : Fin k} (hi : i ∈ Ib a 1) :
    (lamStd a i : ℝ) = -1 := by
  rw [lamStd_of_one a ((mem_Ib a).1 hi)]
  have h2' : ¬ 2 ≤ kb (branchMS a) 1 := by omega
  simp [h2']

/-- `Λ°₁ = 2 - k₁` if `k₁ ≥ 2`, and `-k₁` otherwise. -/
theorem sum_lamStd_I1 :
    ∑ i ∈ Ib a 1, (lamStd a i : ℝ) =
      if 2 ≤ kb (branchMS a) 1 then 2 - (kb (branchMS a) 1 : ℝ)
      else -(kb (branchMS a) 1 : ℝ) := by
  split_ifs with h2
  · have hne : (Ib a 1).Nonempty := by
      rw [← Finset.card_pos, ← kb_eq]
      omega
    rw [Finset.sum_congr rfl (fun i hi => lamStd_I1_big a hne h2 hi)]
    have h : ∀ i, (if i = (Ib a 1).min' hne then (1 : ℝ) else -1) =
        -(if i = (Ib a 1).min' hne then (-1 : ℝ) else 1) := by
      intro i
      split_ifs <;> norm_num
    rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_neg_distrib, sum_sign_eq, kb_eq]
    simp only [Finset.min'_mem, ite_true]
    ring
  · rw [Finset.sum_congr rfl (fun i hi => lamStd_I1_small a (by omega) hi)]
    simp [kb_eq]

/-- For `k₁ ≥ 2` the minimum of `I₁` has `λ° = 1` and every other `i ∈ I₁` has `λ° = -1`. -/
theorem exists_lamStd_I1 (h2 : 2 ≤ kb (branchMS a) 1) :
    ∃ i ∈ Ib a 1, ∃ i' ∈ Ib a 1, (lamStd a i : ℝ) = 1 ∧ (lamStd a i' : ℝ) = -1 := by
  have hne : (Ib a 1).Nonempty := by
    rw [← Finset.card_pos, ← kb_eq]
    omega
  have h1 : 1 < (Ib a 1).card := by rw [← kb_eq]; omega
  obtain ⟨i', hi', hne'⟩ := Finset.exists_mem_ne h1 ((Ib a 1).min' hne)
  refine ⟨_, Finset.min'_mem _ hne, i', hi', ?_, ?_⟩
  · rw [lamStd_I1_big a hne h2 (Finset.min'_mem _ hne)]
    simp
  · rw [lamStd_I1_big a hne h2 hi']
    simp [hne']

theorem lamStd_pm {i : Fin k} (hi : a i = 1) : (lamStd a i : ℝ) = 1 ∨ (lamStd a i : ℝ) = -1 := by
  rw [lamStd_of_one a hi]
  split_ifs <;> simp

end P8Small
