import Mathlib

/-! Scalar arithmetic only. All numerical inequalities are explicit helper
premises; the original-graph theorem derives each one from its real witnesses. -/
set_option autoImplicit false
noncomputable section

namespace Paper7IntroLeafDegreeCandidates

theorem pure_leaf_star_scalar_candidate_reduction
    (m d n : ℕ) (hm1 : 1 ≤ m) (hm7 : m ≤ 7) (hm2 : m ≠ 2)
    (hd3 : 3 ≤ d) (hn : n ≤ 21)
    (hQ : 0 ≤ (m : ℝ) * (36 - 35 * (m : ℝ) + 12 * (m : ℝ) ^ 2 -
      (m : ℝ) ^ 3 - (m : ℝ) * (d : ℝ)))
    (hP : 0 ≤ (d : ℝ) + (m : ℝ) ^ 2 - 11 * (m : ℝ) + 23)
    (hlower : (d : ℝ) ^ 2 + (m : ℝ) + 2 ≤
      (14 - 2 * (m : ℝ)) * (d : ℝ) - (m : ℝ) ^ 3 +
        11 * (m : ℝ) ^ 2 - 21 * (m : ℝ) - 13)
    (hupper : (14 - 2 * (m : ℝ)) * (d : ℝ) - (m : ℝ) ^ 3 +
      11 * (m : ℝ) ^ 2 - 21 * (m : ℝ) - 13 + (d : ℝ) + 1 ≤
        (d : ℝ) ^ 2 + (n : ℝ) + 3) :
    m = 1 ∨ (m = 3 ∧ (d = 3 ∨ d = 4)) ∨ (m = 4 ∧ d = 6) ∨
      (m = 5 ∧ d = 7) ∨ (m = 7 ∧ d = 5) := by
  have hm : m = 1 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 := by omega
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · have hd4 : d ≤ 4 := by
      have h : (d : ℝ) ≤ 4 := by norm_num at hQ; nlinarith only [hQ]
      exact_mod_cast h
    exact Or.inr (Or.inl ⟨rfl, by omega⟩)
  · have hd5 : 5 ≤ d := by
      have h : (5 : ℝ) ≤ d := by norm_num at hP; nlinarith only [hP]
      exact_mod_cast h
    have hd6 : d ≤ 6 := by
      have h : (d : ℝ) ≤ 6 := by norm_num at hQ; nlinarith only [hQ]
      exact_mod_cast h
    have hd : d = 5 ∨ d = 6 := by omega
    rcases hd with rfl | rfl
    · exfalso
      have hnR : (n : ℝ) ≤ 21 := by exact_mod_cast hn
      norm_num at hupper
      nlinarith only [hupper, hnR]
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  · have hd7 : 7 ≤ d := by
      have h : (7 : ℝ) ≤ d := by norm_num at hP; nlinarith only [hP]
      exact_mod_cast h
    have hd8 : d < 8 := by
      have h : (d : ℝ) < 8 := by norm_num at hQ; nlinarith only [hQ]
      exact_mod_cast h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, by omega⟩)))
  · have hd7 : 7 ≤ d := by
      have h : (7 : ℝ) ≤ d := by norm_num at hP; nlinarith only [hP]
      exact_mod_cast h
    have hd7' : d ≤ 7 := by
      have h : (d : ℝ) ≤ 7 := by norm_num at hQ; nlinarith only [hQ]
      exact_mod_cast h
    have hd : d = 7 := by omega
    subst d
    norm_num at hlower
  · have hd5 : 5 ≤ d := by
      have h : (5 : ℝ) ≤ d := by norm_num at hP; nlinarith only [hP]
      exact_mod_cast h
    have hd6 : d < 6 := by
      have h : (d : ℝ) < 6 := by norm_num at hQ; nlinarith only [hQ]
      exact_mod_cast h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by omega⟩)))
#print axioms Paper7IntroLeafDegreeCandidates.pure_leaf_star_scalar_candidate_reduction

end Paper7IntroLeafDegreeCandidates
