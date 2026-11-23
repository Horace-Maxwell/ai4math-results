import Research.TaskV.FEI.Challenge

namespace Fei
open Finset

/-- Peeling off the least weight proves the finite superlevel summation inequality. -/
theorem upper_layer_sum {α : Type*} [DecidableEq α] (s : Finset α) (a g : α → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i)
    (h : ∀ r : ℝ, 0 < r → ∑ i ∈ s.filter (fun i => r ≤ a i), g i ≤ 0) :
    ∑ i ∈ s, a i * g i ≤ 0 := by
  classical
  induction s using Finset.strongInductionOn generalizing a with
  | _ s ih =>
    by_cases hs : s.Nonempty
    · obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image s a hs
      have hbase : a j * (∑ i ∈ s, g i) ≤ 0 := by
        rcases (ha j hj).eq_or_lt with hz | hp
        · rw [← hz, zero_mul]
        · have hh := h (a j) hp
          rw [Finset.filter_eq_self.mpr hmin] at hh
          exact mul_nonpos_of_nonneg_of_nonpos hp.le hh
      let a' (i : α) := a i - a j
      have ha' (i) (hi : i ∈ s.erase j) : 0 ≤ a' i :=
        sub_nonneg.mpr (hmin i (Finset.mem_of_mem_erase hi))
      have h' (r : ℝ) (hr : 0 < r) : ∑ i ∈ (s.erase j).filter (fun i => r ≤ a' i), g i ≤ 0 := by
        have he : (s.erase j).filter (fun i => r ≤ a' i) =
            s.filter (fun i => r + a j ≤ a i) := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_erase, a']
          constructor
          · rintro ⟨⟨_, hi⟩, hi'⟩
            exact ⟨hi, by linarith⟩
          · rintro ⟨hi, hi'⟩
            refine ⟨⟨?_, hi⟩, by linarith⟩
            rintro rfl
            linarith
        rw [he]
        exact h _ (add_pos_of_pos_of_nonneg hr (ha j hj))
      have hrec := ih (s.erase j) (Finset.erase_ssubset hj) a' ha' h'
      have hfull : ∑ i ∈ s, a' i * g i ≤ 0 := by
        rw [← Finset.sum_erase_add _ _ hj]
        simpa [a'] using hrec
      calc
        _ = ∑ i ∈ s, (a' i * g i + a j * g i) := by
          apply Finset.sum_congr rfl
          intro i _
          dsimp [a']
          ring
        _ = (∑ i ∈ s, a' i * g i) + a j * (∑ i ∈ s, g i) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
        _ ≤ 0 := add_nonpos hfull hbase
    · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
      simp

end Fei
