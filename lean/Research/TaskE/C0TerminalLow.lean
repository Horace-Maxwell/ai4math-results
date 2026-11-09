import Research.TaskE.ChallengeC0
import Research.TaskE.FTail

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.FCProof
open Finset BackfillPaper1.Challenge

lemma repeat_before_terminal_impossible {a j : ℕ} (ha : 1 ≤ a)
    {g : ℕ → ℝ} (hg : IsSignVec a g) (hlast : g (a - 1) = g a)
    (hlow : DeltaC a 3 g ≤ 2 * deltaK a 3) (hj : j < a - 1) : g j ≠ g (j + 1) := by
  classical
  intro hjrep
  let w : ℕ → ℝ := fun l => mu 3 (l : ℤ) * |z 3 a g (l : ℤ)|
  have hw0 (l : ℕ) : 0 ≤ w l := by
    dsimp [w]
    exact mul_nonneg (by have hh := SProof.mu_lower (p := (3 : ℝ)) (by norm_num) l; linarith)
      (abs_nonneg _)
  have hjmem : j ∈ NA a g := mem_filter.mpr ⟨mem_range.mpr (by omega), hjrep⟩
  have hlastmem : a - 1 ∈ NA a g := by
    apply mem_filter.mpr
    refine ⟨mem_range.mpr (by omega), ?_⟩
    simpa only [Nat.sub_add_cancel ha] using hlast
  have hsubset : ({j, a - 1} : Finset ℕ) ⊆ NA a g := by
    intro l hl
    simp only [mem_insert, mem_singleton] at hl
    rcases hl with rfl | rfl
    · exact hjmem
    · exact hlastmem
  have hs : w j + w (a - 1) ≤ ∑ l ∈ NA a g, w l := by
    have he := sum_le_sum_of_subset_of_nonneg hsubset (fun l _hl _hl' => hw0 l)
    simpa only [sum_insert, mem_singleton, show j ≠ a - 1 by omega,
      not_false_eq_true, sum_singleton] using he
  have hjp : 0 < w j := by
    have hm := SProof.mu_lower (p := (3 : ℝ)) (by norm_num) j
    have hz := (SProof.path_bounds ha (j := j) (by omega) (by norm_num : (3 : ℝ) ≤ 3) hg).2.1
    dsimp [w]
    exact mul_pos (by norm_num at hm; linarith) (by norm_num at hz; linarith)
  have hga : |g a| = 1 := by rcases hg a le_rfl with h | h <;> norm_num [h]
  have he : (3 : ℝ) ^ a * w (a - 1) = deltaK a 3 := by
    dsimp [w]
    rw [z_end ha g, hga, mul_one, show ((a - 1 : ℕ) : ℤ) = (a : ℤ) - 1 by omega]
    exact CodexPaper1.ClosedForms.weighted_mu_eq_deltaK (by norm_num) a
  have hd := SProof.deficit_identity (by norm_num : (3 : ℝ) ≤ 3) hg
  change DeltaC a 3 g = 2 * (3 : ℝ) ^ a * (∑ l ∈ NA a g, w l) at hd
  have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * (3 : ℝ) ^ a by positivity)
  have hp := mul_pos (show 0 < (3 : ℝ) ^ a by positivity) hjp
  nlinarith

lemma terminal_low : CodexPaper1.TaskE.Challenge.TerminalLowThree := by
  intro a ha g hg hga hnot hlow hlast
  have ha1 : 1 ≤ a := by omega
  have hprev : g (a - 1) = -1 := hlast.trans hga
  have hn : ∀ j, j < a - 1 → g j ≠ g (j + 1) := by
    intro j hj
    exact repeat_before_terminal_impossible ha1 hg hlast hlow hj
  have hprefix : ∀ d, d ≤ a - 1 → g (a - 1 - d) = (-1 : ℝ) ^ d * g (a - 1) := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      have hidx : a - 1 - (d + 1) + 1 = a - 1 - d := by omega
      have hne := hn (a - 1 - (d + 1)) (by omega)
      rw [hidx] at hne
      have hsg : g (a - 1 - (d + 1)) = -g (a - 1 - d) := by
        rcases hg (a - 1 - (d + 1)) (by omega) with h | h <;>
          rcases hg (a - 1 - d) (by omega) with h' | h' <;> simp_all
      rw [hsg, ih (by omega), pow_succ]
      ring
  apply hnot
  intro i hi
  by_cases hia : i = a
  · subst i
    have hs : sAlt a * sAlt a = 1 := by
      rcases neg_one_pow_eq_or ℝ a with h | h <;> norm_num [sAlt, h]
    rw [gPlus, ite_eq_left rfl]
    change g a = sAlt a * sAlt a - 2
    rw [hga, hs]
    norm_num
  · have hia' : i < a := by omega
    let d := a - 1 - i
    have hidx : a - 1 - d = i := by dsimp [d]; omega
    have hd := hprefix d (by dsimp [d]; omega)
    rw [hidx, hprev] at hd
    have hs : sAlt i * sAlt i = 1 := by
      rcases neg_one_pow_eq_or ℝ i with h | h <;> norm_num [sAlt, h]
    have hsign : sAlt a = (-1 : ℝ) ^ d * (-1) * sAlt i := by
      have hsum : d + 1 + i = a := by dsimp [d]; omega
      simp only [sAlt]
      rw [← pow_succ, ← pow_add, hsum]
    rw [gPlus, ite_eq_right hia, sub_zero, hd]
    change (-1 : ℝ) ^ d * (-1) = sAlt a * sAlt i
    calc
      _ = ((-1 : ℝ) ^ d * (-1)) * (sAlt i * sAlt i) := by rw [hs, mul_one]
      _ = sAlt a * sAlt i := by rw [hsign]; ring

end CodexPaper1.TaskE.FCProof
#print axioms CodexPaper1.TaskE.FCProof.terminal_low
