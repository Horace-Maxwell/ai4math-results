import Research.TaskH.ColorWordsStrict

/-!
Seven-color equality in the generic endpoint capacity. No rainbow or
periodicity premise is assumed: the actual adjacent-unequal word forces
the eight initial entries needed by the strict multiplier proof.
-/

set_option autoImplicit false

namespace TaskH.Seven.ColorWords

open _root_.TaskH.ColorWords

theorem seven_tight_of_first_ne_zero (w : ℕ → Fin 7) (L b : ℕ)
    (hlen : L + 2 = 7 * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : w 0 ≠ 0) :
    (w 0).val = 1 ∧ descents w L = b ∧ (w L).val = 6 ∧
      L + (w 0).val = (w L).val + 7 * descents w L := by
  have he := endpoint_capacity w L hne
  have hb := (w L).isLt
  have hz : (w 0).val ≠ 0 := by
    intro hh
    apply hfirst
    exact Fin.ext hh
  omega

theorem seven_tight_prefix (w : ℕ → Fin 7) (L b : ℕ)
    (hlen : L + 2 = 7 * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : w 0 ≠ 0) :
    (w 0).val = 1 ∧ (w 1).val = 2 ∧ (w 2).val = 3 ∧ (w 3).val = 4 ∧ (w 4).val = 5 ∧ (w 5).val = 6 ∧ (w 6).val = 0 ∧ (w 7).val = 1 := by
  obtain ⟨h0, _, _, htight⟩ := seven_tight_of_first_ne_zero w L b hlen hne hcount hfirst
  have h1 : (w 1).val = 2 := by
    have hs := tight_step w L hne htight 0 (by omega)
    have hh := (w 1).isLt
    change 1 + (w 0).val = (w 1).val +
      7 * (if (w 1).val < (w 0).val then 1 else 0) at hs
    rw [h0] at hs
    split_ifs at hs <;> omega
  have h2 : (w 2).val = 3 := by
    have hs := tight_step w L hne htight 1 (by omega)
    have hh := (w 2).isLt
    change 1 + (w 1).val = (w 2).val +
      7 * (if (w 2).val < (w 1).val then 1 else 0) at hs
    rw [h1] at hs
    split_ifs at hs <;> omega
  have h3 : (w 3).val = 4 := by
    have hs := tight_step w L hne htight 2 (by omega)
    have hh := (w 3).isLt
    change 1 + (w 2).val = (w 3).val +
      7 * (if (w 3).val < (w 2).val then 1 else 0) at hs
    rw [h2] at hs
    split_ifs at hs <;> omega
  have h4 : (w 4).val = 5 := by
    have hs := tight_step w L hne htight 3 (by omega)
    have hh := (w 4).isLt
    change 1 + (w 3).val = (w 4).val +
      7 * (if (w 4).val < (w 3).val then 1 else 0) at hs
    rw [h3] at hs
    split_ifs at hs <;> omega
  have h5 : (w 5).val = 6 := by
    have hs := tight_step w L hne htight 4 (by omega)
    have hh := (w 5).isLt
    change 1 + (w 4).val = (w 5).val +
      7 * (if (w 5).val < (w 4).val then 1 else 0) at hs
    rw [h4] at hs
    split_ifs at hs <;> omega
  have h6 : (w 6).val = 0 := by
    have hs := tight_step w L hne htight 5 (by omega)
    have hh := (w 6).isLt
    change 1 + (w 5).val = (w 6).val +
      7 * (if (w 6).val < (w 5).val then 1 else 0) at hs
    rw [h5] at hs
    split_ifs at hs <;> omega
  have h7 : (w 7).val = 1 := by
    have hs := tight_step w L hne htight 6 (by omega)
    have hh := (w 7).isLt
    change 1 + (w 6).val = (w 7).val +
      7 * (if (w 7).val < (w 6).val then 1 else 0) at hs
    rw [h6] at hs
    split_ifs at hs <;> omega
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

theorem seven_tight_no_one_zero (w : ℕ → Fin 7) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + 7 * descents w L) :
    ∀ j : ℕ, j < L → ¬ (w j = 1 ∧ w (j + 1) = 0) := by
  intro j hj hbad
  obtain ⟨h1, h0⟩ := hbad
  have hs := tight_step w L hne htight j hj
  rw [h1, h0] at hs
  norm_num at hs

end TaskH.Seven.ColorWords

#print axioms TaskH.Seven.ColorWords.seven_tight_of_first_ne_zero
#print axioms TaskH.Seven.ColorWords.seven_tight_prefix
#print axioms TaskH.Seven.ColorWords.seven_tight_no_one_zero
