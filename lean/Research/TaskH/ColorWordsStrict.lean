import Research.TaskH.ColorWordsCount

/-!
Equality in the word-capacity inequality, for the strict multiplicity step.
The tight-step lemma is generic. The following concrete prefix is the k=4
instance needed when the missing prefix color is placed first.
-/

set_option autoImplicit false

namespace TaskH.ColorWords

variable {k : ℕ}

/-- Equality in the global endpoint capacity forces equality at every step. -/
theorem tight_step (w : ℕ → Fin k) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + k * descents w L)
    (j : ℕ) (hj : j < L) :
    1 + (w j).val = (w (j + 1)).val +
      k * (if w (j + 1) < w j then 1 else 0) := by
  have hp := endpoint_capacity w j (fun i hi => hne i (by omega))
  have hs := endpoint_capacity (fun i => w (j + 1 + i)) (L - (j + 1))
    (fun i hi => hne (j + 1 + i) (by omega))
  have hadd : j + 1 + (L - (j + 1)) = L := by omega
  simp only [Nat.add_zero, hadd] at hs
  have hc := descents_add w (j + 1) (L - (j + 1))
  rw [hadd, descents_succ] at hc
  have hcmul := congrArg (fun n : ℕ => k * n) hc
  simp only [Nat.mul_add] at hcmul
  have hlocal := endpoint_capacity (fun i => w (j + i)) 1 (by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simpa using hne j hj)
  simp only [Nat.add_zero, descents_succ, descents_zero, zero_add] at hlocal
  omega

/-- In the extremal k=4 length, placing a missing color first makes the
endpoint capacity tight. The first word color is therefore rank 1. -/
theorem four_tight_of_first_ne_zero (w : ℕ → Fin 4) (L b : ℕ)
    (hlen : L + 2 = 4 * (b + 1))
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : w 0 ≠ 0) :
    (w 0).val = 1 ∧ descents w L = b ∧ (w L).val = 3 ∧
      L + (w 0).val = (w L).val + 4 * descents w L := by
  have he := endpoint_capacity w L hne
  have hb := (w L).isLt
  have hz : (w 0).val ≠ 0 := by
    intro hh
    apply hfirst
    exact Fin.ext hh
  omega

/-- The first five ranks are forced to be 1,2,3,0,1 for a long tight word. -/
theorem four_tight_prefix (w : ℕ → Fin 4) (L b : ℕ)
    (hlen : L + 2 = 4 * (b + 1)) (hb : 1 ≤ b)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (hcount : descents w L ≤ b) (hfirst : w 0 ≠ 0) :
    (w 0).val = 1 ∧ (w 1).val = 2 ∧ (w 2).val = 3 ∧
      (w 3).val = 0 ∧ (w 4).val = 1 := by
  obtain ⟨h0, _, _, htight⟩ := four_tight_of_first_ne_zero w L b hlen hne hcount hfirst
  have h1 : (w 1).val = 2 := by
    have hs := tight_step w L hne htight 0 (by omega)
    have hh := (w 1).isLt
    change 1 + (w 0).val = (w 1).val +
      4 * (if (w 1).val < (w 0).val then 1 else 0) at hs
    rw [h0] at hs
    split_ifs at hs <;> omega
  have h2 : (w 2).val = 3 := by
    have hs := tight_step w L hne htight 1 (by omega)
    have hh := (w 2).isLt
    change 1 + (w 1).val = (w 2).val +
      4 * (if (w 2).val < (w 1).val then 1 else 0) at hs
    rw [h1] at hs
    split_ifs at hs <;> omega
  have h3 : (w 3).val = 0 := by
    have hs := tight_step w L hne htight 2 (by omega)
    have hh := (w 3).isLt
    change 1 + (w 2).val = (w 3).val +
      4 * (if (w 3).val < (w 2).val then 1 else 0) at hs
    rw [h2] at hs
    split_ifs at hs <;> omega
  have h4 : (w 4).val = 1 := by
    have hs := tight_step w L hne htight 3 (by omega)
    have hh := (w 4).isLt
    change 1 + (w 3).val = (w 4).val +
      4 * (if (w 4).val < (w 3).val then 1 else 0) at hs
    rw [h3] at hs
    split_ifs at hs <;> omega
  exact ⟨h0, h1, h2, h3, h4⟩

/-- A tight k=4 word cannot have the opposite transition 1→0. -/
theorem four_tight_no_one_zero (w : ℕ → Fin 4) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + 4 * descents w L) :
    ∀ j : ℕ, j < L → ¬ (w j = 1 ∧ w (j + 1) = 0) := by
  intro j hj hbad
  obtain ⟨h1, h0⟩ := hbad
  have hs := tight_step w L hne htight j hj
  rw [h1, h0] at hs
  norm_num at hs

end TaskH.ColorWords

#print axioms TaskH.ColorWords.tight_step
#print axioms TaskH.ColorWords.four_tight_of_first_ne_zero
#print axioms TaskH.ColorWords.four_tight_prefix
#print axioms TaskH.ColorWords.four_tight_no_one_zero
