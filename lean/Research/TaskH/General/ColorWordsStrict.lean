import Research.TaskH.ColorWordsStrict
import Research.TaskH.General.ColorCycle

/-!
Tight endpoint capacity forces the actual successor rotation, for every
number of colors. Shared generic descent/capacity/tight-step machinery is
imported unchanged. The whole-word orbit is proved by natural induction.
-/

set_option autoImplicit false

namespace TaskH.General.ColorWords

open _root_.TaskH.ColorWords

variable {k : ℕ}

/-- The tight scalar step is exactly the genuine Fin successor rotation. -/
theorem step_eq_rotate (x y : Fin k)
    (he : 1 + x.val = y.val + k * (if y < x then 1 else 0)) :
    y = finRotate k x := by
  cases k with
  | zero => exact x.elim0
  | succ n =>
    apply Fin.ext
    rw [coe_finRotate]
    have hx := x.isLt
    have hy := y.isLt
    by_cases hd : y < x
    · simp only [ite_eq_left hd, Nat.mul_one] at he
      have hy0 : y.val = 0 := by omega
      have hlast : x = Fin.last n := by
        apply Fin.ext
        simp only [Fin.val_last]
        omega
      rw [ite_eq_left hlast]
      exact hy0
    · simp only [ite_eq_right hd, Nat.mul_zero, Nat.add_zero] at he
      have hlast : x ≠ Fin.last n := by
        intro hh
        have hv := congrArg Fin.val hh
        simp only [Fin.val_last] at hv
        omega
      rw [ite_eq_right hlast]
      omega

theorem tight_step_rotate (w : ℕ → Fin k) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + k * descents w L)
    (j : ℕ) (hj : j < L) : w (j + 1) = finRotate k (w j) := by
  exact step_eq_rotate (w j) (w (j + 1))
    (_root_.TaskH.ColorWords.tight_step w L hne htight j hj)

/-- Every actual prefix entry is the corresponding rotation power. -/
theorem tight_word_get (w : ℕ → Fin k) (L : ℕ)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + k * descents w L) :
    ∀ n : ℕ, n ≤ L → w n = ((finRotate k) ^ n) (w 0) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [tight_step_rotate w L hne htight n (by omega), ih (by omega), pow_succ']
    rfl

/-- Tightness proves coverage of every color in the first k actual entries. -/
theorem tight_prefix_surjective (hk : 3 ≤ k) (w : ℕ → Fin k) (L : ℕ)
    (hkL : k ≤ L)
    (hne : ∀ i : ℕ, i < L → w i ≠ w (i + 1))
    (htight : L + (w 0).val = (w L).val + k * descents w L) :
    Function.Surjective (fun i : Fin k => w i.val) := by
  intro z
  obtain ⟨i, hi⟩ := _root_.TaskH.General.rotate_orbit_surjective hk (w 0) z
  refine ⟨i, ?_⟩
  have hiL : i.val ≤ L := by have := i.isLt; omega
  exact (tight_word_get w L hne htight i.val hiL).trans hi

end TaskH.General.ColorWords

#print axioms TaskH.General.ColorWords.step_eq_rotate
#print axioms TaskH.General.ColorWords.tight_step_rotate
#print axioms TaskH.General.ColorWords.tight_word_get
#print axioms TaskH.General.ColorWords.tight_prefix_surjective
