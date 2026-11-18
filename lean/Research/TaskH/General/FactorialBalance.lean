import Research.TaskH.Challenge
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace TaskH.General

/-- The original denominator divides the original factorial for all k>=3. -/
theorem two_mul_dvd_succ_factorial {k : ℕ} (hk : 3 ≤ k) :
    2 * k ∣ (k + 1).factorial := by
  have ht : 2 ∣ (k - 1).factorial := by
    simpa only [Nat.factorial_two] using
      (Nat.factorial_dvd_factorial (show 2 ≤ k - 1 by omega))
  obtain ⟨r, hr⟩ := ht
  have he : k - 1 + 1 = k := by omega
  have hf := Nat.factorial_succ (k - 1)
  rw [he] at hf
  refine ⟨(k + 1) * r, ?_⟩
  rw [Nat.factorial_succ, hf, hr]
  ring

/-- Exact balance for full S_k orders and the original unrounded bound. -/
theorem original_bound_balance {k : ℕ} (hk : 3 ≤ k) :
    k.factorial * (k + 1) = _root_.TaskH.Challenge.bound k * (2 * k) := by
  rw [_root_.TaskH.Challenge.bound, Nat.div_mul_cancel (two_mul_dvd_succ_factorial hk),
    Nat.factorial_succ]
  exact Nat.mul_comm _ _

end TaskH.General

#print axioms TaskH.General.two_mul_dvd_succ_factorial
#print axioms TaskH.General.original_bound_balance
