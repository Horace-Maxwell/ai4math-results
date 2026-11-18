import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Tactic

/-!
Rotation facts for an arbitrary number of colors. The proofs use the actual
cycle support and order APIs; no bounded table or finite enumeration occurs.
-/

set_option autoImplicit false

namespace TaskH.General

variable {k : ℕ}

/-- The successor rotation has order equal to the number of colors. -/
theorem rotate_order (hk : 3 ≤ k) : orderOf (finRotate k) = k := by
  classical
  rw [(isCycle_finRotate_of_le (by omega : 2 ≤ k)).orderOf,
    support_finRotate_of_le (by omega : 2 ≤ k), Finset.card_univ, Fintype.card_fin]

theorem rotate_kth_power (hk : 3 ≤ k) : (finRotate k) ^ k = 1 := by
  simpa only [rotate_order hk] using pow_orderOf_eq_one (finRotate k)

theorem rotate_no_fixed (hk : 3 ≤ k) (a : Fin k) : finRotate k a ≠ a := by
  apply Equiv.Perm.mem_support.mp
  rw [support_finRotate_of_le (by omega : 2 ≤ k)]
  exact Finset.mem_univ a

/-- A rotation power fixes any color exactly at multiples of k. -/
theorem rotate_pow_fixed_iff (hk : 3 ≤ k) (a : Fin k) (n : ℕ) :
    ((finRotate k) ^ n) a = a ↔ k ∣ n := by
  have hf := isCycle_finRotate_of_le (by omega : 2 ≤ k)
  rw [← hf.pow_eq_one_iff' (rotate_no_fixed hk a),
    ← orderOf_dvd_iff_pow_eq_one, rotate_order hk]

theorem rotate_no_two_step (hk : 3 ≤ k) (a : Fin k) :
    finRotate k (finRotate k a) ≠ a := by
  intro h
  have hfix : ((finRotate k) ^ 2) a = a := by
    simpa only [pow_two, Equiv.Perm.mul_apply] using h
  have hd : k ∣ 2 := (rotate_pow_fixed_iff hk a 2).mp hfix
  have hle : k ≤ 2 := Nat.le_of_dvd (by omega : 0 < 2) hd
  omega

theorem rotate_small_fixed_iff (hk : 3 ≤ k) (a r : Fin k) :
    ((finRotate k) ^ r.val) a = a ↔ r.val = 0 := by
  rw [rotate_pow_fixed_iff hk]
  constructor
  · intro hd
    have hr := r.isLt
    by_contra hn
    have hle := Nat.le_of_dvd (by omega : 0 < r.val) hd
    omega
  · intro hz
    rw [hz]
    exact dvd_zero k

/-- Every color occurs in the first k terms of every rotation orbit. -/
theorem rotate_orbit_surjective (hk : 3 ≤ k) (a : Fin k) :
    Function.Surjective (fun i : Fin k => ((finRotate k) ^ i.val) a) := by
  intro b
  obtain ⟨n, hn⟩ := (isCycle_finRotate_of_le (by omega : 2 ≤ k)).exists_pow_eq
    (rotate_no_fixed hk a) (rotate_no_fixed hk b)
  refine ⟨⟨n % k, Nat.mod_lt _ (by omega : 0 < k)⟩, ?_⟩
  have hp : (finRotate k) ^ (n % k) = (finRotate k) ^ n := by
    simpa only [rotate_order hk] using pow_mod_orderOf (finRotate k) n
  exact (congrArg (fun σ : Equiv.Perm (Fin k) => σ a) hp).trans hn

end TaskH.General

#print axioms TaskH.General.rotate_order
#print axioms TaskH.General.rotate_kth_power
#print axioms TaskH.General.rotate_no_fixed
#print axioms TaskH.General.rotate_pow_fixed_iff
#print axioms TaskH.General.rotate_no_two_step
#print axioms TaskH.General.rotate_small_fixed_iff
#print axioms TaskH.General.rotate_orbit_surjective
