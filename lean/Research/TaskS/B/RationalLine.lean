import Mathlib

open scoped BigOperators
namespace TaskS.B.Rounding

theorem integer_direction {ι : Type*} [Fintype ι] (K : Submodule ℚ (ι → ℚ))
    (q : K) (hq : ∀ j, 0 < q.val j) :
    ∃ w : ι → ℕ, (∀ j, 0 < w j) ∧ (fun j => (w j : ℚ)) ∈ K := by
  classical
  let A : Matrix (Fin 1) ι ℚ := fun _ j => q.val j
  have hd : 0 < (A.den : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero A.den_ne_zero
  have hm (j : ι) : (A.num 0 j : ℚ) = (A.den : ℚ) * q.val j := by
    rw [mul_comm]
    exact (div_eq_iff hd.ne').mp (A.num_div_den 0 j)
  have hp (j : ι) : 0 < A.num 0 j := by
    exact_mod_cast (hm j ▸ mul_pos hd (hq j) : 0 < (A.num 0 j : ℚ))
  refine ⟨fun j => (A.num 0 j).toNat, fun j => Int.pos_iff_toNat_pos.mp (hp j), ?_⟩
  convert K.smul_mem (A.den : ℚ) q.property using 1
  funext j
  change ((A.num 0 j).toNat : ℚ) = (A.den : ℚ) * q.val j
  rw [← hm j, ← Int.cast_natCast, Int.toNat_of_nonneg (hp j).le]

end TaskS.B.Rounding
