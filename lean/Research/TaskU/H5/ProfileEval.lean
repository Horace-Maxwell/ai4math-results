import Research.TaskU.H5.Profile
import Research.TaskU.H5.CycEval

namespace TaskU.H5
noncomputable section
open Finset
open scoped BigOperators

theorem ch_nat (s : F) (n : ℕ) : ch (s*(n:F)) = (ch s)^n := by
  rw [← AddChar.map_nsmul_eq_pow]
  simp [nsmul_eq_mul, mul_comm]

theorem ch_two (s : F) : ch (s*2) = (ch s)^2 := by simpa only [Nat.cast_ofNat] using ch_nat s 2
theorem ch_three (s : F) : ch (s*3) = (ch s)^3 := by simpa only [Nat.cast_ofNat] using ch_nat s 3
theorem ch_four (s : F) : ch (s*4) = (ch s)^4 := by simpa only [Nat.cast_ofNat] using ch_nat s 4

theorem ch_four_rel (s : F) (hs : s ≠ 0) :
    1 + ch s + (ch s)^2 + (ch s)^3 + (ch s)^4 = 0 := by
  have h := orthog s
  rw [sum_five, ite_eq_right hs] at h
  norm_num only [mul_zero, mul_one, AddChar.map_zero_eq_one] at h
  simpa only [ch_two, ch_three, ch_four] using h

theorem evalProfile (p : F → ℤ) (s : F) (hs : s ≠ 0) :
    Cyc5.val (profile p) (ch s) = ∑ i, (p i:ℂ)*ch (s*i) := by
  rw [sum_five]
  simp only [Cyc5.val, profile, Int.cast_sub, mul_zero, mul_one, AddChar.map_zero_eq_one]
  have hc := ch_four_rel s hs
  simp only [ch_two, ch_three, ch_four]
  linear_combination -(p 4:ℂ)*hc

theorem prod_four {R : Type*} [CommMonoid R] (p : F → R) :
    ∏ i ∈ (Finset.univ : Finset F).erase 0, p i = p 1 * p 2 * p 3 * p 4 := by
  have he : (Finset.univ : Finset F).erase 0 = {1,2,3,4} := by decide
  rw [he]
  simp +decide [mul_assoc]

theorem norm_values (v : Cyc5.V) :
    (Cyc5.norm v : ℂ) = ∏ s ∈ (Finset.univ : Finset F).erase 0, Cyc5.val v (ch s) := by
  rw [prod_four, Cyc5.norm_embeddings _ _ Cyc5.zeta_rel]
  simp only [Cyc5.zeta_pow, Nat.cast_ofNat]
  rfl

end
end TaskU.H5
