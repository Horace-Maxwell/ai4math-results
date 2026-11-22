import Research.TaskU.H5.SmallMultiples

namespace TaskU.H5.SmallMultiples
open Finset

/-- Cancel the compulsory powers before applying any size bound. -/
theorem cancel_baseline (m a e d : ℤ) (u : ZMod 5 → ℤ)
    (he : 5^28*m = (5*a) * (25*e) * (∏ j, 5*u j) * (625*d)^5) :
    m = a*e*(∏ j, u j)*d^5 := by
  simp only [prod_mul_distrib, prod_const, card_univ, ZMod.card] at he
  apply mul_left_cancel₀ (show (5:ℤ)^28 ≠ 0 by decide)
  rw [he]
  ring

theorem each_dvd (m a e d : ℤ) (u : ZMod 5 → ℤ)
    (h : m = a*e*(∏ j, u j)*d^5) (j : ZMod 5) : u j ∣ m := by
  rw [h]
  apply dvd_mul_of_dvd_left
  apply dvd_mul_of_dvd_right
  exact dvd_prod_of_mem u (mem_univ j)

/-- A quartic norm that is a divisor of a cofactor from 1 through 10, is
1 modulo 5, and has the inert-prime divisibilities at 2 and 3, equals 1.
This test includes negative divisors. -/
theorem small_signed_unit (m n : ℤ) (hm : 1 ≤ m) (hm' : m ≤ 10) (hn : n ∣ m)
    (hr : (n : ZMod 5) = 1) (h2 : 2 ∣ n → 16 ∣ n) (h3 : 3 ∣ n → 81 ∣ n) :
    n = 1 := by
  have nu := Int.le_of_dvd (show 0 < m by omega) hn
  have nl := Int.le_of_dvd (show 0 < m by omega) (show -n ∣ m from neg_dvd.mpr hn)
  have hn' : n ≤ 10 := by omega
  have hn'' : -10 ≤ n := by omega
  have no2 : ¬ (2:ℤ) ∣ n := by
    intro h
    have := Int.le_of_dvd (show 0<m by omega) ((h2 h).trans hn)
    omega
  have no3 : ¬ (3:ℤ) ∣ n := by
    intro h
    have := Int.le_of_dvd (show 0<m by omega) ((h3 h).trans hn)
    omega
  interval_cases n <;> first
    | rfl
    | exact (no2 (by decide)).elim
    | exact (no3 (by decide)).elim
    | exact (absurd hr (by decide))

end TaskU.H5.SmallMultiples
