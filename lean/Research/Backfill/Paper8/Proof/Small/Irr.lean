import Mathlib

/-!
# Paper 8, Proposition 5.1: irrational roots of integer quadratics

If `t² - m t + c = 0` with `m, c ∈ ℤ` and `m² - 4c` is not the square of an integer, then
`2t - m` is irrational (`irrational_nrt_of_notint_nrt`), so an integer linear relation
`p t + q = 0` forces `p = q = 0`. A number strictly between `(m - 2)²` and `m²` of the form
`m² - 4c` is not a square: it could only be `(m - 1)²`, which has the other parity.
-/

set_option autoImplicit false

namespace P8Small

theorem irrational_of_quadratic {t : ℝ} {m c : ℤ} (h : t ^ 2 - m * t + c = 0)
    (hns : ∀ y : ℤ, y ^ 2 ≠ m ^ 2 - 4 * c) : Irrational (2 * t - m) := by
  apply irrational_nrt_of_notint_nrt 2 (m ^ 2 - 4 * c)
  · push_cast
    linear_combination 4 * h
  · rintro ⟨y, hy⟩
    apply hns y
    have h2 : ((y : ℝ)) ^ 2 = (m : ℝ) ^ 2 - 4 * c := by
      rw [← hy]
      linear_combination 4 * h
    exact_mod_cast h2
  · norm_num

theorem eq_zero_of_irrational {x : ℝ} (hx : Irrational x) {p q : ℤ}
    (h : (p : ℝ) * x + q = 0) : p = 0 ∧ q = 0 := by
  by_cases hp : p = 0
  · subst hp
    refine ⟨rfl, ?_⟩
    have hq : (q : ℝ) = 0 := by simpa using h
    exact_mod_cast hq
  · exfalso
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    apply hx.ne_rational (-q) p
    field_simp
    push_cast
    linarith

/-- An integer linear relation `p t + q = 0` at a root `t` of `x² - m x + c` whose discriminant
is not a square is trivial. -/
theorem lin_rel_trivial {t : ℝ} {m c : ℤ} (h : t ^ 2 - m * t + c = 0)
    (hns : ∀ y : ℤ, y ^ 2 ≠ m ^ 2 - 4 * c) {p q : ℤ} (hl : (p : ℝ) * t + q = 0) :
    p = 0 ∧ q = 0 := by
  have hirr := irrational_of_quadratic h hns
  have h2 : (p : ℝ) * (2 * t - m) + ((2 * q + p * m : ℤ) : ℝ) = 0 := by
    push_cast
    linear_combination 2 * hl
  obtain ⟨hp, hq⟩ := eq_zero_of_irrational hirr h2
  subst hp
  exact ⟨rfl, by omega⟩

/-- `m² - 4c` is not a square if `(m - 2)² < m² - 4c` and `c > 0`. -/
theorem not_square_of_between {m c : ℤ} (hm : 2 ≤ m) (hc : 0 < c)
    (hlow : (m - 2) ^ 2 < m ^ 2 - 4 * c) : ∀ y : ℤ, y ^ 2 ≠ m ^ 2 - 4 * c := by
  intro y hy
  have h1 : |y| < m := abs_lt_of_sq_lt_sq (by rw [hy]; linarith) (by omega)
  have h2 : |m - 2| < |y| := sq_lt_sq.mp (hlow.trans_eq hy.symm)
  rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ m - 2)] at h2
  have h3 : |y| = m - 1 := by omega
  have h4 : (m - 1) ^ 2 = m ^ 2 - 4 * c := by rw [← h3, sq_abs, hy]
  have h5 : 2 * m - 1 = 4 * c := by linear_combination (-1 : ℤ) * h4
  omega

end P8Small
