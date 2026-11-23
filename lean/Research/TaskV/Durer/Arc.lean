import Research.TaskV.Durer.Challenge
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace DurerDV

open scoped BigOperators

private def clipped (f : Profile) (j : ℕ) (t : ℝ) : ℝ :=
  min (f.knot (j+1)) (max (f.knot j) t) - f.knot j

private theorem knots_le (f : Profile) {a b : ℕ} (hab : a ≤ b) (hb : b ≤ f.count) :
    f.knot a ≤ f.knot b := by
  rcases lt_or_eq_of_le hab with h | rfl
  · exact (f.increasing _ _ h hb).le
  · rfl

private theorem clipped_on (f : Profile) {i : ℕ} {t : ℝ} (h : piece f i t) :
    clipped f i t = t - f.knot i := by
  simp [clipped, max_eq_right h.2.1, min_eq_right h.2.2]

private theorem clipped_off (f : Profile) {i j : ℕ} {x y : ℝ}
    (hx : piece f i x) (hy : piece f i y) (hj : j < f.count) (hne : j ≠ i) :
    clipped f j x = clipped f j y := by
  rcases lt_or_gt_of_ne hne with h | h
  · have he : f.knot (j+1) ≤ f.knot i := knots_le f h hx.1.le
    have h1 := he.trans hx.2.1
    have h2 := he.trans hy.2.1
    simp only [clipped, min_eq_left (h1.trans (le_max_right _ _)),
      min_eq_left (h2.trans (le_max_right _ _))]
  · have he : f.knot (i+1) ≤ f.knot j := knots_le f h hj.le
    simp only [clipped, max_eq_left (hx.2.2.trans he), max_eq_left (hy.2.2.trans he)]

theorem existsArc (s : Solid) (f : Profile) : ∃ u, arcValid s f u := by
  let base : ℝ := Real.sqrt (1-s.c^2)
  let extra : ℕ → ℝ := fun i => Real.sqrt (1+f.slope i^2-s.c^2) - base
  have hc : 0 < 1 - s.c^2 := by
    have h1 := s.c_min
    have h2 := s.c_max
    nlinarith [mul_pos (show 0 < 1+s.c by linarith) (show 0 < 1-s.c by linarith)]
  have hb : 0 < base := Real.sqrt_pos.2 hc
  have hpos (i : ℕ) : 0 ≤ extra i := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (f.slope i)]
  refine ⟨fun t => base*t + ∑ j ∈ Finset.range f.count, extra j * clipped f j t, ?_, ?_, ?_⟩
  · change base*0 + (∑ j ∈ Finset.range f.count, extra j * clipped f j 0) = 0
    rw [mul_zero, zero_add]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have hk : 0 ≤ f.knot j := f.first ▸ knots_le f (Nat.zero_le _) hj'.le
    have hnext := knots_le f (Nat.le_succ j) hj'
    simp [clipped, max_eq_left hk, min_eq_right hnext]
  · intro x _ y _ hxy
    apply add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left hxy hb)
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_left _ (hpos j)
    exact sub_le_sub_right (min_le_min_left _ (max_le_max_left _ hxy.le)) _
  · intro i x y hx hy
    have he : (∑ j ∈ Finset.range f.count, (extra j * clipped f j x - extra j * clipped f j y)) =
        extra i * (x-y) := by
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_range.mpr hx.1)]
      · rw [clipped_on f hx, clipped_on f hy]; ring
      · intro j hj hne
        rw [clipped_off f hx hy (Finset.mem_range.mp hj) hne, sub_self]
    rw [Finset.sum_sub_distrib] at he
    change base*x + _ - (base*y + _) = _
    dsimp only [extra] at he
    linarith only [he, show base*x - base*y +
        (Real.sqrt (1+f.slope i^2-s.c^2)-base)*(x-y) =
        Real.sqrt (1+f.slope i^2-s.c^2)*(x-y) by ring]

end DurerDV
