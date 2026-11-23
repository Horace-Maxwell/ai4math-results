import Research.TaskV.Illumination.Challenge
import Mathlib.Tactic

namespace PrismIllumination

def dx (e : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else if j = 1 then -1 else if j = 2 then e else -1

def dy (e : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then 1 else if j = 1 then e else if j = 2 then -1 else -1

def Step (x y a b : ℝ) : Prop :=
  ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 0 < x + t * a ∧ 0 < y + t * b ∧
    (x + t * a) + (y + t * b) < 1

private theorem towardsAxis {x y e : ℝ} (hx : 0 < x) (hX : x ≤ 1)
    (hy : 0 ≤ y) (he : 0 < e) (h : y + x * e < 1) : Step x y (-1) e := by
  obtain ⟨w, hw, hw'⟩ := exists_between (lt_min hx (sub_pos.mpr h))
  have hwx := lt_of_lt_of_le hw' (min_le_left _ _)
  have hwg := lt_of_lt_of_le hw' (min_le_right _ _)
  have ht : 0 < x-w := sub_pos.mpr hwx
  have hew := mul_pos hw he
  refine ⟨x-w, ht, by linarith, by linarith, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos hy (mul_pos ht he)
  · nlinarith

private theorem threeCore {x y e : ℝ} (hx : 0 ≤ x) (hX : x ≤ 1)
    (hy : 0 ≤ y) (hY : y ≤ 1) (he : 0 < e) (hE : e < 1)
    (h : y + x*e < 1 ∨ x + y*e < 1) :
    ∃ j : ℕ, j < 3 ∧ Step x y (dx e j) (dy e j) := by
  have flip (s : Step y x (-1) e) : Step x y e (-1) := by
    obtain ⟨t, ht, hT, a, b, c⟩ := s
    exact ⟨t, ht, hT, b, a, by linarith⟩
  by_cases h0 : x = 0
  · subst x
    by_cases h1 : y = 0
    · subst y
      refine ⟨0, by decide, 1/4, ?_⟩
      norm_num [dx, dy]
    · refine ⟨2, by decide, ?_⟩
      simpa [dx, dy] using flip (towardsAxis (lt_of_le_of_ne hy (Ne.symm h1)) hY
        le_rfl he (by nlinarith [mul_le_mul_of_nonneg_right hY he.le] : (0:ℝ) + y*e < 1))
  · have xp : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    by_cases ok : y+x*e < 1
    · exact ⟨1, by decide, by simpa [dx,dy] using towardsAxis xp hX hy he ok⟩
    · have yp : 0 < y := by
        by_contra! hn
        have := mul_le_mul_of_nonneg_right hX he.le
        nlinarith
      exact ⟨2, by decide, by simpa [dx,dy] using flip (towardsAxis yp hY hx he (h.resolve_left ok))⟩

theorem planarThree {x y e r : ℝ} (hx : 0 ≤ x) (hX : x ≤ 1)
    (hy : 0 ≤ y) (hY : y ≤ 1) (he : 0 < e) (hE : e < 1)
    (her : e < r) (hg : r ≤ max (1-x) (1-y)) :
    ∃ j : ℕ, j < 3 ∧ Step x y (dx e j) (dy e j) := by
  apply threeCore hx hX hy hY he hE
  rcases le_max_iff.mp hg with h | h
  · right
    nlinarith [mul_le_mul_of_nonneg_right hY he.le]
  · left
    nlinarith [mul_le_mul_of_nonneg_right hX he.le]

theorem planarFour {x y e : ℝ} (hx : 0 ≤ x) (hX : x ≤ 1)
    (hy : 0 ≤ y) (hY : y ≤ 1) (he : 0 < e) (hE : e < 1/4) :
    ∃ j : ℕ, j < 4 ∧ Step x y (dx e j) (dy e j) := by
  by_cases h : y + x*e < 1 ∨ x + y*e < 1
  · obtain ⟨j, hj, hs⟩ := threeCore hx hX hy hY he (by linarith) h
    exact ⟨j, by omega, hs⟩
  · push Not at h
    obtain ⟨ha,hb⟩ := h
    refine ⟨3, by decide, 3/4, by norm_num, by norm_num, ?_, ?_, ?_⟩ <;>
      norm_num [dx,dy] <;>
      nlinarith [mul_le_mul_of_nonneg_right hX he.le, mul_le_mul_of_nonneg_right hY he.le]

end PrismIllumination
