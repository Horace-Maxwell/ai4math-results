import Mathlib

/-! NEW SOURCE ONLY. Small positive continuants vanish only at bounded
integer diagonal sums. The proof uses inequalities and elimination at one. -/
set_option autoImplicit false
namespace Paper7EightCycle

theorem positive_three_continuant_sum (a b c : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (he : a*b*c = a+c) : a+b+c ≤ 5 := by
  have hac := mul_nonneg (show 0 ≤ a-1 by omega) (show 0 ≤ c-1 by omega)
  have hacpos : 0 < a*c := mul_pos (by omega) (by omega)
  have htwo : a+c ≤ 2*(a*c) := by nlinarith only [hac,ha,hc]
  have hb2 : b ≤ 2 := by
    by_contra hh
    have hprod := mul_nonneg (show 0 ≤ b-3 by omega) (show 0 ≤ a*c by omega)
    nlinarith only [hprod,he,htwo,hacpos]
  by_cases hb1 : b = 1
  · have ha2 : 2 ≤ a := by
      by_contra hh
      have ha1 : a = 1 := by omega
      rw [hb1,ha1] at he
      nlinarith only [he]
    have hc2 : 2 ≤ c := by
      by_contra hh
      have hc1 : c = 1 := by omega
      rw [hb1,hc1] at he
      nlinarith only [he]
    have hprod := mul_nonneg (show 0 ≤ a-2 by omega) (show 0 ≤ c-2 by omega)
    rw [hb1] at he
    nlinarith only [he,hprod,hb1]
  · have hbval : b = 2 := by omega
    rw [hbval] at he
    nlinarith only [he,hac,hbval]
#print axioms Paper7EightCycle.positive_three_continuant_sum

theorem positive_four_continuant_sum (a b c d : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (he : a*b*c*d-a*b-a*d-c*d+1 = 0) : a+b+c+d ≤ 8 := by
  by_cases ha1 : a = 1
  · have hb2 : 2 ≤ b := by
      by_contra hh
      have hb1 : b = 1 := by omega
      rw [ha1,hb1] at he
      nlinarith only [he,hd]
    have ht : (b-1)*c*d = (b-1)+d := by rw [ha1] at he; nlinarith only [he]
    have hs := positive_three_continuant_sum (b-1) c d (by omega) hc hd ht
    omega
  by_cases hd1 : d = 1
  · have hc2 : 2 ≤ c := by
      by_contra hh
      have hc1 : c = 1 := by omega
      rw [hd1,hc1] at he
      nlinarith only [he,ha]
    have ht : (c-1)*b*a = (c-1)+a := by rw [hd1] at he; nlinarith only [he]
    have hs := positive_three_continuant_sum (c-1) b a (by omega) hb ha ht
    omega
  by_cases hb1 : b = 1
  · have hc2 : 2 ≤ c := by
      by_contra hh
      have hc1 : c = 1 := by omega
      rw [hb1,hc1] at he
      nlinarith only [he,ha,hd]
    have ht : (a-1)*(c-1)*d = (a-1)+d := by rw [hb1] at he; nlinarith only [he]
    have hs := positive_three_continuant_sum (a-1) (c-1) d (by omega) (by omega) hd ht
    omega
  by_cases hc1 : c = 1
  · have ht : (d-1)*(b-1)*a = (d-1)+a := by rw [hc1] at he; nlinarith only [he]
    have hs := positive_three_continuant_sum (d-1) (b-1) a (by omega) (by omega) ha ht
    omega
  have ha2 : 2 ≤ a := by omega
  have hb2 : 2 ≤ b := by omega
  have hc2 : 2 ≤ c := by omega
  have hd2 : 2 ≤ d := by omega
  let u : ℤ := a*b-1
  let v : ℤ := c*u-a
  have hu : a+1 ≤ u := by
    have hh := mul_nonneg (show 0 ≤ a by omega) (show 0 ≤ b-2 by omega)
    dsimp [u]
    nlinarith only [hh,ha2]
  have hv : u+1 ≤ v := by
    have hh := mul_nonneg (show 0 ≤ c-2 by omega) (show 0 ≤ u by omega)
    dsimp [v]
    nlinarith only [hh,hu]
  have hlast := mul_nonneg (show 0 ≤ d-2 by omega) (show 0 ≤ v by omega)
  have hz : d*v-u = 0 := by dsimp [u,v]; nlinarith only [he]
  nlinarith only [hlast,hz,hu,hv,ha2]
#print axioms Paper7EightCycle.positive_four_continuant_sum

end Paper7EightCycle
