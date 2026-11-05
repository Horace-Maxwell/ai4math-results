import Mathlib

/-! Source-only analytic bound for the positive integer unit-root equation.
The proof uses inequalities and cyclic symmetry, with no parameter enumeration. -/
set_option autoImplicit false
namespace Paper7B4Analytic

theorem unit_four_all_ge_two_bound (a b c d : ℤ)
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c) (hd : 2 ≤ d)
    (he : a*b*c*d = (a+c)*(b+d)) : a+b+c+d ≤ 8 := by
  have hAC := mul_nonneg (show 0 ≤ a-2 by omega) (show 0 ≤ c-2 by omega)
  have hBD := mul_nonneg (show 0 ≤ b-2 by omega) (show 0 ≤ d-2 by omega)
  have hA : 0 ≤ a*c-a-c := by nlinarith only [hAC,ha,hc]
  have hB : 0 ≤ b*d-b-d := by nlinarith only [hBD,hb,hd]
  have hX := mul_nonneg hA (mul_nonneg (show 0 ≤ b by omega) (show 0 ≤ d by omega))
  have hY := mul_nonneg (show 0 ≤ a+c by omega) hB
  have hXe : (a*c-a-c)*(b*d) = 0 := by nlinarith only [he,hX,hY]
  have hYe : (a+c)*(b*d-b-d) = 0 := by nlinarith only [he,hX,hY]
  have hbd0 : b*d ≠ 0 := mul_ne_zero (by omega) (by omega)
  have hAz : a*c-a-c = 0 := (mul_eq_zero.mp hXe).resolve_right hbd0
  have hBz : b*d-b-d = 0 :=
    (mul_eq_zero.mp hYe).resolve_left (show a+c ≠ 0 by omega)
  have hsAC : a+c = 4 := by nlinarith only [ha,hc,hAC,hAz]
  have hsBD : b+d = 4 := by nlinarith only [hb,hd,hBD,hBz]
  omega
#print axioms Paper7B4Analytic.unit_four_all_ge_two_bound

theorem unit_four_one_oriented_bound (b c d : ℤ)
    (hb : 2 ≤ b) (hc : 1 ≤ c) (hd : 3 ≤ d)
    (he : c*b*d = (c+1)*(b+d)) : 1+b+c+d ≤ 11 := by
  let D : ℤ := b*d-b-d
  have hbase := mul_nonneg (show 0 ≤ b-2 by omega) (show 0 ≤ d-1 by omega)
  have hD : 1 ≤ D := by dsimp [D]; nlinarith only [hbase,hd]
  have hcD : c*D = b+d := by dsimp [D]; nlinarith only [he]
  have hcorner := mul_nonneg (show 0 ≤ b-2 by omega) (show 0 ≤ d-3 by omega)
  have hsumD : b+d ≤ 5*D := by dsimp [D]; nlinarith only [hcorner,hb,hd]
  have hc5 : c ≤ 5 := by
    by_contra hh
    have hc6 : 6 ≤ c := by omega
    have hprod := mul_nonneg (show 0 ≤ c-6 by omega) (show 0 ≤ D by omega)
    nlinarith only [hprod,hD,hcD,hsumD]
  by_cases hc1 : c = 1
  · rw [hc1] at he
    have hb3 : 3 ≤ b := by
      by_contra hh
      have hb2 : b = 2 := by omega
      rw [hb2] at he
      nlinarith only [he]
    have hprod := mul_nonneg (show 0 ≤ b-3 by omega) (show 0 ≤ d-3 by omega)
    nlinarith only [he,hprod,hc1]
  · have hc2 : 2 ≤ c := by omega
    have hrect := mul_nonneg (show 0 ≤ b-2 by omega) (show 0 ≤ d-2 by omega)
    have hrectc := mul_nonneg (show 0 ≤ c by omega) hrect
    have hsum : (c-1)*(b+d) ≤ 4*c := by nlinarith only [he,hrectc]
    have hinterval := mul_nonneg (show 0 ≤ c-2 by omega) (show 0 ≤ 5-c by omega)
    by_contra hh
    have hlarge : 11 ≤ b+c+d := by omega
    have hgap := mul_nonneg (show 0 ≤ c-1 by omega) (show 0 ≤ b+c+d-11 by omega)
    nlinarith only [hsum,hinterval,hgap,hc2]
#print axioms Paper7B4Analytic.unit_four_one_oriented_bound

theorem unit_four_one_bound (b c d : ℤ)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (he : c*b*d = (c+1)*(b+d)) : 1+b+c+d ≤ 11 := by
  have hb2 : 2 ≤ b := by
    by_contra hh
    have hb1 : b = 1 := by omega
    rw [hb1] at he
    nlinarith only [he,hc,hd]
  have hd2 : 2 ≤ d := by
    by_contra hh
    have hd1 : d = 1 := by omega
    rw [hd1] at he
    nlinarith only [he,hc,hb]
  by_cases hd3 : 3 ≤ d
  · exact unit_four_one_oriented_bound b c d hb2 hc hd3 he
  · have hdval : d = 2 := by omega
    have hb3 : 3 ≤ b := by
      by_contra hh
      have hbval : b = 2 := by omega
      rw [hdval,hbval] at he
      nlinarith only [he]
    have hrot : c*d*b = (c+1)*(d+b) := by nlinarith only [he]
    have hbound := unit_four_one_oriented_bound d c b hd2 hc hb3 hrot
    linarith only [hbound]
#print axioms Paper7B4Analytic.unit_four_one_bound

theorem unit_four_int_sum_bound (a b c d : ℤ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (he : a*b*c*d = (a+c)*(b+d)) : a+b+c+d ≤ 11 := by
  by_cases ha1 : a = 1
  · have hrot : c*b*d = (c+1)*(b+d) := by rw [ha1] at he; nlinarith only [he]
    have hbound := unit_four_one_bound b c d hb hc hd hrot
    linarith only [hbound,ha1]
  by_cases hb1 : b = 1
  · have hrot : d*c*a = (d+1)*(c+a) := by rw [hb1] at he; nlinarith only [he]
    have hbound := unit_four_one_bound c d a hc hd ha hrot
    linarith only [hbound,hb1]
  by_cases hc1 : c = 1
  · have hrot : a*d*b = (a+1)*(d+b) := by rw [hc1] at he; nlinarith only [he]
    have hbound := unit_four_one_bound d a b hd ha hb hrot
    linarith only [hbound,hc1]
  by_cases hd1 : d = 1
  · have hrot : b*a*c = (b+1)*(a+c) := by rw [hd1] at he; nlinarith only [he]
    have hbound := unit_four_one_bound a b c ha hb hc hrot
    linarith only [hbound,hd1]
  have hbound := unit_four_all_ge_two_bound a b c d
    (by omega) (by omega) (by omega) (by omega) he
  omega
#print axioms Paper7B4Analytic.unit_four_int_sum_bound

theorem positive_unit_product_sum_le_eleven (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (he : a*b*c*d = (a+c)*(b+d)) : a+b+c+d ≤ 11 := by
  have haI : (1 : ℤ) ≤ a := by exact_mod_cast (show 1 ≤ a by omega)
  have hbI : (1 : ℤ) ≤ b := by exact_mod_cast (show 1 ≤ b by omega)
  have hcI : (1 : ℤ) ≤ c := by exact_mod_cast (show 1 ≤ c by omega)
  have hdI : (1 : ℤ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have heI : (a : ℤ)*b*c*d = ((a : ℤ)+c)*((b : ℤ)+d) := by exact_mod_cast he
  have hbound := unit_four_int_sum_bound a b c d haI hbI hcI hdI heI
  exact_mod_cast hbound
#print axioms Paper7B4Analytic.positive_unit_product_sum_le_eleven

end Paper7B4Analytic
