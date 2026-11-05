import Mathlib

/-! Source-only integer exclusions for the three-root opposite-support cubics.
All four are excluded by signs on integer intervals, without enumeration. -/
set_option autoImplicit false
namespace Paper7B4Analytic

theorem opposite_three_root_234_impossible (z : ℤ)
    (he : z^3-26*z^2+216*z-551 = 0) : False := by
  by_cases hz4 : z ≤ 4
  · have hq : 0 ≤ z^2-22*z+128 := by nlinarith only [sq_nonneg z,hz4]
    have hprod := mul_nonneg (show 0 ≤ 4-z by omega) hq
    nlinarith only [he,hprod]
  · have hz5 : 5 ≤ z := by omega
    have hprod := mul_nonneg (show 0 ≤ z-5 by omega) (sq_nonneg (2*z-21))
    nlinarith only [he,hprod,hz5]
#print axioms Paper7B4Analytic.opposite_three_root_234_impossible

theorem opposite_three_root_235_impossible (z : ℤ)
    (he : z^3-35*z^2+324*z-866 = 0) : False := by
  by_cases hz4 : z ≤ 4
  · have hq : 0 ≤ z^2-31*z+200 := by nlinarith only [sq_nonneg z,hz4]
    have hprod := mul_nonneg (show 0 ≤ 4-z by omega) hq
    nlinarith only [he,hprod]
  have hz5 : 5 ≤ z := by omega
  by_cases hz7 : z ≤ 7
  · have hprod := mul_nonneg
      (mul_nonneg (show 0 ≤ z-5 by omega) (show 0 ≤ 7-z by omega))
      (show 0 ≤ 23-z by omega)
    nlinarith only [he,hprod,hz5]
  by_cases hz22 : z ≤ 22
  · have hprod := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (show 0 ≤ z-8 by omega) (show 0 ≤ z-5 by omega))
      (show z-22 ≤ 0 by omega)
    have hz8 : 8 ≤ z := by omega
    nlinarith only [he,hprod,hz8]
  · have hbase := mul_nonneg (show 0 ≤ z by omega) (show 0 ≤ z-12 by omega)
    have hq : 0 ≤ z^2-12*z+48 := by nlinarith only [hbase]
    have hprod := mul_nonneg (show 0 ≤ z-23 by omega) hq
    nlinarith only [he,hprod]
#print axioms Paper7B4Analytic.opposite_three_root_235_impossible

theorem opposite_three_root_236_impossible (z : ℤ)
    (he : z^3-46*z^2+456*z-1251 = 0) : False := by
  by_cases hz4 : z ≤ 4
  · have hq : 0 ≤ z^2-42*z+288 := by nlinarith only [sq_nonneg z,hz4]
    have hprod := mul_nonneg (show 0 ≤ 4-z by omega) hq
    nlinarith only [he,hprod]
  have hz5 : 5 ≤ z := by omega
  by_cases hz7 : z ≤ 7
  · have hprod := mul_nonneg
      (mul_nonneg (show 0 ≤ z-5 by omega) (show 0 ≤ 7-z by omega))
      (show 0 ≤ 34-z by omega)
    nlinarith only [he,hprod,hz5]
  by_cases hz33 : z ≤ 33
  · have hprod := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (show 0 ≤ z-5 by omega) (show 0 ≤ z-8 by omega))
      (show z-33 ≤ 0 by omega)
    have hz8 : 8 ≤ z := by omega
    nlinarith only [he,hprod,hz8]
  · have hbase := mul_nonneg (show 0 ≤ z by omega) (show 0 ≤ z-12 by omega)
    have hq : 0 ≤ z^2-12*z+48 := by nlinarith only [hbase]
    have hprod := mul_nonneg (show 0 ≤ z-34 by omega) hq
    nlinarith only [he,hprod]
#print axioms Paper7B4Analytic.opposite_three_root_236_impossible

theorem opposite_three_root_245_impossible (z : ℤ)
    (he : z^3-42*z^2+520*z-1559 = 0) : False := by
  by_cases hz4 : z ≤ 4
  · have hq : 0 ≤ z^2-38*z+368 := by nlinarith only [sq_nonneg z,hz4]
    have hprod := mul_nonneg (show 0 ≤ 4-z by omega) hq
    nlinarith only [he,hprod]
  by_cases hz20 : z ≤ 20
  · have hprod := mul_nonneg (show 0 ≤ z-5 by omega) (sq_nonneg (2*z-37))
    nlinarith only [he,hprod,hz20]
  · have hbase := mul_nonneg (show 0 ≤ z by omega) (show 0 ≤ z-21 by omega)
    have hq : 0 ≤ z^2-21*z+79 := by nlinarith only [hbase]
    have hprod := mul_nonneg (show 0 ≤ z-21 by omega) hq
    nlinarith only [he,hprod]
#print axioms Paper7B4Analytic.opposite_three_root_245_impossible

end Paper7B4Analytic
