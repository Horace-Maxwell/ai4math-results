import Mathlib

/-! Source-only analytic exclusions for four three-root coefficient triples.
The cubic obstructions use signs of factored expressions, with no enumeration. -/
set_option autoImplicit false
namespace Paper7B4Analytic

theorem three_coefficients_cubic (a b c T E D : ℤ)
    (hT : a+b+c+4 = T)
    (hE : a*b+a*c+b*c+2*(a+b+c) = E)
    (hD : b*(a*c+a+c) = D) :
    b^3+(3-T)*b^2+(E-T+4)*b-D = 0 := by
  have hTb := congrArg (fun x : ℤ => x*b) hT
  have hTb2 := congrArg (fun x : ℤ => x*b^2) hT
  have hEb := congrArg (fun x : ℤ => x*b) hE
  nlinarith only [hTb,hTb2,hEb,hD]
#print axioms Paper7B4Analytic.three_coefficients_cubic

theorem three_cubic_234_impossible (b : ℤ) (hb : b ≤ 23)
    (he : b^3-26*b^2+219*b-576 = 0) : False := by
  by_cases hb5 : b ≤ 5
  · have hq : 0 ≤ b^2-21*b+114 := by nlinarith only [sq_nonneg b,hb5]
    have hprod := mul_nonneg (show 0 ≤ 5-b by omega) hq
    nlinarith only [he,hprod]
  · have hprod := mul_nonneg (show 0 ≤ b-6 by omega) (sq_nonneg (b-10))
    nlinarith only [he,hprod,hb]
#print axioms Paper7B4Analytic.three_cubic_234_impossible

theorem three_cubic_235_impossible (b : ℤ)
    (he : b^3-35*b^2+327*b-900 = 0) : False := by
  by_cases hb5 : b ≤ 5
  · have hq : 0 ≤ b^2-30*b+177 := by nlinarith only [sq_nonneg b,hb5]
    have hprod := mul_nonneg (show 0 ≤ 5-b by omega) hq
    nlinarith only [he,hprod]
  by_cases hb7 : b ≤ 7
  · have hprod := mul_nonneg
      (mul_nonneg (show 0 ≤ b-6 by omega) (show 0 ≤ 7-b by omega))
      (show 0 ≤ 22-b by omega)
    nlinarith only [he,hprod,hb7]
  by_cases hb21 : b ≤ 21
  · have htriple := mul_nonneg
      (mul_nonneg (show 0 ≤ b-6 by omega) (show 0 ≤ b-8 by omega))
      (show 0 ≤ 22-b by omega)
    have hinterval := mul_nonneg (show 0 ≤ b-8 by omega) (show 0 ≤ 21-b by omega)
    nlinarith only [he,htriple,hinterval]
  · have hbase := mul_nonneg (show 0 ≤ b by omega) (show 0 ≤ b-13 by omega)
    have hq : 0 ≤ b^2-13*b+41 := by nlinarith only [hbase]
    have hprod := mul_nonneg (show 0 ≤ b-22 by omega) hq
    nlinarith only [he,hprod]
#print axioms Paper7B4Analytic.three_cubic_235_impossible

theorem three_cubic_236_impossible (b : ℤ)
    (he : b^3-46*b^2+459*b-1296 = 0) : False := by
  by_cases hb5 : b ≤ 5
  · have hq : 0 ≤ b^2-41*b+254 := by nlinarith only [sq_nonneg b,hb5]
    have hprod := mul_nonneg (show 0 ≤ 5-b by omega) hq
    nlinarith only [he,hprod]
  by_cases hb7 : b ≤ 7
  · have hprod := mul_nonneg
      (mul_nonneg (show 0 ≤ b-6 by omega) (show 0 ≤ 7-b by omega))
      (show 0 ≤ 33-b by omega)
    nlinarith only [he,hprod,hb7]
  have hb8 : 8 ≤ b := by omega
  by_cases hb33 : b ≤ 33
  · have hprod := mul_nonneg
      (mul_nonneg (show 0 ≤ b-6 by omega) (show 0 ≤ b-7 by omega))
      (show 0 ≤ 33-b by omega)
    nlinarith only [he,hprod,hb8]
  · have hbase := mul_nonneg (show 0 ≤ b by omega) (show 0 ≤ b-12 by omega)
    have hq : 0 ≤ b^2-12*b+51 := by nlinarith only [hbase]
    have hprod := mul_nonneg (show 0 ≤ b-34 by omega) hq
    nlinarith only [he,hprod]
#print axioms Paper7B4Analytic.three_cubic_236_impossible

theorem three_cubic_245_impossible (b : ℤ)
    (he : b^3-42*b^2+523*b-1600 = 0) : False := by
  by_cases hb4 : b ≤ 4
  · have hq : 0 ≤ b^2-38*b+371 := by nlinarith only [sq_nonneg b,hb4]
    have hprod := mul_nonneg (show 0 ≤ 4-b by omega) hq
    nlinarith only [he,hprod]
  by_cases hb19 : b ≤ 19
  · have hprod := mul_nonneg (show 0 ≤ b-5 by omega) (sq_nonneg (b-18))
    have hpos := mul_pos (show 0 < 20-b by omega) (show 0 < b+1 by omega)
    nlinarith only [he,hprod,hpos]
  · have hbase := mul_nonneg (show 0 ≤ b-20 by omega) (show 0 ≤ b-2 by omega)
    have hq : 0 ≤ b^2-22*b+83 := by nlinarith only [hbase]
    have hprod := mul_nonneg (show 0 ≤ b-20 by omega) hq
    nlinarith only [he,hprod]
#print axioms Paper7B4Analytic.three_cubic_245_impossible

theorem three_root_234_impossible (a b c : ℕ)
    (ha : 0 < a) (_hb : 0 < b) (hc : 0 < c)
    (hT : a+b+c+4 = 29)
    (hE : a*b+a*c+b*c+2*(a+b+c) = 244)
    (hD : b*(a*c+a+c) = 576) : False := by
  have hTI : (a : ℤ)+b+c+4 = 29 := by exact_mod_cast hT
  have hEI : (a : ℤ)*b+(a : ℤ)*c+(b : ℤ)*c+2*((a : ℤ)+b+c) = 244 := by
    exact_mod_cast hE
  have hDI : (b : ℤ)*((a : ℤ)*c+a+c) = 576 := by exact_mod_cast hD
  have hpoly := three_coefficients_cubic a b c 29 244 576 hTI hEI hDI
  have hbound : b ≤ 23 := by omega
  have hboundI : (b : ℤ) ≤ 23 := by exact_mod_cast hbound
  apply three_cubic_234_impossible b hboundI
  nlinarith only [hpoly]
#print axioms Paper7B4Analytic.three_root_234_impossible

theorem three_root_235_impossible (a b c : ℕ)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hT : a+b+c+4 = 38)
    (hE : a*b+a*c+b*c+2*(a+b+c) = 361)
    (hD : b*(a*c+a+c) = 900) : False := by
  have hTI : (a : ℤ)+b+c+4 = 38 := by exact_mod_cast hT
  have hEI : (a : ℤ)*b+(a : ℤ)*c+(b : ℤ)*c+2*((a : ℤ)+b+c) = 361 := by
    exact_mod_cast hE
  have hDI : (b : ℤ)*((a : ℤ)*c+a+c) = 900 := by exact_mod_cast hD
  have hpoly := three_coefficients_cubic a b c 38 361 900 hTI hEI hDI
  apply three_cubic_235_impossible b
  nlinarith only [hpoly]
#print axioms Paper7B4Analytic.three_root_235_impossible

theorem three_root_236_impossible (a b c : ℕ)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hT : a+b+c+4 = 49)
    (hE : a*b+a*c+b*c+2*(a+b+c) = 504)
    (hD : b*(a*c+a+c) = 1296) : False := by
  have hTI : (a : ℤ)+b+c+4 = 49 := by exact_mod_cast hT
  have hEI : (a : ℤ)*b+(a : ℤ)*c+(b : ℤ)*c+2*((a : ℤ)+b+c) = 504 := by
    exact_mod_cast hE
  have hDI : (b : ℤ)*((a : ℤ)*c+a+c) = 1296 := by exact_mod_cast hD
  have hpoly := three_coefficients_cubic a b c 49 504 1296 hTI hEI hDI
  apply three_cubic_236_impossible b
  nlinarith only [hpoly]
#print axioms Paper7B4Analytic.three_root_236_impossible

theorem three_root_245_impossible (a b c : ℕ)
    (_ha : 0 < a) (_hb : 0 < b) (_hc : 0 < c)
    (hT : a+b+c+4 = 45)
    (hE : a*b+a*c+b*c+2*(a+b+c) = 564)
    (hD : b*(a*c+a+c) = 1600) : False := by
  have hTI : (a : ℤ)+b+c+4 = 45 := by exact_mod_cast hT
  have hEI : (a : ℤ)*b+(a : ℤ)*c+(b : ℤ)*c+2*((a : ℤ)+b+c) = 564 := by
    exact_mod_cast hE
  have hDI : (b : ℤ)*((a : ℤ)*c+a+c) = 1600 := by exact_mod_cast hD
  have hpoly := three_coefficients_cubic a b c 45 564 1600 hTI hEI hDI
  apply three_cubic_245_impossible b
  nlinarith only [hpoly]
#print axioms Paper7B4Analytic.three_root_245_impossible

end Paper7B4Analytic
