import Research.Backfill.Paper7.C61AlternatingPairAlgebra

/-! NEW SOURCE ONLY. Sign bounds for the symmetric alternating-pair identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four

theorem pair_sum_all_positive (S x y z : ℝ)
    (hx : 2/3 ≤ x) (hy : 2/3 ≤ y) (hz : 2/3 ≤ z)
    (hx2 : x ≤ 2) (hy2 : y ≤ 2) (hz2 : z ≤ 2)
    (h : S*x*y*z=2*x*y+2*x*z+2*y*z-x^2-y^2-z^2) : 0 < S := by
  have hxb := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hx2)
  have hyb := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hy2)
  have hzb := mul_nonneg (sub_nonneg.mpr hz) (sub_nonneg.mpr hz2)
  have hxy := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)
  have hxz := mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hz)
  have hyz := mul_nonneg (sub_nonneg.mpr hy) (sub_nonneg.mpr hz)
  have hp : 0 < x*y*z := mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  by_contra hn
  have hn' : S ≤ 0 := by linarith
  have hm := mul_nonpos_of_nonpos_of_nonneg hn' hp.le
  nlinarith only [h, hxb, hyb, hzb, hxy, hxz, hyz, hm]
#print axioms Paper7C61Four.pair_sum_all_positive

theorem pair_sum_one_negative (S x y z : ℝ)
    (hx : x < 0) (hy : 0 < y) (hz : 0 < z)
    (h : S*x*y*z=2*x*y+2*x*z+2*y*z-x^2-y^2-z^2) : 0 < S := by
  have hxsq : 0 < x^2 := sq_pos_of_ne_zero (ne_of_lt hx)
  have hdiff := sq_nonneg (y-z)
  have hxy : 0 < (-x)*(y+z) := mul_pos (neg_pos.mpr hx) (add_pos hy hz)
  have hp : x*y*z < 0 := mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hx hy) hz
  by_contra hn
  have hn' : S ≤ 0 := by linarith
  have hm := mul_nonneg_of_nonpos_of_nonpos hn' hp.le
  nlinarith only [h, hxsq, hdiff, hxy, hm]
#print axioms Paper7C61Four.pair_sum_one_negative

theorem pair_sum_two_negative (S x y z : ℝ)
    (hx : x ≤ -2/3) (hy : y ≤ -2/3) (hz : 0 < z) (hz2 : z ≤ 2)
    (hs : -2/3 ≤ x+y+z)
    (h : S*x*y*z=2*x*y+2*x*z+2*y*z-x^2-y^2-z^2) : S < -4 := by
  let u : ℝ := -x
  let v : ℝ := -y
  have hu : 2/3 ≤ u := by dsimp [u]; linarith
  have hv : 2/3 ≤ v := by dsimp [v]; linarith
  have hzmin : u+v-2/3 ≤ z := by dsimp [u, v]; linarith
  have hsmin : 4/3 ≤ u+v := by linarith
  have hsmax : u+v ≤ 8/3 := by linarith
  have hsbox := mul_nonneg (sub_nonneg.mpr hsmin) (sub_nonneg.mpr hsmax)
  have hdiff := sq_nonneg (u-v)
  have huv : u*v ≤ u+v-8/9 := by nlinarith only [hsbox, hdiff]
  have hzuv : 0 < z-u*v := by linarith
  have hscap := mul_nonneg (show 0 ≤ u+v by linarith) (sub_nonneg.mpr hsmax)
  have hlin : 0 ≤ 2*(u+v)-3*u*v := by nlinarith only [hscap, hdiff]
  have hK := mul_nonneg hz.le hlin
  have hL := mul_pos hz hzuv
  have hR : S*u*v*z = -(u^2+v^2+z^2+2*u*z+2*v*z-2*u*v) := by
    dsimp [u, v]
    nlinarith only [h]
  have hp : 0 < u*v*z := mul_pos (mul_pos (by linarith) (by linarith)) hz
  have hneg : (S+4)*(u*v*z) < 0 := by nlinarith only [hR, hK, hL, hdiff]
  by_contra hn
  have hn' : 0 ≤ S+4 := by linarith
  have hm := mul_nonneg hn' hp.le
  linarith
#print axioms Paper7C61Four.pair_sum_two_negative

theorem pair_zero_coefficient_sum_positive (a c e x y z : ℝ)
    (hx : x = 0) (hs : -2/3 ≤ x+y+z)
    (hy : y = 0 ∨ 2/3 ≤ y ∨ y ≤ -2/3)
    (h0 : a*x+e*y=2) (h1 : c*x+e*z=2) (h2 : c*y+a*z=2) : 0 < a+c+e := by
  rw [hx, mul_zero, zero_add] at h0 h1
  have he : e ≠ 0 := by intro hz; rw [hz, zero_mul] at h0; norm_num at h0
  have hyz : y = z := mul_left_cancel₀ he (h0.trans h1.symm)
  rw [← hyz] at hs h2
  have hypos : 0 < y := by
    rcases hy with hy | hy | hy
    · rw [hy, mul_zero] at h0
      norm_num at h0
    · linarith
    · rw [hx] at hs
      linarith
  have hepos : 0 < e := by
    by_contra hn
    have hn' : e ≤ 0 := by linarith
    have hm := mul_nonpos_of_nonpos_of_nonneg hn' hypos.le
    linarith
  have hsum : a+c=e := by
    apply mul_right_cancel₀ (ne_of_gt hypos)
    nlinarith only [h0, h2]
  linarith
#print axioms Paper7C61Four.pair_zero_coefficient_sum_positive

end Paper7C61Four
