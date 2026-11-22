import Research.TaskP.RootRadius.Challenge

open Filter
open scoped Topology

namespace TaskP.GraphRootRadius.Proof
open Challenge

theorem scale_pos {a c s m : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) (hm : 1 < m) :
    0 < scale a c s m := by
  have hL : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm)
  exact Real.rpow_pos_of_pos (by positivity) _

theorem scale_pow {a c s m : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) (hm : 1 < m) :
    (scale a c s m)^c = (c : ℝ)*s*m/(a*Real.log m) := by
  have hL : 0 < Real.log m := Real.log_pos (by exact_mod_cast hm)
  unfold scale
  rw [one_div, Real.rpow_inv_natCast_pow (by positivity) hc.ne']

theorem logNat_atTop : Tendsto (fun m : ℕ => Real.log m) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem scale_log_limit {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) :
    Tendsto (fun m : ℕ => Real.log (scale a c s m) / Real.log m) atTop (𝓝 (1/(c:ℝ))) := by
  let K : ℝ := (c:ℝ)*s/a
  have hK : 0 < K := by dsimp [K]; positivity
  have hLL : Tendsto (fun m : ℕ => Real.log (Real.log m) / Real.log m) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp logNat_atTop
  have hConst := logNat_atTop.const_div_atTop (Real.log K)
  have h := (((hConst.add_const 1).sub hLL).const_mul (1 / (c : ℝ)))
  simp only [zero_add, sub_zero, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 1] with m hm
  have hM : (1:ℝ) < m := by exact_mod_cast hm
  have hL := Real.log_pos hM
  have hKval : (c:ℝ)*s*m/(a*Real.log m) = K*m/Real.log m := by dsimp [K]; ring
  dsimp only [scale]
  rw [hKval, Real.log_rpow (by positivity), Real.log_div (by positivity) hL.ne',
    Real.log_mul hK.ne' (by positivity)]
  field_simp

theorem scale_atTop {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s) :
    Tendsto (scale a c s) atTop atTop := by
  have h := (scale_log_limit ha hc hs).pos_mul_atTop (by positivity) logNat_atTop
  have hlog : Tendsto (fun m : ℕ => Real.log (scale a c s m)) atTop atTop := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with m hm
    exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast hm)).ne'
  refine (Real.tendsto_exp_atTop.comp hlog).congr' ?_
  filter_upwards [eventually_gt_atTop 1] with m hm
  exact Real.exp_log (scale_pos ha hc hs hm)

end TaskP.GraphRootRadius.Proof
