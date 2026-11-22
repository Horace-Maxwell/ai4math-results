import Research.TaskP.RootRadius.LogLimit

open Filter Set Metric Polynomial
open scoped Topology
namespace TaskP.GraphRootRadius.Proof
open Challenge

/-- At a fixed multiplicative enlargement of the scale the logarithmic bounds
for the two sides of the root equation become strictly separated. -/
theorem upper_separation {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s)
    {B : ℝ} (hB : 1 < B) (K : ℝ) :
    ∀ᶠ m : ℕ in atTop, let T := B*scale a c s m
      Real.exp ((m:ℝ)*((s:ℝ)+K/T)/T^c) < T^a/2 := by
  let T := fun m => B*scale a c s m
  have hB0 : 0 < B := by linarith
  have hT : Tendsto T atTop atTop := (scale_atTop ha hc hs).const_mul_atTop hB0
  let D := (a:ℝ)/((c:ℝ)*s*B^c)
  have hr := ((hT.const_div_atTop K).const_add (s:ℝ)).const_mul D
  have hR : Tendsto (fun m : ℕ => ((m:ℝ)*((s:ℝ)+K/T m)/(T m)^c)/Real.log m)
      atTop (𝓝 (D*s)) := by
    simp only [add_zero] at hr
    refine hr.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hL := Real.log_pos (by exact_mod_cast hm : (1:ℝ) < m)
    have hM : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    dsimp [T,D]
    rw [mul_pow, scale_pow ha hc hs hm]
    field_simp
  have hlt := (logNat_atTop.const_div_atTop (Real.log B)).add (scale_log_limit ha hc hs)
  have hLHS := (hlt.const_mul (a:ℝ)).sub (logNat_atTop.const_div_atTop (Real.log 2))
  have hL : Tendsto (fun m : ℕ => Real.log ((T m)^a/2)/Real.log m)
      atTop (𝓝 ((a:ℝ)/c)) := by
    simp only [zero_add,sub_zero, mul_one_div] at hLHS
    refine hLHS.congr' ?_
    filter_upwards [eventually_gt_atTop 1] with m hm
    have hS := scale_pos ha hc hs hm
    have hL := Real.log_pos (by exact_mod_cast hm : (1:ℝ) < m)
    dsimp [T]
    rw [Real.log_div (by positivity) (by norm_num), Real.log_pow, Real.log_mul hB0.ne' hS.ne']
    ring
  have hpow : 1 < B^c := one_lt_pow₀ hB hc.ne'
  have hgap : D*s < (a:ℝ)/c := by
    dsimp [D]
    field_simp
    nlinarith [mul_lt_mul_of_pos_left hpow (show (0:ℝ) < (a:ℝ)*s*c by positivity)]
  filter_upwards [hR.eventually_lt hL hgap,eventually_gt_atTop 1] with m hm hM
  have hlog := Real.log_pos (by exact_mod_cast hM : (1:ℝ) < m)
  have hTpos : 0 < T m := mul_pos hB0 (scale_pos ha hc hs hM)
  exact (Real.lt_log_iff_exp_lt (by positivity : 0 < T m^a/2)).mp
    ((div_lt_div_iff_of_pos_right hlog).mp hm)

theorem upper_Q {s c : ℕ} (E : ℂ[X]) {K T : ℝ} (hT : 1 ≤ T) (_hK : 0 ≤ K)
    (he : ∀ w : ℂ, ‖w‖ ≤ 1 → ‖E.eval w‖ ≤ K) {y : ℂ} (hy : T ≤ ‖y‖) :
    ‖1+delta c s E y⁻¹‖ ≤ 1 + ((s:ℝ)+K/T)/T^c := by
  have hTpos : 0 < T := by linarith
  have hw : ‖y⁻¹‖ ≤ 1/T := by rw [norm_inv, one_div]; exact inv_anti₀ hTpos hy
  have hw1 : ‖y⁻¹‖ ≤ 1 := hw.trans (by simpa using (inv_anti₀ zero_lt_one hT))
  have hterm : ‖-(s:ℂ)+y⁻¹*E.eval y⁻¹‖ ≤ (s:ℝ)+K/T := by
    calc
      _ ≤ ‖-(s:ℂ)‖ + ‖y⁻¹ * E.eval y⁻¹‖ := norm_add_le _ _
      _ ≤ (s:ℝ) + (1/T)*K := by
        rw [norm_neg, Complex.norm_natCast, norm_mul]
        gcongr
        exact he _ hw1
      _ = _ := by ring
  calc
    _ ≤ 1 + ‖delta c s E y⁻¹‖ := by simpa using norm_add_le (1:ℂ) (delta c s E y⁻¹)
    _ ≤ 1 + (1/T)^c*((s:ℝ)+K/T) := by
      simp only [delta,norm_mul,norm_pow]
      gcongr
    _ = _ := by rw [div_pow]; ring

theorem roots_upper {a c s : ℕ} (ha : 0 < a) (hc : 0 < c) (hs : 0 < s)
    (E : ℂ[X]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ m : ℕ in atTop, ∀ y : ℂ, ((1 + delta c s E y⁻¹)^m = 1-y^a ∨ y = 0) →
      ‖y-1‖ ≤ (1+ε)*scale a c s m := by
  obtain ⟨w,hw,hmax⟩ := (isCompact_closedBall (0:ℂ) 1).exists_isMaxOn
    (nonempty_closedBall.mpr zero_le_one) E.continuous.norm.continuousOn
  let K := ‖E.eval w‖
  have hK : 0 ≤ K := norm_nonneg _
  have he : ∀ z : ℂ, ‖z‖ ≤ 1 → ‖E.eval z‖ ≤ K := fun z hz => hmax (by simpa using hz)
  let B := 1+ ε/2
  have hB : 1 < B := by dsimp [B]; linarith
  have hB0 : 0 < B := by linarith
  have hconst := (scale_atTop ha hc hs).eventually_ge_atTop (2/ε)
  have hbig := ((scale_atTop ha hc hs).const_mul_atTop hB0).eventually_ge_atTop 2
  filter_upwards [upper_separation ha hc hs hB K,hconst,hbig,eventually_gt_atTop 1] with m
    hsep hwide htwo hm
  let S := scale a c s m
  let T := B*S
  have h2 : 2 ≤ T := htwo
  have h1 : 1 ≤ T := by linarith
  have hS : 0 < S := scale_pos ha hc hs hm
  intro y hroot
  have hry : ‖y‖ < T := by
    by_contra! hle
    rcases hroot with heq | rfl
    · have low : T^a/2 ≤ ‖1-y^a‖ := by
        have h := norm_sub_norm_le (y^a) (1:ℂ)
        rw [norm_sub_rev] at h
        simp only [norm_pow,norm_one] at h
        have hmono : T^a ≤ ‖y‖^a := by gcongr
        have hbase : 2 ≤ T^a := h2.trans (le_self_pow₀ h1 ha.ne')
        linarith
      have hr : ‖1-y^a‖ ≤ Real.exp ((m:ℝ)*((s:ℝ)+K/T)/T^c) := by
        rw [← heq, norm_pow]
        calc
          _ ≤ (1 + ((s:ℝ)+K/T)/T^c)^m := by gcongr; exact upper_Q E h1 hK he hle
          _ ≤ (Real.exp (((s:ℝ)+K/T)/T^c))^m := by
            gcongr
            simpa [add_comm] using Real.add_one_le_exp (((s:ℝ)+K/T)/T^c)
          _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring
      exact (not_lt_of_ge (low.trans hr)) hsep
    · simp at hle
      linarith
  have hh : 2 ≤ S*ε := (div_le_iff₀ hε).mp hwide
  have h := norm_sub_le y (1 : ℂ)
  rw [norm_one] at h
  change ‖y-1‖ ≤ (1+ε)*S
  dsimp [T,B] at hry
  linarith

end TaskP.GraphRootRadius.Proof
