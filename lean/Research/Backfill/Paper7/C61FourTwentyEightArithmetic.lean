import Research.Backfill.Paper7.C61DoubleRootMonodromy

/-! NEW SOURCE ONLY. Five actual nonzero-side coordinates of the
twenty-eight / two-hundred-forty moment domain, with a zero at the head. -/
set_option autoImplicit false
namespace Paper7C61Four

theorem five_at_least_four_not_moments (b c d e f : ℤ)
    (hb : 4 ≤ b) (hc : 4 ≤ c) (hd : 4 ≤ d) (he : 4 ≤ e) (hf : 4 ≤ f)
    (hs : b+c+d+e+f = 28) (hq : b^2+c^2+d^2+e^2+f^2 = 240) : False := by
  have bound (x : ℤ) (hx : 4 ≤ x) (hx' : x ≤ 12) : x^2 ≤ 16*x-48 := by
    nlinarith [mul_nonneg (show 0 ≤ x-4 by omega) (show 0 ≤ 12-x by omega)]
  have hb' := bound b hb (by omega)
  have hc' := bound c hc (by omega)
  have hd' := bound d hd (by omega)
  have he' := bound e he (by omega)
  have hf' := bound f hf (by omega)
  nlinarith only [hs,hq,hb',hc',hd',he',hf']
#print axioms Paper7C61Four.five_at_least_four_not_moments

theorem mixed_factor_sum_bound (b c d e f : ℤ)
    (hb : 4 ≤ b) (hc : 5 ≤ c) (he : e ≤ 3) (hf : f ≤ 2)
    (hprod : e = (b-3)*(c-4))
    (hpair : (4-d)*(4-e) = 4*b-8) : b+c+d+e+f ≤ 21 := by
  have hb6 : b ≤ 6 := by
    have hm := mul_nonneg (show 0 ≤ b-3 by omega) (show 0 ≤ c-5 by omega)
    nlinarith only [hm,hprod,he]
  have hc7 : c ≤ 7 := by
    have hm := mul_nonneg (show 0 ≤ b-4 by omega) (show 0 ≤ c-4 by omega)
    nlinarith only [hm,hprod,he]
  have hd3 : d ≤ 3 := by
    by_contra hn
    have hm := mul_nonpos_of_nonpos_of_nonneg
      (show 4-d ≤ 0 by omega) (show 0 ≤ 4-e by omega)
    nlinarith only [hm,hpair,hb]
  omega
#print axioms Paper7C61Four.mixed_factor_sum_bound

theorem five_head_zero_moment_obstruction (b c d e f : ℤ)
    (_hb0 : 0 ≤ b) (hc0 : 0 ≤ c) (_hd0 : 0 ≤ d) (he0 : 0 ≤ e) (_hf0 : 0 ≤ f)
    (hd13 : d ≤ 13) (hs : b+c+d+e+f = 28)
    (hq : b^2+c^2+d^2+e^2+f^2 = 240)
    (hE : e = (b-3)*(c-4)) (hC : c = (f-3)*(e-4))
    (hDE : (4-d)*(4-e) = 4*b-8) (hCD : (4-c)*(4-d) = 4*f-8) : False := by
  by_cases hc : c = 0
  · rw [hc] at hs hq hCD
    have hdf : d+f = 6 := by nlinarith only [hCD]
    have hbe : b+e = 22 := by omega
    have hbe2 : (b+e)^2 = 484 := by rw [hbe]; norm_num
    nlinarith only [hq,hbe2,sq_nonneg (b-e),sq_nonneg d,sq_nonneg f]
  by_cases he : e = 0
  · rw [he] at hs hq hDE
    have hbd : b+d = 6 := by nlinarith only [hDE]
    have hcf : c+f = 22 := by omega
    have hcf2 : (c+f)^2 = 484 := by rw [hcf]; norm_num
    nlinarith only [hq,hcf2,sq_nonneg (c-f),sq_nonneg b,sq_nonneg d]
  have hEp : 0 < (b-3)*(c-4) := by rw [← hE]; omega
  have hCp : 0 < (f-3)*(e-4) := by rw [← hC]; omega
  rcases mul_pos_iff.mp hEp with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · rcases mul_pos_iff.mp hCp with ⟨hf,he⟩ | ⟨hf,he⟩
    · have hd5 : 5 ≤ d := by
        by_contra hn
        have hm := mul_nonpos_of_nonneg_of_nonpos
          (show 0 ≤ 4-d by omega) (show 4-e ≤ 0 by omega)
        nlinarith only [hm,hDE,hb]
      exact five_at_least_four_not_moments b c d e f
        (by omega) (by omega) (by omega) (by omega) (by omega) hs hq
    · have hbound := mixed_factor_sum_bound b c d e f
        (by omega) (by omega) (by omega) (by omega) hE hDE
      omega
  · rcases mul_pos_iff.mp hCp with ⟨hf,he⟩ | ⟨hf,he⟩
    · have hbound := mixed_factor_sum_bound f e d c b
        (by omega) (by omega) (by omega) (by omega) hC
        (by nlinarith only [hCD])
      omega
    · omega
#print axioms Paper7C61Four.five_head_zero_moment_obstruction

end Paper7C61Four
