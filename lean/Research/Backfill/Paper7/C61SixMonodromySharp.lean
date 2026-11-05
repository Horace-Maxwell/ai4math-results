import Research.Backfill.Paper7.C61SixMonodromyBound

/-! Source-only sharp sum bound for integral six-step identity monodromy.
All arguments are symbolic integer inequalities and sign splits. -/
set_option autoImplicit false
namespace Paper7C61Sharp
open Paper7C61BetaEight

theorem negative_triple_middle (a b c e : ℤ)
    (ha : a ≤ -1) (hb : b ≤ -1) (hc : c ≤ -1) (he : e ≤ -1)
    (h : e = a+c-a*b*c) : b = -1 := by
  by_contra hne
  have hb2 : b ≤ -2 := by omega
  have hac : 0 ≤ a*c := mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  have hA := mul_nonneg (show 0 ≤ -a by omega) (show 0 ≤ -c-1 by omega)
  have hC := mul_nonneg (show 0 ≤ -c by omega) (show 0 ≤ -a-1 by omega)
  have hB := mul_nonneg (show 0 ≤ -b-2 by omega) hac
  nlinarith only [h,he,hA,hC,hB]
#print axioms Paper7C61Sharp.negative_triple_middle

theorem positive_triple_shape (C D E : ℤ)
    (hC : 1 ≤ C) (hD : 1 ≤ D) (hE : 1 ≤ E)
    (hCD : 3 ≤ C*D) (hDE : 3 ≤ D*E)
    (h : E*(C*D-1) = C+1) : C = 1 ∧ D = 3 ∧ E = 1 := by
  have hD2 : 2 ≤ D := by
    by_contra hn
    have hD1 : D = 1 := by omega
    rw [hD1] at hCD hDE h
    norm_num at hCD hDE h
    have hm := mul_nonneg (show 0 ≤ E-3 by omega) (show 0 ≤ C-1 by omega)
    nlinarith only [h,hCD,hm]
  have hC1 : C = 1 := by
    by_contra hn
    have hC2 : 2 ≤ C := by omega
    have hE1 : E = 1 := by
      by_contra hnE
      have hE2 : 2 ≤ E := by omega
      have hm1 := mul_nonneg (show 0 ≤ E-2 by omega) (show 0 ≤ C*D-1 by omega)
      have hm2 := mul_nonneg (show 0 ≤ C by omega) (show 0 ≤ D-2 by omega)
      nlinarith only [h,hC2,hm1,hm2]
    rw [hE1] at h hDE
    norm_num at h hDE
    have hm := mul_nonneg (show 0 ≤ C by omega) (show 0 ≤ D-3 by omega)
    nlinarith only [h,hC2,hm]
  rw [hC1] at hCD h
  norm_num at hCD h
  have hm := mul_nonneg (show 0 ≤ E by omega) (show 0 ≤ D-3 by omega)
  have hE1 : E = 1 := by nlinarith only [h,hE,hm]
  rw [hE1] at h
  exact ⟨hC1,by omega,hE1⟩
#print axioms Paper7C61Sharp.positive_triple_shape

theorem six_product_zero_sum (b c d e f : ℤ)
    (hc : c ≤ 1) (hd : d ≤ 1) (he : e ≤ 1)
    (h : sixProduct 0 b c d e f = 1) : b+c+d+e+f = -6 := by
  obtain ⟨h01,h12,_hpoly⟩ := six_product_triple_data 0 b c d e f h
  have h1 := six_product_rotate 0 b c d e f h
  have h2 := six_product_rotate b c d e f 0 h1
  have h23 := (six_product_triple_data c d e f 0 b h2).1
  norm_num at h01 h23
  have hd0 : d ≠ 0 := by intro hz; rw [hz] at h01; norm_num at h01
  have hec : e = c := by
    apply mul_left_cancel₀ hd0
    nlinarith only [h01,h23]
  have hdneg : d ≤ -1 := by
    by_contra hn
    have hcased : d = 0 ∨ d = 1 := by omega
    rcases hcased with hz | ho
    · exact hd0 hz
    · rw [ho] at h01
      nlinarith only [h01,he]
  have hcneg : c ≤ -1 := by
    by_contra hn
    have hc0 : 0 ≤ c := by omega
    have hm := mul_nonpos_of_nonneg_of_nonpos hc0 (show d ≤ 0 by omega)
    nlinarith only [h23,hm]
  have hm := mul_nonneg (show 0 ≤ -c by omega) (show 0 ≤ -d-1 by omega)
  have hclo : -2 ≤ c := by nlinarith only [h23,hm]
  have hcases : c = -2 ∨ c = -1 := by omega
  rcases hcases with hceq | hceq
  · have hdeq : d = -1 := by rw [hceq] at h23; nlinarith only [h23]
    have heeq : e = -2 := by omega
    rw [hceq,heeq] at h12
    nlinarith only [h12,hceq,hdeq,heeq]
  · have hdeq : d = -2 := by rw [hceq] at h23; nlinarith only [h23]
    have heeq : e = -1 := by omega
    rw [hceq,heeq] at h12
    nlinarith only [h12,hceq,hdeq,heeq]
#print axioms Paper7C61Sharp.six_product_zero_sum

theorem six_product_adjacent_units (c d e f : ℤ)
    (hc : c ≤ 1) (hf : f ≤ 1)
    (h : sixProduct 1 1 c d e f = 1) : c = 1 ∧ d = 1 ∧ e = 1 ∧ f = 1 := by
  obtain ⟨h01,h12,hpoly⟩ := six_product_triple_data 1 1 c d e f h
  have he : e = 1 := by nlinarith only [hpoly]
  rw [he] at h01 h12
  have hd : d = 1 := by nlinarith only [h01]
  exact ⟨by nlinarith only [h12,hc,hf],hd,he,by nlinarith only [h12,hc,hf]⟩
#print axioms Paper7C61Sharp.six_product_adjacent_units

theorem six_product_unit_head_sum (b c d e f : ℤ)
    (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (hb0 : b ≠ 0) (hf0 : f ≠ 0)
    (h : sixProduct 1 b c d e f = 1) : -6 ≤ 1+b+c+d+e+f := by
  by_cases hb1 : b = 1
  · rw [hb1] at h
    obtain ⟨hc1,hd1,he1,hf1⟩ := six_product_adjacent_units c d e f hc hf h
    omega
  by_cases hf1 : f = 1
  · have h1 := six_product_rotate 1 b c d e f h
    have h2 := six_product_rotate b c d e f 1 h1
    have h3 := six_product_rotate c d e f 1 b h2
    have h4 := six_product_rotate d e f 1 b c h3
    have h5 := six_product_rotate e f 1 b c d h4
    rw [hf1] at h5
    obtain ⟨hb1,hc1,hd1,he1⟩ := six_product_adjacent_units b c d e hb he h5
    omega
  have hbneg : b ≤ -1 := by omega
  have hfneg : f ≤ -1 := by omega
  obtain ⟨h01,h12,hpoly⟩ := six_product_triple_data 1 b c d e f h
  have h1 := six_product_rotate 1 b c d e f h
  have h2 := six_product_rotate b c d e f 1 h1
  have h23 := (six_product_triple_data c d e f 1 b h2).1
  norm_num at h01 h23 hpoly
  have hde : 3 ≤ d*e := by nlinarith only [h01,hbneg]
  have hcd : 3 ≤ c*d := by nlinarith only [h23,hfneg]
  have hdneg : d ≤ -1 := by
    by_contra hn
    have hcases : d = 0 ∨ d = 1 := by omega
    rcases hcases with hz | ho
    · rw [hz] at hde; norm_num at hde
    · rw [ho] at hde; nlinarith only [hde,he]
  have heneg : e ≤ -1 := by
    by_contra hn
    have he0 : 0 ≤ e := by omega
    have hm := mul_nonpos_of_nonpos_of_nonneg (show d ≤ 0 by omega) he0
    nlinarith only [hde,hm]
  have hcneg : c ≤ -1 := by
    by_contra hn
    have hc0 : 0 ≤ c := by omega
    have hm := mul_nonpos_of_nonneg_of_nonpos hc0 (show d ≤ 0 by omega)
    nlinarith only [hcd,hm]
  have heqn : (-e)*((-c)*(-d)-1) = (-c)+1 := by
    linear_combination hpoly - c*h01
  obtain ⟨hC,hD,hE⟩ := positive_triple_shape (-c) (-d) (-e)
    (by omega) (by omega) (by omega) (by nlinarith only [hcd])
    (by nlinarith only [hde]) heqn
  have hc1 : c = -1 := by omega
  have hd3 : d = -3 := by omega
  have he1 : e = -1 := by omega
  rw [hc1,hd3] at h23
  rw [hd3,he1] at h01
  nlinarith only [h01,h23,hc1,hd3,he1]
#print axioms Paper7C61Sharp.six_product_unit_head_sum

/-- Every integral identity monodromy of length six with coefficients at most
one has coefficient sum at least minus six. -/
theorem six_product_sharp_sum_lower (a b c d e f : ℤ)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (h : sixProduct a b c d e f = 1) : -6 ≤ a+b+c+d+e+f := by
  have h1 := six_product_rotate a b c d e f h
  have h2 := six_product_rotate b c d e f a h1
  have h3 := six_product_rotate c d e f a b h2
  have h4 := six_product_rotate d e f a b c h3
  have h5 := six_product_rotate e f a b c d h4
  by_cases ha0 : a = 0
  · rw [ha0] at h
    have hs := six_product_zero_sum b c d e f hc hd he h
    omega
  by_cases hb0 : b = 0
  · rw [hb0] at h1
    have hs := six_product_zero_sum c d e f a hd he hf h1
    omega
  by_cases hc0 : c = 0
  · rw [hc0] at h2
    have hs := six_product_zero_sum d e f a b he hf ha h2
    omega
  by_cases hd0 : d = 0
  · rw [hd0] at h3
    have hs := six_product_zero_sum e f a b c hf ha hb h3
    omega
  by_cases he0 : e = 0
  · rw [he0] at h4
    have hs := six_product_zero_sum f a b c d ha hb hc h4
    omega
  by_cases hf0 : f = 0
  · rw [hf0] at h5
    have hs := six_product_zero_sum a b c d e hb hc hd h5
    omega
  by_cases ha1 : a = 1
  · rw [ha1] at h
    have hs := six_product_unit_head_sum b c d e f hb hc hd he hf hb0 hf0 h
    omega
  by_cases hb1 : b = 1
  · rw [hb1] at h1
    have hs := six_product_unit_head_sum c d e f a hc hd he hf ha hc0 ha0 h1
    omega
  by_cases hc1 : c = 1
  · rw [hc1] at h2
    have hs := six_product_unit_head_sum d e f a b hd he hf ha hb hd0 hb0 h2
    omega
  by_cases hd1 : d = 1
  · rw [hd1] at h3
    have hs := six_product_unit_head_sum e f a b c he hf ha hb hc he0 hc0 h3
    omega
  by_cases he1 : e = 1
  · rw [he1] at h4
    have hs := six_product_unit_head_sum f a b c d hf ha hb hc hd hf0 hd0 h4
    omega
  by_cases hf1 : f = 1
  · rw [hf1] at h5
    have hs := six_product_unit_head_sum a b c d e ha hb hc hd he ha0 he0 h5
    omega
  have han : a ≤ -1 := by omega
  have hbn : b ≤ -1 := by omega
  have hcn : c ≤ -1 := by omega
  have hdn : d ≤ -1 := by omega
  have hen : e ≤ -1 := by omega
  have hfn : f ≤ -1 := by omega
  have hbe := negative_triple_middle a b c e han hbn hcn hen
    (six_product_triple_data a b c d e f h).2.2
  have hce := negative_triple_middle b c d f hbn hcn hdn hfn
    (six_product_triple_data b c d e f a h1).2.2
  have hde := negative_triple_middle c d e a hcn hdn hen han
    (six_product_triple_data c d e f a b h2).2.2
  have hee := negative_triple_middle d e f b hdn hen hfn hbn
    (six_product_triple_data d e f a b c h3).2.2
  have hfe := negative_triple_middle e f a c hen hfn han hcn
    (six_product_triple_data e f a b c d h4).2.2
  have hae := negative_triple_middle f a b d hfn han hbn hdn
    (six_product_triple_data f a b c d e h5).2.2
  omega
#print axioms Paper7C61Sharp.six_product_sharp_sum_lower

end Paper7C61Sharp
