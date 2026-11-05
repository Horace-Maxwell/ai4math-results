import Research.Backfill.Paper7.C61FourTwentyEightArithmetic
import Mathlib

/-! NEW SOURCE ONLY. Analytic obstructions for the integral effective pendant
parameters obtained when the unique q value is 3, 6, or 9. -/
set_option autoImplicit false
namespace Paper7C61Four

theorem two_pairs_marked_three_impossible (a b c d t : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : t ≤ 10) (hab : a+b=22) (hcd : c+d=6)
    (hs : a^2+b^2+c^2+d^2=244+2*t)
    (hm : t+4=a ∨ t+4=b ∨ t+4=c ∨ t+4=d) : False := by
  have ht8 : 8 ≤ t := by nlinarith [sq_nonneg (a-b),sq_nonneg (c-d)]
  have hbig : t+4=a ∨ t+4=b := by omega
  have hbox := mul_nonneg (show 0 ≤ t-8 by omega) (show 0 ≤ t-7 by omega)
  rcases hbig with hm | hm <;> nlinarith [sq_nonneg (c-d)]
#print axioms Paper7C61Four.two_pairs_marked_three_impossible

theorem two_pairs_marked_nine_impossible (a b c d t : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (ht : t ≤ 4) (hab : a+b=24) (hcd : c+d=6)
    (hs : a^2+b^2+c^2+d^2=288+6*t)
    (hm : t+12=a ∨ t+12=b ∨ t+12=c ∨ t+12=d) : False := by
  have ht3 : 3 ≤ t := by nlinarith [sq_nonneg (a-b),sq_nonneg (c-d)]
  have hbig : t+12=a ∨ t+12=b := by omega
  have hbox := mul_nonneg (show 0 ≤ t by omega) (show 0 ≤ t-3 by omega)
  rcases hbig with hm | hm <;> nlinarith [sq_nonneg (c-d)]
#print axioms Paper7C61Four.two_pairs_marked_nine_impossible

theorem five_positive_factors_small_square (b c d e f : ℤ)
    (hs : b+c+d+e+f=28 ∨ b+c+d+e+f=30)
    (hq : (b+c+d+e+f=28 → 244 ≤ b^2+c^2+d^2+e^2+f^2) ∧
      (b+c+d+e+f=30 → 288 ≤ b^2+c^2+d^2+e^2+f^2))
    (hdcap : d ≤ 16) (hc0 : 0 ≤ c) (he0 : 0 ≤ e)
    (hE : e=(b-3)*(c-4)) (hC : c=(f-3)*(e-4))
    (hDE : (4-d)*(4-e)=4*b-8) (hCD : (4-c)*(4-d)=4*f-8) :
    c=0 ∨ e=0 := by
  by_contra! hn
  have hEp : 0 < (b-3)*(c-4) := by rw [← hE]; omega
  have hCp : 0 < (f-3)*(e-4) := by rw [← hC]; omega
  rcases mul_pos_iff.mp hEp with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · rcases mul_pos_iff.mp hCp with ⟨hf,he⟩ | ⟨hf,he⟩
    · have hd5 : 5 ≤ d := by
        by_contra hh
        have hh' := mul_nonpos_of_nonneg_of_nonpos
          (show 0 ≤ 4-d by omega) (show 4-e ≤ 0 by omega)
        nlinarith only [hh',hDE,hb]
      have bound (x : ℤ) (hx : 4 ≤ x) (hx' : x ≤ 12) : x^2 ≤ 16*x-48 := by
        nlinarith [mul_nonneg (show 0 ≤ x-4 by omega) (show 0 ≤ 12-x by omega)]
      have bound' (x : ℤ) (hx : 4 ≤ x) (hx' : x ≤ 14) : x^2 ≤ 18*x-56 := by
        nlinarith [mul_nonneg (show 0 ≤ x-4 by omega) (show 0 ≤ 14-x by omega)]
      rcases hs with hs | hs
      · have hb' := bound b (by omega) (by omega)
        have hc' := bound c (by omega) (by omega)
        have hd' := bound d (by omega) (by omega)
        have he' := bound e (by omega) (by omega)
        have hf' := bound f (by omega) (by omega)
        have hh := hq.1 hs
        nlinarith only [hs,hh,hb',hc',hd',he',hf']
      · have hb' := bound' b (by omega) (by omega)
        have hc' := bound' c (by omega) (by omega)
        have hd' := bound' d (by omega) (by omega)
        have he' := bound' e (by omega) (by omega)
        have hf' := bound' f (by omega) (by omega)
        have hh := hq.2 hs
        nlinarith only [hs,hh,hb',hc',hd',he',hf']
    · have hbnd := mixed_factor_sum_bound b c d e f
        (by omega) (by omega) (by omega) (by omega) hE hDE
      omega
  · rcases mul_pos_iff.mp hCp with ⟨hf,he⟩ | ⟨hf,he⟩
    · have hbnd := mixed_factor_sum_bound f e d c b
        (by omega) (by omega) (by omega) (by omega) hC (by nlinarith only [hCD])
      omega
    · omega
#print axioms Paper7C61Four.five_positive_factors_small_square

theorem small_factors_not_minus_272 (d x y : ℤ)
    (hd0 : 0 ≤ d) (hd15 : d ≤ 15)
    (hx0 : -11 ≤ x) (hx4 : x ≤ 4) (hy0 : -11 ≤ y) (hy4 : y ≤ 4)
    (h : d*(4-d)*x*y = -272) : False := by
  let : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have small (z : ℤ) (hz0 : -17 < z) (hz1 : z < 17)
      (hz : (z : ZMod 17)=0) : z=0 := by
    have hdiv : (17 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 17).mp hz
    obtain ⟨w,hw⟩ := hdiv
    omega
  have hmod := congrArg (fun z : ℤ => (z : ZMod 17)) h
  norm_num at hmod
  have hz272 : (-272 : ZMod 17) = 0 := by decide
  rw [hz272] at hmod
  have hz : (d : ZMod 17)=0 ∨ ((4-d : ℤ) : ZMod 17)=0 ∨
      (x : ZMod 17)=0 ∨ (y : ZMod 17)=0 := by
    simpa only [Int.cast_sub,Int.cast_ofNat,mul_eq_zero,or_assoc] using hmod
  rcases hz with hz | hz | hz | hz
  · have he := small d (by omega) (by omega) hz
    rw [he] at h
    norm_num at h
  · have he := small (4-d) (by omega) (by omega) hz
    rw [he] at h
    norm_num at h
  · have he := small x (by omega) (by omega) hz
    rw [he] at h
    norm_num at h
  · have he := small y (by omega) (by omega) hz
    rw [he] at h
    norm_num at h
#print axioms Paper7C61Four.small_factors_not_minus_272

theorem twenty_nine_scalar_impossible (b c d e f : ℤ)
    (hd0 : 0 ≤ d) (hd15 : d ≤ 15) (hc0 : 0 ≤ c) (hc15 : c ≤ 15)
    (he0 : 0 ≤ e) (he15 : e ≤ 15)
    (hs : b+c+d+e+f=29)
    (hleft : 4*(4-b)+(4-d)*(4-e)=8)
    (hright : (4-c)*(4-d)+(4-f)*4=8)
    (htriple : 16=4*((4-c)+(4-e))-(4-c)*(4-d)*(4-e)) : False := by
  have hfactor : d*(4-((4-c)+(4-e)))=68 := by
    nlinarith only [hs,hleft,hright]
  have hprod : d*((4-d)*(4-c)*(4-e)) = -272 := by
    have heq : (4-d)*(4-c)*(4-e)=4*((4-c)+(4-e))-16 := by
      nlinarith only [htriple]
    rw [heq]
    nlinarith only [hfactor]
  exact small_factors_not_minus_272 d (4-c) (4-e) hd0 hd15 (by omega)
    (by omega) (by omega) (by omega) (by simpa only [mul_assoc] using hprod)
#print axioms Paper7C61Four.twenty_nine_scalar_impossible

end Paper7C61Four
