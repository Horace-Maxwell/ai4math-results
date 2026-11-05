import Mathlib

/-! Source-only analytic bound for six integral transfer coefficients.
No parameter enumeration, compilation, or formal acceptance is claimed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61BetaEight
open scoped Matrix

/-- The first neighbour of a coefficient at most -4 must be negative. -/
theorem large_negative_neighbour (a b c d e : ℤ)
    (ha : a ≤ -4) (hb : b ≤ 1) (hc : c ≤ 1) (hd : d ≤ 1) (_he : e ≤ 1)
    (hprod : a*b+d*e = 2) (hpoly : e = a+c-a*b*c) : b ≤ -1 := by
  by_contra hneg
  have hb0 : 0 ≤ b := by omega
  have hcases : b = 0 ∨ b = 1 := by omega
  rcases hcases with rfl | rfl
  · have he3 : e ≤ -3 := by nlinarith only [hpoly,ha,hc]
    have hde : d*e = 2 := by nlinarith only [hprod]
    have hdneg : d ≤ -1 := by
      by_contra h
      have hd0 : 0 ≤ d := by omega
      have hmul := mul_nonpos_of_nonneg_of_nonpos hd0 (show e ≤ 0 by omega)
      nlinarith only [hde,hmul]
    have hmul := mul_nonneg (show 0 ≤ -d-1 by omega) (show 0 ≤ -e by omega)
    nlinarith only [hde,hmul,he3]
  · have hc0 : c ≤ 0 := by
      by_contra h
      have hc1 : c = 1 := by omega
      rw [hc1] at hpoly
      have he1 : e = 1 := by nlinarith only [hpoly]
      rw [he1] at hprod
      nlinarith only [hprod,ha,hd]
    have hea : e ≤ a := by
      have hmul := mul_nonpos_of_nonpos_of_nonneg hc0 (show 0 ≤ 1-a by omega)
      nlinarith only [hpoly,hmul]
    have hdneg : d ≤ -1 := by
      by_contra h
      have hd0 : 0 ≤ d := by omega
      have hmul := mul_nonpos_of_nonneg_of_nonpos hd0 (show e ≤ 0 by omega)
      nlinarith only [hprod,hmul,ha]
    have hc_eq : c = 0 := by
      by_contra h
      have hc1 : c ≤ -1 := by omega
      have hmul1 := mul_nonpos_of_nonpos_of_nonneg
        (show c+1 ≤ 0 by omega) (show 0 ≤ 1-a by omega)
      have he2 : e ≤ 2*a-1 := by nlinarith only [hpoly,hmul1]
      have hmul2 := mul_nonneg (show 0 ≤ -d-1 by omega) (show 0 ≤ -e by omega)
      nlinarith only [hprod,he2,hmul2,ha]
    have hea_eq : e = a := by rw [hc_eq] at hpoly; nlinarith only [hpoly]
    rw [hea_eq] at hprod
    have hd2 : d ≤ -2 := by
      by_contra h
      have hd1 : d = -1 := by omega
      rw [hd1] at hprod
      nlinarith only [hprod]
    have hmul := mul_nonneg (show 0 ≤ -d-2 by omega) (show 0 ≤ -a by omega)
    nlinarith only [hprod,hmul,ha]
#print axioms Paper7C61BetaEight.large_negative_neighbour

/-- The scalar identities of a six-step identity monodromy bound every head
coefficient below by -3. The argument splits by signs, without tuple search. -/
theorem six_scalar_head_lower (a b c d e f : ℤ)
    (_ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (h01 : a*b+d*e = 2) (h12 : b*c+e*f = 2)
    (h23 : c*d+f*a = 2) (hpoly : e = a+c-a*b*c) : -3 ≤ a := by
  by_contra h
  have ha4 : a ≤ -4 := by omega
  have hb1 := large_negative_neighbour a b c d e ha4 hb hc hd he h01 hpoly
  have hrev : c = a+e-a*f*e := by
    linear_combination -hpoly + a*h12
  have hprodrev : a*f+d*c = 2 := by nlinarith only [h23]
  have hf1 := large_negative_neighbour a f e d c ha4 hf he hd hc hprodrev hrev
  have hab : 4 ≤ a*b := by
    have hmul := mul_nonneg (show 0 ≤ -a-4 by omega) (show 0 ≤ -b by omega)
    nlinarith only [hmul,hb1]
  have haf : 4 ≤ a*f := by
    have hmul := mul_nonneg (show 0 ≤ -a-4 by omega) (show 0 ≤ -f by omega)
    nlinarith only [hmul,hf1]
  have hde : d*e ≤ -2 := by nlinarith only [h01,hab]
  have hcd : c*d ≤ -2 := by nlinarith only [h23,haf]
  have hd1 : d = 1 := by
    by_contra h
    have hd0 : d ≤ 0 := by omega
    have he1 : e = 1 := by
      by_contra h
      have he0 : e ≤ 0 := by omega
      have hmul := mul_nonneg_of_nonpos_of_nonpos hd0 he0
      nlinarith only [hde,hmul]
    have hc1 : c = 1 := by
      by_contra h
      have hc0 : c ≤ 0 := by omega
      have hmul := mul_nonneg_of_nonpos_of_nonpos hc0 hd0
      nlinarith only [hcd,hmul]
    rw [he1,hc1] at h12
    nlinarith only [h12,hb1,hf1]
  have he_eq : e = 2-a*b := by rw [hd1] at h01; nlinarith only [h01]
  have hc_eq : c = 2-a*f := by rw [hd1] at h23; nlinarith only [h23]
  rw [he_eq,hc_eq] at h12
  have hbf : 1 ≤ b*f := by
    have hmul := mul_nonneg (show 0 ≤ -b-1 by omega) (show 0 ≤ -f-1 by omega)
    nlinarith only [hmul,hb1,hf1]
  have hB : -b ≤ b*f := by
    have hmul := mul_nonneg (show 0 ≤ -b by omega) (show 0 ≤ -f-1 by omega)
    nlinarith only [hmul]
  have hF : -f ≤ b*f := by
    have hmul := mul_nonneg (show 0 ≤ -f by omega) (show 0 ≤ -b-1 by omega)
    nlinarith only [hmul]
  have hlarge := mul_nonneg (show 0 ≤ -a-4 by omega) (show 0 ≤ b*f by omega)
  nlinarith only [h12,hbf,hB,hF,hlarge]
#print axioms Paper7C61BetaEight.six_scalar_head_lower

def intTransfer (a : ℤ) : Matrix (Fin 2) (Fin 2) ℝ := !![(a : ℝ),-1;1,0]
#print axioms Paper7C61BetaEight.intTransfer

def sixProduct (a b c d e f : ℤ) : Matrix (Fin 2) (Fin 2) ℝ :=
  intTransfer f * intTransfer e * intTransfer d *
    intTransfer c * intTransfer b * intTransfer a
#print axioms Paper7C61BetaEight.sixProduct

theorem six_product_rotate (a b c d e f : ℤ) (h : sixProduct a b c d e f = 1) :
    sixProduct b c d e f a = 1 := by
  unfold sixProduct at h ⊢
  have hr := mul_eq_one_comm.mp h
  simpa only [mul_assoc] using hr
#print axioms Paper7C61BetaEight.six_product_rotate

/-- Comparing the first triple with the explicit inverse of the last triple. -/
theorem six_product_triple_data (a b c d e f : ℤ)
    (h : sixProduct a b c d e f = 1) :
    a*b+d*e = 2 ∧ b*c+e*f = 2 ∧ e = a+c-a*b*c := by
  let U : Matrix (Fin 2) (Fin 2) ℝ :=
    !![-(e : ℝ),(f : ℝ)*e-1;1-(e : ℝ)*d,(f : ℝ)*e*d-f-d]
  have hinv : U * (intTransfer f * intTransfer e * intTransfer d) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U,intTransfer,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  have hp : (intTransfer f * intTransfer e * intTransfer d) *
      (intTransfer c * intTransfer b * intTransfer a) = 1 := by
    simpa only [sixProduct,mul_assoc] using h
  have ht : intTransfer c * intTransfer b * intTransfer a = U := by
    calc
      _ = 1 * (intTransfer c * intTransfer b * intTransfer a) := by simp
      _ = (U * (intTransfer f * intTransfer e * intTransfer d)) *
          (intTransfer c * intTransfer b * intTransfer a) := by rw [hinv]
      _ = U * ((intTransfer f * intTransfer e * intTransfer d) *
          (intTransfer c * intTransfer b * intTransfer a)) := by rw [mul_assoc]
      _ = U := by rw [hp,mul_one]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) ht
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) ht
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) ht
  norm_num [U,intTransfer,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h10
  refine ⟨?_,?_,?_⟩
  · exact_mod_cast (by nlinarith only [h10] :
      (a : ℝ)*b+(d : ℝ)*e = 2)
  · exact_mod_cast (by nlinarith only [h01] :
      (b : ℝ)*c+(e : ℝ)*f = 2)
  · exact_mod_cast (by nlinarith only [h00] :
      (e : ℝ) = (a : ℝ)+c-(a : ℝ)*b*c)
#print axioms Paper7C61BetaEight.six_product_triple_data

theorem six_product_head_lower (a b c d e f : ℤ)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (h : sixProduct a b c d e f = 1) : -3 ≤ a := by
  obtain ⟨h01,h12,hpoly⟩ := six_product_triple_data a b c d e f h
  have hr1 := six_product_rotate a b c d e f h
  have hr2 := six_product_rotate b c d e f a hr1
  have h23 := (six_product_triple_data c d e f a b hr2).1
  exact six_scalar_head_lower a b c d e f ha hb hc hd he hf h01 h12 h23 hpoly
#print axioms Paper7C61BetaEight.six_product_head_lower

theorem six_product_sum_lower (a b c d e f : ℤ)
    (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) (he : e ≤ 1) (hf : f ≤ 1)
    (h : sixProduct a b c d e f = 1) : -18 ≤ a+b+c+d+e+f := by
  have h1 := six_product_rotate a b c d e f h
  have h2 := six_product_rotate b c d e f a h1
  have h3 := six_product_rotate c d e f a b h2
  have h4 := six_product_rotate d e f a b c h3
  have h5 := six_product_rotate e f a b c d h4
  have hla := six_product_head_lower a b c d e f ha hb hc hd he hf h
  have hlb := six_product_head_lower b c d e f a hb hc hd he hf ha h1
  have hlc := six_product_head_lower c d e f a b hc hd he hf ha hb h2
  have hld := six_product_head_lower d e f a b c hd he hf ha hb hc h3
  have hle := six_product_head_lower e f a b c d he hf ha hb hc hd h4
  have hlf := six_product_head_lower f a b c d e hf ha hb hc hd he h5
  omega
#print axioms Paper7C61BetaEight.six_product_sum_lower

end Paper7C61BetaEight
