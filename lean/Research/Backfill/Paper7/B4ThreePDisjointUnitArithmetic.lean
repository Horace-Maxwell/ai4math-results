import Research.Backfill.Paper7.B4ThreePDisjointPolynomial

/-! Source-only exceptional-root arithmetic. The two zero-determinant
parameter shapes are derived from inequalities, without a parameter table. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge

theorem positive_three_unit_product_cases (u v w : ℕ)
    (hu : 0 < u) (hv : 0 < v) (hw : 0 < w) (he : u*v*w = u+w) :
    (u = 1 ∧ v = 2 ∧ w = 1) ∨ (u = 2 ∧ v = 1 ∧ w = 2) := by
  have huR : (1 : ℝ) ≤ u := by exact_mod_cast (show 1 ≤ u by omega)
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast (show 1 ≤ w by omega)
  have heR : (u : ℝ)*v*w = (u : ℝ)+w := by exact_mod_cast he
  have hu_le : (u : ℝ) ≤ (u : ℝ)*w := by
    have hh := mul_nonneg (show (0 : ℝ) ≤ u by linarith) (show 0 ≤ (w : ℝ)-1 by linarith)
    nlinarith only [hh]
  have hw_le : (w : ℝ) ≤ (u : ℝ)*w := by
    have hh := mul_nonneg (show 0 ≤ (u : ℝ)-1 by linarith) (show (0 : ℝ) ≤ w by linarith)
    nlinarith only [hh]
  have huwpos : (0 : ℝ) < (u : ℝ)*w := mul_pos (by linarith) (by linarith)
  have hv2 : v ≤ 2 := by
    by_contra hh
    have hv3 : (3 : ℝ) ≤ v := by exact_mod_cast (show 3 ≤ v by omega)
    have hprod := mul_nonneg (show 0 ≤ (v : ℝ)-3 by linarith) huwpos.le
    nlinarith only [heR,hu_le,hw_le,huwpos,hprod]
  have hvcases : v = 1 ∨ v = 2 := by omega
  rcases hvcases with hv1 | hv2
  · subst v
    norm_num at heR
    have hu2 : 2 ≤ u := by
      by_contra hh
      have hu1 : u = 1 := by omega
      rw [hu1] at he
      norm_num at he
    have hw2 : 2 ≤ w := by
      by_contra hh
      have hw1 : w = 1 := by omega
      rw [hw1] at he
      norm_num at he
    have hu2R : (2 : ℝ) ≤ u := by exact_mod_cast hu2
    have hw2R : (2 : ℝ) ≤ w := by exact_mod_cast hw2
    have hcross := mul_nonneg (show 0 ≤ (u : ℝ)-2 by linarith)
      (show 0 ≤ (w : ℝ)-2 by linarith)
    have hsumR : (u : ℝ)+w ≤ 4 := by nlinarith only [heR,hcross]
    have hsum : u+w ≤ 4 := by exact_mod_cast hsumR
    exact Or.inr ⟨by omega,rfl,by omega⟩
  · subst v
    norm_num at heR
    have hcross := mul_nonneg (show 0 ≤ (u : ℝ)-1 by linarith)
      (show 0 ≤ (w : ℝ)-1 by linarith)
    have hu1R : (u : ℝ) ≤ 1 := by nlinarith only [heR,hcross,hu_le]
    have hw1R : (w : ℝ) ≤ 1 := by nlinarith only [heR,hcross,hw_le]
    have hu1 : u ≤ 1 := by exact_mod_cast hu1R
    have hw1 : w ≤ 1 := by exact_mod_cast hw1R
    exact Or.inl ⟨by omega,rfl,by omega⟩
#print axioms Paper7B4Analytic.positive_three_unit_product_cases

theorem three_disjoint_integral_delta_positive (a b c d : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hG : IsIntegralGraph (SG 4 (threePDisjointP a b c) (threePDisjointQ d))) :
    2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c ∧ 0 < threePDisjointDelta a b c := by
  have hdelta := three_disjoint_integral_delta_nonneg a b c d ha hb hc hd hG
  have hnoones : ¬ (a = 1 ∧ c = 1) := by
    rintro ⟨ha1,hc1⟩
    subst a
    subst c
    exact three_disjoint_opposite_ones_nonintegral b d hb hd hG
  have ha2 : 2 ≤ a := by
    by_contra hh
    have ha1 : a = 1 := by omega
    have hcR : (c : ℝ) ≤ 1 := by
      unfold threePDisjointDelta at hdelta
      rw [ha1] at hdelta
      norm_num at hdelta
      linarith only [hdelta]
    have hc1 : c ≤ 1 := by exact_mod_cast hcR
    exact hnoones ⟨ha1,by omega⟩
  have hc2 : 2 ≤ c := by
    by_contra hh
    have hc1 : c = 1 := by omega
    have haR : (a : ℝ) ≤ 1 := by
      unfold threePDisjointDelta at hdelta
      rw [hc1] at hdelta
      norm_num at hdelta
      linarith only [hdelta]
    have ha1 : a ≤ 1 := by exact_mod_cast haR
    exact hnoones ⟨by omega,hc1⟩
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha2
  have hcR : (2 : ℝ) ≤ c := by exact_mod_cast hc2
  have hb2 : 2 ≤ b := by
    by_contra hh
    have hb1 : b = 1 := by omega
    unfold threePDisjointDelta at hdelta
    rw [hb1] at hdelta
    norm_num at hdelta
    linarith only [hdelta,haR,hcR]
  refine ⟨ha2,hb2,hc2,?_⟩
  by_contra hh
  have hzero : threePDisjointDelta a b c = 0 := by linarith only [hh,hdelta]
  let u := a-1
  let v := b-1
  let w := c-1
  have hau : a = u+1 := by dsimp [u]; omega
  have hbv : b = v+1 := by dsimp [v]; omega
  have hcw : c = w+1 := by dsimp [w]; omega
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have hw : 0 < w := by omega
  have heR : (u : ℝ)*v*w = (u : ℝ)+w := by
    unfold threePDisjointDelta at hzero
    rw [hau,hbv,hcw] at hzero
    push_cast at hzero
    nlinarith only [hzero]
  have he : u*v*w = u+w := by exact_mod_cast heR
  have hcases := positive_three_unit_product_cases u v w hu hv hw he
  have hca : c = a := by rcases hcases with h | h <;> omega
  have ha3 : a ≤ 3 := by rcases hcases with h | h <;> omega
  rw [hca] at hG
  exact three_disjoint_small_equal_nonintegral a b d ha2 ha3 hG
#print axioms Paper7B4Analytic.three_disjoint_integral_delta_positive

end Paper7B4Analytic
