import Research.Backfill.Paper7.C61TwoSiteConcentration
import Research.Backfill.Paper7.C61PolynomialTransport
import Research.Backfill.Paper7.BMS32Polynomial
import Research.Backfill.Paper7.C61TwoSiteDet

set_option autoImplicit false
noncomputable section
namespace Paper7C61Small
open Polynomial BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters
open scoped Matrix Classical

def twoSiteCore (j : Fin 6) : Matrix (Fin 6) (Fin 6) ℤ :=
  !![4-(twoSite j 0 : ℤ),-2,0,0,0,-2;
     -2,4-(twoSite j 1 : ℤ),-2,0,0,0;
     0,-2,4-(twoSite j 2 : ℤ),-2,0,0;
     0,0,-2,4-(twoSite j 3 : ℤ),-2,0;
     0,0,0,-2,4-(twoSite j 4 : ℤ),-2;
     -2,0,0,0,-2,4-(twoSite j 5 : ℤ)]
#print axioms Paper7C61Small.twoSiteCore

theorem twoSiteCore_det_one : (twoSiteCore 1).det = -288 := by
  change (Paper7C61TwoSiteDet.nearCore 1 4).det = -288
  exact Paper7C61TwoSiteDet.nearCore_one_four
#print axioms Paper7C61Small.twoSiteCore_det_one

theorem twoSiteCore_det_two : (twoSiteCore 2).det = 576 := by
  change (Paper7C61TwoSiteDet.nearCore 4 1).det = 576
  exact Paper7C61TwoSiteDet.nearCore_four_one
#print axioms Paper7C61Small.twoSiteCore_det_two

theorem twoSiteCore_det_three : (twoSiteCore 3).det = 864 := by
  change (!![-2,-2,0,0,0,-2;
              -2,4,-2,0,0,0;
              0,-2,4,-2,0,0;
              0,0,-2,1,-2,0;
              0,0,0,-2,4,-2;
              -2,0,0,0,-2,4] : Matrix (Fin 6) (Fin 6) ℤ).det = 864
  rw [Paper7BMS32.det_six_reflection]
  norm_num
#print axioms Paper7C61Small.twoSiteCore_det_three

theorem twoSiteCore_det_four : (twoSiteCore 4).det = 576 := by
  have hm : (twoSiteCore 4).submatrix Paper7C61TwoSiteDet.reflection
      Paper7C61TwoSiteDet.reflection = twoSiteCore 2 := by
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;>
      norm_num [twoSiteCore, twoSite, Paper7C61TwoSiteDet.reflection,
        Matrix.submatrix_apply]
  have hd := Matrix.det_submatrix_equiv_self Paper7C61TwoSiteDet.reflection (twoSiteCore 4)
  rw [hm] at hd
  rw [← hd]
  exact twoSiteCore_det_two
#print axioms Paper7C61Small.twoSiteCore_det_four

theorem twoSiteCore_det_five : (twoSiteCore 5).det = -288 := by
  have hm : (twoSiteCore 5).submatrix Paper7C61TwoSiteDet.reflection
      Paper7C61TwoSiteDet.reflection = twoSiteCore 1 := by
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;>
      norm_num [twoSiteCore, twoSite, Paper7C61TwoSiteDet.reflection,
        Matrix.submatrix_apply]
  have hd := Matrix.det_submatrix_equiv_self Paper7C61TwoSiteDet.reflection (twoSiteCore 5)
  rw [hm] at hd
  rw [← hd]
  exact twoSiteCore_det_one
#print axioms Paper7C61Small.twoSiteCore_det_five

theorem twoSiteCore_det_ne_zero (j : Fin 6) (hj : j ≠ 0) : (twoSiteCore j).det ≠ 0 := by
  fin_cases j
  · exact (hj rfl).elim
  · change (twoSiteCore 1).det ≠ 0
    rw [twoSiteCore_det_one]; norm_num
  · change (twoSiteCore 2).det ≠ 0
    rw [twoSiteCore_det_two]; norm_num
  · change (twoSiteCore 3).det ≠ 0
    rw [twoSiteCore_det_three]; norm_num
  · change (twoSiteCore 4).det ≠ 0
    rw [twoSiteCore_det_four]; norm_num
  · change (twoSiteCore 5).det ≠ 0
    rw [twoSiteCore_det_five]; norm_num
#print axioms Paper7C61Small.twoSiteCore_det_ne_zero

theorem twoSite_eval_two_ne_zero (j : Fin 6) (hj : j ≠ 0) :
    (clearedF 6 (twoSite j) (fun _ => 0)).eval 2 ≠ 0 := by
  have hm : (clearedMatrix 6 (twoSite j) (fun _ => 0)).map (Polynomial.evalRingHom (2 : ℤ)) =
      (3 : ℤ) • twoSiteCore j := by
    apply Matrix.ext
    intro i k
    fin_cases i <;> fin_cases k <;>
      norm_num [Matrix.map_apply,clearedMatrix,Paper7BMS32.cycle_adjacency_six,
        twoSiteCore,Matrix.smul_apply,smul_eq_mul] <;> ring
  change (Polynomial.evalRingHom (2 : ℤ)) (clearedF 6 (twoSite j) (fun _ => 0)) ≠ 0
  rw [clearedF,RingHom.map_det]
  change ((clearedMatrix 6 (twoSite j) (fun _ => 0)).map
    (Polynomial.evalRingHom (2 : ℤ))).det ≠ 0
  rw [hm,Matrix.det_smul,Fintype.card_fin]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (3 : ℤ) ≠ 0)) (twoSiteCore_det_ne_zero j hj)
#print axioms Paper7C61Small.twoSite_eval_two_ne_zero

theorem root_three_one_two_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) (h0 : (actual p q 0).val = 1) : False := by
  obtain ⟨hq,_he,hP,hS,_hmax⟩ := root_three_one_two_data p q hn hG h3 h0
  obtain ⟨k,j,hjk,hk,hj,hz⟩ := sum9_square45_two_sites p hP hS
  obtain ⟨σ,t,hσ,ht,hpσ⟩ := two_sites_normalize p k j hjk hk hj hz
  have hF := Paper7C61Saturated.clearedF_comp p q σ hσ
  have hqσ : q ∘ σ = (fun _ => 0) := by rw [hq]; rfl
  rw [hpσ,hqσ] at hF
  have hzero : (clearedF 6 p q).eval 2 = 0 := by
    rw [clearedF_profile p q hn hG]
    obtain ⟨h1,h2,h3',h4⟩ := h3
    norm_num [polynomial,Fin.prod_univ_succ,value,h0,h1,h2,h3',h4]
  apply twoSite_eval_two_ne_zero t ht
  rw [hF]
  exact hzero
#print axioms Paper7C61Small.root_three_one_two_impossible

theorem root_three_has_two_twos (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) : (actual p q 0).val = 2 := by
  have hlt := (actual p q 0).isLt
  by_contra h
  have hc : (actual p q 0).val = 0 ∨ (actual p q 0).val = 1 := by omega
  rcases hc with h0 | h0
  · exact root_three_zero_twos_impossible p q hn hG h3 h0
  · exact root_three_one_two_impossible p q hn hG h3 h0
#print axioms Paper7C61Small.root_three_has_two_twos

end Paper7C61Small
