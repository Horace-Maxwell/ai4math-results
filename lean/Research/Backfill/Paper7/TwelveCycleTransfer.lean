import Research.Backfill.Paper7.C61ThreeMonodromy
import Research.Backfill.Paper7.TwelveCycleUnitRank
import Research.Backfill.Paper7.ZeroGapParity

/-! Source-only positive six-step rigidity and its actual twelve-cycle
exceptional-root consequence. No root profile is assumed in the conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MainReduction
open BackfillPaper7.Challenge
open Paper7C61Three
open scoped BigOperators Matrix Classical

theorem positive_six_transfer_identity (a b c d e f : ℝ)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d) (he : 1 ≤ e) (hf : 1 ≤ f)
    (h : realSixProduct a b c d e f = 1) :
    a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 ∧ e = 1 ∧ f = 1 := by
  obtain ⟨hab,hbc,_htriple⟩ := real_six_triple_data a b c d e f h
  have hprodab : 1 ≤ a*b := by nlinarith [mul_nonneg (by linarith : 0 ≤ a-1) (by linarith : 0 ≤ b-1)]
  have hprodde : 1 ≤ d*e := by nlinarith [mul_nonneg (by linarith : 0 ≤ d-1) (by linarith : 0 ≤ e-1)]
  have haab : a ≤ a*b := by nlinarith only [mul_nonneg (by linarith : 0 ≤ a) (by linarith : 0 ≤ b-1)]
  have hbab : b ≤ a*b := by nlinarith only [mul_nonneg (by linarith : 0 ≤ a-1) (by linarith : 0 ≤ b)]
  have hdde : d ≤ d*e := by nlinarith only [mul_nonneg (by linarith : 0 ≤ d) (by linarith : 0 ≤ e-1)]
  have hede : e ≤ d*e := by nlinarith only [mul_nonneg (by linarith : 0 ≤ d-1) (by linarith : 0 ≤ e)]
  have ha1 : a = 1 := by linarith only [ha,hab,hprodde,haab]
  have hb1 : b = 1 := by linarith only [hb,hab,hprodde,hbab]
  have hd1 : d = 1 := by linarith only [hd,hab,hprodab,hdde]
  have he1 : e = 1 := by linarith only [he,hab,hprodab,hede]
  rw [hb1,he1,one_mul,one_mul] at hbc
  exact ⟨ha1,hb1,by linarith,hd1,he1,by linarith⟩
#print axioms Paper7MainReduction.positive_six_transfer_identity

theorem twelve_alternating_unit_identity_zero (p : Fin 12 → ℕ)
    (h1 : p 1 = 0) (h3 : p 3 = 0) (h5 : p 5 = 0)
    (h7 : p 7 = 0) (h9 : p 9 = 0) (h11 : p 11 = 0)
    (hid : Mono 12 p (fun _ => 0) 1 = 1) : p 0 = 0 := by
  let C : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;1,-1]
  have hfac : realSixProduct ((p 0 : ℝ)+1) ((p 2 : ℝ)+1) ((p 4 : ℝ)+1)
      ((p 6 : ℝ)+1) ((p 8 : ℝ)+1) ((p 10 : ℝ)+1) = C*Mono 12 p (fun _ => 0) 1*C := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [C,Mono,Tk,fk,realSixProduct,realTransfer,List.finRange_succ,
        h1,h3,h5,h7,h9,h11,Matrix.mul_apply,Fin.sum_univ_two]
    all_goals ring
  have hI : realSixProduct ((p 0 : ℝ)+1) ((p 2 : ℝ)+1) ((p 4 : ℝ)+1)
      ((p 6 : ℝ)+1) ((p 8 : ℝ)+1) ((p 10 : ℝ)+1) = 1 := by
    rw [hfac,hid,mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [C,Matrix.mul_apply,Fin.sum_univ_two]
  have hpos (i : Fin 12) : (1 : ℝ) ≤ (p i : ℝ)+1 := by
    have hh : (0 : ℝ) ≤ p i := Nat.cast_nonneg _
    linarith
  have hzero := (positive_six_transfer_identity _ _ _ _ _ _
    (hpos 0) (hpos 2) (hpos 4) (hpos 6) (hpos 8) (hpos 10) hI).1
  have hz : (p 0 : ℝ) = 0 := by linarith only [hzero]
  exact_mod_cast hz
#print axioms Paper7MainReduction.twelve_alternating_unit_identity_zero

end Paper7MainReduction
