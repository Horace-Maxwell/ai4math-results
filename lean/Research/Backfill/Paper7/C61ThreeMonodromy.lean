import Research.Backfill.Paper7.C61TwoSiteExclusion
import Research.Backfill.Paper7.C61PerronDegreeBound
import Research.Backfill.Paper7.SmatMonodromyEquivalence
import Research.Backfill.Paper7.C61SixMonodromyBound

/-! Source-only bridges from the original Perron-three profile to its
ordinary eigenvalue-two monodromy. No monodromy hypothesis is added. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Three
open BackfillPaper7.Challenge
open Paper7C61Profile Paper7C61Small Paper7C61Higher
open scoped Matrix Classical

def realTransfer (a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![a,-1;1,0]
#print axioms Paper7C61Three.realTransfer

def realSixProduct (a b c d e f : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  realTransfer f * realTransfer e * realTransfer d *
    realTransfer c * realTransfer b * realTransfer a
#print axioms Paper7C61Three.realSixProduct

theorem real_six_rotate (a b c d e f : ℝ) (h : realSixProduct a b c d e f = 1) :
    realSixProduct b c d e f a = 1 := by
  unfold realSixProduct at h ⊢
  have hr := mul_eq_one_comm.mp h
  simpa only [mul_assoc] using hr
#print axioms Paper7C61Three.real_six_rotate

theorem real_six_triple_data (a b c d e f : ℝ)
    (h : realSixProduct a b c d e f = 1) :
    a*b+d*e = 2 ∧ b*c+e*f = 2 ∧ e = a+c-a*b*c := by
  let U : Matrix (Fin 2) (Fin 2) ℝ := !![-e,f*e-1;1-e*d,f*e*d-f-d]
  have hinv : U * (realTransfer f * realTransfer e * realTransfer d) = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [U,realTransfer,Matrix.mul_apply,Fin.sum_univ_two] <;> ring
  have hp : (realTransfer f * realTransfer e * realTransfer d) *
      (realTransfer c * realTransfer b * realTransfer a) = 1 := by
    simpa only [realSixProduct,mul_assoc] using h
  have ht : realTransfer c * realTransfer b * realTransfer a = U := by
    calc
      _ = 1 * (realTransfer c * realTransfer b * realTransfer a) := by simp
      _ = (U * (realTransfer f * realTransfer e * realTransfer d)) *
          (realTransfer c * realTransfer b * realTransfer a) := by rw [hinv]
      _ = U * ((realTransfer f * realTransfer e * realTransfer d) *
          (realTransfer c * realTransfer b * realTransfer a)) := by rw [mul_assoc]
      _ = U := by rw [hp,mul_one]
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) ht
  have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) ht
  have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 1 0) ht
  norm_num [U,realTransfer,Matrix.mul_apply,Fin.sum_univ_two] at h00 h01 h10
  exact ⟨by nlinarith only [h10],by nlinarith only [h01],by nlinarith only [h00]⟩
#print axioms Paper7C61Three.real_six_triple_data

theorem root_three_monodromy_two (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) : Mono 6 p q 2 = 1 := by
  have h0 := root_three_has_two_twos p q hn hG h3
  have hm : mult (SG 6 p q) 2 = 2 := by
    have hi := actual_eq_mult p q (0 : Fin 5)
    norm_num [value] at hi
    omega
  exact (Paper7Lemma22Periodic.lemma22_ordinary_clause 6 p q (by decide)
    2 (by norm_num) (by norm_num) (by norm_num)).2.2.1.mp hm
#print axioms Paper7C61Three.root_three_monodromy_two

def coefficientTwo (p q : Fin 6 → ℕ) (k : Fin 6) : ℝ :=
  2-(p k : ℝ)/2-2*(q k : ℝ)/3
#print axioms Paper7C61Three.coefficientTwo

theorem mono_two_six_product (p q : Fin 6 → ℕ) :
    Mono 6 p q 2 = realSixProduct (coefficientTwo p q 0)
      (coefficientTwo p q 1) (coefficientTwo p q 2)
      (coefficientTwo p q 3) (coefficientTwo p q 4) (coefficientTwo p q 5) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Mono,Tk,fk,realSixProduct,realTransfer,coefficientTwo,
      List.finRange_succ] <;> ring
#print axioms Paper7C61Three.mono_two_six_product

theorem root_three_six_product (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) :
    realSixProduct (coefficientTwo p q 0) (coefficientTwo p q 1)
      (coefficientTwo p q 2) (coefficientTwo p q 3)
      (coefficientTwo p q 4) (coefficientTwo p q 5) = 1 := by
  rw [← mono_two_six_product]
  exact root_three_monodromy_two p q hn hG h3
#print axioms Paper7C61Three.root_three_six_product

theorem root_three_coefficient_pairs (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) :
    coefficientTwo p q 0 * coefficientTwo p q 1 +
      coefficientTwo p q 3 * coefficientTwo p q 4 = 2 ∧
    coefficientTwo p q 1 * coefficientTwo p q 2 +
      coefficientTwo p q 4 * coefficientTwo p q 5 = 2 ∧
    coefficientTwo p q 2 * coefficientTwo p q 3 +
      coefficientTwo p q 5 * coefficientTwo p q 0 = 2 := by
  have h := root_three_six_product p q hn hG h3
  have ht := real_six_triple_data _ _ _ _ _ _ h
  have hr := real_six_rotate _ _ _ _ _ _ (real_six_rotate _ _ _ _ _ _ h)
  exact ⟨ht.1,ht.2.1,(real_six_triple_data _ _ _ _ _ _ hr).1⟩
#print axioms Paper7C61Three.root_three_coefficient_pairs

theorem root_three_load_le_six (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h3 : RootThree (actual p q)) : ∀ k, p k+q k ≤ 6 := by
  obtain ⟨_h1,h2,h3,h4⟩ := h3
  have hb := spectrum_upper_from_profile p q hn hG 3 (by norm_num) (by
    intro i hi
    fin_cases i
    · norm_num [value]
    · norm_num [value]
    · change 0 < (actual p q 2).val at hi
      rw [h2] at hi; omega
    · change 0 < (actual p q 3).val at hi
      rw [h3] at hi; omega
    · change 0 < (actual p q 4).val at hi
      rw [h4] at hi; omega)
  intro k
  have hd := sun_load_lt_sq_sub_two p q 3 (by norm_num) hb k
  norm_num at hd
  have hnat : 2+p k+q k < 9 := by exact_mod_cast hd
  omega
#print axioms Paper7C61Three.root_three_load_le_six

end Paper7C61Three
