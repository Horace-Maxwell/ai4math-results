import Research.Backfill.Paper7.C61DoubleRootMonodromy
import Research.Backfill.Paper7.C61AlphaSixParity
import Research.Backfill.Paper7.C61ParameterSquares

/-! NEW SOURCE ONLY. An actual eigenvalue-two trace detects the missing
cubic information in the alternating three-site moment domain. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Three
open scoped BigOperators Matrix Classical

theorem actual_one_two_trace (p q : Fin 6 → ℕ)
    (h : (actual p q 0).val = 1) : (Mono 6 p q 2).trace = 2 := by
  have hm : mult (SG 6 p q) 2 = 1 := by
    have hi := actual_eq_mult p q (0 : Fin 5)
    norm_num [value] at hi
    omega
  exact ((Paper7Lemma22Periodic.lemma22_ordinary_clause 6 p q (by decide)
    2 (by norm_num) (by norm_num) (by norm_num)).2.2.2.mp hm).2
#print axioms Paper7C61Four.actual_one_two_trace

theorem alternating_trace_rotate (a b c d e f : ℝ) :
    (realSixProduct a b c d e f).trace = (realSixProduct b c d e f a).trace := by
  have h := Matrix.trace_mul_comm
    (realTransfer f*realTransfer e*realTransfer d*realTransfer c*realTransfer b)
    (realTransfer a)
  simpa only [realSixProduct,mul_assoc] using h
#print axioms Paper7C61Four.alternating_trace_rotate

theorem alternating_trace_product (a b c : ℕ)
    (hs : a+b+c = 23) (hq : a^2+b^2+c^2 = 243)
    (ht : (realSixProduct (2-(a : ℝ)/2) 2 (2-(b : ℝ)/2) 2
      (2-(c : ℝ)/2) 2).trace = 2) : (a+2)*(b+2)*(c+2) = 603 := by
  have hsR : (a : ℝ)+b+c = 23 := by exact_mod_cast hs
  have hqR : (a : ℝ)^2+(b : ℝ)^2+(c : ℝ)^2 = 243 := by exact_mod_cast hq
  have hss : ((a : ℝ)+b+c)^2 = 529 := by rw [hsR]; norm_num
  norm_num [realSixProduct,realTransfer,Matrix.trace,Matrix.mul_apply,Fin.sum_univ_two] at ht
  have hp : ((a : ℝ)+2)*((b : ℝ)+2)*((c : ℝ)+2) = 603 := by
    nlinarith only [ht,hsR,hqR,hss]
  exact_mod_cast hp
#print axioms Paper7C61Four.alternating_trace_product

theorem bounded_three_product_not_603 (a b c : ℕ)
    (ha : a ≤ 13) (hb : b ≤ 13) (hc : c ≤ 13)
    (h : (a+2)*(b+2)*(c+2) = 603) : False := by
  have hprime : Nat.Prime 67 := by norm_num
  have hdiv : 67 ∣ (a+2)*(b+2)*(c+2) := by rw [h]; norm_num
  rcases hprime.dvd_mul.mp hdiv with hab | hcc
  · rcases hprime.dvd_mul.mp hab with haa | hbb
    · have hle := Nat.le_of_dvd (by omega : 0 < a+2) haa
      omega
    · have hle := Nat.le_of_dvd (by omega : 0 < b+2) hbb
      omega
  · have hle := Nat.le_of_dvd (by omega : 0 < c+2) hcc
    omega
#print axioms Paper7C61Four.bounded_three_product_not_603

theorem alternating_sum23_square243_trace_impossible (p : Fin 6 → ℕ)
    (ha : zeroExponent p = 6) (hP : totalP 6 p = 23) (hS : squares 6 p = 243)
    (hcap : ∀ k, p k ≤ 13) (ht : (Mono 6 p (fun _ => 0) 2).trace = 2) : False := by
  rw [mono_two_six_product] at ht
  have hP' : p 0+p 1+p 2+p 3+p 4+p 5 = 23 := by
    simpa [totalP,Fin.sum_univ_succ,Nat.add_assoc] using hP
  have hS' : p 0^2+p 1^2+p 2^2+p 3^2+p 4^2+p 5^2 = 243 := by
    simpa [squares,Fin.sum_univ_succ,Nat.add_assoc] using hS
  rcases alpha_six_parity p ha with ⟨hp1,hp3,hp5⟩ | ⟨hp0,hp2,hp4⟩
  · norm_num [coefficientTwo,hp1,hp3,hp5] at ht
    have hs : p 0+p 2+p 4 = 23 := by omega
    have hq : p 0^2+p 2^2+p 4^2 = 243 := by simp only [hp1,hp3,hp5] at hS'; omega
    exact bounded_three_product_not_603 _ _ _ (hcap 0) (hcap 2) (hcap 4)
      (alternating_trace_product _ _ _ hs hq ht)
  · norm_num [coefficientTwo,hp0,hp2,hp4] at ht
    have hrot := (alternating_trace_rotate 2 (2-(p 1 : ℝ)/2) 2
      (2-(p 3 : ℝ)/2) 2 (2-(p 5 : ℝ)/2)).symm.trans ht
    have hs : p 1+p 3+p 5 = 23 := by omega
    have hq : p 1^2+p 3^2+p 5^2 = 243 := by simp only [hp0,hp2,hp4] at hS'; omega
    exact bounded_three_product_not_603 _ _ _ (hcap 1) (hcap 3) (hcap 5)
      (alternating_trace_product _ _ _ hs hq hrot)
#print axioms Paper7C61Four.alternating_sum23_square243_trace_impossible

theorem root_four_one_two_one_three_qzero_beta_six_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 1) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 6) : False := by
  obtain ⟨hc,hs,hf⟩ := root_four_profile (actual p q) h4
  rw [h0,h1] at hc hs hf
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 6 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hP : totalP 6 p = 23 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf,hP] at hm
  have hS : squares 6 p = 243 := by
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 243)
  have hcap (k : Fin 6) : p k ≤ 13 := by
    have h := Paper7C61Higher.root_four_load_le_thirteen p q hn hG h4 k
    omega
  exact alternating_sum23_square243_trace_impossible p ha hP hS hcap
    (by simpa only [hq] using actual_one_two_trace p q h0)
#print axioms Paper7C61Four.root_four_one_two_one_three_qzero_beta_six_impossible

end Paper7C61Four
