import Research.Backfill.Paper7.C61FourOddArithmetic
import Research.Backfill.Paper7.C61ThreeMonodromy
import Research.Backfill.Paper7.C61BetaEightSharpExclusions

/-! NEW SOURCE ONLY. Actual monodromy implies the generic arithmetic bound.
This closes the original Perron-four, no-three, zero-q branch without an
additional coordinate, support-pattern, or monodromy assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Small Paper7C61Parameters Paper7C61Three
open scoped BigOperators Classical

theorem half_pair_numerator (a b c d : ℕ)
    (h : (2-(a : ℝ)/2)*(2-(b : ℝ)/2)+
      (2-(c : ℝ)/2)*(2-(d : ℝ)/2) = 2) :
    (4-(a : ℤ))*(4-(b : ℤ))+(4-(c : ℤ))*(4-(d : ℤ)) = 8 := by
  have hr : (4-(a : ℝ))*(4-(b : ℝ))+(4-(c : ℝ))*(4-(d : ℝ)) = 8 := by
    nlinarith only [h]
  exact_mod_cast hr
#print axioms Paper7C61Four.half_pair_numerator

theorem mono_two_pair_numerators (p : Fin 6 → ℕ)
    (hm : Mono 6 p (fun _ => 0) 2 = 1) : PairNumerators p := by
  have hs : realSixProduct (coefficientTwo p (fun _ => 0) 0)
      (coefficientTwo p (fun _ => 0) 1) (coefficientTwo p (fun _ => 0) 2)
      (coefficientTwo p (fun _ => 0) 3) (coefficientTwo p (fun _ => 0) 4)
      (coefficientTwo p (fun _ => 0) 5) = 1 := by
    rw [← mono_two_six_product]
    exact hm
  have h := real_six_triple_data _ _ _ _ _ _ hs
  have hr := real_six_rotate _ _ _ _ _ _ (real_six_rotate _ _ _ _ _ _ hs)
  have h2 := (real_six_triple_data _ _ _ _ _ _ hr).1
  refine ⟨half_pair_numerator _ _ _ _ ?_, half_pair_numerator _ _ _ _ ?_,
    half_pair_numerator _ _ _ _ ?_⟩
  · simpa [coefficientTwo] using h.1
  · simpa [coefficientTwo] using h.2.1
  · simpa [coefficientTwo] using h2
#print axioms Paper7C61Four.mono_two_pair_numerators

theorem support_four_odd_square_monodromy_total_le_eighteen (p : Fin 6 → ℕ)
    (hK : (Kp 6 p).card ≤ 4) (hS : squares 6 p % 4 = 3)
    (hm : Mono 6 p (fun _ => 0) 2 = 1) : totalP 6 p ≤ 18 := by
  exact support_four_odd_count_pair_total_bound p hK
    (square_remainder_three_odd_count p hS) (mono_two_pair_numerators p hm)
#print axioms Paper7C61Four.support_four_odd_square_monodromy_total_le_eighteen

theorem root_four_without_three_monodromy_two (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 0) :
    Mono 6 p q 2 = 1 := by
  have h0 := root_four_without_three_has_two_twos p q hn hG h4 h1
  have hm : mult (SG 6 p q) 2 = 2 := by
    have hi := actual_eq_mult p q (0 : Fin 5)
    norm_num [value] at hi
    omega
  exact (Paper7Lemma22Periodic.lemma22_ordinary_clause 6 p q (by decide)
    2 (by norm_num) (by norm_num) (by norm_num)).2.2.1.mp hm
#print axioms Paper7C61Four.root_four_without_three_monodromy_two

theorem root_four_without_three_qzero_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 0)
    (hq : q = (fun _ => 0)) : False := by
  obtain ⟨hb,hP,hS⟩ := Paper7C61Sharp.root_four_without_three_qzero_remaining_data
    p q hn hG h4 h1 hq
  have h0 := root_four_without_three_has_two_twos p q hn hG h4 h1
  have hc := (root_four_profile (actual p q) h4).1
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 4 := by omega
  have hd := support_add_delta0_le_six p
  have hcard : (Kp 6 p).card ≤ 6 := by
    simpa only [Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Kp 6 p))
  have hK : (Kp 6 p).card ≤ 4 := by unfold zeroExponent at ha; omega
  have hm : Mono 6 p (fun _ => 0) 2 = 1 := by
    simpa only [hq] using root_four_without_three_monodromy_two p q hn hG h4 h1
  have hbound := support_four_odd_square_monodromy_total_le_eighteen p hK
    (by rw [hS]) hm
  omega
#print axioms Paper7C61Four.root_four_without_three_qzero_impossible

end Paper7C61Four
