import Research.Backfill.Paper7.C61CappedMoments
import Research.Backfill.Paper7.C61RootFourReduction

set_option autoImplicit false
noncomputable section
namespace Paper7C61Higher
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small

theorem root_four_three_only_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 0)
    (h1 : (actual p q 1).val = 1) : False := by
  have hload := root_four_load_le_thirteen p q hn hG h4
  have hcap : ∀ k,p k ≤ 13 := by intro k; have := hload k; omega
  obtain ⟨hc,hs,hf⟩ := root_four_profile (actual p q) h4
  rw [h0,h1] at hc hs hf
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have he := unitExponent_le_eight p q
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hsum := parameter_sum_eq_profile p q hn hG
  have hm := q_zero_moment p q hn hG hq
  rw [hf] at hm
  have hcases : unitExponent p q = 7 ∨ unitExponent p q = 8 := by omega
  rcases hcases with he7 | he8
  · have hP : totalP 6 p = 20 := by omega
    have hS : squares 6 p = 240 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 240)
    exact cap13_sum20_square240_impossible p hP hS hcap
  · have hP : totalP 6 p = 21 := by omega
    have hS : squares 6 p = 237 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 237)
    exact cap13_sum21_square237_impossible p hP hS hcap
#print axioms Paper7C61Higher.root_four_three_only_impossible

theorem root_four_card_at_least_three (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) : 3 ≤ card (actual p q) := by
  have hc := (root_four_profile (actual p q) h4).1
  by_contra h
  have hcases :
      ((actual p q 0).val = 0 ∧ (actual p q 1).val = 0) ∨
      ((actual p q 0).val = 1 ∧ (actual p q 1).val = 0) ∨
      ((actual p q 0).val = 0 ∧ (actual p q 1).val = 1) := by omega
  rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩ | ⟨h0,h1⟩
  · exact root_four_only_impossible p q hn hG h4 h0 h1
  · exact root_four_one_two_impossible p q hn hG h4 h0 h1
  · exact root_four_three_only_impossible p q hn hG h4 h0 h1
#print axioms Paper7C61Higher.root_four_card_at_least_three

end Paper7C61Higher
