import Research.Backfill.Paper7.C61CappedMoments

set_option autoImplicit false
noncomputable section
namespace Paper7C61Higher
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small
open scoped BigOperators Classical

def RootFive (m : Fin 5 → Fin 3) : Prop := (m 3).val = 1 ∧ (m 4).val = 0
#print axioms Paper7C61Higher.RootFive

theorem root_five_profile (m : Fin 5 → Fin 3) (h : RootFive m) :
    card m = (m 0).val+(m 1).val+(m 2).val+1 ∧
      square m = 4*(m 0).val+9*(m 1).val+16*(m 2).val+25 ∧
      fourth m = 12*((m 0).val : ℤ)+72*((m 1).val : ℤ)+240*((m 2).val : ℤ)+600 := by
  obtain ⟨h3,h4⟩ := h
  constructor
  · norm_num [card,Fin.sum_univ_succ,h3,h4]
    omega
  constructor
  · norm_num [square,value,Fin.sum_univ_succ,h3,h4]
    ring
  · norm_num [fourth,value,Fin.sum_univ_succ,h3,h4]
    ring
#print axioms Paper7C61Higher.root_five_profile

theorem root_five_only_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 0)
    (h1 : (actual p q 1).val = 0) (h2 : (actual p q 2).val = 0) : False := by
  obtain ⟨hc,hs,hf⟩ := root_five_profile (actual p q) h5
  rw [h0,h1,h2] at hc hs hf
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have he := unitExponent_le_eight p q
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hbeta : unitExponent p q = 8 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hP : totalP 6 p = 21 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf,hP] at hm
  norm_num at hm
  have hS : squares 6 p = 525 := by
    exact_mod_cast (by linarith : (squares 6 p : ℤ) = 525)
  have hbound := squares_le_total_square 6 p
  rw [hP,hS] at hbound
  norm_num at hbound
#print axioms Paper7C61Higher.root_five_only_impossible

theorem root_five_with_three_only_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 0)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0) : False := by
  have hload := no_six_load_le_twenty_two p q hn hG h5.2
  have hcap : ∀ k,p k ≤ 22 := by intro k; have := hload k; omega
  obtain ⟨hc,hs,hf⟩ := root_five_profile (actual p q) h5
  rw [h0,h1,h2] at hc hs hf
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
  · have hP : totalP 6 p = 29 := by omega
    have hS : squares 6 p = 573 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 573)
    exact cap22_sum29_square573_impossible p hP hS hcap
  · have hP : totalP 6 p = 30 := by omega
    have hS : squares 6 p = 570 := by
      rw [hP] at hm
      norm_num at hm
      exact_mod_cast (by linarith : (squares 6 p : ℤ) = 570)
    exact cap22_sum30_square570_impossible p hP hS hcap
#print axioms Paper7C61Higher.root_five_with_three_only_impossible

theorem root_five_with_four_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 0)
    (h1 : (actual p q 1).val = 0) (h2 : (actual p q 2).val = 1) : False := by
  have hload := no_six_load_le_twenty_two p q hn hG h5.2
  have hcap : ∀ k,p k ≤ 22 := by intro k; have := hload k; omega
  obtain ⟨hc,hs,hf⟩ := root_five_profile (actual p q) h5
  rw [h0,h1,h2] at hc hs hf
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have he := unitExponent_le_eight p q
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hsum := parameter_sum_eq_profile p q hn hG
  have hPbound : totalP 6 p ≤ 36 := by
    unfold totalP
    unfold nOf at hn
    omega
  have hbeta : unitExponent p q = 7 := by omega
  have hP : totalP 6 p = 36 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf,hP] at hm
  norm_num at hm
  have hS : squares 6 p = 720 := by
    exact_mod_cast (by linarith : (squares 6 p : ℤ) = 720)
  exact cap22_sum36_square720_impossible p hP hS hcap
#print axioms Paper7C61Higher.root_five_with_four_impossible

theorem root_five_small_card_profile (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (hc : card (actual p q) ≤ 2) :
    (actual p q 0).val = 1 ∧ (actual p q 1).val = 0 ∧ (actual p q 2).val = 0 := by
  have hcard := (root_five_profile (actual p q) h5).1
  have hcases :
      ((actual p q 0).val = 0 ∧ (actual p q 1).val = 0 ∧ (actual p q 2).val = 0) ∨
      ((actual p q 0).val = 1 ∧ (actual p q 1).val = 0 ∧ (actual p q 2).val = 0) ∨
      ((actual p q 0).val = 0 ∧ (actual p q 1).val = 1 ∧ (actual p q 2).val = 0) ∨
      ((actual p q 0).val = 0 ∧ (actual p q 1).val = 0 ∧ (actual p q 2).val = 1) := by omega
  rcases hcases with ⟨h0,h1,h2⟩ | h | ⟨h0,h1,h2⟩ | ⟨h0,h1,h2⟩
  · exact (root_five_only_impossible p q hn hG h5 h0 h1 h2).elim
  · exact h
  · exact (root_five_with_three_only_impossible p q hn hG h5 h0 h1 h2).elim
  · exact (root_five_with_four_impossible p q hn hG h5 h0 h1 h2).elim
#print axioms Paper7C61Higher.root_five_small_card_profile

end Paper7C61Higher
