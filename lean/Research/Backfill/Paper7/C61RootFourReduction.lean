import Research.Backfill.Paper7.C61RootThreeReduction

set_option autoImplicit false
noncomputable section
namespace Paper7C61Small
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters
open scoped BigOperators Classical

theorem root_four_only_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 0)
    (h1 : (actual p q 1).val = 0) : False := by
  obtain ⟨hc,hs,hf⟩ := root_four_profile (actual p q) h4
  rw [h0,h1] at hc hs hf
  have hq := q_zero_of_card_le_two p q hn hG (by omega)
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have he := unitExponent_le_eight p q
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hbeta : unitExponent p q = 8 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hP : totalP 6 p = 12 := by omega
  have hm := q_zero_moment p q hn hG hq
  rw [hf,hP] at hm
  have hS : squares 6 p = 192 := by
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 192)
  have hbound := squares_le_total_square 6 p
  rw [hP,hS] at hbound
  norm_num at hbound
#print axioms Paper7C61Small.root_four_only_impossible

theorem root_four_one_two_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 0) : False := by
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
  rcases hcases with hbeta | hbeta
  · have hP : totalP 6 p = 15 := by omega
    have hS : squares 6 p = 195 := by
      rw [hP] at hm
      exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 195)
    exact no_sum15_square195 p hP hS
  · have hP : totalP 6 p = 16 := by omega
    have hS : squares 6 p = 192 := by
      rw [hP] at hm
      exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 192)
    exact no_sum16_square192 p hP hS
#print axioms Paper7C61Small.root_four_one_two_impossible

theorem root_four_without_three_has_two_twos (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 0) :
    (actual p q 0).val = 2 := by
  have hlt := (actual p q 0).isLt
  by_contra h
  have hc : (actual p q 0).val = 0 ∨ (actual p q 0).val = 1 := by omega
  rcases hc with h0 | h0
  · exact root_four_only_impossible p q hn hG h4 h0 h1
  · exact root_four_one_two_impossible p q hn hG h4 h0 h1
#print axioms Paper7C61Small.root_four_without_three_has_two_twos

theorem root_four_without_three_qzero_cases (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 0)
    (hq : q = (fun _ => 0)) :
    (unitExponent p q = 7 ∧ totalP 6 p = 19 ∧ squares 6 p = 195) ∨
    (unitExponent p q = 8 ∧ totalP 6 p = 20 ∧ squares 6 p = 192) := by
  have h0 := root_four_without_three_has_two_twos p q hn hG h4 h1
  obtain ⟨_hc,hs,hf⟩ := root_four_profile (actual p q) h4
  rw [h0,h1] at hs hf
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hel := qzero_unitExponent_lower p q hq
  have heu := unitExponent_le_eight p q
  have hsum := parameter_sum_eq_profile p q hn hG
  have hm := q_zero_moment p q hn hG hq
  rw [hf] at hm
  have hnot6 : unitExponent p q ≠ 6 := by
    intro he6
    have hP : totalP 6 p = 18 := by omega
    have hS : squares 6 p = 198 := by
      rw [hP] at hm
      exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 198)
    exact no_sum18_square198 p hP hS
  have hcases : unitExponent p q = 7 ∨ unitExponent p q = 8 := by omega
  rcases hcases with he7 | he8
  · left
    have hP : totalP 6 p = 19 := by omega
    rw [hP] at hm
    refine ⟨he7,hP,?_⟩
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 195)
  · right
    have hP : totalP 6 p = 20 := by omega
    rw [hP] at hm
    refine ⟨he8,hP,?_⟩
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 p : ℤ) = 192)
#print axioms Paper7C61Small.root_four_without_three_qzero_cases

theorem root_four_without_three_qpositive_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 0)
    (hK : (Kq 6 q).Nonempty) :
    (actual p q 0).val = 2 ∧ unitExponent p q = 6 ∧ zeroExponent p = 6 ∧
      totalP 6 p + totalQ 6 q = 18 ∧
      squares 6 (fun k => p k+q k) + 2*totalQ 6 q = 198 ∧
      (Kp 6 p).card ≤ 3 ∧ (Kq 6 q).card ≤ 3 := by
  have h0 := root_four_without_three_has_two_twos p q hn hG h4 h1
  obtain ⟨hc,hs,hf⟩ := root_four_profile (actual p q) h4
  rw [h0,h1] at hc hs hf
  have he := unitExponent_le_six_of_nonempty p q hK
  have ha := zeroExponent_le_six p
  have hb := exponent_budget p q hn hG
  have hbeta : unitExponent p q = 6 := by omega
  have halpha : zeroExponent p = 6 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hL : totalP 6 p + totalQ 6 q = 18 := by omega
  have hm := profile_parameter_moment p q hn hG
  rw [hf] at hm
  have hLZ : (totalP 6 p : ℤ) + totalQ 6 q = 18 := by exact_mod_cast hL
  have hS : squares 6 (fun k => p k+q k) + 2*totalQ 6 q = 198 := by
    exact_mod_cast (by norm_num at hm; linarith : (squares 6 (fun k => p k+q k) : ℤ) + 2*(totalQ 6 q : ℤ) = 198)
  have hqc := q_support_le_profile p q hn hG
  exact ⟨h0,hbeta,halpha,hL,hS,alpha_six_support p halpha,by omega⟩
#print axioms Paper7C61Small.root_four_without_three_qpositive_data

end Paper7C61Small
