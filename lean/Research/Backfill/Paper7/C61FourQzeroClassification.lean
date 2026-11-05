import Research.Backfill.Paper7.C61FourAlternatingTrace
import Research.Backfill.Paper7.C61FourTwentyFourMoments
import Research.Backfill.Paper7.C61FourTwentyEightExclusion
import Research.Backfill.Paper7.C61ThirtyThreeZero
import Research.Backfill.Paper7.C61SaturatedAnalyticUniqueness
import Research.Backfill.Paper7.C61HigherRemainderData

/-! NEW SOURCE ONLY. Complete original Perron-four forward classification
when q is zero. All nonsaturated profiles are excluded; the saturated
profile is identified with the actual C61 rotation orbit analytically. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open scoped BigOperators Classical

theorem alpha_at_least_four_support (p : Fin 6 → ℕ) (ha : 4 ≤ zeroExponent p) :
    (Kp 6 p).card ≤ 4 := by
  have hd := support_add_delta0_le_six p
  unfold zeroExponent at ha
  omega
#print axioms Paper7C61Four.alpha_at_least_four_support

theorem alpha_at_least_two_zero (p : Fin 6 → ℕ) (ha : 2 ≤ zeroExponent p) :
    ∃ j : Fin 6, p j = 0 := by
  have hd := support_add_delta0_le_six p
  have hK : (Kp 6 p).card ≤ 5 := by unfold zeroExponent at ha; omega
  have hc : 0 < ((Kp 6 p)ᶜ).card := by
    rw [Finset.card_compl,Fintype.card_fin]
    omega
  obtain ⟨j,hj⟩ := Finset.card_pos.mp hc
  have hn := Finset.mem_compl.mp hj
  have hp : ¬ 0 < p j := by
    simpa only [Kp,Finset.mem_filter,Finset.mem_univ,true_and] using hn
  exact ⟨j,by omega⟩
#print axioms Paper7C61Four.alpha_at_least_two_zero

theorem root_four_qzero_parameter_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (hq : q = (fun _ => 0)) :
    totalP 6 p = 4*(actual p q 0).val+9*(actual p q 1).val+unitExponent p q+4 ∧
      squares 6 p+3*unitExponent p q = 45*(actual p q 1).val+216 := by
  obtain ⟨hL,hM⟩ := root_four_parameter_relations p q hn hG h4
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hload : squares 6 (fun k => p k+q k) = squares 6 p := by simp [hq]
  rw [hQ] at hL hM
  rw [hload] at hM
  exact ⟨by omega,by omega⟩
#print axioms Paper7C61Four.root_four_qzero_parameter_data

theorem root_four_two_twos_one_three_qzero_beta_six_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h0 : (actual p q 0).val = 2)
    (h1 : (actual p q 1).val = 1) (hq : q = (fun _ => 0))
    (hb : unitExponent p q = 6) : False := by
  have hc := (root_four_profile (actual p q) h4).1
  have he := exponent_budget p q hn hG
  have ha : zeroExponent p = 4 := by omega
  have hdata := root_four_qzero_parameter_data p q hn hG h4 hq
  have hP : totalP 6 p = 27 := by omega
  have hS : squares 6 p = 243 := by omega
  have hm : Mono 6 p (fun _ => 0) 2 = 1 := by
    simpa only [hq] using actual_two_monodromy p q h0
  have hbound := support_four_odd_square_monodromy_total_le_eighteen p
    (alpha_at_least_four_support p (by omega)) (by rw [hS]) hm
  omega
#print axioms Paper7C61Four.root_four_two_twos_one_three_qzero_beta_six_impossible

theorem root_four_two_threes_qzero_nonsaturated_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (h1 : (actual p q 1).val = 2)
    (hcard : card (actual p q) < 5) (hq : q = (fun _ => 0)) : False := by
  have hc := (root_four_profile (actual p q) h4).1
  have he := exponent_budget p q hn hG
  have hdata := root_four_qzero_parameter_data p q hn hG h4 hq
  have hbl := qzero_unitExponent_lower p q hq
  have hbu := unitExponent_le_eight p q
  have hb8 : unitExponent p q ≠ 8 := fun h =>
    Paper7C61Sharp.root_four_qzero_beta_eight_impossible p q hn hG h4 hq h
  have hm : Mono 6 p (fun _ => 0) 3 = 1 := by
    simpa only [hq] using actual_three_monodromy p q h1
  have hcap (k : Fin 6) : p k ≤ 13 := by
    have hi := root_four_load_le_thirteen p q hn hG h4 k
    omega
  have ha0 : (actual p q 0).val = 0 ∨ (actual p q 0).val = 1 := by omega
  have hbeta : unitExponent p q = 6 ∨ unitExponent p q = 7 := by omega
  rcases hbeta with hb | hb
  · have hAlpha : 4 ≤ zeroExponent p := by omega
    have hS : squares 6 p = 288 := by omega
    have hP : totalP 6 p = 28 ∨ totalP 6 p = 32 := by omega
    rcases support_four_mono_three_moment_cases p hcap
      (alpha_at_least_four_support p hAlpha) hm with ⟨h24,_⟩ | ⟨_,hSnot⟩
    · omega
    · exact hSnot hS
  · rcases ha0 with h0 | h0
    · have hAlpha : zeroExponent p = 4 := by omega
      have hP : totalP 6 p = 29 := by omega
      rcases support_four_mono_three_moment_cases p hcap
        (alpha_at_least_four_support p (by omega)) hm with ⟨h24,_⟩ | ⟨h32,_⟩ <;> omega
    · have hAlpha : zeroExponent p = 2 := by omega
      have hP : totalP 6 p = 33 := by omega
      exact sum_thirty_three_zero_monodromy_three_impossible p hP
        (alpha_at_least_two_zero p (by omega)) hm
#print axioms Paper7C61Four.root_four_two_threes_qzero_nonsaturated_impossible

theorem root_four_qzero_nonsaturated_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (hcard : card (actual p q) < 5)
    (hq : q = (fun _ => 0)) : False := by
  have hc := (root_four_profile (actual p q) h4).1
  have hcl := root_four_card_at_least_three p q hn hG h4
  have haLt := (actual p q 0).isLt
  have hbLt := (actual p q 1).isLt
  have hcases : (actual p q 1).val = 0 ∨ (actual p q 1).val = 1 ∨
      (actual p q 1).val = 2 := by omega
  rcases hcases with h1 | h1 | h1
  · exact root_four_without_three_qzero_impossible p q hn hG h4 h1 hq
  · have h0 : (actual p q 0).val = 1 ∨ (actual p q 0).val = 2 := by omega
    have hbl := qzero_unitExponent_lower p q hq
    have hbu := unitExponent_le_eight p q
    have hb8 : unitExponent p q ≠ 8 := fun h =>
      Paper7C61Sharp.root_four_qzero_beta_eight_impossible p q hn hG h4 hq h
    have hbeta : unitExponent p q = 6 ∨ unitExponent p q = 7 := by omega
    rcases h0 with h0 | h0
    · rcases hbeta with hb | hb
      · exact root_four_one_two_one_three_qzero_beta_six_impossible p q hn hG h4 h0 h1 hq hb
      · exact root_four_one_two_one_three_qzero_beta_seven_impossible p q hn hG h4 h0 h1 hq hb
    · rcases hbeta with hb | hb
      · exact root_four_two_twos_one_three_qzero_beta_six_impossible p q hn hG h4 h0 h1 hq hb
      · exact root_four_two_twos_one_three_qzero_beta_seven_impossible p q hn hG h4 h0 h1 hq hb
  · exact root_four_two_threes_qzero_nonsaturated_impossible p q hn hG h4 h1 hcard hq
#print axioms Paper7C61Four.root_four_qzero_nonsaturated_impossible

theorem root_four_qzero_rotations (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k+q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (h4 : RootFour (actual p q))
    (hq : q = (fun _ => 0)) : p ∈ C61Rotations := by
  have hc := (root_four_profile (actual p q) h4).1
  have haLt := (actual p q 0).isLt
  have hbLt := (actual p q 1).isLt
  by_cases h5 : card (actual p q) = 5
  · exact (saturated_rotations_analytic p q hp hn hG h5).2
  · exact (root_four_qzero_nonsaturated_impossible p q hn hG h4 (by omega) hq).elim
#print axioms Paper7C61Four.root_four_qzero_rotations

end Paper7C61Four
