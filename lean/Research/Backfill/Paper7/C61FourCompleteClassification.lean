import Research.Backfill.Paper7.C61FourTwoTwiceSingleton
import Research.Backfill.Paper7.C61MultiQExclusion
import Research.Backfill.Paper7.C61FourTwoTwosOneThreeBetaFive
import Research.Backfill.Paper7.C61FourCardThreeQpositiveExclusion

/-! NEW SOURCE ONLY. Complete original Perron-four forward classification.
Every q-positive cardinality and both nonsaturated four-root profiles are
covered; no monodromy, support pattern, or candidate list is an input. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open scoped BigOperators Classical

theorem root_four_card_four_qpositive_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q≤42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (hc : card (actual p q)=4)
    (hK : (Kq 6 q).Nonempty) : False := by
  have hp := (root_four_profile (actual p q) h4).1
  have h0Lt := (actual p q 0).isLt
  have h1Lt := (actual p q 1).isLt
  have hcases : ((actual p q 0).val=2 ∧ (actual p q 1).val=1) ∨
      ((actual p q 0).val=1 ∧ (actual p q 1).val=2) := by omega
  have he := exponent_budget p q hn hG
  have ha := zeroExponent_le_six p
  have hb := unitExponent_le_six_of_nonempty p q hK
  have hbeta : unitExponent p q=5 ∨ unitExponent p q=6 := by omega
  rcases hbeta with hbeta | hbeta
  · rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩
    · exact root_four_two_twos_one_three_qpositive_beta_five_impossible p q hn hG h4 h0 h1 hK hbeta
    · exact root_four_one_two_two_threes_qpositive_beta_five_impossible p q hn hG h4 h0 h1 hK hbeta
  · have hpos := Finset.card_pos.mpr hK
    by_cases hsingle : (Kq 6 q).card=1
    · rcases hcases with ⟨h0,h1⟩ | ⟨h0,h1⟩
      · exact root_four_two_twos_one_three_qpositive_beta_six_singleton_impossible
          p q hn hG h4 h0 h1 hbeta hsingle
      · exact root_four_one_two_two_threes_qpositive_beta_six_singleton_impossible
          p q hn hG h4 h0 h1 hbeta hsingle
    · exact root_four_card_four_multiq_beta_six_impossible p q hn hG h4 hc hbeta (by omega)
#print axioms Paper7C61Four.root_four_card_four_qpositive_impossible

theorem root_four_qpositive_impossible (p q : Fin 6 → ℕ)
    (hp : 0<∑ k, (p k+q k)) (hn : nOf 6 p q≤42)
    (hG : IsIntegralGraph (SG 6 p q)) (h4 : RootFour (actual p q))
    (hK : (Kq 6 q).Nonempty) : False := by
  have hc := (root_four_profile (actual p q) h4).1
  have h0Lt := (actual p q 0).isLt
  have h1Lt := (actual p q 1).isLt
  have hcl := root_four_card_at_least_three p q hn hG h4
  have hcases : card (actual p q)=3 ∨ card (actual p q)=4 ∨ card (actual p q)=5 := by omega
  rcases hcases with h3 | h4c | h5
  · exact root_four_card_three_qpositive_impossible p q hn hG h4 h3 hK
  · exact root_four_card_four_qpositive_impossible p q hn hG h4 h4c hK
  · have hq := (saturated_rotations_analytic p q hp hn hG h5).1
    obtain ⟨j,hj⟩ := hK
    have hjp := (Finset.mem_filter.mp hj).2
    simp only [hq] at hjp
    omega
#print axioms Paper7C61Four.root_four_qpositive_impossible

theorem root_four_classification (p q : Fin 6 → ℕ)
    (hp : 0<∑ k, (p k+q k)) (hn : nOf 6 p q≤42)
    (hG : IsIntegralGraph (SG 6 p q)) (h4 : RootFour (actual p q)) :
    q=(fun _ => 0) ∧ p∈C61Rotations := by
  have hK : ¬ (Kq 6 q).Nonempty := fun h => root_four_qpositive_impossible p q hp hn hG h4 h
  have hq := zero_of_totalQ_zero 6 q
    (Paper7Rank.support_sum_zero 6 q (Finset.not_nonempty_iff_eq_empty.mp hK))
  exact ⟨hq,root_four_qzero_rotations p q hp hn hG h4 hq⟩
#print axioms Paper7C61Four.root_four_classification

end Paper7C61Four
