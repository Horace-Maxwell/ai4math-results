import Research.Backfill.Paper7.C61PerronFiveThreeMoments

/-! Source-only restrictions on the last Perron-five profile. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61FiveThree
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open Paper7C61Sparse Paper7C61ThreeSquareObstruction
open scoped BigOperators Classical

theorem root_five_three_qzero_beta_six_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0)
    (hq : q = (fun _ => 0)) (hb : unitExponent p q = 6) : False := by
  have hc := (root_five_profile (actual p q) h5).1
  rw [h0,h1,h2] at hc
  have hbudget := exponent_budget p q hn hG
  have ha : zeroExponent p = 6 := by omega
  have hK := alpha_six_support p ha
  obtain ⟨hL,hM⟩ := root_five_three_parameter_relations p q hn hG h5 h1 h2
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hload : squares 6 (fun k => p k + q k) = squares 6 p := by simp only [hq,add_zero]
  have hP : totalP 6 p = 32 := by omega
  rw [hload] at hM
  have hS : squares 6 p = 576 := by omega
  obtain ⟨a,b,c,hs,hsq⟩ := support_three_moments p hK
  rw [hP] at hs
  rw [hS] at hsq
  exact not_sum32_squares576 a b c hs hsq
#print axioms Paper7C61FiveThree.root_five_three_qzero_beta_six_impossible

theorem root_five_three_qzero_beta_seven_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0)
    (hq : q = (fun _ => 0)) (hb : unitExponent p q = 7) : False := by
  have _hc := (root_five_profile (actual p q) h5).1
  rw [h0,h1,h2] at _hc
  obtain ⟨hL,hM⟩ := root_five_three_parameter_relations p q hn hG h5 h1 h2
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hload : squares 6 (fun k => p k + q k) = squares 6 p := by simp only [hq,add_zero]
  have hP : totalP 6 p = 33 := by omega
  rw [hload] at hM
  have hS : squares 6 p = 573 := by omega
  have hc := no_six_load_le_twenty_two p q hn hG h5.2
  have hcap : ∀ k, p k ≤ 22 := by intro k; have := hc k; omega
  exact cap22_sum33_square573_impossible p hP hS hcap
#print axioms Paper7C61FiveThree.root_five_three_qzero_beta_seven_impossible

/-- Exact remaining zero-q domain after the beta-six and beta-seven exclusions.
This theorem does not assert that the remaining domain is realizable. -/
theorem root_five_three_qzero_remaining_data (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h5 : RootFive (actual p q)) (h0 : (actual p q 0).val = 1)
    (h1 : (actual p q 1).val = 1) (h2 : (actual p q 2).val = 0)
    (hq : q = (fun _ => 0)) :
    unitExponent p q = 8 ∧ zeroExponent p = 2 ∧ totalP 6 p = 34 ∧
      squares 6 p = 570 ∧ (∀ k, p k ≤ 22) := by
  have hlo := qzero_unitExponent_lower p q hq
  have hhi := unitExponent_le_eight p q
  have h6 : unitExponent p q ≠ 6 := fun hb =>
    root_five_three_qzero_beta_six_impossible p q hn hG h5 h0 h1 h2 hq hb
  have h7 : unitExponent p q ≠ 7 := fun hb =>
    root_five_three_qzero_beta_seven_impossible p q hn hG h5 h0 h1 h2 hq hb
  have hb : unitExponent p q = 8 := by omega
  have hc := (root_five_profile (actual p q) h5).1
  rw [h0,h1,h2] at hc
  have hbudget := exponent_budget p q hn hG
  obtain ⟨hL,hM⟩ := root_five_three_parameter_relations p q hn hG h5 h1 h2
  have hQ : totalQ 6 q = 0 := by simp [hq,totalQ]
  have hload : squares 6 (fun k => p k + q k) = squares 6 p := by simp only [hq,add_zero]
  rw [hload] at hM
  have hcap := no_six_load_le_twenty_two p q hn hG h5.2
  exact ⟨hb,by omega,by omega,by omega,by intro k; have := hcap k; omega⟩
#print axioms Paper7C61FiveThree.root_five_three_qzero_remaining_data

end Paper7C61FiveThree
