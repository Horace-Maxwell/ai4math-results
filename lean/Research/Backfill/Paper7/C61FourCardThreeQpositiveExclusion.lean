import Research.Backfill.Paper7.C61FourThreeCardRotation
import Research.Backfill.Paper7.C61FourWithoutThreeQpositive

/-! NEW SOURCE ONLY. The complete original Perron-four q-positive branch
with profile cardinality three, including all three multiplicity patterns. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61Four
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Small Paper7C61Higher Paper7C61Three
open scoped Classical

theorem root_four_card_three_qpositive_impossible (p q : Fin 6 → ℕ)
    (hn : nOf 6 p q ≤ 42) (hG : IsIntegralGraph (SG 6 p q))
    (h4 : RootFour (actual p q)) (hc : card (actual p q) = 3)
    (hK : (Kq 6 q).Nonempty) : False := by
  obtain ⟨hcard, hsquare, _hfourth⟩ := root_four_profile (actual p q) h4
  have haBound := zeroExponent_le_six p
  have hbBound := unitExponent_le_six_of_nonempty p q hK
  have hexp := exponent_budget p q hn hG
  have hbeta : unitExponent p q = 6 := by omega
  have halpha : zeroExponent p = 6 := by omega
  have hsum := parameter_sum_eq_profile p q hn hG
  have hp := alpha_six_parity p halpha
  have hw := beta_six_full_unit_witness p q hbeta
  have hl := root_four_load_le_thirteen p q hn hG h4
  have hq : ∃ k, 0 < q k := by
    obtain ⟨k, hk⟩ := hK
    exact ⟨k, (Finset.mem_filter.mp hk).2⟩
  have haLt := (actual p q 0).isLt
  have hbLt := (actual p q 1).isLt
  have hcases : ((actual p q 1).val = 0) ∨
      ((actual p q 0).val = 1 ∧ (actual p q 1).val = 1) ∨
      ((actual p q 0).val = 0 ∧ (actual p q 1).val = 2) := by omega
  rcases hcases with h1 | ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact root_four_without_three_qpositive_impossible p q hn hG h4 h1 hK
  · have hL : totalP 6 p + totalQ 6 q = 23 := by omega
    have hd : ThreeCardData p q := Or.inl ⟨actual_two_once_trace p q h0, hL⟩
    exact alternating_three_card_qpositive_impossible p q hp hw hd hl hq
  · have hL : totalP 6 p + totalQ 6 q = 28 := by omega
    have hd : ThreeCardData p q := Or.inr ⟨actual_three_twice_pair_three p q h1, hL⟩
    exact alternating_three_card_qpositive_impossible p q hp hw hd hl hq
#print axioms Paper7C61Four.root_four_card_three_qpositive_impossible

end Paper7C61Four
