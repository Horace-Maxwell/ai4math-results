import Research.Backfill.Paper7.C61PerronFiveThreeReduction
import Research.Backfill.Paper7.C61PerronFiveQpositive
import Research.Backfill.Paper7.C61PerronFiveBetaEight

/-! Source-only exclusion of every actual Perron-five profile under the
original positive-pendant, order and integrality assumptions. -/
set_option autoImplicit false
noncomputable section
namespace Paper7C61FiveThree
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open Paper7C61Profile Paper7C61Parameters Paper7C61Small Paper7C61Higher
open Paper7C61Sparse Paper7C61BetaEight
open scoped BigOperators Classical

theorem root_five_impossible (p q : Fin 6 → ℕ)
    (hp : 0 < ∑ k, (p k + q k)) (hn : nOf 6 p q ≤ 42)
    (hG : IsIntegralGraph (SG 6 p q)) (h5 : RootFive (actual p q)) : False := by
  obtain ⟨h0,h1,h2⟩ := root_five_remaining_shape p q hp hn hG h5
  by_cases hq : q = (fun _ => 0)
  · have hb := (root_five_three_qzero_remaining_data p q hn hG h5 h0 h1 h2 hq).1
    exact root_five_three_qzero_beta_eight_impossible p q hn hG h5 h0 h1 h2 hq hb
  · have hK : (Kq 6 q).Nonempty := by
      by_contra h
      have hz := Paper7Rank.support_sum_zero 6 q (Finset.not_nonempty_iff_eq_empty.mp h)
      exact hq (zero_of_totalQ_zero 6 q hz)
    exact root_five_three_qpositive_impossible p q hn hG h5 h0 h1 h2 hK
#print axioms Paper7C61FiveThree.root_five_impossible

end Paper7C61FiveThree
