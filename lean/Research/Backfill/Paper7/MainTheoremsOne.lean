import Research.Backfill.Paper7.TenCycleSpectrumContradiction
import Research.Backfill.Paper7.MainRemainingCycleReduction

/-! Source-only candidates for the exact frozen Theorem1 and minimum-order
contracts. Every exclusion used here has a proof body. This file and its
new parents have not been compiled or accepted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Main
open BackfillPaper7.Challenge

theorem original_ten_order_gt_forty_two (L : Fin 10 → List ℕ)
    (hp : 0 < pendantCount 10 L) (hG : IsIntegralGraph (sunGraph 10 L)) :
    42 < order 10 L := by
  by_contra hn
  obtain ⟨p,hp',hn',hI,_hiso⟩ := Paper7MainReduction.original_ten_reduction L hp hG (by omega)
  exact Paper7TenCycle.pure_p_sum_le_thirty_two_nonintegral p hp' hn' hI
#print axioms Paper7Main.original_ten_order_gt_forty_two

theorem check_Theorem1 : BackfillPaper7.Challenge.Theorem1 := by
  refine ⟨Paper7CycleLength.c61_counterexample_with_order,?_⟩
  intro b L hC hn
  rcases Paper7CycleLength.counterexample_order_le_forty_two_six_or_ten b L hC hn with
    hc | hten
  · exact hc.2
  · subst b
    have hh := original_ten_order_gt_forty_two L hC.2.1 hC.2.2.1
    omega
#print axioms Paper7Main.check_Theorem1

theorem check_Theorem1MinOrder : BackfillPaper7.Challenge.Theorem1MinOrder :=
  Paper7MainReduction.theorem1_implies_minimum_order check_Theorem1
#print axioms Paper7Main.check_Theorem1MinOrder

theorem remaining_cycles_order_forty_one (b : ℕ) (L : Fin b → List ℕ)
    (hb : 3 ≤ b) (hp : 0 < pendantCount b L) (hG : IsIntegralGraph (sunGraph b L))
    (hn : order b L ≤ 41) : b = 4 ∨ b = 8 := by
  rcases Paper7MainReduction.remaining_cycles_order_forty_one b L hb hp hG hn with
    h4 | h8 | h10
  · exact Or.inl h4
  · exact Or.inr h8
  · subst b
    have hh := original_ten_order_gt_forty_two L hp hG
    omega
#print axioms Paper7Main.remaining_cycles_order_forty_one

end Paper7Main
