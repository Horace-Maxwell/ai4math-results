import Research.Backfill.Paper7.EightAlternatingExclusion
import Research.Backfill.Paper7.EightOppositeSiteExclusion
import Research.Backfill.Paper7.CycleThreeReduction

/-! NEW SOURCE ONLY. Necessary conditions for the still-open eight-cycle
branches. No full eight-cycle exclusion or original main check is asserted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_qzero_integral_gap_strict (p : Fin 8 → ℕ)
    (hp : 0 < ∑ i, p i) (hn : nOf 8 p (fun _ => 0) ≤ 41)
    (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) : delta0 8 p < (Kp 8 p).card := by
  have hK : (Kp 8 p).Nonempty := by
    by_contra hh
    have hz := Paper7Rank.support_sum_zero 8 p (Finset.not_nonempty_iff_eq_empty.mp hh)
    omega
  have hd := Paper7Rank.delta0_le_card_of_nonempty 8 p hK
  have hne : delta0 8 p ≠ (Kp 8 p).card := by
    intro heq
    exact eight_qzero_saturated_nonintegral p hp hn heq hG
  omega
#print axioms Paper7EightCycle.eight_qzero_integral_gap_strict

theorem eight_qzero_integral_unit_required (p : Fin 8 → ℕ)
    (hp : 0 < ∑ i, p i) (hn : nOf 8 p (fun _ => 0) ≤ 41)
    (hG : IsIntegralGraph (SG 8 p (fun _ => 0))) : 1 ∈ spec (SG 8 p (fun _ => 0)) := by
  by_contra hh
  have hm : mult (SG 8 p (fun _ => 0)) 1 = 0 := Multiset.count_eq_zero.mpr hh
  have hd := eight_qzero_integral_gap_strict p hp hn hG
  have hr := Paper7MainReduction.qzero_positive_rank_balance 8 p (by decide) (by decide) hG
  have hc := (eight_big_card_bounds p (fun _ => 0) (by simpa using hp) hn hG).2
  omega
#print axioms Paper7EightCycle.eight_qzero_integral_unit_required

theorem original_eight_pure_p_unit_required (L : Fin 8 → List ℕ)
    (hp : 0 < pendantCount 8 L) (hn : order 8 L ≤ 41)
    (hG : IsIntegralGraph (sunGraph 8 L))
    (hq : Paper7Normalize.countP2 8 L = (fun _ => 0)) :
    1 ∈ spec (SG 8 (Paper7Normalize.countP1 8 L) (fun _ => 0)) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 8 L (by decide) hG k _ (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 8 L
  let e := Paper7Normalize.sunNormalizeIso 8 L (by decide) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hc := Fintype.card_congr e.toEquiv
  change order 8 L = order 8 (pq 8 p (Paper7Normalize.countP2 8 L)) at hc
  rw [hq,Paper7Setup.sg_order] at hc
  rw [hq] at hI
  have hpend := Paper7CycleThree.order_eq_add_pendantCount 8 L
  have hs : order 8 L = 8+∑ i, p i := by
    simpa only [nOf,Finset.sum_const_zero,mul_zero,add_zero] using hc
  exact eight_qzero_integral_unit_required p (by omega) (by omega) hI
#print axioms Paper7EightCycle.original_eight_pure_p_unit_required

end Paper7EightCycle
