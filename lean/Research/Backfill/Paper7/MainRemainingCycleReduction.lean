import Research.Backfill.Paper7.SunSmallOrderCycleReduction
import Research.Backfill.Paper7.TwelveCycleExclusion

/-! Source-only global reductions for the original main contracts.
The unresolved eight- and ten-cycle exclusions are not assumed or hidden. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MainReduction
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem remaining_cycles_order_forty_two (b : ℕ) (L : Fin b → List ℕ)
    (hb : 3 ≤ b) (hp : 0 < pendantCount b L) (hG : IsIntegralGraph (sunGraph b L))
    (hn : order b L ≤ 42) : b = 4 ∨ b = 6 ∨ b = 8 ∨ b = 10 := by
  rcases Paper7CycleLength.integral_order_le_forty_two_cycle_cases b L hb hp hG hn with
    h4 | h6 | h8 | h10 | h12
  · exact Or.inl h4
  · exact Or.inr (Or.inl h6)
  · exact Or.inr (Or.inr (Or.inl h8))
  · exact Or.inr (Or.inr (Or.inr h10))
  · subst b
    have hh := original_twelve_order_gt_forty_two L hp hG
    omega
#print axioms Paper7MainReduction.remaining_cycles_order_forty_two

theorem remaining_cycles_order_forty_one (b : ℕ) (L : Fin b → List ℕ)
    (hb : 3 ≤ b) (hp : 0 < pendantCount b L) (hG : IsIntegralGraph (sunGraph b L))
    (hn : order b L ≤ 41) : b = 4 ∨ b = 8 ∨ b = 10 := by
  rcases Paper7CycleLength.integral_order_le_forty_one_cycle_cases b L hb hp hG hn with
    h4 | h8 | h10 | h12
  · exact Or.inl h4
  · exact Or.inr (Or.inl h8)
  · exact Or.inr (Or.inr h10)
  · subst b
    have hh := original_twelve_order_gt_forty_two L hp hG
    omega
#print axioms Paper7MainReduction.remaining_cycles_order_forty_one

theorem counterexample_c61_or_pure_ten (b : ℕ) (L : Fin b → List ℕ)
    (hC : IsCounterexample b L) (hn : order b L ≤ 42) :
    (order b L = 42 ∧ Nonempty (sunGraph b L ≃g sunGraph 6 C61)) ∨
      (b = 10 ∧ Paper7Normalize.countP2 b L = (fun _ => 0)) := by
  rcases Paper7CycleLength.counterexample_order_le_forty_two_six_or_ten b L hC hn with
    hc | hten
  · exact Or.inl hc
  · exact Or.inr ⟨hten,original_ten_or_twelve_no_p2 b L (Or.inl hten) hn hC.2.2.1⟩
#print axioms Paper7MainReduction.counterexample_c61_or_pure_ten

theorem original_ten_reduction (L : Fin 10 → List ℕ)
    (hp : 0 < pendantCount 10 L) (hG : IsIntegralGraph (sunGraph 10 L))
    (hn : order 10 L ≤ 42) :
    ∃ p : Fin 10 → ℕ, 0 < ∑ i, p i ∧ (∑ i, p i) ≤ 32 ∧
      IsIntegralGraph (SG 10 p (fun _ => 0)) ∧
      Nonempty (sunGraph 10 L ≃g SG 10 p (fun _ => 0)) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 10 L (by decide) hG k _ (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 10 L
  let q := Paper7Normalize.countP2 10 L
  let e : sunGraph 10 L ≃g SG 10 p q := Paper7Normalize.sunNormalizeIso 10 L (by decide) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hq : q = (fun _ => 0) := original_ten_or_twelve_no_p2 10 L (Or.inl rfl) hn hG
  have hc := Fintype.card_congr e.toEquiv
  change order 10 L = order 10 (pq 10 p q) at hc
  rw [Paper7Setup.sg_order,hq] at hc
  have hsize : order 10 L = 10+∑ i, p i := by
    simpa only [nOf,Finset.sum_const_zero,mul_zero,add_zero] using hc
  have hpend := Paper7CycleThree.order_eq_add_pendantCount 10 L
  have hiso : Nonempty (sunGraph 10 L ≃g SG 10 p (fun _ => 0)) := by
    rw [← hq]
    exact ⟨e⟩
  rw [hq] at hI
  exact ⟨p,by omega,by omega,hI,hiso⟩
#print axioms Paper7MainReduction.original_ten_reduction

theorem theorem1_implies_minimum_order (h : Theorem1) : Theorem1MinOrder := by
  refine ⟨⟨6,C61,h.1.1,h.1.2⟩,?_⟩
  intro b L hC
  by_contra hn
  obtain ⟨e⟩ := h.2 b L hC (by omega)
  have hc := Fintype.card_congr e.toEquiv
  change order b L = order 6 C61 at hc
  rw [h.1.2] at hc
  omega
#print axioms Paper7MainReduction.theorem1_implies_minimum_order

end Paper7MainReduction
