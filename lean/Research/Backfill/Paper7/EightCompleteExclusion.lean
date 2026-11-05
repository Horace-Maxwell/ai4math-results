import Research.Backfill.Paper7.EightCoefficientBridge
import Research.Backfill.Paper7.EightQPositiveExclusion

/-! Source-only complete order-at-most-41 exclusion for eight-cycle suns.
The original p/q and list contracts carry no extra finite coverage premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_pure_p_nonintegral (p : Fin 8 → ℕ) (hp : 0 < ∑ i, p i)
    (hn : nOf 8 p (fun _ => 0) ≤ 41) : ¬ IsIntegralGraph (SG 8 p (fun _ => 0)) := by
  intro hG
  obtain ⟨p',hsum,hn',hI,hpar⟩ := eight_integral_odd_normalization p hp hn hG
  exact eight_opposite_odd_nonintegral p' (by rw [hsum]; exact hp) hn' hpar hI
#print axioms Paper7EightCycle.eight_pure_p_nonintegral

theorem eight_nonintegral (p q : Fin 8 → ℕ) (hp : 0 < ∑ i, (p i+q i))
    (hn : nOf 8 p q ≤ 41) : ¬ IsIntegralGraph (SG 8 p q) := by
  intro hG
  have hq := eight_integral_qzero p q hn hG
  subst q
  exact eight_pure_p_nonintegral p (by simpa using hp) hn hG
#print axioms Paper7EightCycle.eight_nonintegral

theorem original_eight_nonintegral (L : Fin 8 → List ℕ)
    (hp : 0 < pendantCount 8 L) (hn : order 8 L ≤ 41) :
    ¬ IsIntegralGraph (sunGraph 8 L) := by
  intro hG
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 8 L (by decide) hG k _ (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 8 L
  let q := Paper7Normalize.countP2 8 L
  let e : sunGraph 8 L ≃g SG 8 p q := Paper7Normalize.sunNormalizeIso 8 L (by decide) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hc := Fintype.card_congr e.toEquiv
  change order 8 L = order 8 (pq 8 p q) at hc
  rw [Paper7Setup.sg_order] at hc
  have hn' : nOf 8 p q ≤ 41 := by omega
  have hq := eight_integral_qzero p q hn' hI
  have hpend := Paper7CycleThree.order_eq_add_pendantCount 8 L
  have hsize : order 8 L = 8+∑ i, p i := by simpa [hq,nOf] using hc
  have hp' : 0 < ∑ i, p i := by omega
  rw [hq] at hn' hI
  exact eight_pure_p_nonintegral p hp' hn' hI
#print axioms Paper7EightCycle.original_eight_nonintegral

end Paper7EightCycle
