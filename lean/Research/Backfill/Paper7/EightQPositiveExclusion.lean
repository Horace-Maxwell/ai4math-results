import Research.Backfill.Paper7.EightMixedQExclusion
import Research.Backfill.Paper7.EightPureQExclusion
import Research.Backfill.Paper7.CycleThreeReduction

/-! NEW SOURCE ONLY. Full Q-positive eight-cycle exclusion and its original
list-of-paths consequence. No unrestricted eight-cycle main check is claimed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7EightCycle
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem eight_qpositive_nonintegral (p q : Fin 8 → ℕ)
    (hq : 0 < ∑ i, q i) (hn : nOf 8 p q ≤ 41) : ¬ IsIntegralGraph (SG 8 p q) := by
  by_cases hp : 0 < ∑ i, p i
  · exact eight_mixed_nonintegral p q hp hq hn
  · have hpz : p = (fun _ => 0) := by
      funext i
      have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (p j)) (Finset.mem_univ i)
      omega
    rw [hpz] at hn ⊢
    exact eight_pure_q_nonintegral q hq hn
#print axioms Paper7EightCycle.eight_qpositive_nonintegral

theorem eight_integral_qzero (p q : Fin 8 → ℕ) (hn : nOf 8 p q ≤ 41)
    (hG : IsIntegralGraph (SG 8 p q)) : q = (fun _ => 0) := by
  have hsum : ∑ i, q i = 0 := by
    by_contra hh
    exact eight_qpositive_nonintegral p q (by omega) hn hG
  funext i
  have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ i)
  omega
#print axioms Paper7EightCycle.eight_integral_qzero

theorem original_eight_count_p2_zero (L : Fin 8 → List ℕ)
    (hn : order 8 L ≤ 41) (hG : IsIntegralGraph (sunGraph 8 L)) :
    Paper7Normalize.countP2 8 L = (fun _ => 0) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 8 L (by decide) hG k _ (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 8 L
  let q := Paper7Normalize.countP2 8 L
  let e := Paper7Normalize.sunNormalizeIso 8 L (by decide) hL
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hc := Fintype.card_congr e.toEquiv
  change order 8 L = order 8 (pq 8 p q) at hc
  rw [Paper7Setup.sg_order] at hc
  exact eight_integral_qzero p q (by omega) hI
#print axioms Paper7EightCycle.original_eight_count_p2_zero

end Paper7EightCycle
