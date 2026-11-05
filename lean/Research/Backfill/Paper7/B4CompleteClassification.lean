import Research.Backfill.Paper7.B4QzeroBranch
import Research.Backfill.Paper7.B4PureQBranch
import Research.Backfill.Paper7.B4MixedCompleteBranch

/-! Source-only full forward classification, assembled from complete source
branches. The original parameter and arm-list domains are retained. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Classical

theorem normalized_b4_integral_four (p q : Fin 4 → ℕ)
    (hpend : 0 < ∑ i, (p i+q i)) (hn : nOf 4 p q ≤ 49)
    (hG : IsIntegralGraph (SG 4 p q)) :
    Nonempty (SG 4 p q ≃g sunGraph 4 G13) ∨
      Nonempty (SG 4 p q ≃g sunGraph 4 G20a) ∨
      Nonempty (SG 4 p q ≃g sunGraph 4 G20b) ∨
      Nonempty (SG 4 p q ≃g sunGraph 4 C42Ten) := by
  by_cases hq : (∑ i, q i) = 0
  · have hqzero : q = (fun _ => 0) := by
      funext i
      have hi : q i ≤ ∑ j, q j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (q j)) (Finset.mem_univ i)
      omega
    rw [hqzero] at hpend hn hG ⊢
    exact Or.inl (qzero_integral_iso_g13 p (by simpa using hpend) hn hG)
  have hqpos : 0 < ∑ i, q i := Nat.pos_of_ne_zero hq
  by_cases hp : (∑ i, p i) = 0
  · have hpzero : p = (fun _ => 0) := by
      funext i
      have hi : p i ≤ ∑ j, p j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le (p j)) (Finset.mem_univ i)
      omega
    rw [hpzero] at hn hG ⊢
    exact Or.inr (Or.inr (pure_q_integral_named q hqpos hn hG))
  have hppos : 0 < ∑ i, p i := Nat.pos_of_ne_zero hp
  exact Or.inr (Or.inl (mixed_integral_iso_g20a p q hppos hqpos hn hG))
#print axioms Paper7B4Analytic.normalized_b4_integral_four

theorem original_b4_integral_four (L : Fin 4 → List ℕ)
    (hpend : 0 < pendantCount 4 L) (hn : order 4 L ≤ 49)
    (hG : IsIntegralGraph (sunGraph 4 L)) :
    Nonempty (sunGraph 4 L ≃g sunGraph 4 G13) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G20a) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 G20b) ∨
      Nonempty (sunGraph 4 L ≃g sunGraph 4 C42Ten) := by
  have hL : ∀ k (j : Fin (L k).length), (L k).get j ≤ 2 := by
    intro k j
    exact Paper7BMS.check_OnlyP1P2 4 L (by omega) hG k _
      (List.mem_iff_get.mpr ⟨j,rfl⟩)
  let p := Paper7Normalize.countP1 4 L
  let q := Paper7Normalize.countP2 4 L
  let e : sunGraph 4 L ≃g SG 4 p q := Paper7Normalize.sunNormalizeIso 4 L (by omega) hL
  have hcard := Fintype.card_congr e.toEquiv
  change order 4 L = order 4 (pq 4 p q) at hcard
  have hpos : 0 < pendantCount 4 (pq 4 p q) := by
    rw [Paper7CycleThree.order_eq_add_pendantCount,
      Paper7CycleThree.order_eq_add_pendantCount] at hcard
    omega
  have hpq : 0 < ∑ i, (p i+q i) := (Paper7CycleThree.pq_pendants_positive 4 p q).mp hpos
  have hI := Paper7Normalize.graphIso_integral _ _ e hG
  have hn' : nOf 4 p q ≤ 49 := by rw [← Paper7Setup.sg_order,← hcard]; exact hn
  rcases normalized_b4_integral_four p q hpq hn' hI with hf | hf | hf | hf
  · exact Or.inl ⟨e.trans (Classical.choice hf)⟩
  · exact Or.inr (Or.inl ⟨e.trans (Classical.choice hf)⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.trans (Classical.choice hf)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨e.trans (Classical.choice hf)⟩))
#print axioms Paper7B4Analytic.original_b4_integral_four

end Paper7B4Analytic
