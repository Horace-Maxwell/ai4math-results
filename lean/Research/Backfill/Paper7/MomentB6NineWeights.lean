import Research.Backfill.Paper7.MomentB6NineShapes
import Research.Backfill.Paper7.MomentB6EndpointWeights

/-! Source-only exact weights for the complete Z9 families. Small certificates
below range over actual positions/subsets and arithmetic products or cards;
the original q-fibres are connected by the proved generic bijections. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

theorem b6_nine_pair_tail_products :
    (∀ i j : Fin 6, i ≠ j →
      (∏ k : {k : Fin 6 // k ≠ i}, (b6TwoPoint 7 2 i j k.val + 1)) = 3) ∧
    (∀ i j : Fin 6, i ≠ j →
      (∏ k : {k : Fin 6 // k ≠ i}, (b6TwoPoint 6 3 i j k.val + 1)) = 4) := by
  decide
#print axioms Paper7MomentCounts.b6_nine_pair_tail_products

theorem b6_nine_spike_tail_product :
    ∀ (i : Fin 6) (s : Finset (Fin 6)), i ∉ s → s.card = 2 →
      (∏ k : {k : Fin 6 // k ≠ i}, (b6SpikeOnes 7 i s k.val + 1)) = 4 := by
  decide
#print axioms Paper7MomentCounts.b6_nine_spike_tail_product

theorem b6_nine_endpoint_support_cards :
    (∀ i j k : Fin 6, i ≠ j → i ≠ k → j ≠ k →
      Fintype.card {a : Fin 6 // 0 < b6ThreePoint 6 2 1 i j k a} = 3) ∧
    (∀ i j : Fin 6, i ≠ j →
      Fintype.card {a : Fin 6 // 0 < b6TwoPoint 5 4 i j a} = 2) := by
  decide
#print axioms Paper7MomentCounts.b6_nine_endpoint_support_cards

theorem b6_nine_pair63_weights (i j : Fin 6) (hij : i ≠ j) :
    Paper7MomentDP.boundedQDP 6 (b6TwoPoint 6 3 i j) 0 = 1 ∧
      Paper7MomentDP.boundedQDP 6 (b6TwoPoint 6 3 i j) 6 = 4 := by
  refine ⟨boundedQDP_zero_capacity_eq_one 6 _,?_⟩
  have hs := (b6TwoPoint_sums 6 3 i j hij).1
  have he := Finset.sum_erase_add Finset.univ (b6TwoPoint 6 3 i j) (Finset.mem_univ i)
  have hi : b6TwoPoint 6 3 i j i = 6 := by simp [b6TwoPoint]
  rw [boundedQDP_dominant_product 6 _ i 6 (by rw [hi]) (by omega)]
  exact b6_nine_pair_tail_products.2 i j hij
#print axioms Paper7MomentCounts.b6_nine_pair63_weights

theorem b6_nine_pair72_weight (i j : Fin 6) (hij : i ≠ j) :
    Paper7MomentDP.boundedQDP 6 (b6TwoPoint 7 2 i j) 2 = 3 := by
  have hs := (b6TwoPoint_sums 7 2 i j hij).1
  have he := Finset.sum_erase_add Finset.univ (b6TwoPoint 7 2 i j) (Finset.mem_univ i)
  have hi : b6TwoPoint 7 2 i j i = 7 := by simp [b6TwoPoint]
  rw [boundedQDP_dominant_product 6 _ i 2 (by rw [hi]; decide) (by omega)]
  exact b6_nine_pair_tail_products.1 i j hij
#print axioms Paper7MomentCounts.b6_nine_pair72_weight

theorem b6_nine_spike72_weight (i : Fin 6) (s : Finset (Fin 6)) (his : i ∉ s)
    (hc : s.card = 2) : Paper7MomentDP.boundedQDP 6 (b6SpikeOnes 7 i s) 3 = 4 := by
  have hs := (b6SpikeOnes_sums 7 i s his).1
  have he := Finset.sum_erase_add Finset.univ (b6SpikeOnes 7 i s) (Finset.mem_univ i)
  have hi : b6SpikeOnes 7 i s i = 7 := by simp [b6SpikeOnes]
  rw [boundedQDP_dominant_product 6 _ i 3 (by rw [hi]; decide) (by omega)]
  exact b6_nine_spike_tail_product i s his hc
#print axioms Paper7MomentCounts.b6_nine_spike72_weight

theorem b6_nine_triple621_weight (i j k : Fin 6)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Paper7MomentDP.boundedQDP 6 (b6ThreePoint 6 2 1 i j k) 8 = 3 := by
  have hs := (b6ThreePoint_sums 6 2 1 i j k hij hik hjk).1
  have h := (b6_total_nine_endpoint_weights _ hs).2.1
  rw [Nat.card_eq_fintype_card] at h
  exact h.trans (b6_nine_endpoint_support_cards.1 i j k hij hik hjk)
#print axioms Paper7MomentCounts.b6_nine_triple621_weight

theorem b6_nine_spike63_weight (i : Fin 6) (s : Finset (Fin 6)) (his : i ∉ s)
    (hc : s.card = 3) : Paper7MomentDP.boundedQDP 6 (b6SpikeOnes 6 i s) 9 = 1 := by
  have hs : (∑ k, b6SpikeOnes 6 i s k) = 9 := by
    simpa [hc] using (b6SpikeOnes_sums 6 i s his).1
  exact (b6_total_nine_endpoint_weights _ hs).2.2
#print axioms Paper7MomentCounts.b6_nine_spike63_weight

theorem b6_nine_pair54_weight (i j : Fin 6) (hij : i ≠ j) :
    Paper7MomentDP.boundedQDP 6 (b6TwoPoint 5 4 i j) 8 = 2 := by
  have hs := (b6TwoPoint_sums 5 4 i j hij).1
  have h := (b6_total_nine_endpoint_weights _ hs).2.1
  rw [Nat.card_eq_fintype_card] at h
  exact h.trans (b6_nine_endpoint_support_cards.2 i j hij)
#print axioms Paper7MomentCounts.b6_nine_pair54_weight

end Paper7MomentCounts
