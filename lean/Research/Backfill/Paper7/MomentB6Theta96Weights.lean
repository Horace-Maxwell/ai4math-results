import Research.Backfill.Paper7.MomentB6Theta96Profiles
import Research.Backfill.Paper7.MomentB6EightWeights

/-! True bounded-q multiplicities and ordered-position cardinalities.
The first 22 weights reuse the successful seven/eight/nine/ten proofs.
Only the 32 new profiles use small pivot-tail certificates, with both pivot
inequalities and the proved complement bijection retained. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators

def b6Theta96Weight : Fin 54 → ℕ :=
  ![1,2,4,3,4,3,1,2, 4,2,8,9,12,15,3,9,6,4,1,3,1,1,
    3,8,14,23,32,1,9,16,13,23,27,23,23,17,16,21,20,16,10,5,1,1,4,1,
    1,1,5,4,1,1,1,1]
#print axioms Paper7MomentCounts.b6Theta96Weight

def b6Theta96Card : Fin 54 → ℕ :=
  ![6,30,30,30,60,120,60,30, 60,30,120,60,180,30,15,120,120,180,180,60,90,60,
    120,180,180,120,6,60,120,180,60,360,120,60,180,30,60,180,60,180,180,360,30,120,60,60,
    120,60,180,360,20,30,180,180]
#print axioms Paper7MomentCounts.b6Theta96Card

theorem b6Theta96Ten_weight_identifications : ∀ j : Fin 14,
    b6Theta96Nat (b6Theta96TenIndex j) = b6TenReferenceNat j ∧
      b6Theta96Q (b6Theta96TenIndex j) = b6TenProfileQ j ∧
      b6Theta96Weight (b6Theta96TenIndex j) = b6TenProfileWeight j := by decide +kernel
#print axioms Paper7MomentCounts.b6Theta96Ten_weight_identifications

theorem b6Theta96Reference_weight_low (j : Fin 54) (hj : j.val < 22) :
    Paper7MomentDP.boundedQDP 6 (b6Theta96Nat j) (b6Theta96Q j) =
      b6Theta96Weight j := by
  by_cases he : j.val < 8
  · have hv : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨
        j.val = 4 ∨ j.val = 5 ∨ j.val = 6 ∨ j.val = 7 := by omega
    rcases hv with h | h | h | h | h | h | h | h
    · have heq0 : j = 0 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 0 = b6SevenSingle 0 := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 0) 7 = 1
      rw [hz]
      exact b6_boundedQDP_single_eq_one 0 7 (by decide +kernel)
    · have heq1 : j = 1 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 1 = b6TwoPointUnit 7 0 1 := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 1) 5 = 2
      rw [hz]
      exact boundedQDP_twoPointUnit_eq_two 7 0 1 (by decide +kernel) 5 (by decide +kernel) (by decide +kernel)
    · have heq2 : j = 2 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 2 = b6TwoPoint 6 3 0 1 := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 2) 6 = 4
      rw [hz]
      exact (b6_nine_pair63_weights 0 1 (by decide +kernel)).2
    · have heq3 : j = 3 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 3 = b6TwoPoint 7 2 0 1 := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 3) 2 = 3
      rw [hz]
      exact b6_nine_pair72_weight 0 1 (by decide +kernel)
    · have heq4 : j = 4 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 4 = b6SpikeOnes 7 0 {1,2} := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 4) 3 = 4
      rw [hz]
      exact b6_nine_spike72_weight 0 {1,2} (by decide +kernel) (by decide +kernel)
    · have heq5 : j = 5 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 5 = b6ThreePoint 6 2 1 0 1 2 := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 5) 8 = 3
      rw [hz]
      exact b6_nine_triple621_weight 0 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    · have heq6 : j = 6 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 6 = b6SpikeOnes 6 0 {1,2,3} := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 6) 9 = 1
      rw [hz]
      exact b6_nine_spike63_weight 0 {1,2,3} (by decide +kernel) (by decide +kernel)
    · have heq7 : j = 7 := Fin.ext h
      subst j
      have hz : b6Theta96Nat 7 = b6TwoPoint 5 4 0 1 := by decide +kernel
      change Paper7MomentDP.boundedQDP 6 (b6Theta96Nat 7) 8 = 2
      rw [hz]
      exact b6_nine_pair54_weight 0 1 (by decide +kernel)
  · let k : Fin 14 := ⟨j.val-8,by omega⟩
    have hjk : j = b6Theta96TenIndex k := Fin.ext (by dsimp [k,b6Theta96TenIndex]; omega)
    rw [hjk]
    obtain ⟨hz,hq,hw⟩ := b6Theta96Ten_weight_identifications k
    rw [hz,hq,hw]
    exact b6TenReference_weight k
#print axioms Paper7MomentCounts.b6Theta96Reference_weight_low

def b6Theta96HalfQ (j : Fin 54) : ℕ :=
  min (b6Theta96Q j) ((∑ i, b6Theta96Nat j i) - b6Theta96Q j)
#print axioms Paper7MomentCounts.b6Theta96HalfQ

def b6Theta96TailGuard (j : Fin 54)
    (a : (k : {k : Fin 6 // k ≠ 0}) → Fin (b6Theta96Nat j k.val + 1)) : Bool :=
  decide ((∑ k, boundedTailValue 6 (b6Theta96Nat j) 0 a k) ≤ b6Theta96HalfQ j) &&
    decide (b6Theta96HalfQ j ≤ b6Theta96Nat j 0 +
      (∑ k, boundedTailValue 6 (b6Theta96Nat j) 0 a k))
#print axioms Paper7MomentCounts.b6Theta96TailGuard

def b6Theta96TailSum (j : Fin 54) : ℕ :=
  ∑ a : (k : {k : Fin 6 // k ≠ 0}) → Fin (b6Theta96Nat j k.val + 1),
    if b6Theta96TailGuard j a then 1 else 0
#print axioms Paper7MomentCounts.b6Theta96TailSum

theorem b6Theta96TailSum_high : ∀ k : Fin 32,
    b6Theta96TailSum ⟨k.val+22,by omega⟩ = b6Theta96Weight ⟨k.val+22,by omega⟩ := by
  decide +kernel
#print axioms Paper7MomentCounts.b6Theta96TailSum_high

theorem b6Theta96Reference_weight (j : Fin 54) :
    Paper7MomentDP.boundedQDP 6 (b6Theta96Nat j) (b6Theta96Q j) = b6Theta96Weight j := by
  classical
  by_cases hj : j.val < 22
  · exact b6Theta96Reference_weight_low j hj
  · have hQ := (b6Theta96Reference_data j).2.2.1
    have hh : Paper7MomentDP.boundedQDP 6 (b6Theta96Nat j) (b6Theta96Q j) =
        Paper7MomentDP.boundedQDP 6 (b6Theta96Nat j) (b6Theta96HalfQ j) := by
      by_cases he : b6Theta96Q j ≤ (∑ i, b6Theta96Nat j i) - b6Theta96Q j
      · simp only [b6Theta96HalfQ,min_eq_left he]
      · rw [b6Theta96HalfQ,min_eq_right (by omega)]
        exact boundedQDP_complement 6 (b6Theta96Nat j) (b6Theta96Q j) hQ
    rw [hh,boundedQDP_sliced_sum 6 (b6Theta96Nat j) 0]
    calc
      (∑ a : (k : {k : Fin 6 // k ≠ 0}) → Fin (b6Theta96Nat j k.val + 1),
        if BoundedTailSlice 6 (b6Theta96Nat j) 0 (b6Theta96HalfQ j) a then 1 else 0)
          = b6Theta96TailSum j := by
        apply Finset.sum_congr rfl
        intro a _ha
        simp [BoundedTailSlice,b6Theta96TailGuard]
        by_cases hc : (∑ k, boundedTailValue 6 (b6Theta96Nat j) 0 a k) ≤ b6Theta96HalfQ j ∧
            b6Theta96HalfQ j ≤ b6Theta96Nat j 0 +
              (∑ k, boundedTailValue 6 (b6Theta96Nat j) 0 a k)
        · simp only [ite_eq_left hc]
          exact ite_eq_left hc
        · simp only [ite_eq_right hc]
          exact ite_eq_right hc
      _ = b6Theta96Weight j := by
        let k : Fin 32 := ⟨j.val-22,by omega⟩
        have hjk : (⟨k.val+22,by omega⟩ : Fin 54) = j :=
          Fin.ext (by dsimp [k]; omega)
        simpa only [hjk] using b6Theta96TailSum_high k
#print axioms Paper7MomentCounts.b6Theta96Reference_weight

theorem b6Theta96Card_factorials : ∀ j : Fin 54,
    b6Theta96Card j * (∏ v : Fin 8, (b6Theta96Profile j v).factorial) = 720 ∧
      0 < (∏ v : Fin 8, (b6Theta96Profile j v).factorial) := by decide +kernel
#print axioms Paper7MomentCounts.b6Theta96Card_factorials

theorem b6Theta96Histogram_card (j : Fin 54) :
    Fintype.card (FiniteHistogramFiber (b6Theta96Reference j)) = b6Theta96Card j := by
  have h := finiteHistogramFiber_natCard_factorial (b6Theta96Reference j)
  have hp : (∏ v : Fin 8, (finiteValueHistogram (b6Theta96Reference j) v).factorial) =
      ∏ v : Fin 8, (b6Theta96Profile j v).factorial := by
    rw [b6Theta96Reference_histogram]
  rw [hp] at h
  have ht := b6Theta96Card_factorials j
  calc
    Fintype.card (FiniteHistogramFiber (b6Theta96Reference j)) =
        Nat.card (FiniteHistogramFiber (b6Theta96Reference j)) :=
      (Nat.card_eq_fintype_card).symm
    _ = b6Theta96Card j := Nat.mul_right_cancel ht.2 (h.trans ht.1.symm)
#print axioms Paper7MomentCounts.b6Theta96Histogram_card

theorem b6Theta96_weighted_sum :
    (∑ j : Fin 54, b6Theta96Card j * b6Theta96Weight j) = 53903 := by decide +kernel
#print axioms Paper7MomentCounts.b6Theta96_weighted_sum

end Paper7MomentCounts
