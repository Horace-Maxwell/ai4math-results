import Research.Backfill.Paper7.MomentB6W6DominantFastWeight
import Research.Backfill.Paper7.MomentB6EndpointWeights

/-! SOURCE ONLY. Exact endpoints before the two dominant-coordinate tests.
Q=0 and Q=capacity return one. Q=1 and Q+1=capacity return the explicit
six-coordinate positive-capacity count. All other Q retain the proven dominant
weight. Branch order handles capacity zero/one overlaps without any premise.
Nat.card occurs only in proof interfaces, never in either evaluator definition.
No numeric theta value, native computation, budget change or execution plan. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6W6PositiveCapacityCount (z : Fin 6 → ℕ) : ℕ :=
  (if 0 < z 0 then 1 else 0) +
  (if 0 < z 1 then 1 else 0) +
  (if 0 < z 2 then 1 else 0) +
  (if 0 < z 3 then 1 else 0) +
  (if 0 < z 4 then 1 else 0) +
  (if 0 < z 5 then 1 else 0)
#print axioms Paper7MomentCounts.b6W6PositiveCapacityCount

theorem b6W6PositiveSupportCard_eq (z : Fin 6 → ℕ) :
    Nat.card {i : Fin 6 // 0 < z i} = b6W6PositiveCapacityCount z := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simp [b6W6PositiveCapacityCount, Fin.card_filter_univ_succ', Finset.filter_singleton, Nat.add_assoc]
  split_ifs <;> simp
#print axioms Paper7MomentCounts.b6W6PositiveSupportCard_eq

theorem b6W6ProductFastWeight_zero_endpoint (z : Fin 6 → ℕ) :
    b6W6ProductFastWeight z 0 = 1 := by
  rw [b6W6ProductFastWeight_eq_boundedQDP, boundedQDP_zero_capacity_eq_one]
  norm_num
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_zero_endpoint

theorem b6W6ProductFastWeight_full_endpoint (z : Fin 6 → ℕ) :
    b6W6ProductFastWeight z (b6W6CapacitySum z) = 1 := by
  rw [b6W6ProductFastWeight_eq_boundedQDP, b6W6CapacitySum_eq,
    boundedQDP_full_capacity_eq_one]
  norm_num
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_full_endpoint

theorem b6W6ProductFastWeight_one_endpoint (z : Fin 6 → ℕ) :
    b6W6ProductFastWeight z 1 = (b6W6PositiveCapacityCount z : ℤ) := by
  rw [b6W6ProductFastWeight_eq_boundedQDP,
    boundedQDP_one_eq_positive_support_card, b6W6PositiveSupportCard_eq]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_one_endpoint

theorem b6W6ProductFastWeight_capacity_predecessor (z : Fin 6 → ℕ) (Q : ℕ)
    (hnext : Q + 1 = b6W6CapacitySum z) :
    b6W6ProductFastWeight z Q = (b6W6PositiveCapacityCount z : ℤ) := by
  have hc : b6W6CapacitySum z = ∑ i, z i := b6W6CapacitySum_eq z
  have hpos : 0 < ∑ i, z i := by omega
  have hQ : Q = (∑ i, z i) - 1 := by omega
  rw [b6W6ProductFastWeight_eq_boundedQDP, hQ,
    boundedQDP_capacity_sub_one_eq_positive_support_card 6 z hpos,
    b6W6PositiveSupportCard_eq]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_capacity_predecessor

def b6W6EndpointDominantFastWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  bif decide (Q = 0) then 1 else
    bif decide (Q = b6W6CapacitySum z) then 1 else
      bif decide (Q = 1) then (b6W6PositiveCapacityCount z : ℤ) else
        bif decide (Q + 1 = b6W6CapacitySum z) then
          (b6W6PositiveCapacityCount z : ℤ)
        else b6W6DominantFastWeight z Q
#print axioms Paper7MomentCounts.b6W6EndpointDominantFastWeight

theorem b6W6EndpointDominantFastWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6EndpointDominantFastWeight z Q = b6W6ProductFastWeight z Q := by
  unfold b6W6EndpointDominantFastWeight
  by_cases h0 : Q = 0
  · rw [decide_eq_true h0, Bool.cond_true, h0]
    exact (b6W6ProductFastWeight_zero_endpoint z).symm
  · rw [decide_eq_false h0, Bool.cond_false]
    by_cases hcap : Q = b6W6CapacitySum z
    · rw [decide_eq_true hcap, Bool.cond_true, hcap]
      exact (b6W6ProductFastWeight_full_endpoint z).symm
    · rw [decide_eq_false hcap, Bool.cond_false]
      by_cases h1 : Q = 1
      · rw [decide_eq_true h1, Bool.cond_true, h1]
        exact (b6W6ProductFastWeight_one_endpoint z).symm
      · rw [decide_eq_false h1, Bool.cond_false]
        by_cases hnext : Q + 1 = b6W6CapacitySum z
        · rw [decide_eq_true hnext, Bool.cond_true]
          exact (b6W6ProductFastWeight_capacity_predecessor z Q hnext).symm
        · rw [decide_eq_false hnext, Bool.cond_false]
          exact b6W6DominantFastWeight_eq z Q
#print axioms Paper7MomentCounts.b6W6EndpointDominantFastWeight_eq

end Paper7MomentCounts
