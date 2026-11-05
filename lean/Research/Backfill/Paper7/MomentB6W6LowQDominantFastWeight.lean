import Research.Backfill.Paper7.MomentB6W6EndpointDominantFastWeight
import Research.Backfill.Paper7.MomentB6LowQThree

/-! SOURCE ONLY. Universal six-coordinate low-Q weight, not a numeric table.
Targets 0/1/2/3 are checked before capacity sums and dominant-coordinate guards.
Only the remaining branch computes capacity and checks its four endpoints.
The two/three formulas use six explicit capacity indicators; no Nat.card or
Finset enumeration occurs in evaluator definitions. Complement conditions
supply their own capacity bound. All natural capacities and Q remain allowed.
The exact generic DP2 source has saved successful Windows evidence; DP3 is
still a pending execution dependency, not a successful parent. No graph premise, deterministic budget or runtime plan. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6W6CapacitySupportCount (z : Fin 6 → ℕ) (k : ℕ) : ℕ :=
  (if k ≤ z 0 then 1 else 0) +
  (if k ≤ z 1 then 1 else 0) +
  (if k ≤ z 2 then 1 else 0) +
  (if k ≤ z 3 then 1 else 0) +
  (if k ≤ z 4 then 1 else 0) +
  (if k ≤ z 5 then 1 else 0)
#print axioms Paper7MomentCounts.b6W6CapacitySupportCount

theorem boundedQCapacitySupport_six_eq (z : Fin 6 → ℕ) (k : ℕ) :
    boundedQCapacitySupport 6 z k = b6W6CapacitySupportCount z k := by
  unfold boundedQCapacitySupport
  simp [b6W6CapacitySupportCount, Fin.card_filter_univ_succ',
    Finset.filter_singleton, Nat.add_assoc]
  split_ifs <;> simp
#print axioms Paper7MomentCounts.boundedQCapacitySupport_six_eq

def b6W6TwoCapacityWeight (z : Fin 6 → ℕ) : ℕ :=
  (b6W6CapacitySupportCount z 1).choose 2 + b6W6CapacitySupportCount z 2
#print axioms Paper7MomentCounts.b6W6TwoCapacityWeight

def b6W6ThreeCapacityWeight (z : Fin 6 → ℕ) : ℕ :=
  let s1 := b6W6CapacitySupportCount z 1
  let s2 := b6W6CapacitySupportCount z 2
  let s3 := b6W6CapacitySupportCount z 3
  s1.choose 3 + s2 * (s1 - 1) + s3
#print axioms Paper7MomentCounts.b6W6ThreeCapacityWeight

theorem b6W6ProductFastWeight_two_low (z : Fin 6 → ℕ) :
    b6W6ProductFastWeight z 2 = (b6W6TwoCapacityWeight z : ℤ) := by
  rw [b6W6ProductFastWeight_eq_boundedQDP, boundedQDP_two_eq_capacitySupports]
  simp only [boundedQCapacitySupport_six_eq, b6W6TwoCapacityWeight]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_two_low

theorem b6W6ProductFastWeight_three_low (z : Fin 6 → ℕ) :
    b6W6ProductFastWeight z 3 = (b6W6ThreeCapacityWeight z : ℤ) := by
  rw [b6W6ProductFastWeight_eq_boundedQDP, boundedQDP_three_eq_capacitySupports]
  simp only [boundedQCapacitySupport_six_eq, b6W6ThreeCapacityWeight]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_three_low

theorem b6W6ProductFastWeight_complement_at (z : Fin 6 → ℕ) (Q k : ℕ)
    (hnext : Q + k = b6W6CapacitySum z) :
    b6W6ProductFastWeight z Q = b6W6ProductFastWeight z k := by
  have hc : b6W6CapacitySum z = ∑ i, z i := b6W6CapacitySum_eq z
  have hle : Q ≤ ∑ i, z i := by omega
  have hsub : (∑ i, z i) - Q = k := by omega
  calc
    b6W6ProductFastWeight z Q = (Paper7MomentDP.boundedQDP 6 z Q : ℤ) :=
      b6W6ProductFastWeight_eq_boundedQDP z Q
    _ = (Paper7MomentDP.boundedQDP 6 z k : ℤ) := by
      rw [boundedQDP_complement 6 z Q hle, hsub]
    _ = b6W6ProductFastWeight z k :=
      (b6W6ProductFastWeight_eq_boundedQDP z k).symm
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_complement_at

def b6W6LowQDominantFastWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  bif decide (Q = 0) then 1 else
    bif decide (Q = 1) then (b6W6PositiveCapacityCount z : ℤ) else
      bif decide (Q = 2) then (b6W6TwoCapacityWeight z : ℤ) else
        bif decide (Q = 3) then (b6W6ThreeCapacityWeight z : ℤ) else
          let cap := b6W6CapacitySum z
          bif decide (Q = cap) then 1 else
            bif decide (Q + 1 = cap) then (b6W6PositiveCapacityCount z : ℤ) else
              bif decide (Q + 2 = cap) then (b6W6TwoCapacityWeight z : ℤ) else
                bif decide (Q + 3 = cap) then (b6W6ThreeCapacityWeight z : ℤ) else
                  b6W6DominantFastWeight z Q
#print axioms Paper7MomentCounts.b6W6LowQDominantFastWeight

theorem b6W6LowQDominantFastWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6LowQDominantFastWeight z Q = b6W6ProductFastWeight z Q := by
  unfold b6W6LowQDominantFastWeight
  by_cases h0 : Q = 0
  · rw [decide_eq_true h0, Bool.cond_true, h0]
    exact (b6W6ProductFastWeight_zero_endpoint z).symm
  · rw [decide_eq_false h0, Bool.cond_false]
    by_cases h1 : Q = 1
    · rw [decide_eq_true h1, Bool.cond_true, h1]
      exact (b6W6ProductFastWeight_one_endpoint z).symm
    · rw [decide_eq_false h1, Bool.cond_false]
      by_cases h2 : Q = 2
      · rw [decide_eq_true h2, Bool.cond_true, h2]
        exact (b6W6ProductFastWeight_two_low z).symm
      · rw [decide_eq_false h2, Bool.cond_false]
        by_cases h3 : Q = 3
        · rw [decide_eq_true h3, Bool.cond_true, h3]
          exact (b6W6ProductFastWeight_three_low z).symm
        · rw [decide_eq_false h3, Bool.cond_false]
          dsimp only
          by_cases hcap : Q = b6W6CapacitySum z
          · rw [decide_eq_true hcap, Bool.cond_true, hcap]
            exact (b6W6ProductFastWeight_full_endpoint z).symm
          · rw [decide_eq_false hcap, Bool.cond_false]
            by_cases hnext1 : Q + 1 = b6W6CapacitySum z
            · rw [decide_eq_true hnext1, Bool.cond_true]
              exact (b6W6ProductFastWeight_capacity_predecessor z Q hnext1).symm
            · rw [decide_eq_false hnext1, Bool.cond_false]
              by_cases hnext2 : Q + 2 = b6W6CapacitySum z
              · rw [decide_eq_true hnext2, Bool.cond_true]
                exact ((b6W6ProductFastWeight_complement_at z Q 2 hnext2).trans
                  (b6W6ProductFastWeight_two_low z)).symm
              · rw [decide_eq_false hnext2, Bool.cond_false]
                by_cases hnext3 : Q + 3 = b6W6CapacitySum z
                · rw [decide_eq_true hnext3, Bool.cond_true]
                  exact ((b6W6ProductFastWeight_complement_at z Q 3 hnext3).trans
                    (b6W6ProductFastWeight_three_low z)).symm
                · rw [decide_eq_false hnext3, Bool.cond_false]
                  exact b6W6DominantFastWeight_eq z Q
#print axioms Paper7MomentCounts.b6W6LowQDominantFastWeight_eq

end Paper7MomentCounts
