import Research.Backfill.Paper7.MomentB6W6LowQDominantFastWeight
import Research.Backfill.Paper7.MomentB6LowQFive

/-! SOURCE ONLY. Extend the successful universal six-coordinate low-Q weight
through Q = 4, 5 and their capacity complements. The Q = 0, 1, 2, 3 tests
and values remain first and unchanged. All support counts use the successful
six explicit indicators. The generic DP4/DP5 formulas hold for every natural
capacity, including zero and targets beyond total capacity. Complement bounds
are derived inside the already proved all-k complement lemma. No new graph
premise, numerical certificate, deterministic budget or execution plan. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6W6FourCapacityWeight (z : Fin 6 → ℕ) : ℕ :=
  let s1 := b6W6CapacitySupportCount z 1
  let s2 := b6W6CapacitySupportCount z 2
  let s3 := b6W6CapacitySupportCount z 3
  let s4 := b6W6CapacitySupportCount z 4
  s1.choose 4 + s2 * (s1 - 1).choose 2 + s2.choose 2 + s3 * (s1 - 1) + s4
#print axioms Paper7MomentCounts.b6W6FourCapacityWeight

def b6W6FiveCapacityWeight (z : Fin 6 → ℕ) : ℕ :=
  let s1 := b6W6CapacitySupportCount z 1
  let s2 := b6W6CapacitySupportCount z 2
  let s3 := b6W6CapacitySupportCount z 3
  let s4 := b6W6CapacitySupportCount z 4
  let s5 := b6W6CapacitySupportCount z 5
  s1.choose 5 + s2 * (s1 - 1).choose 3 + s2.choose 2 * (s1 - 2) +
    s3 * (s1 - 1).choose 2 + s3 * (s2 - 1) + s4 * (s1 - 1) + s5
#print axioms Paper7MomentCounts.b6W6FiveCapacityWeight

theorem b6W6ProductFastWeight_four_low (z : Fin 6 → ℕ) :
    b6W6ProductFastWeight z 4 = (b6W6FourCapacityWeight z : ℤ) := by
  rw [b6W6ProductFastWeight_eq_boundedQDP, boundedQDP_four_eq_capacitySupports]
  simp only [boundedQCapacitySupport_six_eq, b6W6FourCapacityWeight]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_four_low

theorem b6W6ProductFastWeight_five_low (z : Fin 6 → ℕ) :
    b6W6ProductFastWeight z 5 = (b6W6FiveCapacityWeight z : ℤ) := by
  rw [b6W6ProductFastWeight_eq_boundedQDP, boundedQDP_five_eq_capacitySupports]
  simp only [boundedQCapacitySupport_six_eq, b6W6FiveCapacityWeight]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_five_low

def b6W6LowQFiveDominantFastWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  bif decide (Q = 0) then 1 else
    bif decide (Q = 1) then (b6W6PositiveCapacityCount z : ℤ) else
      bif decide (Q = 2) then (b6W6TwoCapacityWeight z : ℤ) else
        bif decide (Q = 3) then (b6W6ThreeCapacityWeight z : ℤ) else
          bif decide (Q = 4) then (b6W6FourCapacityWeight z : ℤ) else
            bif decide (Q = 5) then (b6W6FiveCapacityWeight z : ℤ) else
              let cap := b6W6CapacitySum z
              bif decide (Q = cap) then 1 else
                bif decide (Q + 1 = cap) then (b6W6PositiveCapacityCount z : ℤ) else
                  bif decide (Q + 2 = cap) then (b6W6TwoCapacityWeight z : ℤ) else
                    bif decide (Q + 3 = cap) then (b6W6ThreeCapacityWeight z : ℤ) else
                      bif decide (Q + 4 = cap) then (b6W6FourCapacityWeight z : ℤ) else
                        bif decide (Q + 5 = cap) then (b6W6FiveCapacityWeight z : ℤ) else
                          b6W6DominantFastWeight z Q
#print axioms Paper7MomentCounts.b6W6LowQFiveDominantFastWeight

theorem b6W6LowQFiveDominantFastWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6LowQFiveDominantFastWeight z Q = b6W6ProductFastWeight z Q := by
  unfold b6W6LowQFiveDominantFastWeight
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
          by_cases h4 : Q = 4
          · rw [decide_eq_true h4, Bool.cond_true, h4]
            exact (b6W6ProductFastWeight_four_low z).symm
          · rw [decide_eq_false h4, Bool.cond_false]
            by_cases h5 : Q = 5
            · rw [decide_eq_true h5, Bool.cond_true, h5]
              exact (b6W6ProductFastWeight_five_low z).symm
            · rw [decide_eq_false h5, Bool.cond_false]
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
                      by_cases hnext4 : Q + 4 = b6W6CapacitySum z
                      · rw [decide_eq_true hnext4, Bool.cond_true]
                        exact ((b6W6ProductFastWeight_complement_at z Q 4 hnext4).trans
                          (b6W6ProductFastWeight_four_low z)).symm
                      · rw [decide_eq_false hnext4, Bool.cond_false]
                        by_cases hnext5 : Q + 5 = b6W6CapacitySum z
                        · rw [decide_eq_true hnext5, Bool.cond_true]
                          exact ((b6W6ProductFastWeight_complement_at z Q 5 hnext5).trans
                            (b6W6ProductFastWeight_five_low z)).symm
                        · rw [decide_eq_false hnext5, Bool.cond_false]
                          exact b6W6DominantFastWeight_eq z Q
#print axioms Paper7MomentCounts.b6W6LowQFiveDominantFastWeight_eq

end Paper7MomentCounts
