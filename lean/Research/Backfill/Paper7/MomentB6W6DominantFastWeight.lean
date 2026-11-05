import Research.Backfill.Paper7.MomentB6W6ProductWeight
import Research.Backfill.Paper7.MomentB6DominantWeights

/-! SOURCE ONLY. Exact dominant-coordinate shortcuts at the two sorted maxima.
Both branch premises are tested internally. The full original product weight
is the fallback, so no original-graph hypothesis or domain is restricted.
Evaluation branches use explicit five-coordinate additions and products only;
finite subtype products occur in the proofs, never in the new evaluator. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

theorem b6W6ProductFastWeight_eq_boundedQDP (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6ProductFastWeight z Q = (Paper7MomentDP.boundedQDP 6 z Q : ℤ) := by
  rw [b6W6ProductFastWeight_eq, b6W6FastWeight_eq, b6W6EvalWeight_eq,
    labelledSixQWeight_eq_actual_card, Paper7MomentDP.boundedQDP_eq_fibre_card]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_eq_boundedQDP

theorem b6W6ProductFastWeight_dominant (z : Fin 6 → ℕ) (i : Fin 6) (Q : ℕ)
    (hQ : Q ≤ z i) (hrest : (∑ k ∈ Finset.univ.erase i, z k) ≤ Q) :
    b6W6ProductFastWeight z Q =
      ((∏ k : {k : Fin 6 // k ≠ i}, (z k.val+1) : ℕ) : ℤ) := by
  rw [b6W6ProductFastWeight_eq_boundedQDP,
    boundedQDP_dominant_product 6 z i Q hQ hrest]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_dominant

theorem b6W6RestSum_zero (z : Fin 6 → ℕ) :
    (∑ k ∈ Finset.univ.erase (0 : Fin 6), z k) = z 1+z 2+z 3+z 4+z 5 := by
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ (0 : Fin 6))
  rw [← b6W6CapacitySum_eq] at he
  dsimp only [b6W6CapacitySum] at he
  omega
#print axioms Paper7MomentCounts.b6W6RestSum_zero

theorem b6W6RestSum_three (z : Fin 6 → ℕ) :
    (∑ k ∈ Finset.univ.erase (3 : Fin 6), z k) = z 0+z 1+z 2+z 4+z 5 := by
  have he := Finset.sum_erase_add Finset.univ z (Finset.mem_univ (3 : Fin 6))
  rw [← b6W6CapacitySum_eq] at he
  dsimp only [b6W6CapacitySum] at he
  omega
#print axioms Paper7MomentCounts.b6W6RestSum_three

theorem b6W6RestProduct_zero (z : Fin 6 → ℕ) :
    (∏ k : {k : Fin 6 // k ≠ (0 : Fin 6)}, (z k.val+1)) =
      (z 1+1)*(z 2+1)*(z 3+1)*(z 4+1)*(z 5+1) := by
  classical
  calc
    _ = ∏ k ∈ Finset.univ.erase (0 : Fin 6), (z k+1) := by
      exact (Finset.prod_subtype (p := fun k : Fin 6 => k ≠ 0)
        (Finset.univ.erase (0 : Fin 6)) (by intro k; simp)
        (fun k : Fin 6 => z k+1)).symm
    _ = _ := by
      have he : Finset.univ.erase (0 : Fin 6) = {1,2,3,4,5} := by decide
      rw [he]
      norm_num [Finset.prod_insert, Finset.prod_singleton, mul_assoc]
#print axioms Paper7MomentCounts.b6W6RestProduct_zero

theorem b6W6RestProduct_three (z : Fin 6 → ℕ) :
    (∏ k : {k : Fin 6 // k ≠ (3 : Fin 6)}, (z k.val+1)) =
      (z 0+1)*(z 1+1)*(z 2+1)*(z 4+1)*(z 5+1) := by
  classical
  calc
    _ = ∏ k ∈ Finset.univ.erase (3 : Fin 6), (z k+1) := by
      exact (Finset.prod_subtype (p := fun k : Fin 6 => k ≠ 3)
        (Finset.univ.erase (3 : Fin 6)) (by intro k; simp)
        (fun k : Fin 6 => z k+1)).symm
    _ = _ := by
      have he : Finset.univ.erase (3 : Fin 6) = {0,1,2,4,5} := by decide
      rw [he]
      norm_num [Finset.prod_insert, Finset.prod_singleton, mul_assoc]
#print axioms Paper7MomentCounts.b6W6RestProduct_three

theorem b6W6ProductFastWeight_dominant_zero (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ z 0) (hrest : z 1+z 2+z 3+z 4+z 5 ≤ Q) :
    b6W6ProductFastWeight z Q =
      (((z 1+1)*(z 2+1)*(z 3+1)*(z 4+1)*(z 5+1) : ℕ) : ℤ) := by
  have hr : (∑ k ∈ Finset.univ.erase (0 : Fin 6), z k) ≤ Q := by
    rw [b6W6RestSum_zero]
    exact hrest
  rw [b6W6ProductFastWeight_dominant z 0 Q hQ hr, b6W6RestProduct_zero]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_dominant_zero

theorem b6W6ProductFastWeight_dominant_three (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : Q ≤ z 3) (hrest : z 0+z 1+z 2+z 4+z 5 ≤ Q) :
    b6W6ProductFastWeight z Q =
      (((z 0+1)*(z 1+1)*(z 2+1)*(z 4+1)*(z 5+1) : ℕ) : ℤ) := by
  have hr : (∑ k ∈ Finset.univ.erase (3 : Fin 6), z k) ≤ Q := by
    rw [b6W6RestSum_three]
    exact hrest
  rw [b6W6ProductFastWeight_dominant z 3 Q hQ hr, b6W6RestProduct_three]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_dominant_three

def b6W6DominantFastWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  bif decide (Q ≤ z 0 ∧ z 1+z 2+z 3+z 4+z 5 ≤ Q) then
    (((z 1+1)*(z 2+1)*(z 3+1)*(z 4+1)*(z 5+1) : ℕ) : ℤ)
  else bif decide (Q ≤ z 3 ∧ z 0+z 1+z 2+z 4+z 5 ≤ Q) then
    (((z 0+1)*(z 1+1)*(z 2+1)*(z 4+1)*(z 5+1) : ℕ) : ℤ)
  else b6W6ProductFastWeight z Q
#print axioms Paper7MomentCounts.b6W6DominantFastWeight

theorem b6W6DominantFastWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6DominantFastWeight z Q = b6W6ProductFastWeight z Q := by
  unfold b6W6DominantFastWeight
  by_cases h0 : Q ≤ z 0 ∧ z 1+z 2+z 3+z 4+z 5 ≤ Q
  · rw [decide_eq_true h0, Bool.cond_true]
    exact (b6W6ProductFastWeight_dominant_zero z Q h0.1 h0.2).symm
  · rw [decide_eq_false h0, Bool.cond_false]
    by_cases h3 : Q ≤ z 3 ∧ z 0+z 1+z 2+z 4+z 5 ≤ Q
    · rw [decide_eq_true h3, Bool.cond_true]
      exact (b6W6ProductFastWeight_dominant_three z Q h3.1 h3.2).symm
    · rw [decide_eq_false h3, Bool.cond_false]
#print axioms Paper7MomentCounts.b6W6DominantFastWeight_eq

end Paper7MomentCounts
