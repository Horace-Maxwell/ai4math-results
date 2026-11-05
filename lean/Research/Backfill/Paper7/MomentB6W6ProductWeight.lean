import Research.Backfill.Paper7.MomentB6ChooseFiveProduct

/- Ordinary product-quotient weights with exactly the original six differences
   and the original Q-zero / above-capacity branches. No value is evaluated. -/
set_option autoImplicit false

namespace Paper7MomentCounts

def b6W6ProductBinomial (Q : ℕ) : ℤ :=
  (((Q : ℤ) + 1) * ((Q : ℤ) + 2) * ((Q : ℤ) + 3) *
    ((Q : ℤ) + 4) * ((Q : ℤ) + 5)) / 120
#print axioms Paper7MomentCounts.b6W6ProductBinomial

theorem b6W6ProductBinomial_eq (Q : ℕ) :
    b6W6ProductBinomial Q = b6W6BinaryBinomial Q := by
  exact (b6W6BinaryBinomial_eq_int_product_div Q).symm
#print axioms Paper7MomentCounts.b6W6ProductBinomial_eq

def b6W6ProductWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  b6W6BinaryDelta (z 0+1)
    (b6W6BinaryDelta (z 1+1)
      (b6W6BinaryDelta (z 2+1)
        (b6W6BinaryDelta (z 3+1)
          (b6W6BinaryDelta (z 4+1)
            (b6W6BinaryDelta (z 5+1) b6W6ProductBinomial))))) Q
#print axioms Paper7MomentCounts.b6W6ProductWeight

theorem b6W6ProductWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6ProductWeight z Q = b6W6BinaryWeight z Q := by
  have h : b6W6ProductBinomial = b6W6BinaryBinomial := by
    funext q
    exact b6W6ProductBinomial_eq q
  unfold b6W6ProductWeight b6W6BinaryWeight
  rw [h]
#print axioms Paper7MomentCounts.b6W6ProductWeight_eq

def b6W6ProductFastWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  bif decide (Q=0) then 1 else
    bif decide (b6W6CapacitySum z < Q) then 0 else b6W6ProductWeight z Q
#print axioms Paper7MomentCounts.b6W6ProductFastWeight

theorem b6W6ProductFastWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6ProductFastWeight z Q = b6W6FastWeight z Q := by
  unfold b6W6ProductFastWeight b6W6FastWeight
  rw [b6W6ProductWeight_eq]
#print axioms Paper7MomentCounts.b6W6ProductFastWeight_eq

end Paper7MomentCounts
