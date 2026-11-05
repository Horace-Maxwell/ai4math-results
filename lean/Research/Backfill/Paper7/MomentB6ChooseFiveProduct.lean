import Research.Backfill.Paper7.MomentB6W6BinaryWeight

/- Exact quotient identities for all natural Q, including Q = 0.
   The successful original weight definition is imported unchanged. -/
set_option autoImplicit false

namespace Paper7MomentCounts

theorem b6ChooseFive_eq_nat_product_div (Q : ℕ) :
    (Q + 5).choose 5 =
      ((Q + 1) * (Q + 2) * (Q + 3) * (Q + 4) * (Q + 5)) / 120 := by
  have hprod : (Q + 1).ascFactorial 5 =
      (Q + 1) * (Q + 2) * (Q + 3) * (Q + 4) * (Q + 5) := by
    simp only [Nat.ascFactorial]
    ring
  rw [Nat.choose_eq_asc_factorial_div_factorial Q 5, hprod]
  norm_num [Nat.factorial]

#print axioms Paper7MomentCounts.b6ChooseFive_eq_nat_product_div

theorem b6W6BinaryBinomial_eq_int_product_div (Q : ℕ) :
    b6W6BinaryBinomial Q =
      (((Q : ℤ) + 1) * ((Q : ℤ) + 2) * ((Q : ℤ) + 3) *
        ((Q : ℤ) + 4) * ((Q : ℤ) + 5)) / 120 := by
  have h := congrArg (fun n : ℕ => (n : ℤ))
    (b6ChooseFive_eq_nat_product_div Q)
  simpa only [b6W6BinaryBinomial, Int.natCast_ediv, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using h

#print axioms Paper7MomentCounts.b6W6BinaryBinomial_eq_int_product_div

end Paper7MomentCounts
