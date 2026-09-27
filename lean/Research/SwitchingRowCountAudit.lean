import Research.SwitchingRowCount

/-! Audit file for `Research.SwitchingRowCount`: prints the final statements and checks the
statement on a concrete instance (K = ℚ, w = 1/3, θ = 2, u = 1). -/

set_option autoImplicit false

#check @SwitchingRow.card_bad_le_two
#check @SwitchingRow.card_bad_le_one_of_ne
#check @SwitchingRow.affine_injective

-- concrete instance: u + Λ/3 ∈ {2, -2} has the two integer solutions Λ = 3 and Λ = -9
example : Set.ncard {Λ : ℤ | (1 : ℚ) + (Λ : ℚ) * (1 / 3) = 2 ∨ (1 : ℚ) + (Λ : ℚ) * (1 / 3) = -2} ≤ 2 :=
  SwitchingRow.card_bad_le_two (1 : ℚ) (1 / 3) 2 (by norm_num)

#print axioms SwitchingRow.card_bad_le_two
#print axioms SwitchingRow.card_bad_le_one_of_ne
