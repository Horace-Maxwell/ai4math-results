import Research.Backfill.Paper7.RootFactorizationCoverage

/-! The actual three residual families satisfy the exact coefficient filter.
The only budget is the original order at most49; zero parameters remain allowed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThreeCertificate
open Polynomial Paper7CycleThree

theorem oneQ_certificate_pattern (p : Fin 3 → ℕ) (q : ℕ)
    (hn : 3 + p 0 + p 1 + p 2 + 2*q ≤ 49) :
    coefficientPattern (triangleResidualOneQ p q) := by
  obtain ⟨h7, h6, h5, _h4, h3, h1, h0⟩ := oneQ_coefficient_data p q
  have hnZ : (3 : ℤ) + p 0 + p 1 + p 2 + 2*q ≤ 49 := by exact_mod_cast hn
  refine ⟨h7, h5, ?_, Or.inl ⟨h3, h1, ?_, ?_⟩⟩
  · rw [h0]
    positivity
  · rw [h6]
    omega
  · rw [h6]
    omega
#print axioms Paper7CycleThreeCertificate.oneQ_certificate_pattern

theorem offZero_certificate_pattern (b c u v : ℕ)
    (hn : 3 + b + c + 2*(u+v) ≤ 49) :
    coefficientPattern (triangleResidualOffZero b c u v) := by
  obtain ⟨h7, h6, h5, h3, h1, h0⟩ := offZero_coefficient_data b c u v
  have hnZ : (3 : ℤ) + b + c + 2*((u : ℤ)+v) ≤ 49 := by exact_mod_cast hn
  refine ⟨h7, h5, ?_, Or.inr ⟨h3, h1, ?_, ?_⟩⟩
  · rw [h0]
    positivity
  · rw [h6]
    omega
  · rw [h6]
    omega
#print axioms Paper7CycleThreeCertificate.offZero_certificate_pattern

theorem atZero_certificate_pattern (a b u v : ℕ)
    (hn : 3 + a + b + 2*(u+v) ≤ 49) :
    coefficientPattern (triangleResidualAtZero a b u v) := by
  obtain ⟨h7, h6, h5, _h4, h3, h1, h0⟩ := atZero_coefficient_data a b u v
  have hnZ : (3 : ℤ) + a + b + 2*((u : ℤ)+v) ≤ 49 := by exact_mod_cast hn
  refine ⟨h7, h5, ?_, Or.inr ⟨h3, h1, ?_, ?_⟩⟩
  · rw [h0]
    positivity
  · rw [h6]
    omega
  · rw [h6]
    omega
#print axioms Paper7CycleThreeCertificate.atZero_certificate_pattern

end Paper7CycleThreeCertificate
