import Research.Backfill.Paper7.RootCoefficientRecurrence

/-! Literal data copied from Root's candidate run, not a completeness theorem.
The small identities below are ordinary kernel obligations. -/
set_option autoImplicit false
namespace Paper7CycleThreeCertificate

def candidateRows : List (List ℤ) :=
  [[-1, -1, -1, -1, 0, 1, 1, 2], [-1, -1, -1, 0, 0, 0, 1, 2]]
#print axioms Paper7CycleThreeCertificate.candidateRows

theorem candidateRows_cases (a : List ℤ) (ha : a ∈ candidateRows) :
    a = [-1, -1, -1, -1, 0, 1, 1, 2] ∨ a = [-1, -1, -1, 0, 0, 0, 1, 2] := by
  simpa only [candidateRows, List.mem_cons, List.not_mem_nil, or_false] using ha
#print axioms Paper7CycleThreeCertificate.candidateRows_cases

theorem candidateRows_domain (a : List ℤ) (ha : a ∈ candidateRows) :
    a.length = 8 ∧ a.Pairwise (· ≤ ·) ∧ (∀ z ∈ a, -9 ≤ z ∧ z ≤ 9) ∧ a.sum = 0 := by
  rcases candidateRows_cases a ha with rfl | rfl <;> decide
#print axioms Paper7CycleThreeCertificate.candidateRows_domain

theorem candidateRows_key_coefficients (a : List ℤ) (ha : a ∈ candidateRows) :
    (rootCoefficient a 3 = 2 ∧ rootCoefficient a 6 = -4) ∨
    (rootCoefficient a 3 = 4 ∧ rootCoefficient a 6 = -5) := by
  rcases candidateRows_cases a ha with rfl | rfl
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
#print axioms Paper7CycleThreeCertificate.candidateRows_key_coefficients

theorem candidateRows_pattern (a : List ℤ) (ha : a ∈ candidateRows) : rootPattern a := by
  rcases candidateRows_cases a ha with rfl | rfl <;> decide
#print axioms Paper7CycleThreeCertificate.candidateRows_pattern

end Paper7CycleThreeCertificate
