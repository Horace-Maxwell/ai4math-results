import Research.TaskE.Challenge
set_option autoImplicit false
namespace CodexPaper1.TaskE.StatementTests
open BackfillPaper1.Challenge

theorem prime_three_left : DistinctOddPrimes 3 5 := by unfold DistinctOddPrimes; decide
theorem prime_three_right : DistinctOddPrimes 5 3 := by unfold DistinctOddPrimes; decide
theorem unbounded_exponent_sample : 3 ≤ min 3 101 ∧ Even (3 + 101) := by decide
theorem fallback_interior : 3 ≤ min 8 100 ∧ min 8 100 ≤ 8 ∧ Even (8 + 100) := by decide
theorem fallback_rejects_nine : ¬ (3 ≤ min 9 11 ∧ min 9 11 ≤ 8) := by decide
theorem rejects_distinctness_failure : ¬ DistinctOddPrimes 3 3 := by unfold DistinctOddPrimes; decide
theorem rejects_wrong_parity : ¬ Even (3 + 4) := by decide
end CodexPaper1.TaskE.StatementTests
#print CodexPaper1.TaskE.Challenge.SameParityThree
#print CodexPaper1.TaskE.Challenge.SameParityThreeMinEight
#print CodexPaper1.TaskE.Challenge.UniformConditionsBothRegions
#print BackfillPaper1.Challenge.MaxEnergy
#print BackfillPaper1.Challenge.energy
#print BackfillPaper1.Challenge.graphEnergy
#print axioms CodexPaper1.TaskE.Challenge.SameParityThree
#print axioms CodexPaper1.TaskE.Challenge.SameParityThreeMinEight
#print axioms CodexPaper1.TaskE.Challenge.UniformConditionsBothRegions
#print axioms CodexPaper1.TaskE.StatementTests.prime_three_left
#print axioms CodexPaper1.TaskE.StatementTests.prime_three_right
#print axioms CodexPaper1.TaskE.StatementTests.unbounded_exponent_sample
#print axioms CodexPaper1.TaskE.StatementTests.fallback_interior
#print axioms CodexPaper1.TaskE.StatementTests.fallback_rejects_nine
#print axioms CodexPaper1.TaskE.StatementTests.rejects_distinctness_failure
#print axioms CodexPaper1.TaskE.StatementTests.rejects_wrong_parity
