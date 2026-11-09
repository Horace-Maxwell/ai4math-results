import Research.TaskE.Main
import Research.TaskE.StatementTests
import Research.Backfill.Paper1.FinalContractAudit

set_option autoImplicit false
noncomputable section
open BackfillPaper1.Challenge

example : CodexPaper1.TaskE.Challenge.SameParityThree := CodexPaper1.TaskE.check_SameParityThree
example : CodexPaper1.TaskE.Challenge.SameParityThreeMinEight := CodexPaper1.TaskE.check_SameParityThreeMinEight
example (a : ℕ) (ha : 3 ≤ a) (q : ℝ) (hq : 5 ≤ q) : CondC a 3 q := CodexPaper1.TaskE.FCProof.full_C ha hq
example : CodexPaper1.TaskE.Challenge.ConditionsFThreePrimeDomain := CodexPaper1.TaskE.FCProof.full_F
example : CodexPaper1.TaskE.Challenge.ConditionsSUniform := CodexPaper1.TaskE.check_ConditionsSUniform

example : MaxEnergy (3 ^ 3 * 5 ^ 101)
    ((((3 ^ 3 * 5 ^ 101 : ℕ) : ℝ) + dClosed 3 3 * dClosed 101 5) / 2 - deltaK 3 3 * deltaK 101 5)
    {oddSet 3 5 3 101, (evenSet 3 5 3 101).erase (3 ^ 3 * 5 ^ 101)} :=
  CodexPaper1.TaskE.check_SameParityThree 3 5 3 101 (by unfold DistinctOddPrimes; decide)
    (Or.inl rfl) (by decide) (by decide)

example : MaxEnergy (5 ^ 101 * 3 ^ 3)
    ((((5 ^ 101 * 3 ^ 3 : ℕ) : ℝ) + dClosed 101 5 * dClosed 3 3) / 2 - deltaK 101 5 * deltaK 3 3)
    {oddSet 5 3 101 3, (evenSet 5 3 101 3).erase (5 ^ 101 * 3 ^ 3)} :=
  CodexPaper1.TaskE.check_SameParityThree 5 3 101 3 (by unfold DistinctOddPrimes; decide)
    (Or.inr rfl) (by decide) (by decide)

#print axioms CodexPaper1.TaskE.check_SameParityThree
#print axioms CodexPaper1.TaskE.check_SameParityThreeMinEight
#print axioms CodexPaper1.TaskE.FCProof.full_C
#print axioms CodexPaper1.TaskE.FCProof.full_F
#print axioms CodexPaper1.TaskE.FCProof.prime_conditions
#print axioms CodexPaper1.TaskE.FCProof.prime_sign_conclusion
#print axioms CodexPaper1.TaskE.GraphTransport.graph_result
