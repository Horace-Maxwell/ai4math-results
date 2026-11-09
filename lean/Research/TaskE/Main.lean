import Research.TaskE.PrimeConditions
import Research.TaskE.GraphTransport

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE
open BackfillPaper1

/-- Full original graph statement, both prime orientations and unbounded exponents. -/
theorem check_SameParityThree : Challenge.SameParityThree := by
  intro p q a b hpq hthree hmin hab
  have ha : 3 ≤ a := le_trans hmin (Nat.min_le_left a b)
  have hb : 3 ≤ b := le_trans hmin (Nat.min_le_right a b)
  rcases hthree with rfl | rfl
  · exact GraphTransport.graph_result hpq (by omega) (by omega) hab
      (FCProof.prime_sign_conclusion ha hpq.2.1 hpq.2.2.2.2 (Ne.symm hpq.2.2.1))
  · have hs := FCProof.prime_sign_conclusion hb hpq.1 hpq.2.2.2.1 hpq.2.2.1
    have hh := GraphTransport.graph_result (CodexPaper1.EqualParityMax.distinctOddPrimes_swap hpq)
      (by omega : 1 ≤ b) (by omega : 1 ≤ a) (by simpa only [add_comm] using hab) hs
    rw [CodexPaper1.EqualParityMax.oddSet_swap, CodexPaper1.EqualParityMax.evenSet_swap] at hh
    simpa only [mul_comm] using hh

/-- A direct consequence; the certificate fallback is not activated. -/
theorem check_SameParityThreeMinEight : Challenge.SameParityThreeMinEight := by
  intro p q a b hpq hthree hmin _hupper hpar
  exact check_SameParityThree p q a b hpq hthree hmin hpar

end CodexPaper1.TaskE
#print axioms CodexPaper1.TaskE.check_SameParityThree
#print axioms CodexPaper1.TaskE.check_SameParityThreeMinEight
