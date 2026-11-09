import Research.TaskE.ChallengeC1

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.Challenge
open Finset BackfillPaper1.Challenge

/-- The remaining k=1 C1 branch with an alternating next column, for the stronger unit interval. -/
def C1OneAltThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ g : ℕ → ℝ,
    IsSignVec a g → ¬ IsPmAlt a g → ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
    ∀ c : ℕ → ℝ, IsSignVec a c → IsPmAlt a c →
      (q - 1) * (1 + etaMap q 1 y) * DeltaC a 3 g +
        psi a 3 q y c (fun i => -mu q 0 * g i) >
      q * etaMap q 2 y * (2 * deltaK a 3 - DeltaC a 3 g)

end CodexPaper1.TaskE.Challenge
