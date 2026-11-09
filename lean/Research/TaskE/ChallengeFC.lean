import Research.TaskE.ChallengeS

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.Challenge
open Finset BackfillPaper1.Challenge

/-- Quantitative potential bound, derived from the original matrix and path. -/
def PotentialLowerThree : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ q μ : ℝ, 5 ≤ q → 0 ≤ μ → μ ≤ 1 →
    ∀ c ζ : ℕ → ℝ, IsSignVec a c → (∀ i ≤ a, |ζ i| ≤ 1) →
      (q - 1) * DeltaC a 3 c ≤ psi a 3 q μ c ζ

/-- Uniform nonalternating-column deficit; both exponent and sign vector unbounded. -/
def DeficitLowerThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ c : ℕ → ℝ, IsSignVec a c → ¬ IsPmAlt a c →
    (8 / 27 : ℝ) * 3 ^ a ≤ DeltaC a 3 c

/-- The original C2 inequality, without new assumptions on the graph. -/
def FiveChainThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ g : ℕ → ℝ,
    IsSignVec a g → ¬ IsPmAlt a g → ∀ y : ℝ,
    (if Even a then mu q 0 ≤ y ∧ y ≤ muInf q else muInf q ≤ y ∧ y ≤ mu q 1) →
      (∑ n ∈ range 5, (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g) >
        q * etaMap q 5 y * (2 * deltaK a 3 - DeltaC a 3 g)

/-- The original C3 inequalities for all nonalternating columns. -/
def TerminalRatiosThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ g : ℕ → ℝ,
    IsSignVec a g → ¬ IsPmAlt a g →
    (if Even a then DeltaC a 3 g * (Dhat1 q / mu q 1 + 2) > 2 * deltaK a 3
     else DeltaC a 3 g * Dhat1 q / mu q 0 > 2 * deltaK a 3 ∧
       DeltaC a 3 g * (Dhat2 q / muInf q + 2) > 2 * deltaK a 3)

/-- Only the high-deficit branch of F; this does not assert CondF. -/
def HighDeficitFThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ c : ℕ → ℝ,
    IsSignVec a c → 2 * deltaK a 3 ≤ DeltaC a 3 c →
    ∀ t : ℝ × ℝ × ℝ, FamF a q t →
      psi a 3 q t.1 c (fun i => t.2.1 * sAlt i) > 2 * q * deltaK a 3 * t.2.2

end CodexPaper1.TaskE.Challenge
