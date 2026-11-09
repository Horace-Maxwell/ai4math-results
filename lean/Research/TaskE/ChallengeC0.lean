import Research.TaskE.ChallengeC1

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.Challenge
open Finset BackfillPaper1.Challenge

/-- Tail accounting for the original path; no graph or Perron premise. -/
def ZeroTailBudgetThree : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ g : ℕ → ℝ, IsSignVec a g → ∀ j : ℕ, j < a →
    2 * deltaK a 3 ≤
      2 * (3 : ℝ) ^ a * (mu 3 (j : ℤ) * |z 3 a g (j : ℤ)| +
        2 * ∑ l ∈ (NA a g).filter (fun l => j < l), mu 3 (l : ℤ) * |z 3 a g (l : ℤ)|) +
      2 * (3 ^ (a - 1) * (3 - 1)) * (1 - |z 3 a g (j : ℤ)|)

/-- A terminal repetition under the low-deficit branch forces the old excluded gPlus. -/
def TerminalLowThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ g : ℕ → ℝ, IsSignVec a g → g a = -1 →
    ¬ (∀ i ≤ a, g i = gPlus a i) → DeltaC a 3 g ≤ 2 * deltaK a 3 →
    g (a - 1) ≠ g a

/-- The exact remaining k=0 branch of original C1, including both next-column parity directions. -/
def C1ZeroThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ g : ℕ → ℝ,
    IsSignVec a g → g a = -1 →
    ¬ (∀ i ≤ a, g i = -((-1) ^ a * sAlt i)) →
    ¬ (∀ i ≤ a, g i = gPlus a i) → DeltaC a 3 g ≤ 2 * deltaK a 3 →
    ∀ y : ℝ, Ik a 0 q y → ∀ c : ℕ → ℝ, IsSignVec a c →
    ¬ (∀ i ≤ a, c i = -g i) →
      psi a 3 q y c g > q * etaMap q 1 y * (2 * deltaK a 3 - DeltaC a 3 g)

end CodexPaper1.TaskE.Challenge
