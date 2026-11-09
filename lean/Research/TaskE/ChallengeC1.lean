import Research.TaskE.ChallengeFC

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.Challenge
open Finset BackfillPaper1.Challenge

/-- C1 after at least two preceding columns; the stronger unit interval is intentional. -/
def C1LongThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ g : ℕ → ℝ,
    IsSignVec a g → ¬ IsPmAlt a g → ∀ k : ℕ, 2 ≤ k → ∀ y : ℝ,
    0 ≤ y → y ≤ 1 → ∀ c : ℕ → ℝ, IsSignVec a c →
      (∑ n ∈ Icc 1 k, (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g) +
        psi a 3 q y c (fun i => (-1) ^ k * mu q ((k : ℤ) - 1) * g i) >
      q * etaMap q (k + 1) y * (2 * deltaK a 3 - DeltaC a 3 g)

/-- C1 at k=1 when the next sign column is nonalternating. -/
def C1OneNonaltThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ g : ℕ → ℝ,
    IsSignVec a g → ¬ IsPmAlt a g → ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
    ∀ c : ℕ → ℝ, IsSignVec a c → ¬ IsPmAlt a c →
      (q - 1) * (1 + etaMap q 1 y) * DeltaC a 3 g +
        psi a 3 q y c (fun i => -mu q 0 * g i) >
      q * etaMap q 2 y * (2 * deltaK a 3 - DeltaC a 3 g)

/-- C1 for a next column with high deficit, at every chain length. -/
def C1HighThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, 5 ≤ q → ∀ g : ℕ → ℝ,
    IsSignVec a g → ¬ IsPmAlt a g → ∀ k : ℕ, ∀ y : ℝ,
    0 ≤ y → y ≤ 1 → ∀ c : ℕ → ℝ, IsSignVec a c →
    2 * deltaK a 3 ≤ DeltaC a 3 c →
      (∑ n ∈ Icc 1 k, (q - 1) * (1 + etaMap q n y) * DeltaC a 3 g) +
        psi a 3 q y c (fun i => (-1) ^ k * mu q ((k : ℤ) - 1) * g i) >
      q * etaMap q (k + 1) y * (2 * deltaK a 3 - DeltaC a 3 g)

end CodexPaper1.TaskE.Challenge
