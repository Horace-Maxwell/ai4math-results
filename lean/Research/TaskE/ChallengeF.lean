import Research.TaskE.ChallengeFC

set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.Challenge
open Finset BackfillPaper1.Challenge

/-- The real domain contains every possible odd prime other than3. -/
def FPrimeDomain (q : ℝ) : Prop := q = 5 ∨ q = 7 ∨ 8 ≤ q

/-- A uniform scalar estimate for the full frozen F family, with both parities. -/
def FScalarPrimeDomain : Prop :=
  ∀ a : ℕ, ∀ q : ℝ, FPrimeDomain q → ∀ t : ℝ × ℝ × ℝ, FamF a q t →
    (41 / 27 : ℝ) * q * t.2.2 <
      2 * (q - 1) - (5 / 9 : ℝ) * (q - 1) * (1 - t.1) - (28 / 9 : ℝ) * t.1 * t.2.1

/-- Uniform normalization of the original delta; no new graph premise. -/
def DeltaRatioThree : Prop :=
  ∀ a : ℕ, 3 ≤ a → 2 * deltaK a 3 ≤
    (41 / 27 : ℝ) * (3 ^ (a - 1) * (3 - 1))

/-- Full F (not a conditional or a bounded-exponent substitute). -/
def ConditionsFThreePrimeDomain : Prop :=
  ∀ a : ℕ, 3 ≤ a → ∀ q : ℝ, FPrimeDomain q → CondF a 3 q

end CodexPaper1.TaskE.Challenge
