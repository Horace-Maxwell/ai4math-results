import Research.Backfill.Paper1.Challenge

/-! Task E candidate 01. Definitions only; no theorem has been proved.
The imported Challenge is the immutable Task D formal-batch02 source.
-/
set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.Challenge
open BackfillPaper1.Challenge

/-- Full remaining prime-three same-parity result, both exponent orientations. -/
def SameParityThree : Prop :=
  ∀ p q a b : ℕ, DistinctOddPrimes p q → (p = 3 ∨ q = 3) →
    3 ≤ min a b → Even (a + b) →
    MaxEnergy (p ^ a * q ^ b)
      ((((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2 -
        deltaK a p * deltaK b q)
      {oddSet p q a b, (evenSet p q a b).erase (p ^ a * q ^ b)}

/-- Dormant fallback; the larger exponent is still unbounded. -/
def SameParityThreeMinEight : Prop :=
  ∀ p q a b : ℕ, DistinctOddPrimes p q → (p = 3 ∨ q = 3) →
    3 ≤ min a b → min a b ≤ 8 → Even (a + b) →
    MaxEnergy (p ^ a * q ^ b)
      ((((p ^ a * q ^ b : ℕ) : ℝ) + dClosed a p * dClosed b q) / 2 -
        deltaK a p * deltaK b q)
      {oddSet p q a b, (evenSet p q a b).erase (p ^ a * q ^ b)}

/-- Stronger real-parameter route milestone, not an extra target hypothesis. -/
def UniformConditionsBothRegions : Prop :=
  ∀ a : ℕ, 3 ≤ a →
    (∀ p q : ℝ, Region1 p q → CondAll a p q 2) ∧
    (∀ p q : ℝ, Region2 p q → CondAll a p q 4)

end CodexPaper1.TaskE.Challenge
