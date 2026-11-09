import Research.TaskE.Challenge
set_option autoImplicit false
noncomputable section
namespace CodexPaper1.TaskE.Challenge
open BackfillPaper1.Challenge Finset

/-- All row masses, without evaluating a geometric sum in the final proof. -/
def RowAbsMass : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ p : ℝ, 3 ≤ p → ∀ i ≤ a,
    rowAbsSum a p i = if i = a then p ^ a else 2 * p ^ (a - 1) * (p - 1)

/-- Exact nonterminal penalty; finite index reversal is part of the conclusion. -/
def NonlastPenaltyIdentity : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ p : ℝ, 3 ≤ p → ∀ c : ℕ → ℝ, IsSignVec a c →
    (∑ i ∈ range a, max 0 (rowAbsSum a p i - 2 * |tMulVec a p c i|)) =
      2 * p ^ (a - 1) * (p - 1) * ∑ j ∈ NA a c, |z p a c (j : ℤ)|

/-- The nonterminal penalty is controlled by twice the genuine norm deficit. -/
def NonlastPenaltyBound : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ p : ℝ, 3 ≤ p → ∀ c : ℕ → ℝ, IsSignVec a c →
    (∑ i ∈ range a, max 0 (rowAbsSum a p i - 2 * |tMulVec a p c i|)) ≤
      2 * DeltaC a p c

/-- Strictness when p≥5 and the vector is not alternating. -/
def NonlastPenaltyStrict : Prop :=
  ∀ a : ℕ, 1 ≤ a → ∀ p : ℝ, 5 ≤ p → ∀ c : ℕ → ℝ,
    IsSignVec a c → ¬ IsPmAlt a c →
    (∑ i ∈ range a, max 0 (rowAbsSum a p i - 2 * |tMulVec a p c i|)) <
      2 * DeltaC a p c

/-- Stronger all-real-parameter S milestone; alone it is no graph theorem. -/
def ConditionsSUniform : Prop :=
  ∀ a : ℕ, 1 ≤ a →
    (∀ p : ℝ, 5 ≤ p → CondS a p 2) ∧
    (∀ p : ℝ, 3 ≤ p → CondS a p 4)

end CodexPaper1.TaskE.Challenge
