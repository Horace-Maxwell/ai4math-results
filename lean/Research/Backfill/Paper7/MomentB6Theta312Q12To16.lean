import Research.Backfill.Paper7.MomentB6ScalarArithmeticPruning

/-! Uncompiled complete original theta312 Q interval [12,16), catalogue (25,312).
This is exactly the corresponding interval of b6ArithmeticPrunedTotal's expanded
outer sum; every original Z/A/B/t range and both outer guards remain. A future
Root-supervised run must generate and kernel-check the full segment value.
No number is prefilled. Binding the pruning import requires actual success;
all successful theta264 sources stay outside this import graph. Limits unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6Theta312Q12To16Expr : ℤ :=
  ∑ Q ∈ Finset.Ico 12 16,
    ∑ Z ∈ b6EvalZRange (25,312) Q,
      bif b6EvalCatalogAccept (25,312) Z Q then
        ∑ A ∈ Finset.range (Z+1),
          ∑ B ∈ b6EvalBRange Z (b6EvalResidual (25,312) Z Q) A,
            bif (b6EvalTripleGuard A B &&
                b6EvalTripleGuard (Z-A) (b6EvalResidual (25,312) Z Q-B)) then
              ∑ t ∈ b6EvalQSplitRange Z A Q,
                b6ArithmeticPrunedKernel A B t *
                  b6ArithmeticPrunedKernel (Z-A) (b6EvalResidual (25,312) Z Q-B) (Q-t)
            else 0
      else 0
#print axioms Paper7MomentCounts.b6Theta312Q12To16Expr

def b6Theta312Q12To16Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6Theta312Q12To16Expr)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained; no certificate emitted."
    let some n ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun n => pure (some n))
      | throwError "Closed Nat payload was not recognized; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta312Q12To16Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta312Q12To16Value
#print Paper7MomentCounts.b6Theta312Q12To16Value

theorem b6Theta312Q12To16_checked : b6Theta312Q12To16Expr = (b6Theta312Q12To16Value : ℤ) := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6Theta312Q12To16_checked

end Paper7MomentCounts
