import Research.Backfill.Paper7.MomentB6ResidualPruned

/-! NEW expression for the complete original theta324 Q interval [4,8).
All three original eleven-theta segment headers and the complete Value and
independent kernel checked blocks are preserved. Only Expr uses actual981's
residual-pruned product expression with the same structural outer interval sum.
No value is prefilled; default limits are unchanged. An emitted Value or an
early axiom print does not establish complete-source success. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6Theta324Q4To8Expr : ℤ :=
  b6StructuralIcoSum (fun Q => b6StructuralResidualPrunedEvalQSlice (29,324) Q) 4 8
#print axioms Paper7MomentCounts.b6Theta324Q4To8Expr

def b6Theta324Q4To8Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6Theta324Q4To8Expr)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained; no certificate emitted."
    let some n ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun n => pure (some n))
      | throwError "Closed Nat payload was not recognized; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta324Q4To8Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta324Q4To8Value
#print Paper7MomentCounts.b6Theta324Q4To8Value

theorem b6Theta324Q4To8_checked : b6Theta324Q4To8Expr = (b6Theta324Q4To8Value : ℤ) := by
  run_tac do
    let proof ← Lean.Meta.mkEqRefl (Lean.mkConst ``Paper7MomentCounts.b6Theta324Q4To8Expr)
    Lean.Elab.Tactic.closeMainGoal `b6Theta324Q4To8_checked proof
#print axioms Paper7MomentCounts.b6Theta324Q4To8_checked

end Paper7MomentCounts
