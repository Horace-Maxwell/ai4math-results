import Research.Backfill.Paper7.MomentB6ComputableKernel

/-! Uncompiled complete original theta264/Q16 slice candidate.
The exact Z window is {16,17,18}. The future supervised reduction uses the
whole b6EvalQSlice expression, retaining all three complete Z blocks.
No prior slice value, subtraction, table or pending Q17-complete theorem is
used. Only a future Root-selected Lean run may generate the numeral, and
with_unfolding_all rfl must certify the full expression in the kernel.
Default budgets and linters remain unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

theorem b6Theta264Q16_eval_ZRange : b6EvalZRange (24,264) 16 = {16,17,18} := by
  ext n
  norm_num [b6EvalZRange]
  omega
#print axioms Paper7MomentCounts.b6Theta264Q16_eval_ZRange

def b6Theta264Q16Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6EvalQSlice (24,264) 16)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int numeral was not obtained; no certificate emitted."
    let some n := nExpr.rawNatLit?
      | throwError "Reduced Int payload is not a Nat literal; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta264Q16Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta264Q16Value
#print Paper7MomentCounts.b6Theta264Q16Value

theorem b6Theta264Q16_eval_checked :
    b6EvalQSlice (24,264) 16 = (b6Theta264Q16Value : ℤ) := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6Theta264Q16_eval_checked

theorem b6Theta264Q16_original_QSlice_checked :
    b6CatalogConvolutionQSlice (24,264) 16 = (b6Theta264Q16Value : ℤ) :=
  (b6EvalQSlice_eq (24,264) 16).symm.trans b6Theta264Q16_eval_checked
#print axioms Paper7MomentCounts.b6Theta264Q16_original_QSlice_checked

end Paper7MomentCounts
