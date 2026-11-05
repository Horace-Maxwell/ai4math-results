import Research.Backfill.Paper7.MomentB6LowQFiveDominantTightCResidualPruned

/-! Claude, 2026-11-03. The complete Q=4 slice of catalogue entry (33,624).
The value is obtained by closed Meta reduction and then checked by the kernel
(`rfl` on the full evaluator expression). The heartbeat budget is raised for
these two declarations only. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

set_option maxHeartbeats 0 in
def claudeB6T624Q4Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (33,624) 4)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained."
    let some k ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun k => pure (some k))
      | throwError "Closed Nat payload was not recognized."
    Lean.Elab.Tactic.closeMainGoal `claudeB6T624Q4Value (Lean.mkRawNatLit k)
#print axioms Paper7MomentCounts.claudeB6T624Q4Value
#print Paper7MomentCounts.claudeB6T624Q4Value

set_option maxHeartbeats 0 in
theorem claudeB6T624Q4_checked :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (33,624) 4 = (claudeB6T624Q4Value : ℤ) := by
  run_tac do
    let proof ← Lean.Meta.mkEqRefl
      (← Lean.Elab.Term.elabTerm (← `(b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (33,624) 4)) none)
    Lean.Elab.Tactic.closeMainGoal `claudeB6T624Q4_checked proof
#print axioms Paper7MomentCounts.claudeB6T624Q4_checked

theorem claudeB6T624Q4_slice :
    b6StructuralProductFastEvalQSlice (33,624) 4 = (claudeB6T624Q4Value : ℤ) := by
  rw [← b6StructuralResidualPrunedEvalQSlice_eq, ← b6StructuralTightCResidualPrunedEvalQSlice_eq,
    ← b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice_eq]
  exact claudeB6T624Q4_checked
#print axioms Paper7MomentCounts.claudeB6T624Q4_slice

end Paper7MomentCounts
