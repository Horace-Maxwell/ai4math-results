import Research.Backfill.Paper7.MomentB6LowQFiveDominantTightCResidualPruned

/-! Claude, 2026-11-03. The complete Q=17 slice of catalogue entry (38,396).
The value is obtained by closed Meta reduction and then checked by the kernel
(`rfl` on the full evaluator expression). The heartbeat budget is raised for
these two declarations only. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

set_option maxHeartbeats 0 in
def claudeB6T396Q17Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (38,396) 17)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained."
    let some k ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun k => pure (some k))
      | throwError "Closed Nat payload was not recognized."
    Lean.Elab.Tactic.closeMainGoal `claudeB6T396Q17Value (Lean.mkRawNatLit k)
#print axioms Paper7MomentCounts.claudeB6T396Q17Value
#print Paper7MomentCounts.claudeB6T396Q17Value

set_option maxHeartbeats 0 in
theorem claudeB6T396Q17_checked :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (38,396) 17 = (claudeB6T396Q17Value : ℤ) := by
  run_tac do
    let proof ← Lean.Meta.mkEqRefl
      (← Lean.Elab.Term.elabTerm (← `(b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (38,396) 17)) none)
    Lean.Elab.Tactic.closeMainGoal `claudeB6T396Q17_checked proof
#print axioms Paper7MomentCounts.claudeB6T396Q17_checked

theorem claudeB6T396Q17_slice :
    b6StructuralProductFastEvalQSlice (38,396) 17 = (claudeB6T396Q17Value : ℤ) := by
  rw [← b6StructuralResidualPrunedEvalQSlice_eq, ← b6StructuralTightCResidualPrunedEvalQSlice_eq,
    ← b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice_eq]
  exact claudeB6T396Q17_checked
#print axioms Paper7MomentCounts.claudeB6T396Q17_slice

end Paper7MomentCounts
