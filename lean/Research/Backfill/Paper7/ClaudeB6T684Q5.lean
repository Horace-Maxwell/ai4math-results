import Research.Backfill.Paper7.MomentB6LowQFiveDominantTightCResidualPruned

/-! Claude, 2026-11-03. The complete Q=5 slice of catalogue entry (38,684).
The value is obtained by closed Meta reduction and then checked by the kernel
(`rfl` on the full evaluator expression). The heartbeat budget is raised for
these two declarations only. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

set_option maxHeartbeats 0 in
def claudeB6T684Q5Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (38,684) 5)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained."
    let some k ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun k => pure (some k))
      | throwError "Closed Nat payload was not recognized."
    Lean.Elab.Tactic.closeMainGoal `claudeB6T684Q5Value (Lean.mkRawNatLit k)
#print axioms Paper7MomentCounts.claudeB6T684Q5Value
#print Paper7MomentCounts.claudeB6T684Q5Value

set_option maxHeartbeats 0 in
theorem claudeB6T684Q5_checked :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (38,684) 5 = (claudeB6T684Q5Value : ℤ) := by
  run_tac do
    let proof ← Lean.Meta.mkEqRefl
      (← Lean.Elab.Term.elabTerm (← `(b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (38,684) 5)) none)
    Lean.Elab.Tactic.closeMainGoal `claudeB6T684Q5_checked proof
#print axioms Paper7MomentCounts.claudeB6T684Q5_checked

theorem claudeB6T684Q5_slice :
    b6StructuralProductFastEvalQSlice (38,684) 5 = (claudeB6T684Q5Value : ℤ) := by
  rw [← b6StructuralResidualPrunedEvalQSlice_eq, ← b6StructuralTightCResidualPrunedEvalQSlice_eq,
    ← b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice_eq]
  exact claudeB6T684Q5_checked
#print axioms Paper7MomentCounts.claudeB6T684Q5_slice

end Paper7MomentCounts
