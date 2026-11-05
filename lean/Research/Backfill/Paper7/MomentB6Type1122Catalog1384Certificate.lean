import Research.Backfill.Paper7.MomentB6Type1122WindowEvalOuter

/-! Uncompiled source-only certificate for the single actual catalogue block
(13,84). No candidate value is supplied or obtained outside Lean. A future
Root-selected Lean command may execute the reduction below under its existing
supervision. The generated literal has no mathematical credit unless the
following ordinary kernel equality and the entire source pass. The pending
outer transport is not asserted to be a successful production parent here.
No other catalogue block or complete reflection count is evaluated. -/
set_option autoImplicit false
namespace Paper7MomentCounts

def b6R1122Catalog1384Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6R1122EvalCatalogBlock (13,84))) (some (Lean.mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let some n := v.consumeMData.rawNatLit?
      | throwError "Closed Nat literal was not obtained; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6R1122Catalog1384Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6R1122Catalog1384Value
#print Paper7MomentCounts.b6R1122Catalog1384Value

theorem b6R1122Catalog1384_eval_checked :
    b6R1122EvalCatalogBlock (13,84)=b6R1122Catalog1384Value := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6R1122Catalog1384_eval_checked

end Paper7MomentCounts
