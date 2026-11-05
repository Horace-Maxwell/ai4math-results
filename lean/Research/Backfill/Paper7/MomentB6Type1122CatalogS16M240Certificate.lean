import Research.Backfill.Paper7.MomentB6Type1122WindowEvalOuter

/-! Uncompiled source-only certificate for the single actual catalogue block
(16,240). No candidate value is supplied or obtained outside Lean. A future
Root-selected Lean command may execute the reduction below under its existing
supervision. The generated literal has no mathematical credit unless the
following ordinary kernel equality and the entire source pass. The outer
transport is bound separately to its actual913 successful production record.
No other catalogue block or complete reflection count is evaluated. -/
set_option autoImplicit false
namespace Paper7MomentCounts

def b6R1122CatalogS16M240Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6R1122EvalCatalogBlock (16,240))) (some (Lean.mkConst ``Nat))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let some n ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue v (fun n => pure (some n))
      | throwError "Closed Nat representation was not recognized; reduced expression: {v}"
    Lean.Elab.Tactic.closeMainGoal `b6R1122CatalogS16M240Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6R1122CatalogS16M240Value
#print Paper7MomentCounts.b6R1122CatalogS16M240Value

theorem b6R1122CatalogS16M240_eval_checked :
    b6R1122EvalCatalogBlock (16,240)=b6R1122CatalogS16M240Value := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6R1122CatalogS16M240_eval_checked

end Paper7MomentCounts
