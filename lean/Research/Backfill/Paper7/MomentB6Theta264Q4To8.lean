import Research.Backfill.Paper7.MomentB6ComputableKernel

/-! Uncompiled complete Q interval [4,8) for original theta264.
All original Z ranges and guards in each QSlice are retained. This expression
is a proper four-Q segment of the failed whole Q0..15 prefix, not a renamed
copy of that whole expression. Future Root-supervised Lean must generate and
kernel-check its value under unchanged default limits. No value is supplied. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6Theta264Q4To8Expr : ℤ :=
  ∑ Q ∈ Finset.Ico 4 8, b6EvalQSlice (24,264) Q
#print axioms Paper7MomentCounts.b6Theta264Q4To8Expr

def b6Theta264Q4To8Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6Theta264Q4To8Expr)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained; no certificate emitted."
    let some n ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun n => pure (some n))
      | throwError "Closed Nat payload was not recognized; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta264Q4To8Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta264Q4To8Value
#print Paper7MomentCounts.b6Theta264Q4To8Value

theorem b6Theta264Q4To8_checked : b6Theta264Q4To8Expr = (b6Theta264Q4To8Value : ℤ) := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6Theta264Q4To8_checked

end Paper7MomentCounts
