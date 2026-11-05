import Research.Backfill.Paper7.MomentB6DominantTightCResidualPruned

/-! SOURCE ONLY. Original complete theta324 Q[12,16), with both TightC
conditions and the universally equal dominant-coordinate weight. Explicit
DominantTightC names expose the NEW implementation; Value-generation and kernel
checked-proof code are preserved modulo this identifier renaming. Exact
(29,324), lower12/upper16 and the original residual target remain unchanged.
No Value is guessed, no budget changes and no automatic activation/queue. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6Theta324DominantTightCQ12To16Expr : ℤ :=
  b6StructuralIcoSum (fun Q => b6StructuralDominantTightCResidualPrunedEvalQSlice (29,324) Q) 12 16
#print axioms Paper7MomentCounts.b6Theta324DominantTightCQ12To16Expr

def b6Theta324DominantTightCQ12To16Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6Theta324DominantTightCQ12To16Expr)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained; no certificate emitted."
    let some n ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun n => pure (some n))
      | throwError "Closed Nat payload was not recognized; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta324DominantTightCQ12To16Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta324DominantTightCQ12To16Value
#print Paper7MomentCounts.b6Theta324DominantTightCQ12To16Value

theorem b6Theta324DominantTightCQ12To16_checked : b6Theta324DominantTightCQ12To16Expr = (b6Theta324DominantTightCQ12To16Value : ℤ) := by
  run_tac do
    let proof ← Lean.Meta.mkEqRefl (Lean.mkConst ``Paper7MomentCounts.b6Theta324DominantTightCQ12To16Expr)
    Lean.Elab.Tactic.closeMainGoal `b6Theta324DominantTightCQ12To16_checked proof
#print axioms Paper7MomentCounts.b6Theta324DominantTightCQ12To16_checked

/-- Exact same original Q[12,16) interval, transported by the full-parameter
cResidual equality. This theorem requires the complete checked Value above. -/
theorem b6Theta324DominantTightCQ12To16_residual_checked :
    b6StructuralIcoSum (fun Q => b6StructuralResidualPrunedEvalQSlice (29,324) Q) 12 16 =
      (b6Theta324DominantTightCQ12To16Value : ℤ) := by
  calc
    _ = b6Theta324DominantTightCQ12To16Expr := by
      simp only [b6Theta324DominantTightCQ12To16Expr, b6StructuralDominantTightCResidualPrunedEvalQSlice_eq,
        b6StructuralTightCResidualPrunedEvalQSlice_eq]
    _ = (b6Theta324DominantTightCQ12To16Value : ℤ) := b6Theta324DominantTightCQ12To16_checked
#print axioms Paper7MomentCounts.b6Theta324DominantTightCQ12To16_residual_checked

end Paper7MomentCounts
