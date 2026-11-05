import Research.Backfill.Paper7.MomentB6StructuralProductFastW6

/-! NEW expression for the complete original theta324 Q interval [0,4).
The actual975 structural product-weight QSlice and structural outer sum retain
the full original ranges and conditions. All four actual965 complete headers,
the original Value-generation strategy and independent kernel reflexivity
check remain unchanged. No value is prefilled or externally calculated.
Only a future Root-selected Lean run may attempt Value generation. An emitted
Value or an earlier axiom print is not whole-source success. Cost is UNKNOWN. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6Theta324W6Q0To4Expr : ℤ :=
  b6StructuralIcoSum (fun Q => b6StructuralProductFastEvalQSlice (29,324) Q) 0 4
#print axioms Paper7MomentCounts.b6Theta324W6Q0To4Expr

def b6Theta324W6Q0To4Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6Theta324W6Q0To4Expr)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int representation was not obtained; no certificate emitted."
    let some n ← Lean.Meta.withTransparency .all <|
        Lean.Meta.withNatValue nExpr (fun n => pure (some n))
      | throwError "Closed Nat payload was not recognized; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta324W6Q0To4Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta324W6Q0To4Value
#print Paper7MomentCounts.b6Theta324W6Q0To4Value

theorem b6Theta324W6Q0To4_checked : b6Theta324W6Q0To4Expr = (b6Theta324W6Q0To4Value : ℤ) := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6Theta324W6Q0To4_checked

theorem b6Theta324W6Q0To4_eq_original_sum :
    (b6Theta324W6Q0To4Value : ℤ) =
      ∑ Q ∈ Finset.Ico 0 4, b6W6FastEvalQSlice (29,324) Q := by
  calc
    (b6Theta324W6Q0To4Value : ℤ) = b6Theta324W6Q0To4Expr :=
      b6Theta324W6Q0To4_checked.symm
    _ = ∑ Q ∈ Finset.Ico 0 4, b6W6FastEvalQSlice (29,324) Q := by
      unfold b6Theta324W6Q0To4Expr
      rw [b6StructuralIcoSum_eq]
      simp only [b6StructuralProductFastEvalQSlice_eq,
        b6StructuralSortedFastEvalQSlice_eq, b6SortedFastEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6Theta324W6Q0To4_eq_original_sum

end Paper7MomentCounts
