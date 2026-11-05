import Research.Backfill.Paper7.MomentB6ComputableKernel

/-! Uncompiled single-fibre supervision candidate. No number is supplied.
Only a future explicit Root-selected Lean run may execute the elaboration-time
reduction below. The generated Nat literal has no counting credit until the
independent kernel equality theorem and the entire source pass. Default
budgets and linters remain unchanged. Scope: theta264, Q=18, Z=18 only.
The complete theta264 fibre still requires the other Q slices. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6Theta264Q18_eval_ZRange : b6EvalZRange (24,264) 18 = {18} := by
  norm_num [b6EvalZRange]
#print axioms Paper7MomentCounts.b6Theta264Q18_eval_ZRange

theorem b6Theta264Q18_eval_single_block :
    b6EvalQSlice (24,264) 18 = b6EvalBlock (24,264) 18 18 := by
  unfold b6EvalQSlice
  rw [b6Theta264Q18_eval_ZRange,Finset.sum_singleton]
#print axioms Paper7MomentCounts.b6Theta264Q18_eval_single_block

def b6Theta264Q18Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6EvalBlock (24,264) 18 18)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int numeral was not obtained; no certificate emitted."
    let some n := nExpr.rawNatLit?
      | throwError "Reduced Int payload is not a Nat literal; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta264Q18Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta264Q18Value
#print Paper7MomentCounts.b6Theta264Q18Value

theorem b6Theta264Q18_eval_checked :
    b6EvalBlock (24,264) 18 18 = (b6Theta264Q18Value : ℤ) := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6Theta264Q18_eval_checked

theorem b6Theta264Q18_QSlice_checked :
    b6EvalQSlice (24,264) 18 = (b6Theta264Q18Value : ℤ) :=
  b6Theta264Q18_eval_single_block.trans b6Theta264Q18_eval_checked
#print axioms Paper7MomentCounts.b6Theta264Q18_QSlice_checked

theorem b6Theta264Q18_original_QSlice_checked :
    b6CatalogConvolutionQSlice (24,264) 18 = (b6Theta264Q18Value : ℤ) :=
  (b6EvalQSlice_eq (24,264) 18).symm.trans b6Theta264Q18_QSlice_checked
#print axioms Paper7MomentCounts.b6Theta264Q18_original_QSlice_checked

theorem b6Theta264Q18_original_statistic_card_checked :
    Nat.card (labelledOriginalPQStatisticFibre 6 18 162 18) = b6Theta264Q18Value := by
  classical
  have ha : b6CatalogStatisticAccept (24,264) 18 18 := by
    norm_num [b6CatalogStatisticAccept,b6CatalogResidual]
  have hc : b6CatalogConvolutionBlock (24,264) 18 18 =
      (labelledExactCapacityQCard 6 18 162 18 : ℤ) := by
    rw [b6CatalogConvolutionBlock_eq_actual,ite_eq_left ha]
    rfl
  have he : (labelledExactCapacityQCard 6 18 162 18 : ℤ) = (b6Theta264Q18Value : ℤ) :=
    hc.symm.trans ((b6EvalBlock_eq (24,264) 18 18).symm.trans b6Theta264Q18_eval_checked)
  have hcard : (Nat.card (labelledOriginalPQStatisticFibre 6 18 162 18) : ℤ) =
      (b6Theta264Q18Value : ℤ) :=
    (congrArg (fun n : ℕ => (n : ℤ)) (labelledOriginalPQStatisticFibre_card 6 18 162 18)).trans he
  exact_mod_cast hcard
#print axioms Paper7MomentCounts.b6Theta264Q18_original_statistic_card_checked

end Paper7MomentCounts
