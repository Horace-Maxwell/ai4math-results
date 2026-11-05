import Research.Backfill.Paper7.MomentB6ComputableKernel

/-! Uncompiled next single-block supervision candidate. No value is supplied.
The entire theta264/Q17 slice consists of Z17 and Z18 blocks. This source
certifies only the Z17 block, and retains the exact unresolved Z18 summand.
The previous successful Q18 source is not imported or recomputed here.
Only a future explicit Root-selected Lean run may generate the numeral;
with_unfolding_all rfl must then provide a kernel-checked equality.
Default budgets and linters remain unchanged. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6Theta264Q17_eval_ZRange : b6EvalZRange (24,264) 17 = {17,18} := by
  ext n
  norm_num [b6EvalZRange]
  omega
#print axioms Paper7MomentCounts.b6Theta264Q17_eval_ZRange

theorem b6Theta264Q17_eval_two_blocks :
    b6EvalQSlice (24,264) 17 =
      b6EvalBlock (24,264) 17 17 + b6EvalBlock (24,264) 18 17 := by
  unfold b6EvalQSlice
  rw [b6Theta264Q17_eval_ZRange,Finset.sum_pair (by norm_num : (17 : ℕ) ≠ 18)]
#print axioms Paper7MomentCounts.b6Theta264Q17_eval_two_blocks

def b6Theta264Q17Z17Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6EvalBlock (24,264) 17 17)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int numeral was not obtained; no certificate emitted."
    let some n := nExpr.rawNatLit?
      | throwError "Reduced Int payload is not a Nat literal; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta264Q17Z17Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta264Q17Z17Value
#print Paper7MomentCounts.b6Theta264Q17Z17Value

theorem b6Theta264Q17Z17_eval_checked :
    b6EvalBlock (24,264) 17 17 = (b6Theta264Q17Z17Value : ℤ) := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6Theta264Q17Z17_eval_checked

theorem b6Theta264Q17Z17_original_block_checked :
    b6CatalogConvolutionBlock (24,264) 17 17 = (b6Theta264Q17Z17Value : ℤ) :=
  (b6EvalBlock_eq (24,264) 17 17).symm.trans b6Theta264Q17Z17_eval_checked
#print axioms Paper7MomentCounts.b6Theta264Q17Z17_original_block_checked

theorem b6Theta264Q17Z17_original_statistic_card_checked :
    Nat.card (labelledOriginalPQStatisticFibre 6 17 167 17) = b6Theta264Q17Z17Value := by
  classical
  have ha : b6CatalogStatisticAccept (24,264) 17 17 := by
    norm_num [b6CatalogStatisticAccept,b6CatalogResidual]
  have hc : b6CatalogConvolutionBlock (24,264) 17 17 =
      (labelledExactCapacityQCard 6 17 167 17 : ℤ) := by
    rw [b6CatalogConvolutionBlock_eq_actual,ite_eq_left ha]
    rfl
  have he : (labelledExactCapacityQCard 6 17 167 17 : ℤ) = (b6Theta264Q17Z17Value : ℤ) :=
    hc.symm.trans b6Theta264Q17Z17_original_block_checked
  have hcard : (Nat.card (labelledOriginalPQStatisticFibre 6 17 167 17) : ℤ) =
      (b6Theta264Q17Z17Value : ℤ) :=
    (congrArg (fun n : ℕ => (n : ℤ)) (labelledOriginalPQStatisticFibre_card 6 17 167 17)).trans he
  exact_mod_cast hcard
#print axioms Paper7MomentCounts.b6Theta264Q17Z17_original_statistic_card_checked

theorem b6Theta264Q17_original_QSlice_partial :
    b6CatalogConvolutionQSlice (24,264) 17 =
      (b6Theta264Q17Z17Value : ℤ) + b6CatalogConvolutionBlock (24,264) 18 17 := by
  calc
    b6CatalogConvolutionQSlice (24,264) 17 = b6EvalQSlice (24,264) 17 :=
      (b6EvalQSlice_eq (24,264) 17).symm
    _ = b6EvalBlock (24,264) 17 17 + b6EvalBlock (24,264) 18 17 :=
      b6Theta264Q17_eval_two_blocks
    _ = (b6Theta264Q17Z17Value : ℤ) + b6CatalogConvolutionBlock (24,264) 18 17 := by
      rw [b6Theta264Q17Z17_eval_checked,b6EvalBlock_eq]
#print axioms Paper7MomentCounts.b6Theta264Q17_original_QSlice_partial

end Paper7MomentCounts
