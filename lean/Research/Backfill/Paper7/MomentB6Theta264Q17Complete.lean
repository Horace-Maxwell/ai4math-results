import Research.Backfill.Paper7.MomentB6Theta264Q17Z17Certificate

/-! Uncompiled final block of the original theta264/Q17 slice.
Only the Z18/R164/Q17 block is newly evaluated. The successful Z17 block
and exact two-block decomposition are imported, never recomputed.
A future Root-selected Lean run generates the new block numeral and checks
it with with_unfolding_all rfl. The Q17 aggregate is only the addition of
certified block values; no whole-slice reduction or external value is used.
Budgets and linters remain unchanged. This does not finish theta264. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6Theta264Q17Z18Value : ℕ := by
  run_tac do
    let e ← Lean.Elab.Term.elabTermEnsuringType
      (← `(b6EvalBlock (24,264) 18 17)) (some (Lean.mkConst ``Int))
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    let e ← Lean.instantiateMVars e
    Lean.Meta.check e
    let v ← Lean.Meta.withTransparency .all <| Lean.Meta.reduce e
    let .app (.const ``Int.ofNat _) nExpr := v.consumeMData
      | throwError "Closed nonnegative Int numeral was not obtained; no certificate emitted."
    let some n := nExpr.rawNatLit?
      | throwError "Reduced Int payload is not a Nat literal; no certificate emitted."
    Lean.Elab.Tactic.closeMainGoal `b6Theta264Q17Z18Value (Lean.mkRawNatLit n)
#print axioms Paper7MomentCounts.b6Theta264Q17Z18Value
#print Paper7MomentCounts.b6Theta264Q17Z18Value

theorem b6Theta264Q17Z18_eval_checked :
    b6EvalBlock (24,264) 18 17 = (b6Theta264Q17Z18Value : ℤ) := by
  with_unfolding_all rfl
#print axioms Paper7MomentCounts.b6Theta264Q17Z18_eval_checked

theorem b6Theta264Q17Z18_original_block_checked :
    b6CatalogConvolutionBlock (24,264) 18 17 = (b6Theta264Q17Z18Value : ℤ) :=
  (b6EvalBlock_eq (24,264) 18 17).symm.trans b6Theta264Q17Z18_eval_checked
#print axioms Paper7MomentCounts.b6Theta264Q17Z18_original_block_checked

theorem b6Theta264Q17Z18_original_statistic_card_checked :
    Nat.card (labelledOriginalPQStatisticFibre 6 18 164 17) = b6Theta264Q17Z18Value := by
  classical
  have ha : b6CatalogStatisticAccept (24,264) 18 17 := by
    norm_num [b6CatalogStatisticAccept,b6CatalogResidual]
  have hc : b6CatalogConvolutionBlock (24,264) 18 17 =
      (labelledExactCapacityQCard 6 18 164 17 : ℤ) := by
    rw [b6CatalogConvolutionBlock_eq_actual,ite_eq_left ha]
    rfl
  have he : (labelledExactCapacityQCard 6 18 164 17 : ℤ) = (b6Theta264Q17Z18Value : ℤ) :=
    hc.symm.trans b6Theta264Q17Z18_original_block_checked
  have hcard : (Nat.card (labelledOriginalPQStatisticFibre 6 18 164 17) : ℤ) =
      (b6Theta264Q17Z18Value : ℤ) :=
    (congrArg (fun n : ℕ => (n : ℤ)) (labelledOriginalPQStatisticFibre_card 6 18 164 17)).trans he
  exact_mod_cast hcard
#print axioms Paper7MomentCounts.b6Theta264Q17Z18_original_statistic_card_checked

def b6Theta264Q17Value : ℕ := b6Theta264Q17Z17Value + b6Theta264Q17Z18Value
#print axioms Paper7MomentCounts.b6Theta264Q17Value
#print Paper7MomentCounts.b6Theta264Q17Value

theorem b6Theta264Q17_original_QSlice_checked :
    b6CatalogConvolutionQSlice (24,264) 17 = (b6Theta264Q17Value : ℤ) := by
  rw [b6Theta264Q17_original_QSlice_partial,b6Theta264Q17Z18_original_block_checked]
  change (b6Theta264Q17Z17Value : ℤ) + (b6Theta264Q17Z18Value : ℤ) =
    ((b6Theta264Q17Z17Value + b6Theta264Q17Z18Value : ℕ) : ℤ)
  exact (Nat.cast_add b6Theta264Q17Z17Value b6Theta264Q17Z18Value).symm
#print axioms Paper7MomentCounts.b6Theta264Q17_original_QSlice_checked

end Paper7MomentCounts
