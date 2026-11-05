import Research.Backfill.Paper7.BudgetLayering

/-! Only the final 24-term and 20-term arithmetic sums are kernel evaluated. -/

set_option autoImplicit false
set_option maxRecDepth 4096

namespace Paper7Budget

open BackfillPaper7.Challenge

theorem budgetPQ_49 : (budgetPQ 3 49).ncard = 3031469 := by
  rw [budgetPQ_ncard 49 (by decide)]
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

#print axioms Paper7Budget.budgetPQ_49

theorem budgetPQ_42 : (budgetPQ 3 42).ncard = 1246783 := by
  rw [budgetPQ_ncard 42 (by decide)]
  simp only [Nat.choose_eq_descFactorial_div_factorial]
  decide +kernel

#print axioms Paper7Budget.budgetPQ_42

theorem check_LabeledBudgetCounts : BackfillPaper7.Challenge.LabeledBudgetCounts := by
  exact ⟨budgetPQ_49, budgetPQ_42⟩

#print axioms Paper7Budget.check_LabeledBudgetCounts

end Paper7Budget
