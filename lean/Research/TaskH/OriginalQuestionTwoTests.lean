import Research.TaskH.OriginalQuestionTwoAssembly

/-! Exact original Question2 and original counterexample-contract regressions.
These tests add no hypotheses to the frozen all-k statement. -/
set_option autoImplicit false
universe u
namespace TaskH.OriginalTests
open SimpleGraph Challenge

theorem exact_frozen_question_two : Question2.{u} :=
  TaskH.original_question_two_all_k

theorem original_all_k_head (k : ℕ) (hk : 4 ≤ k)
    (V : Type u) [Fintype V] (G : SimpleGraph V)
    (hcrit : IsCriticalPlus k G) (hcount : modCycleCount k G = bound k) :
    IsCompleteOfOrder G (k + 1) :=
  TaskH.original_question_two_all_k k hk V G hcrit hcount

theorem no_original_counterexample : ¬ CounterexampleToQuestion2.{u} := by
  rintro ⟨k, hk, V, iV, G, hcrit, hcount, hnot⟩
  let _ : Fintype V := iV
  exact hnot (TaskH.original_question_two_all_k k hk V G hcrit hcount)

end TaskH.OriginalTests
#print axioms TaskH.OriginalTests.exact_frozen_question_two
#print axioms TaskH.OriginalTests.original_all_k_head
#print axioms TaskH.OriginalTests.no_original_counterexample
