import Research.TaskP.RectangleDefect.UpperSparse
import Research.TaskP.RectangleDefect.SmallRows
import Research.TaskP.RectangleDefect.BalanceCases
import Research.TaskP.RectangleDefect.RowPlacement
import Research.TaskP.RectangleDefect.MatchingLower

namespace TaskP.RectangleDefect.Proof
open Challenge

theorem SharpBound : Challenge.SharpBound := by
  refine ⟨multisets_finite,?_,?_⟩
  · intro k n _ hk hn
    have h : failures k n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro m ⟨hm,ht⟩
      exact ht (tiles_of_rowSplit hn (small_rowSplit hk hm))
    rw [defect_eq_failures,h,Set.ncard_empty]
  · intro k hk
    obtain ⟨T,_,hT⟩ := fail_gcd k
    refine ⟨upper_of_sparse (T:=T) hk ?_,Lower.subsequence_lower k hk,
      fun h => Lower.odd_lower k h⟩
    intro n hn m hm
    by_cases hj : (heavy T m).Nonempty
    · have fail : ¬ RowSplit m n := fun h => hm.2 (tiles_of_rowSplit hn h)
      exact sparse_of_gcd hk _ (hT n m hm.1 fail hj)
    · simp [Finset.not_nonempty_iff_eq_empty.mp hj]

end TaskP.RectangleDefect.Proof
