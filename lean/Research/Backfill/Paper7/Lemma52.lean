import Research.Backfill.Paper7.TridiagonalInertia

set_option autoImplicit false

namespace Paper7Pivots

open BackfillPaper7.Challenge

/-- Strong induction for the exact original count and the exact original matrix.
Nonzero edges are needed only when a zero pivot consumes the next vertex. -/
theorem tridiag_pivCount (N : ℕ) (t a : ℕ → ℝ)
    (ha : ∀ k, k+1 < N → a k ≠ 0) :
    pivCount true (pivotEntries N t a) none = nPos (tridiagGen N t a) ∧
      pivCount false (pivotEntries N t a) none = nNeg (tridiagGen N t a) := by
  induction N using Nat.strong_induction_on generalizing t a with
  | h N ih =>
    cases N with
    | zero => exact lemma52_zero t a
    | succ n =>
      by_cases ht : t 0 = 0
      · cases n with
        | zero => exact lemma52_one t a
        | succ k =>
          have he : a 0 ≠ 0 := ha 0 (by omega)
          have htail : ∀ j, j+1 < k → a (j+2) ≠ 0 := by
            intro j hj
            exact ha (j+2) (by omega)
          have hi := ih k (by omega) (fun j => t (j+2)) (fun j => a (j+2)) htail
          have hm := tridiag_zero_step k t a ht he
          constructor
          · rw [pivCount_zero_step true k t a ht, hi.1, hm.1]
          · rw [pivCount_zero_step false k t a ht, hi.2, hm.2]
      · have htail : ∀ j, j+1 < n → a (j+1) ≠ 0 := by
          intro j hj
          exact ha (j+1) (by omega)
        have hi := ih n (by omega) (schurDiagonal t a (t 0)) (fun j => a (j+1)) htail
        have hm := tridiag_nonzero_step n t a ht
        constructor
        · rw [pivCount_nonzero_step true n t a ht, pivotSign_true, hi.1, hm.1]
        · rw [pivCount_nonzero_step false n t a ht, pivotSign_false, hi.2, hm.2]
#print axioms Paper7Pivots.tridiag_pivCount

/-- Exactly the frozen universal contract, without extra premises. -/
theorem check_Lemma52 : BackfillPaper7.Challenge.Lemma52 := by
  intro N t a ha
  exact tridiag_pivCount N t a ha
#print axioms Paper7Pivots.check_Lemma52

end Paper7Pivots
