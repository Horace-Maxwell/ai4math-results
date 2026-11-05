import Research.Backfill.Paper7.MomentB6W6KernelTransport
import Research.Backfill.Paper7.MomentB6ComputableKernel

/-! NEW uncompiled candidate. Unit 5: ordinary constructive definitions,
followed by universal equality proofs. No proof/cardinality operation enters
the evaluation definitions. No runtime improvement is asserted. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open scoped BigOperators

def b6W6EvalWeight (z : Fin 6 → ℕ) (Q : ℕ) : ℤ :=
  ∑ I ∈ (Finset.univ : Finset (Fin 6)).powerset,
    let d : ℕ := ∑ i ∈ I, (z i + 1)
    (-1 : ℤ)^I.card *
      (bif decide (d ≤ Q) then (((Q-d+5).choose 5 : ℕ) : ℤ) else 0)
#print axioms Paper7MomentCounts.b6W6EvalWeight

def b6W6EvalQSplitSum (Z R A B Q : ℕ) : ℤ :=
  ∑ c ∈ b6EvalScalarRange A B,
    bif b6EvalSortedAccept A B c then
      ∑ f ∈ b6EvalScalarRange (Z-A) (R-B),
        bif b6EvalSortedAccept (Z-A) (R-B) f then
          (b6EvalMultiplicity c (b6EvalHigh A B c) (b6EvalLow A B c) : ℤ) *
          (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
            (b6EvalLow (Z-A) (R-B) f) : ℤ) *
          b6W6EvalWeight
            ![c, b6EvalHigh A B c, b6EvalLow A B c,
              f, b6EvalHigh (Z-A) (R-B) f, b6EvalLow (Z-A) (R-B) f] Q
        else 0
    else 0
#print axioms Paper7MomentCounts.b6W6EvalQSplitSum

theorem b6W6EvalWeight_eq (z : Fin 6 → ℕ) (Q : ℕ) :
    b6W6EvalWeight z Q = labelledSixQWeight z Q := by
  classical
  rw [labelledSixQWeight_eq_actual_card, bounded_q_inclusion_exclusion]
  unfold b6W6EvalWeight
  rw [Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro I _hI
  let d : ℕ := ∑ i ∈ I, (z i + 1)
  change (-1 : ℤ)^I.card *
      (bif decide (d ≤ Q) then (((Q-d+5).choose 5 : ℕ) : ℤ) else 0) =
    (-1 : ℤ)^I.card * (if d ≤ Q then (Nat.multichoose 6 (Q-d) : ℤ) else 0)
  apply congrArg (fun k : ℤ => (-1 : ℤ)^I.card * k)
  by_cases hd : d ≤ Q
  · rw [Bool.cond_eq_ite, ite_eq_left (decide_eq_true hd), ite_eq_left hd]
    exact_mod_cast (boundedIE_multichoose_succ 5 (Q-d)).symm
  · have hb : ¬ decide (d ≤ Q) = true := fun h => hd (of_decide_eq_true h)
    rw [Bool.cond_eq_ite, ite_eq_right hb, ite_eq_right hd]
#print axioms Paper7MomentCounts.b6W6EvalWeight_eq

theorem b6W6EvalQSplitSum_eq_symbolic (Z R A B Q : ℕ) :
    b6W6EvalQSplitSum Z R A B Q = labelledTripleKernelW6Sum Z R A B Q := by
  classical
  unfold b6W6EvalQSplitSum labelledTripleKernelW6Sum
  rw [b6EvalScalarRange_eq]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hc : B6SortedTripleDiscriminantAccept A B c
  · rw [Bool.cond_eq_ite,
      ite_eq_left ((b6EvalSortedAccept_iff A B c).mpr hc)]
    simp only [hc, true_and]
    rw [b6EvalScalarRange_eq]
    apply Finset.sum_congr rfl
    intro f _hf
    by_cases hf : B6SortedTripleDiscriminantAccept (Z-A) (R-B) f
    · rw [Bool.cond_eq_ite,
        ite_eq_left ((b6EvalSortedAccept_iff (Z-A) (R-B) f).mpr hf), ite_eq_left hf]
      simp only [b6EvalMultiplicity_eq, b6EvalHigh_eq, b6EvalLow_eq,
        b6W6EvalWeight_eq, labelledJoinedTripleCapacity]
    · have hb : ¬ b6EvalSortedAccept (Z-A) (R-B) f = true :=
        fun h => hf ((b6EvalSortedAccept_iff (Z-A) (R-B) f).mp h)
      rw [Bool.cond_eq_ite, ite_eq_right hb, ite_eq_right hf]
  · have hb : ¬ b6EvalSortedAccept A B c = true :=
      fun h => hc ((b6EvalSortedAccept_iff A B c).mp h)
    rw [Bool.cond_eq_ite, ite_eq_right hb]
    simp only [hc, false_and, ite_false, Finset.sum_const_zero]
#print axioms Paper7MomentCounts.b6W6EvalQSplitSum_eq_symbolic

theorem b6W6EvalQSplitSum_eq (Z R A B Q : ℕ) :
    b6W6EvalQSplitSum Z R A B Q = b6EvalQSplitSum Z R A B Q := by
  rw [b6W6EvalQSplitSum_eq_symbolic,
    ← labelledTripleKernelQSplitSum_eq_W6, b6EvalQSplitSum_eq]
#print axioms Paper7MomentCounts.b6W6EvalQSplitSum_eq

end Paper7MomentCounts
