import Research.Backfill.Paper7.MomentB6W6TripleConvolution
import Research.Backfill.Paper7.MomentB6BSupportPruning

/-! NEW uncompiled candidate. Unit 4: interchange finite sums and replace
the t convolution for each accepted ordered pair of triple shapes by W6.
The complete A range is retained by every downstream caller. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open scoped BigOperators Classical

def labelledTripleKernelW6Sum (Z R A B Q : ℕ) : ℤ :=
  ∑ c ∈ labelledTripleScalarRange A B,
    ∑ f ∈ labelledTripleScalarRange (Z-A) (R-B),
      if B6SortedTripleDiscriminantAccept A B c ∧
          B6SortedTripleDiscriminantAccept (Z-A) (R-B) f then
        (labelledSortedTripleMultiplicity c
          (labelledTripleHigh A B c) (labelledTripleLow A B c) : ℤ) *
        (labelledSortedTripleMultiplicity f
          (labelledTripleHigh (Z-A) (R-B) f) (labelledTripleLow (Z-A) (R-B) f) : ℤ) *
        labelledSixQWeight (labelledJoinedTripleCapacity A B c (Z-A) (R-B) f) Q
      else 0
#print axioms Paper7MomentCounts.labelledTripleKernelW6Sum

theorem labelledTripleKernelQSplitSum_eq_W6 (Z R A B Q : ℕ) :
    labelledTripleKernelQSplitSum Z R A B Q = labelledTripleKernelW6Sum Z R A B Q := by
  unfold labelledTripleKernelQSplitSum labelledTripleDiscriminantKernel
    labelledTripleKernelW6Sum
  simp_rw [Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _hf
  by_cases hc : B6SortedTripleDiscriminantAccept A B c
  · by_cases hf : B6SortedTripleDiscriminantAccept (Z-A) (R-B) f
    · simp only [hc, hf, and_self, ite_true]
      have hu := (labelled_sorted_triple_decode_sound A B c hc).2.2.1
      have hv := (labelled_sorted_triple_decode_sound (Z-A) (R-B) f hf).2.2.1
      have hconv :
          (∑ t ∈ labelledTripleQSplitRange Z A Q,
            labelledTripleQWeight c (labelledTripleHigh A B c) (labelledTripleLow A B c) t *
              labelledTripleQWeight f (labelledTripleHigh (Z-A) (R-B) f)
                (labelledTripleLow (Z-A) (R-B) f) (Q-t)) =
            labelledSixQWeight (labelledJoinedTripleCapacity A B c (Z-A) (R-B) f) Q := by
        simpa only [b6W6QSplitRange, labelledTripleQSplitRange, hu, hv,
          b6W6JoinedCapacity, labelledJoinedTripleCapacity] using
          (labelledTripleQWeight_convolution_W6
            (c, labelledTripleHigh A B c, labelledTripleLow A B c)
            (f, labelledTripleHigh (Z-A) (R-B) f, labelledTripleLow (Z-A) (R-B) f) Q)
      calc
        (∑ t ∈ labelledTripleQSplitRange Z A Q,
          (labelledSortedTripleMultiplicity c
            (labelledTripleHigh A B c) (labelledTripleLow A B c) : ℤ) *
            labelledTripleQWeight c (labelledTripleHigh A B c) (labelledTripleLow A B c) t *
          ((labelledSortedTripleMultiplicity f
            (labelledTripleHigh (Z-A) (R-B) f) (labelledTripleLow (Z-A) (R-B) f) : ℤ) *
            labelledTripleQWeight f (labelledTripleHigh (Z-A) (R-B) f)
              (labelledTripleLow (Z-A) (R-B) f) (Q-t))) =
          ((labelledSortedTripleMultiplicity c
            (labelledTripleHigh A B c) (labelledTripleLow A B c) : ℤ) *
          (labelledSortedTripleMultiplicity f
            (labelledTripleHigh (Z-A) (R-B) f) (labelledTripleLow (Z-A) (R-B) f) : ℤ)) *
          ∑ t ∈ labelledTripleQSplitRange Z A Q,
            labelledTripleQWeight c (labelledTripleHigh A B c) (labelledTripleLow A B c) t *
              labelledTripleQWeight f (labelledTripleHigh (Z-A) (R-B) f)
                (labelledTripleLow (Z-A) (R-B) f) (Q-t) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _ht
            ring
        _ = _ := by rw [hconv]
    · simp only [hc, hf, and_false, ite_true, ite_false, mul_zero, Finset.sum_const_zero]
  · simp only [hc, false_and, ite_false, zero_mul, Finset.sum_const_zero]
#print axioms Paper7MomentCounts.labelledTripleKernelQSplitSum_eq_W6

end Paper7MomentCounts
