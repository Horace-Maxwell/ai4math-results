import Research.Backfill.Paper7.MomentB6SixTripleConvolutionV2
import Research.Backfill.Paper7.LegacyCandidates

/-! Source-only transport for the literal original PQ abbreviation.
All statistic fibres count ordered PQ rows, not spectral witnesses or statistic tuples.
The six-coordinate convolution source is pending. Original contracts are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev labelledOriginalPQStatisticFibre (n A B Q : ℕ) :=
  {x : PQ n // (∑ i, (x.1 i + x.2 i)) = A ∧
    (∑ i, (x.1 i + x.2 i)^2) = B ∧ qSum x = Q}
#print axioms Paper7MomentCounts.labelledOriginalPQStatisticFibre

def labelledOriginalPQStatisticEquiv (n A B Q : ℕ) :
    labelledOriginalPQStatisticFibre n A B Q ≃ labelledCapacityQFibre n A B Q where
  toFun x := ⟨(fun i => x.val.1 i + x.val.2 i, x.val.2),
    ⟨fun _i => Nat.le_add_left _ _, x.property.1, x.property.2.1, x.property.2.2⟩⟩
  invFun y := ⟨(fun i => y.val.1 i - y.val.2 i, y.val.2), by
    have hc (i : Fin n) : (y.val.1 i - y.val.2 i) + y.val.2 i = y.val.1 i :=
      Nat.sub_add_cancel (y.property.1 i)
    refine ⟨?_, ?_, y.property.2.2.2⟩
    · change (∑ i, ((y.val.1 i-y.val.2 i)+y.val.2 i)) = A
      simp_rw [hc]
      exact y.property.2.1
    · change (∑ i, ((y.val.1 i-y.val.2 i)+y.val.2 i)^2) = B
      simp_rw [hc]
      exact y.property.2.2.1⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact Nat.add_sub_cancel_right _ _
    · rfl
  right_inv y := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact Nat.sub_add_cancel (y.property.1 i)
    · rfl
#print axioms Paper7MomentCounts.labelledOriginalPQStatisticEquiv

theorem labelledOriginalPQStatisticFibre_card (n A B Q : ℕ) :
    Nat.card (labelledOriginalPQStatisticFibre n A B Q) =
      labelledExactCapacityQCard n A B Q :=
  Nat.card_congr (labelledOriginalPQStatisticEquiv n A B Q)
#print axioms Paper7MomentCounts.labelledOriginalPQStatisticFibre_card

instance labelledOriginalPQStatisticFibre_six_finite (Z R Q : ℕ) :
    Finite (labelledOriginalPQStatisticFibre 6 Z R Q) :=
  Finite.of_equiv (labelledSixTriplePair Z R Q)
    ((labelledSixTripleEquiv Z R Q).symm.trans (labelledOriginalPQStatisticEquiv 6 Z R Q).symm)
#print axioms Paper7MomentCounts.labelledOriginalPQStatisticFibre_six_finite

def labelledOriginalPQSixTripleEquiv (Z R Q : ℕ) :
    labelledOriginalPQStatisticFibre 6 Z R Q ≃ labelledSixTriplePair Z R Q :=
  (labelledOriginalPQStatisticEquiv 6 Z R Q).trans (labelledSixTripleEquiv Z R Q)
#print axioms Paper7MomentCounts.labelledOriginalPQSixTripleEquiv

theorem labelledOriginalPQ_six_actual_triple_convolution (Z R Q : ℕ) :
    Nat.card (labelledOriginalPQStatisticFibre 6 Z R Q) =
      ∑ A ∈ Finset.range (Z+1), ∑ B ∈ Finset.range (R+1), ∑ t ∈ Finset.range (Q+1),
        Nat.card (labelledOriginalPQStatisticFibre 3 A B t) *
          Nat.card (labelledOriginalPQStatisticFibre 3 (Z-A) (R-B) (Q-t)) := by
  simp only [labelledOriginalPQStatisticFibre_card, labelledExactCapacityQCard_six_convolution]
#print axioms Paper7MomentCounts.labelledOriginalPQ_six_actual_triple_convolution

theorem labelledOriginalPQ_six_kernel_statistic_pruned (Z R Q : ℕ) :
    (Nat.card (labelledOriginalPQStatisticFibre 6 Z R Q) : ℤ) =
      ∑ A ∈ Finset.range (Z+1), ∑ B ∈ Finset.range (R+1),
        if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
          ∑ t ∈ labelledTripleQSplitRange Z A Q,
            labelledTripleDiscriminantKernel A B t *
              labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t)
        else 0 := by
  rw [labelledOriginalPQStatisticFibre_card]
  exact labelledExactCapacityQCard_six_kernel_statistic_pruned Z R Q
#print axioms Paper7MomentCounts.labelledOriginalPQ_six_kernel_statistic_pruned

theorem labelledOriginalPQStatistic_weight (n A B Q : ℕ)
    (x : labelledOriginalPQStatisticFibre n A B Q) : weight x.val = A+Q := by
  have ha := x.property.1
  rw [Finset.sum_add_distrib] at ha
  have hq : (∑ i, x.val.2 i) = Q := x.property.2.2
  change (∑ i, x.val.1 i) + 2*(∑ i, x.val.2 i) = A+Q
  omega
#print axioms Paper7MomentCounts.labelledOriginalPQStatistic_weight

theorem labelledOriginalPQStatistic_theta (n A B Q : ℕ)
    (x : labelledOriginalPQStatisticFibre n A B Q) :
    theta x.val = 2*(n : ℤ)+3*(A : ℤ)+2*(Q : ℤ)+(B : ℤ) := by
  have ha : (∑ i, ((x.val.1 i+x.val.2 i : ℕ) : ℤ)) = A := by
    exact_mod_cast x.property.1
  have hb : (∑ i, ((x.val.1 i+x.val.2 i : ℕ) : ℤ)^2) = B := by
    exact_mod_cast x.property.2.1
  have hqN : (∑ i, x.val.2 i) = Q := x.property.2.2
  have hq : (∑ i, (x.val.2 i : ℤ)) = Q := by exact_mod_cast hqN
  have ht (i : Fin n) : thetaV (x.val.1 i) (x.val.2 i) =
      ((x.val.1 i+x.val.2 i : ℕ) : ℤ)^2 +
        3*((x.val.1 i+x.val.2 i : ℕ) : ℤ)+2+2*(x.val.2 i : ℤ) := by
    unfold thetaV
    push_cast
    ring
  calc
    theta x.val = (∑ i, ((x.val.1 i+x.val.2 i : ℕ) : ℤ)^2) +
        3*(∑ i, ((x.val.1 i+x.val.2 i : ℕ) : ℤ)) + 2*(n : ℤ) +
        2*(∑ i, (x.val.2 i : ℤ)) := by
      unfold theta
      simp_rw [ht]
      simp only [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ = (B : ℤ)+3*(A : ℤ)+2*(n : ℤ)+2*(Q : ℤ) := by rw [ha,hb,hq]
    _ = 2*(n : ℤ)+3*(A : ℤ)+2*(Q : ℤ)+(B : ℤ) := by ring
#print axioms Paper7MomentCounts.labelledOriginalPQStatistic_theta

theorem labelledOriginalPQStatistic_budget_iff (n N A B Q : ℕ)
    (x : labelledOriginalPQStatisticFibre n A B Q) :
    Budget n N x.val ↔ 0 < A+Q ∧ n+(A+Q) ≤ N := by
  unfold Budget
  rw [labelledOriginalPQStatistic_weight n A B Q x]
#print axioms Paper7MomentCounts.labelledOriginalPQStatistic_budget_iff

theorem labelledOriginalPQStatistic_six_budget_bounds (Z R Q : ℕ)
    (x : labelledOriginalPQStatisticFibre 6 Z R Q) (h : Budget 6 42 x.val) :
    0 < Z+Q ∧ Z+Q ≤ 36 ∧ Q ≤ Z ∧ Q ≤ 18 ∧ Z ≤ 36 ∧ R ≤ Z^2 := by
  have hb := (labelledOriginalPQStatistic_budget_iff 6 42 Z R Q x).mp h
  have hq := labelledCapacityQFibre_q_le 6 Z R Q (labelledOriginalPQStatisticEquiv 6 Z R Q x)
  have hr := labelledCapacityQFibre_square_sum_le 6 Z R Q
    (labelledOriginalPQStatisticEquiv 6 Z R Q x)
  omega
#print axioms Paper7MomentCounts.labelledOriginalPQStatistic_six_budget_bounds

end Paper7MomentCounts
