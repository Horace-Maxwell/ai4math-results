import Research.Backfill.Paper7.MomentB6ThetaConvolutionTransport

/-! Uncompiled support reduction. The four sealed ancestors remain pending.
All sums preserve the original ordered-row count. The interval is a necessary
support bound; both original triple guards stay in the narrowed expression,
including when a Nat subtraction in the upper endpoint truncates to zero. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

theorem b6_nat_ceil_third_le_iff (n b : ℕ) : (n+2)/3 ≤ b ↔ n ≤ 3*b := by
  omega
#print axioms Paper7MomentCounts.b6_nat_ceil_third_le_iff

def labelledTripleBSplitLower (Z R A : ℕ) : ℕ :=
  max ((A^2+2)/3) (R-(Z-A)^2)
#print axioms Paper7MomentCounts.labelledTripleBSplitLower

def labelledTripleBSplitUpper (Z R A : ℕ) : ℕ :=
  min (A^2) (R-((Z-A)^2+2)/3)
#print axioms Paper7MomentCounts.labelledTripleBSplitUpper

def labelledTripleBSplitRange (Z R A : ℕ) : Finset ℕ :=
  (Finset.Icc (labelledTripleBSplitLower Z R A) (labelledTripleBSplitUpper Z R A)).filter
    (fun B => B%2 = A%2)
#print axioms Paper7MomentCounts.labelledTripleBSplitRange

theorem labelledTripleStatisticGuards_mem_BSplitRange (Z R A B : ℕ) (hB : B ≤ R)
    (hg : B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B)) :
    B ∈ labelledTripleBSplitRange Z R A := by
  have hl : (A^2+2)/3 ≤ B := (b6_nat_ceil_third_le_iff (A^2) B).mpr hg.1.1
  have hr : ((Z-A)^2+2)/3 ≤ R-B :=
    (b6_nat_ceil_third_le_iff ((Z-A)^2) (R-B)).mpr hg.2.1
  have hul : B ≤ A^2 := hg.1.2.1
  have hur : R-B ≤ (Z-A)^2 := hg.2.2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Icc.mpr ?_,hg.1.2.2⟩
  change max ((A^2+2)/3) (R-(Z-A)^2) ≤ B ∧ B ≤ min (A^2) (R-((Z-A)^2+2)/3)
  exact ⟨max_le hl (by omega),le_min hul (by omega)⟩
#print axioms Paper7MomentCounts.labelledTripleStatisticGuards_mem_BSplitRange

theorem labelledTripleBSplitRange_subset (Z R A : ℕ) :
    labelledTripleBSplitRange Z R A ⊆ Finset.range (R+1) := by
  intro B hB
  have hu := (Finset.mem_Icc.mp (Finset.mem_filter.mp hB).1).2
  change B ≤ min (A^2) (R-((Z-A)^2+2)/3) at hu
  have hs := Nat.sub_le R (((Z-A)^2+2)/3)
  apply Finset.mem_range.mpr
  omega
#print axioms Paper7MomentCounts.labelledTripleBSplitRange_subset

theorem labelledTripleStatisticGuards_total_parity (Z R A B : ℕ) (hA : A ≤ Z) (hB : B ≤ R)
    (hg : B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B)) :
    R%2 = Z%2 := by
  have hbr : B+(R-B) = R := by omega
  have haz : A+(Z-A) = Z := by omega
  calc
    R%2 = (B+(R-B))%2 := congrArg (fun n : ℕ => n%2) hbr.symm
    _ = (A+(Z-A))%2 := by
      rw [Nat.add_mod B (R-B) 2, Nat.add_mod A (Z-A) 2, hg.1.2.2, hg.2.2.2]
    _ = Z%2 := congrArg (fun n : ℕ => n%2) haz
#print axioms Paper7MomentCounts.labelledTripleStatisticGuards_total_parity

def labelledTripleKernelQSplitSum (Z R A B Q : ℕ) : ℤ :=
  ∑ t ∈ labelledTripleQSplitRange Z A Q,
    labelledTripleDiscriminantKernel A B t *
      labelledTripleDiscriminantKernel (Z-A) (R-B) (Q-t)
#print axioms Paper7MomentCounts.labelledTripleKernelQSplitSum

theorem labelledTripleKernelQSplitSum_zero_of_bad_statistics (Z R A B Q : ℕ)
    (hg : ¬ (B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B))) :
    labelledTripleKernelQSplitSum Z R A B Q = 0 := by
  apply Finset.sum_eq_zero
  intro t _ht
  by_cases hl : B6TripleStatisticGuard A B
  · have hr : ¬ B6TripleStatisticGuard (Z-A) (R-B) := fun h => hg ⟨hl,h⟩
    rw [labelledTripleDiscriminantKernel_zero_of_bad_statistics (Z-A) (R-B) (Q-t) hr,mul_zero]
  · rw [labelledTripleDiscriminantKernel_zero_of_bad_statistics A B t hl,zero_mul]
#print axioms Paper7MomentCounts.labelledTripleKernelQSplitSum_zero_of_bad_statistics

theorem labelledTripleKernelQSplitSum_eq_guarded (Z R A B Q : ℕ) :
    labelledTripleKernelQSplitSum Z R A B Q =
      if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
        labelledTripleKernelQSplitSum Z R A B Q else 0 := by
  by_cases hg : B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B)
  · exact (ite_eq_left hg).symm
  · rw [ite_eq_right hg]
    exact labelledTripleKernelQSplitSum_zero_of_bad_statistics Z R A B Q hg
#print axioms Paper7MomentCounts.labelledTripleKernelQSplitSum_eq_guarded

theorem labelledTripleKernelQSplitSum_zero_outside_BSplitRange (Z R A B Q : ℕ)
    (hB : B ≤ R) (hn : B ∉ labelledTripleBSplitRange Z R A) :
    labelledTripleKernelQSplitSum Z R A B Q = 0 := by
  apply labelledTripleKernelQSplitSum_zero_of_bad_statistics
  exact fun hg => hn (labelledTripleStatisticGuards_mem_BSplitRange Z R A B hB hg)
#print axioms Paper7MomentCounts.labelledTripleKernelQSplitSum_zero_outside_BSplitRange

theorem labelledTripleKernel_B_range_eq_support (Z R A Q : ℕ) :
    (∑ B ∈ Finset.range (R+1), labelledTripleKernelQSplitSum Z R A B Q) =
      ∑ B ∈ labelledTripleBSplitRange Z R A, labelledTripleKernelQSplitSum Z R A B Q := by
  symm
  apply Finset.sum_subset (labelledTripleBSplitRange_subset Z R A)
  intro B hB hn
  have hb : B ≤ R := by have h := Finset.mem_range.mp hB; omega
  exact labelledTripleKernelQSplitSum_zero_outside_BSplitRange Z R A B Q hb hn
#print axioms Paper7MomentCounts.labelledTripleKernel_B_range_eq_support

theorem labelledTripleKernel_guarded_B_range_eq_support (Z R A Q : ℕ) :
    (∑ B ∈ Finset.range (R+1),
      if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
        labelledTripleKernelQSplitSum Z R A B Q else 0) =
      ∑ B ∈ labelledTripleBSplitRange Z R A,
        if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
          labelledTripleKernelQSplitSum Z R A B Q else 0 := by
  calc
    (∑ B ∈ Finset.range (R+1),
      if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
        labelledTripleKernelQSplitSum Z R A B Q else 0) =
        ∑ B ∈ Finset.range (R+1), labelledTripleKernelQSplitSum Z R A B Q := by
      apply Finset.sum_congr rfl
      intro B _hB
      exact (labelledTripleKernelQSplitSum_eq_guarded Z R A B Q).symm
    _ = ∑ B ∈ labelledTripleBSplitRange Z R A, labelledTripleKernelQSplitSum Z R A B Q :=
      labelledTripleKernel_B_range_eq_support Z R A Q
    _ = ∑ B ∈ labelledTripleBSplitRange Z R A,
        if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
          labelledTripleKernelQSplitSum Z R A B Q else 0 := by
      apply Finset.sum_congr rfl
      intro B _hB
      exact labelledTripleKernelQSplitSum_eq_guarded Z R A B Q
#print axioms Paper7MomentCounts.labelledTripleKernel_guarded_B_range_eq_support

theorem labelledTripleKernelQSplitSum_zero_of_parity (Z R A B Q : ℕ)
    (hA : A ≤ Z) (hB : B ≤ R) (hp : R%2 ≠ Z%2) :
    labelledTripleKernelQSplitSum Z R A B Q = 0 := by
  apply labelledTripleKernelQSplitSum_zero_of_bad_statistics
  exact fun hg => hp (labelledTripleStatisticGuards_total_parity Z R A B hA hB hg)
#print axioms Paper7MomentCounts.labelledTripleKernelQSplitSum_zero_of_parity

theorem labelledTripleKernel_B_sum_zero_of_parity (Z R A Q : ℕ)
    (hA : A ≤ Z) (hp : R%2 ≠ Z%2) :
    (∑ B ∈ Finset.range (R+1), labelledTripleKernelQSplitSum Z R A B Q) = 0 := by
  apply Finset.sum_eq_zero
  intro B hB
  have hb : B ≤ R := by have h := Finset.mem_range.mp hB; omega
  exact labelledTripleKernelQSplitSum_zero_of_parity Z R A B Q hA hb hp
#print axioms Paper7MomentCounts.labelledTripleKernel_B_sum_zero_of_parity

theorem labelledExactCapacityQCard_six_kernel_B_pruned (Z R Q : ℕ) :
    (labelledExactCapacityQCard 6 Z R Q : ℤ) =
      ∑ A ∈ Finset.range (Z+1), ∑ B ∈ labelledTripleBSplitRange Z R A,
        if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
          labelledTripleKernelQSplitSum Z R A B Q else 0 := by
  rw [labelledExactCapacityQCard_six_kernel_statistic_pruned]
  apply Finset.sum_congr rfl
  intro A _hA
  exact labelledTripleKernel_guarded_B_range_eq_support Z R A Q
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_six_kernel_B_pruned

theorem labelledExactCapacityQCard_six_kernel_B_parity_pruned (Z R Q : ℕ) :
    (labelledExactCapacityQCard 6 Z R Q : ℤ) =
      if R%2 = Z%2 then
        ∑ A ∈ Finset.range (Z+1), ∑ B ∈ labelledTripleBSplitRange Z R A,
          if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
            labelledTripleKernelQSplitSum Z R A B Q else 0
      else 0 := by
  by_cases hp : R%2 = Z%2
  · rw [ite_eq_left hp]
    exact labelledExactCapacityQCard_six_kernel_B_pruned Z R Q
  · rw [ite_eq_right hp,labelledExactCapacityQCard_six_kernel_q_pruned]
    apply Finset.sum_eq_zero
    intro A hA
    have ha : A ≤ Z := by have h := Finset.mem_range.mp hA; omega
    exact labelledTripleKernel_B_sum_zero_of_parity Z R A Q ha hp
#print axioms Paper7MomentCounts.labelledExactCapacityQCard_six_kernel_B_parity_pruned

theorem labelledOriginalPQ_six_kernel_B_parity_pruned (Z R Q : ℕ) :
    (Nat.card (labelledOriginalPQStatisticFibre 6 Z R Q) : ℤ) =
      if R%2 = Z%2 then
        ∑ A ∈ Finset.range (Z+1), ∑ B ∈ labelledTripleBSplitRange Z R A,
          if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (R-B) then
            labelledTripleKernelQSplitSum Z R A B Q else 0
      else 0 := by
  rw [labelledOriginalPQStatisticFibre_card]
  exact labelledExactCapacityQCard_six_kernel_B_parity_pruned Z R Q
#print axioms Paper7MomentCounts.labelledOriginalPQ_six_kernel_B_parity_pruned

def b6CatalogBSupportASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  ∑ B ∈ labelledTripleBSplitRange Z (b6CatalogResidual sm Z Q) A,
    if B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (b6CatalogResidual sm Z Q-B) then
      labelledTripleKernelQSplitSum Z (b6CatalogResidual sm Z Q) A B Q else 0
#print axioms Paper7MomentCounts.b6CatalogBSupportASlice

theorem b6CatalogConvolutionBlock_eq_B_support (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6CatalogConvolutionBlock sm Z Q =
      if b6CatalogStatisticAccept sm Z Q then
        ∑ A ∈ Finset.range (Z+1), b6CatalogBSupportASlice sm Z Q A else 0 := by
  unfold b6CatalogConvolutionBlock
  by_cases ha : b6CatalogStatisticAccept sm Z Q
  · rw [ite_eq_left ha,ite_eq_left ha]
    apply Finset.sum_congr rfl
    intro A _hA
    exact labelledTripleKernel_guarded_B_range_eq_support Z (b6CatalogResidual sm Z Q) A Q
  · rw [ite_eq_right ha,ite_eq_right ha]
#print axioms Paper7MomentCounts.b6CatalogConvolutionBlock_eq_B_support

def b6CatalogBSupportQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  ∑ Z ∈ b6CatalogZRange sm Q,
    if b6CatalogStatisticAccept sm Z Q then
      ∑ A ∈ Finset.range (Z+1), b6CatalogBSupportASlice sm Z Q A else 0
#print axioms Paper7MomentCounts.b6CatalogBSupportQSlice

theorem b6CatalogConvolutionQSlice_eq_B_support (sm : ℤ × ℤ) (Q : ℕ) :
    b6CatalogConvolutionQSlice sm Q = b6CatalogBSupportQSlice sm Q := by
  apply Finset.sum_congr rfl
  intro Z _hZ
  exact b6CatalogConvolutionBlock_eq_B_support sm Z Q
#print axioms Paper7MomentCounts.b6CatalogConvolutionQSlice_eq_B_support

theorem b6CatalogBSupportQSlice_sum_eq_theta_ncard (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    (∑ Q ∈ Finset.range 19, b6CatalogBSupportQSlice sm Q) =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  calc
    (∑ Q ∈ Finset.range 19, b6CatalogBSupportQSlice sm Q) = b6CatalogConvolutionTotal sm := by
      apply Finset.sum_congr rfl
      intro Q _hQ
      exact (b6CatalogConvolutionQSlice_eq_B_support sm Q).symm
    _ = ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) :=
      b6CatalogConvolutionTotal_eq_theta_ncard sm hsm
#print axioms Paper7MomentCounts.b6CatalogBSupportQSlice_sum_eq_theta_ncard

end Paper7MomentCounts
