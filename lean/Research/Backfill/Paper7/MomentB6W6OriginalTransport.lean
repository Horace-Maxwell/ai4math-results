import Research.Backfill.Paper7.MomentB6W6ComputableKernel

/-! NEW uncompiled candidate. Unit 6: retain every original outer range
and guard and transport the universal inner equality to original B1/D2
theta fibres and the complete labelled counts. No numerical count is asserted. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6W6EvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  ∑ B ∈ b6EvalBRange Z (b6EvalResidual sm Z Q) A,
    bif (b6EvalTripleGuard A B &&
      b6EvalTripleGuard (Z-A) (b6EvalResidual sm Z Q-B)) then
      b6W6EvalQSplitSum Z (b6EvalResidual sm Z Q) A B Q else 0
#print axioms Paper7MomentCounts.b6W6EvalASlice

def b6W6EvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    ∑ A ∈ Finset.range (Z+1), b6W6EvalASlice sm Z Q A else 0
#print axioms Paper7MomentCounts.b6W6EvalBlock

def b6W6EvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  ∑ Z ∈ b6EvalZRange sm Q, b6W6EvalBlock sm Z Q
#print axioms Paper7MomentCounts.b6W6EvalQSlice

def b6W6EvalTotal (sm : ℤ × ℤ) : ℤ :=
  ∑ Q ∈ Finset.range 19, b6W6EvalQSlice sm Q
#print axioms Paper7MomentCounts.b6W6EvalTotal

theorem b6W6EvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6W6EvalASlice sm Z Q A = b6EvalASlice sm Z Q A := by
  simp only [b6W6EvalASlice, b6EvalASlice, b6W6EvalQSplitSum_eq]
#print axioms Paper7MomentCounts.b6W6EvalASlice_eq

theorem b6W6EvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6W6EvalBlock sm Z Q = b6EvalBlock sm Z Q := by
  simp only [b6W6EvalBlock, b6EvalBlock, b6W6EvalASlice_eq]
#print axioms Paper7MomentCounts.b6W6EvalBlock_eq

theorem b6W6EvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6W6EvalQSlice sm Q = b6EvalQSlice sm Q := by
  simp only [b6W6EvalQSlice, b6EvalQSlice, b6W6EvalBlock_eq]
#print axioms Paper7MomentCounts.b6W6EvalQSlice_eq

theorem b6W6EvalTotal_eq (sm : ℤ × ℤ) :
    b6W6EvalTotal sm = b6EvalTotal sm := by
  simp only [b6W6EvalTotal, b6EvalTotal, b6W6EvalQSlice_eq]
#print axioms Paper7MomentCounts.b6W6EvalTotal_eq

theorem b6W6EvalTotal_eq_original_B1_theta (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6W6EvalTotal sm = ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6W6EvalTotal_eq]
  exact b6EvalTotal_eq_original_theta_ncard sm hsm
#print axioms Paper7MomentCounts.b6W6EvalTotal_eq_original_B1_theta

theorem b6W6EvalTotal_eq_original_D2_theta (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6W6EvalTotal sm = ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6W6EvalTotal_eq, b6EvalTotal_eq]
  exact b6CatalogConvolutionTotal_eq_theta_ncard_D2 sm hsm
#print axioms Paper7MomentCounts.b6W6EvalTotal_eq_original_D2_theta

theorem b6W6EvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6W6EvalTotal sm) = ((CandB1 6 42).ncard : ℤ) := by
  classical
  rw [b6_candB1_ncard_eq_catalog_Qslices]
  apply Finset.sum_congr rfl
  intro sm _hsm
  rw [b6W6EvalTotal_eq, b6EvalTotal_eq]
  rfl
#print axioms Paper7MomentCounts.b6W6EvalTotal_sum_eq_original_B1

theorem b6W6EvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6W6EvalTotal sm) = ((CandD2 6 42).ncard : ℤ) := by
  classical
  rw [b6_candD2_ncard_eq_catalog_Qslices]
  apply Finset.sum_congr rfl
  intro sm _hsm
  rw [b6W6EvalTotal_eq, b6EvalTotal_eq]
  rfl
#print axioms Paper7MomentCounts.b6W6EvalTotal_sum_eq_original_D2

end Paper7MomentCounts
