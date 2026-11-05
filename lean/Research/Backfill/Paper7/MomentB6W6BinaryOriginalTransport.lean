import Research.Backfill.Paper7.MomentB6W6BinaryWeight

/-! NEW uncompiled full-domain transport of the binary/zero-shortcut weight.
All original ranges, full A, guards, ordered coordinates and multiplicities
remain. No numerical source or concrete value is introduced. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6W6FastEvalQSplitSum (Z R A B Q : ℕ) : ℤ :=
  ∑ c ∈ b6EvalScalarRange A B,
    bif b6EvalSortedAccept A B c then
      ∑ f ∈ b6EvalScalarRange (Z-A) (R-B),
        bif b6EvalSortedAccept (Z-A) (R-B) f then
          (b6EvalMultiplicity c (b6EvalHigh A B c) (b6EvalLow A B c) : ℤ) *
          (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
            (b6EvalLow (Z-A) (R-B) f) : ℤ) *
          b6W6FastWeight
            ![c, b6EvalHigh A B c, b6EvalLow A B c,
              f, b6EvalHigh (Z-A) (R-B) f, b6EvalLow (Z-A) (R-B) f] Q
        else 0
    else 0
#print axioms Paper7MomentCounts.b6W6FastEvalQSplitSum

def b6W6FastEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  ∑ B ∈ b6EvalBRange Z (b6EvalResidual sm Z Q) A,
    bif (b6EvalTripleGuard A B &&
      b6EvalTripleGuard (Z-A) (b6EvalResidual sm Z Q-B)) then
      b6W6FastEvalQSplitSum Z (b6EvalResidual sm Z Q) A B Q else 0
#print axioms Paper7MomentCounts.b6W6FastEvalASlice

def b6W6FastEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    ∑ A ∈ Finset.range (Z+1), b6W6FastEvalASlice sm Z Q A else 0
#print axioms Paper7MomentCounts.b6W6FastEvalBlock

def b6W6FastEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  ∑ Z ∈ b6EvalZRange sm Q, b6W6FastEvalBlock sm Z Q
#print axioms Paper7MomentCounts.b6W6FastEvalQSlice

def b6W6FastEvalTotal (sm : ℤ × ℤ) : ℤ :=
  ∑ Q ∈ Finset.range 19, b6W6FastEvalQSlice sm Q
#print axioms Paper7MomentCounts.b6W6FastEvalTotal

theorem b6W6FastEvalQSplitSum_eq (Z R A B Q : ℕ) :
    b6W6FastEvalQSplitSum Z R A B Q = b6W6EvalQSplitSum Z R A B Q := by
  simp only [b6W6FastEvalQSplitSum, b6W6EvalQSplitSum, b6W6FastWeight_eq]
#print axioms Paper7MomentCounts.b6W6FastEvalQSplitSum_eq

theorem b6W6FastEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6W6FastEvalASlice sm Z Q A = b6W6EvalASlice sm Z Q A := by
  simp only [b6W6FastEvalASlice, b6W6EvalASlice, b6W6FastEvalQSplitSum_eq]
#print axioms Paper7MomentCounts.b6W6FastEvalASlice_eq

theorem b6W6FastEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6W6FastEvalBlock sm Z Q = b6W6EvalBlock sm Z Q := by
  simp only [b6W6FastEvalBlock, b6W6EvalBlock, b6W6FastEvalASlice_eq]
#print axioms Paper7MomentCounts.b6W6FastEvalBlock_eq

theorem b6W6FastEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6W6FastEvalQSlice sm Q = b6W6EvalQSlice sm Q := by
  simp only [b6W6FastEvalQSlice, b6W6EvalQSlice, b6W6FastEvalBlock_eq]
#print axioms Paper7MomentCounts.b6W6FastEvalQSlice_eq

theorem b6W6FastEvalTotal_eq (sm : ℤ × ℤ) :
    b6W6FastEvalTotal sm = b6W6EvalTotal sm := by
  simp only [b6W6FastEvalTotal, b6W6EvalTotal, b6W6FastEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6W6FastEvalTotal_eq

theorem b6W6FastEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6W6FastEvalTotal sm = ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6W6FastEvalTotal_eq]
  exact b6W6EvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6W6FastEvalTotal_eq_original_B1_theta

theorem b6W6FastEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6W6FastEvalTotal sm) = ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6W6FastEvalTotal_eq]
  exact b6W6EvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6W6FastEvalTotal_sum_eq_original_B1

theorem b6W6FastEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6W6FastEvalTotal sm = ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6W6FastEvalTotal_eq]
  exact b6W6EvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6W6FastEvalTotal_eq_original_D2_theta

theorem b6W6FastEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6W6FastEvalTotal sm) = ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6W6FastEvalTotal_eq]
  exact b6W6EvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6W6FastEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
