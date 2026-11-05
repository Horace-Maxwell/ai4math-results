import Research.Backfill.Paper7.MomentB6StructuralProductFastW6

/-! Full-parameter residual necessary-condition pruning. The five complete
actual975 computation layers retain every range, guard, structural sum,
multiplicity and product weight. Only the outer ASlice decision is new.
No numerical candidate, resource change or speedup claim is included. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6SortedLeftBGuard_false_of_residual_large (Z R A B : ℕ)
    (h : A^2 + (Z-A)^2 < R) :
    b6SortedLeftBGuard Z R A B = false := by
  apply Bool.eq_false_iff.mpr
  intro hg
  simp only [b6SortedLeftBGuard, Bool.and_eq_true, decide_eq_true_eq,
    max_le_iff, le_min_iff, and_assoc] at hg
  have hlow : R-(Z-A)^2 ≤ B := hg.2.1
  have hhigh : B ≤ A^2 := hg.2.2.1
  have hR : R ≤ B + (Z-A)^2 := Nat.sub_le_iff_le_add.mp hlow
  omega
#print axioms Paper7MomentCounts.b6SortedLeftBGuard_false_of_residual_large

theorem b6StructuralProductFastASliceRaw_eq_zero_of_residual_large (Z R A Q : ℕ)
    (h : A^2 + (Z-A)^2 < R) :
    b6StructuralProductFastASliceRaw Z R A Q = 0 := by
  simp only [b6StructuralProductFastASliceRaw, b6StructuralIccSum_eq]
  apply Finset.sum_eq_zero
  intro c _hc
  apply Finset.sum_eq_zero
  intro a _ha
  simp only [b6SortedLeftBGuard_false_of_residual_large Z R A (b6SortedLeftSquares A c a) h,
    Bool.cond_false]
#print axioms Paper7MomentCounts.b6StructuralProductFastASliceRaw_eq_zero_of_residual_large

def b6StructuralResidualPrunedASliceRaw (Z R A Q : ℕ) : ℤ :=
  bif decide (R ≤ A^2 + (Z-A)^2) then
    b6StructuralIccSum (fun c =>
      b6StructuralIccSum (fun a =>
        bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
          b6StructuralProductFastTerm Z R A Q (b6SortedLeftSquares A c a) c a (b6SortedLeftLow A c a)
        else 0)
        ((A-c+1)/2) (min c (A-c)))
      ((A+2)/3) A

  else 0
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedASliceRaw

theorem b6StructuralResidualPrunedASliceRaw_eq (Z R A Q : ℕ) :
    b6StructuralResidualPrunedASliceRaw Z R A Q = b6StructuralProductFastASliceRaw Z R A Q := by
  by_cases h : R ≤ A^2 + (Z-A)^2
  · simp only [b6StructuralResidualPrunedASliceRaw, decide_eq_true h, Bool.cond_true,
      b6StructuralProductFastASliceRaw]
  · have hlarge : A^2 + (Z-A)^2 < R := by omega
    rw [b6StructuralProductFastASliceRaw_eq_zero_of_residual_large Z R A Q hlarge]
    simp only [b6StructuralResidualPrunedASliceRaw, decide_eq_false h, Bool.cond_false]
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedASliceRaw_eq

def b6StructuralResidualPrunedEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6StructuralResidualPrunedASliceRaw Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalASlice

theorem b6StructuralResidualPrunedEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6StructuralResidualPrunedEvalASlice sm Z Q A = b6StructuralProductFastEvalASlice sm Z Q A := by
  simp only [b6StructuralResidualPrunedEvalASlice, b6StructuralProductFastEvalASlice,
    b6StructuralResidualPrunedASliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalASlice_eq

def b6StructuralResidualPrunedEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6StructuralRangeOffset (fun A => b6StructuralResidualPrunedEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalBlock

theorem b6StructuralResidualPrunedEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6StructuralResidualPrunedEvalBlock sm Z Q = b6StructuralProductFastEvalBlock sm Z Q := by
  simp only [b6StructuralResidualPrunedEvalBlock, b6StructuralProductFastEvalBlock,
    b6StructuralResidualPrunedEvalASlice_eq]
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalBlock_eq

def b6StructuralResidualPrunedEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun Z => b6StructuralResidualPrunedEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalQSlice

theorem b6StructuralResidualPrunedEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6StructuralResidualPrunedEvalQSlice sm Q = b6StructuralProductFastEvalQSlice sm Q := by
  simp only [b6StructuralResidualPrunedEvalQSlice, b6StructuralProductFastEvalQSlice,
    b6StructuralResidualPrunedEvalBlock_eq]
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalQSlice_eq

def b6StructuralResidualPrunedEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6StructuralRangeOffset (fun Q => b6StructuralResidualPrunedEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalTotal

theorem b6StructuralResidualPrunedEvalTotal_eq (sm : ℤ × ℤ) :
    b6StructuralResidualPrunedEvalTotal sm = b6StructuralProductFastEvalTotal sm := by
  simp only [b6StructuralResidualPrunedEvalTotal, b6StructuralProductFastEvalTotal,
    b6StructuralResidualPrunedEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalTotal_eq

theorem b6StructuralResidualPrunedEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralResidualPrunedEvalTotal_eq]
  exact b6StructuralProductFastEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalTotal_eq_original_B1_theta

theorem b6StructuralResidualPrunedEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralResidualPrunedEvalTotal_eq]
  exact b6StructuralProductFastEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalTotal_eq_original_D2_theta

theorem b6StructuralResidualPrunedEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralResidualPrunedEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralResidualPrunedEvalTotal_eq]
  exact b6StructuralProductFastEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalTotal_sum_eq_original_B1

theorem b6StructuralResidualPrunedEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralResidualPrunedEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralResidualPrunedEvalTotal_eq]
  exact b6StructuralProductFastEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6StructuralResidualPrunedEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
