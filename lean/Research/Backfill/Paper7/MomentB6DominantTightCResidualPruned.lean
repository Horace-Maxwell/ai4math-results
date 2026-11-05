import Research.Backfill.Paper7.MomentB6TightCResidualPruned
import Research.Backfill.Paper7.MomentB6W6DominantFastWeight

/-! SOURCE ONLY. Both proved TightC bounds plus the dominant-coordinate weight.
The original A/c/a/Z/Q ranges, two c inequalities, catalog/B/triple guards,
multiplicities and structural recursions remain. Only the full-parameter
universally equal weight replaces the original product-weight call.
The TightC parent has real Windows compile/checker receipts; the imported
Dominant weight is still uncompiled. No weakC transport module is imported. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6StructuralDominantTightFastTerm (Z R A Q B c a b : ℕ) : ℤ :=
  bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) then
    b6StructuralIccSum (fun f =>
      bif b6EvalSortedAccept (Z-A) (R-B) f then
        (b6EvalMultiplicity c a b : ℤ) *
        (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
          (b6EvalLow (Z-A) (R-B) f) : ℤ) *
        b6W6DominantFastWeight
          ![c,a,b,f,b6EvalHigh (Z-A) (R-B) f,b6EvalLow (Z-A) (R-B) f] Q
      else 0)
      (((Z-A)+2)/3) (min (Z-A) (Nat.sqrt (R-B)))
  else 0
#print axioms Paper7MomentCounts.b6StructuralDominantTightFastTerm

theorem b6StructuralDominantTightFastTerm_eq (Z R A Q B c a b : ℕ) :
    b6StructuralDominantTightFastTerm Z R A Q B c a b =
      b6StructuralProductFastTerm Z R A Q B c a b := by
  simp only [b6StructuralDominantTightFastTerm, b6StructuralProductFastTerm,
    b6W6DominantFastWeight_eq]
#print axioms Paper7MomentCounts.b6StructuralDominantTightFastTerm_eq

def b6StructuralDominantTightCResidualPrunedCSliceRaw (Z R A Q c : ℕ) : ℤ :=
  bif decide (R ≤ b6SortedCUpper A c+(Z-A)^2 ∧ 2*c^2+(A-c)^2 ≤ 2*R) then
    b6StructuralIccSum (fun a =>
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        b6StructuralDominantTightFastTerm Z R A Q (b6SortedLeftSquares A c a)
          c a (b6SortedLeftLow A c a)
      else 0) ((A-c+1)/2) (min c (A-c))
  else 0
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedCSliceRaw

theorem b6StructuralDominantTightCResidualPrunedCSliceRaw_eq (Z R A Q c : ℕ) :
    b6StructuralDominantTightCResidualPrunedCSliceRaw Z R A Q c = b6StructuralTightCResidualPrunedCSliceRaw Z R A Q c := by
  simp only [b6StructuralDominantTightCResidualPrunedCSliceRaw, b6StructuralTightCResidualPrunedCSliceRaw, b6StructuralDominantTightFastTerm_eq]
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedCSliceRaw_eq

def b6StructuralDominantTightCResidualPrunedASliceRaw (Z R A Q : ℕ) : ℤ :=
  bif decide (R ≤ A^2 + (Z-A)^2) then
    b6StructuralIccSum (fun c => b6StructuralDominantTightCResidualPrunedCSliceRaw Z R A Q c)
      ((A+2)/3) A
  else 0
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedASliceRaw

theorem b6StructuralDominantTightCResidualPrunedASliceRaw_eq (Z R A Q : ℕ) :
    b6StructuralDominantTightCResidualPrunedASliceRaw Z R A Q = b6StructuralTightCResidualPrunedASliceRaw Z R A Q := by
  simp only [b6StructuralDominantTightCResidualPrunedASliceRaw, b6StructuralTightCResidualPrunedASliceRaw, b6StructuralDominantTightCResidualPrunedCSliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedASliceRaw_eq

def b6StructuralDominantTightCResidualPrunedEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6StructuralDominantTightCResidualPrunedASliceRaw Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalASlice

theorem b6StructuralDominantTightCResidualPrunedEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6StructuralDominantTightCResidualPrunedEvalASlice sm Z Q A = b6StructuralTightCResidualPrunedEvalASlice sm Z Q A := by
  simp only [b6StructuralDominantTightCResidualPrunedEvalASlice, b6StructuralTightCResidualPrunedEvalASlice, b6StructuralDominantTightCResidualPrunedASliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalASlice_eq

def b6StructuralDominantTightCResidualPrunedEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6StructuralRangeOffset (fun A => b6StructuralDominantTightCResidualPrunedEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalBlock

theorem b6StructuralDominantTightCResidualPrunedEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6StructuralDominantTightCResidualPrunedEvalBlock sm Z Q = b6StructuralTightCResidualPrunedEvalBlock sm Z Q := by
  simp only [b6StructuralDominantTightCResidualPrunedEvalBlock, b6StructuralTightCResidualPrunedEvalBlock, b6StructuralDominantTightCResidualPrunedEvalASlice_eq]
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalBlock_eq

def b6StructuralDominantTightCResidualPrunedEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun Z => b6StructuralDominantTightCResidualPrunedEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalQSlice

theorem b6StructuralDominantTightCResidualPrunedEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6StructuralDominantTightCResidualPrunedEvalQSlice sm Q = b6StructuralTightCResidualPrunedEvalQSlice sm Q := by
  simp only [b6StructuralDominantTightCResidualPrunedEvalQSlice, b6StructuralTightCResidualPrunedEvalQSlice, b6StructuralDominantTightCResidualPrunedEvalBlock_eq]
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalQSlice_eq

def b6StructuralDominantTightCResidualPrunedEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6StructuralRangeOffset (fun Q => b6StructuralDominantTightCResidualPrunedEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalTotal

theorem b6StructuralDominantTightCResidualPrunedEvalTotal_eq (sm : ℤ × ℤ) :
    b6StructuralDominantTightCResidualPrunedEvalTotal sm = b6StructuralTightCResidualPrunedEvalTotal sm := by
  simp only [b6StructuralDominantTightCResidualPrunedEvalTotal, b6StructuralTightCResidualPrunedEvalTotal, b6StructuralDominantTightCResidualPrunedEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalTotal_eq

theorem b6StructuralDominantTightCResidualPrunedEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralDominantTightCResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalTotal_eq_original_B1_theta

theorem b6StructuralDominantTightCResidualPrunedEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralDominantTightCResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalTotal_eq_original_D2_theta

theorem b6StructuralDominantTightCResidualPrunedEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralDominantTightCResidualPrunedEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalTotal_sum_eq_original_B1

theorem b6StructuralDominantTightCResidualPrunedEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralDominantTightCResidualPrunedEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6StructuralDominantTightCResidualPrunedEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
