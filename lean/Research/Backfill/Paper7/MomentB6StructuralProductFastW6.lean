import Research.Backfill.Paper7.MomentB6StructuralSortedFastW6
import Research.Backfill.Paper7.MomentB6W6ProductWeight

/-! Full-domain product-weight transport over the six actual972 structural
sum layers. Only FastWeight and self names change in the computation blocks.
Every original bound, guard, multiplicity, reconstruction and sum recursion
is retained. No numerical evaluation or performance claim is included. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6StructuralProductFastTerm (Z R A Q B c a b : ℕ) : ℤ :=
  bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) then
    b6StructuralIccSum (fun f =>
      bif b6EvalSortedAccept (Z-A) (R-B) f then
        (b6EvalMultiplicity c a b : ℤ) *
        (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
          (b6EvalLow (Z-A) (R-B) f) : ℤ) *
        b6W6ProductFastWeight
          ![c,a,b,f,b6EvalHigh (Z-A) (R-B) f,b6EvalLow (Z-A) (R-B) f] Q
      else 0)
      (((Z-A)+2)/3) (min (Z-A) (Nat.sqrt (R-B)))
  else 0
#print axioms Paper7MomentCounts.b6StructuralProductFastTerm

theorem b6StructuralProductFastTerm_eq (Z R A Q B c a b : ℕ) :
    b6StructuralProductFastTerm Z R A Q B c a b =
      b6StructuralSortedFastTerm Z R A Q B c a b := by
  simp only [b6StructuralProductFastTerm, b6StructuralSortedFastTerm,
    b6W6ProductFastWeight_eq]
#print axioms Paper7MomentCounts.b6StructuralProductFastTerm_eq

def b6StructuralProductFastASliceRaw (Z R A Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun c =>
    b6StructuralIccSum (fun a =>
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        b6StructuralProductFastTerm Z R A Q (b6SortedLeftSquares A c a) c a (b6SortedLeftLow A c a)
      else 0)
      ((A-c+1)/2) (min c (A-c)))
    ((A+2)/3) A
#print axioms Paper7MomentCounts.b6StructuralProductFastASliceRaw

theorem b6StructuralProductFastASliceRaw_eq (Z R A Q : ℕ) :
    b6StructuralProductFastASliceRaw Z R A Q = b6StructuralSortedFastASliceRaw Z R A Q := by
  simp only [b6StructuralProductFastASliceRaw, b6StructuralSortedFastASliceRaw,
    b6StructuralProductFastTerm_eq]
#print axioms Paper7MomentCounts.b6StructuralProductFastASliceRaw_eq

def b6StructuralProductFastEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6StructuralProductFastASliceRaw Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalASlice

theorem b6StructuralProductFastEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6StructuralProductFastEvalASlice sm Z Q A = b6StructuralSortedFastEvalASlice sm Z Q A := by
  simp only [b6StructuralProductFastEvalASlice, b6StructuralSortedFastEvalASlice,
    b6StructuralProductFastASliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalASlice_eq

def b6StructuralProductFastEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6StructuralRangeOffset (fun A => b6StructuralProductFastEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalBlock

theorem b6StructuralProductFastEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6StructuralProductFastEvalBlock sm Z Q = b6StructuralSortedFastEvalBlock sm Z Q := by
  simp only [b6StructuralProductFastEvalBlock, b6StructuralSortedFastEvalBlock,
    b6StructuralProductFastEvalASlice_eq]
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalBlock_eq

def b6StructuralProductFastEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun Z => b6StructuralProductFastEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalQSlice

theorem b6StructuralProductFastEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6StructuralProductFastEvalQSlice sm Q = b6StructuralSortedFastEvalQSlice sm Q := by
  simp only [b6StructuralProductFastEvalQSlice, b6StructuralSortedFastEvalQSlice,
    b6StructuralProductFastEvalBlock_eq]
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalQSlice_eq

def b6StructuralProductFastEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6StructuralRangeOffset (fun Q => b6StructuralProductFastEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalTotal

theorem b6StructuralProductFastEvalTotal_eq (sm : ℤ × ℤ) :
    b6StructuralProductFastEvalTotal sm = b6StructuralSortedFastEvalTotal sm := by
  simp only [b6StructuralProductFastEvalTotal, b6StructuralSortedFastEvalTotal,
    b6StructuralProductFastEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalTotal_eq

theorem b6StructuralProductFastEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralProductFastEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralProductFastEvalTotal_eq]
  exact b6StructuralSortedFastEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalTotal_eq_original_B1_theta

theorem b6StructuralProductFastEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralProductFastEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralProductFastEvalTotal_eq]
  exact b6StructuralSortedFastEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalTotal_eq_original_D2_theta

theorem b6StructuralProductFastEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralProductFastEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralProductFastEvalTotal_eq]
  exact b6StructuralSortedFastEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalTotal_sum_eq_original_B1

theorem b6StructuralProductFastEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralProductFastEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralProductFastEvalTotal_eq]
  exact b6StructuralSortedFastEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6StructuralProductFastEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
