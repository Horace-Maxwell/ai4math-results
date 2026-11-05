import Research.Backfill.Paper7.MomentB6StructuralFuelSum
import Research.Backfill.Paper7.MomentB6SortedFastW6Transport

/-! Uncompiled full-domain replacement of actual964's six sum traversals by
actual969's structural-fuel sums. All sorted c/a bounds, original B arithmetic
guard, both TripleGuards, right reconstruction, multiplicities, FastWeight,
CatalogAccept and full A/Z/Q domains remain. No choose5 rewrite, numerical
candidate, resource option or performance claim is introduced. Only the sum
recursion is structural; other library proof machinery is not claimed absent. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6StructuralIccSum (f : ℕ → ℤ) (a b : ℕ) : ℤ :=
  b6StructuralIcoSum f a (b+1)
#print axioms Paper7MomentCounts.b6StructuralIccSum

theorem b6StructuralIccSum_eq (f : ℕ → ℤ) (a b : ℕ) :
    b6StructuralIccSum f a b = ∑ i ∈ Finset.Icc a b, f i := by
  unfold b6StructuralIccSum
  rw [b6StructuralIcoSum_eq, Finset.Ico_add_one_right_eq_Icc]
#print axioms Paper7MomentCounts.b6StructuralIccSum_eq

def b6StructuralSortedFastTerm (Z R A Q B c a b : ℕ) : ℤ :=
  bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) then
    b6StructuralIccSum (fun f =>
      bif b6EvalSortedAccept (Z-A) (R-B) f then
        (b6EvalMultiplicity c a b : ℤ) *
        (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
          (b6EvalLow (Z-A) (R-B) f) : ℤ) *
        b6W6FastWeight
          ![c,a,b,f,b6EvalHigh (Z-A) (R-B) f,b6EvalLow (Z-A) (R-B) f] Q
      else 0)
      (((Z-A)+2)/3) (min (Z-A) (Nat.sqrt (R-B)))
  else 0
#print axioms Paper7MomentCounts.b6StructuralSortedFastTerm

theorem b6StructuralSortedFastTerm_eq (Z R A Q B c a b : ℕ) :
    b6StructuralSortedFastTerm Z R A Q B c a b = b6SortedFastTerm Z R A Q B c a b := by
  simp only [b6StructuralSortedFastTerm, b6SortedFastTerm,
    b6StructuralIccSum_eq,
    b6BalancedIccSum_eq]
#print axioms Paper7MomentCounts.b6StructuralSortedFastTerm_eq

def b6StructuralSortedFastASliceRaw (Z R A Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun c =>
    b6StructuralIccSum (fun a =>
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        b6StructuralSortedFastTerm Z R A Q (b6SortedLeftSquares A c a) c a (b6SortedLeftLow A c a)
      else 0)
      ((A-c+1)/2) (min c (A-c)))
    ((A+2)/3) A
#print axioms Paper7MomentCounts.b6StructuralSortedFastASliceRaw

theorem b6StructuralSortedFastASliceRaw_eq (Z R A Q : ℕ) :
    b6StructuralSortedFastASliceRaw Z R A Q = b6SortedFastASliceRaw Z R A Q := by
  simp only [b6StructuralSortedFastASliceRaw, b6SortedFastASliceRaw,
    b6StructuralIccSum_eq,
    b6BalancedIccSum_eq,
    b6StructuralSortedFastTerm_eq]
#print axioms Paper7MomentCounts.b6StructuralSortedFastASliceRaw_eq

def b6StructuralSortedFastEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6StructuralSortedFastASliceRaw Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalASlice

theorem b6StructuralSortedFastEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6StructuralSortedFastEvalASlice sm Z Q A = b6SortedFastEvalASlice sm Z Q A := by
  simp only [b6StructuralSortedFastEvalASlice, b6SortedFastEvalASlice,
    b6StructuralSortedFastASliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalASlice_eq

def b6StructuralSortedFastEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6StructuralRangeOffset (fun A => b6StructuralSortedFastEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalBlock

theorem b6StructuralSortedFastEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6StructuralSortedFastEvalBlock sm Z Q = b6SortedFastEvalBlock sm Z Q := by
  simp only [b6StructuralSortedFastEvalBlock, b6SortedFastEvalBlock,
    b6StructuralRangeOffset_zero_eq,
    b6BalancedRangeOffset_eq_range,
    b6StructuralSortedFastEvalASlice_eq]
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalBlock_eq

def b6StructuralSortedFastEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun Z => b6StructuralSortedFastEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalQSlice

theorem b6StructuralSortedFastEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6StructuralSortedFastEvalQSlice sm Q = b6SortedFastEvalQSlice sm Q := by
  simp only [b6StructuralSortedFastEvalQSlice, b6SortedFastEvalQSlice,
    b6StructuralIccSum_eq,
    b6BalancedIccSum_eq,
    b6StructuralSortedFastEvalBlock_eq]
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalQSlice_eq

def b6StructuralSortedFastEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6StructuralRangeOffset (fun Q => b6StructuralSortedFastEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalTotal

theorem b6StructuralSortedFastEvalTotal_eq (sm : ℤ × ℤ) :
    b6StructuralSortedFastEvalTotal sm = b6SortedFastEvalTotal sm := by
  simp only [b6StructuralSortedFastEvalTotal, b6SortedFastEvalTotal,
    b6StructuralRangeOffset_zero_eq,
    b6BalancedRangeOffset_eq_range,
    b6StructuralSortedFastEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalTotal_eq

theorem b6StructuralSortedFastEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralSortedFastEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralSortedFastEvalTotal_eq]
  exact b6SortedFastEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalTotal_eq_original_B1_theta

theorem b6StructuralSortedFastEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralSortedFastEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralSortedFastEvalTotal_eq]
  exact b6SortedFastEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalTotal_eq_original_D2_theta

theorem b6StructuralSortedFastEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralSortedFastEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralSortedFastEvalTotal_eq]
  exact b6SortedFastEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalTotal_sum_eq_original_B1

theorem b6StructuralSortedFastEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralSortedFastEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralSortedFastEvalTotal_eq]
  exact b6SortedFastEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6StructuralSortedFastEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
