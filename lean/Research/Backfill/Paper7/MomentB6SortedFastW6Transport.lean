import Research.Backfill.Paper7.MomentB6SortedLeftReindex
import Research.Backfill.Paper7.MomentB6BalancedFastW6Transport

/-! Uncompiled actual-F specialization of the successful963 weighted bijection.
Both TripleGuards, the right discriminant reconstruction, both multiplicities,
FastWeight, CatalogAccept and the full A/Z/Q domains remain. Left B enumeration
and left square-root reconstruction are replaced by the complete sorted c/a
triangle. All traversals use the successful956/958 balanced sums. No numerical
candidate, resource change or performance claim is supplied. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6SortedFastTerm (Z R A Q B c a b : ℕ) : ℤ :=
  bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) then
    b6BalancedIccSum (fun f =>
      bif b6EvalSortedAccept (Z-A) (R-B) f then
        (b6EvalMultiplicity c a b : ℤ) *
        (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
          (b6EvalLow (Z-A) (R-B) f) : ℤ) *
        b6W6FastWeight
          ![c,a,b,f,b6EvalHigh (Z-A) (R-B) f,b6EvalLow (Z-A) (R-B) f] Q
      else 0)
      (((Z-A)+2)/3) (min (Z-A) (Nat.sqrt (R-B)))
  else 0
#print axioms Paper7MomentCounts.b6SortedFastTerm

theorem b6SortedFastTerm_sum (Z R A B Q : ℕ) :
    (∑ c ∈ b6EvalScalarRange A B,
      bif b6EvalSortedAccept A B c then
        b6SortedFastTerm Z R A Q B c (b6EvalHigh A B c) (b6EvalLow A B c) else 0) =
    (bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) then
      b6W6FastEvalQSplitSum Z R A B Q else 0) := by
  by_cases hg : (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) = true
  · simp only [b6SortedFastTerm, Bool.cond_eq_ite, ite_eq_left hg,
      b6BalancedIccSum_eq, b6W6FastEvalQSplitSum, b6EvalScalarRange]
  · simp only [b6SortedFastTerm, Bool.cond_eq_ite, ite_eq_right hg,
      ite_self, Finset.sum_const_zero]
#print axioms Paper7MomentCounts.b6SortedFastTerm_sum

def b6SortedFastASliceRaw (Z R A Q : ℕ) : ℤ :=
  b6BalancedIccSum (fun c =>
    b6BalancedIccSum (fun a =>
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        b6SortedFastTerm Z R A Q (b6SortedLeftSquares A c a) c a (b6SortedLeftLow A c a)
      else 0)
      ((A-c+1)/2) (min c (A-c)))
    ((A+2)/3) A
#print axioms Paper7MomentCounts.b6SortedFastASliceRaw

theorem b6SortedFastASliceRaw_eq (Z R A Q : ℕ) :
    b6SortedFastASliceRaw Z R A Q =
      ∑ B ∈ b6EvalBRange Z R A,
        bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) then
          b6W6FastEvalQSplitSum Z R A B Q else 0 := by
  calc
    b6SortedFastASliceRaw Z R A Q =
        ∑ c ∈ b6SortedLeftCRange A, ∑ a ∈ b6SortedLeftARange A c,
          bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
            b6SortedFastTerm Z R A Q (b6SortedLeftSquares A c a) c a (b6SortedLeftLow A c a)
          else 0 := by
      simp only [b6SortedFastASliceRaw, b6BalancedIccSum_eq,
        b6SortedLeftCRange, b6SortedLeftARange]
    _ = ∑ B ∈ b6EvalBRange Z R A, ∑ c ∈ b6EvalScalarRange A B,
          bif b6EvalSortedAccept A B c then
            b6SortedFastTerm Z R A Q B c (b6EvalHigh A B c) (b6EvalLow A B c) else 0 :=
      (b6SortedLeftWeightedBSupport Z R A (b6SortedFastTerm Z R A Q)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro B _hB
      exact b6SortedFastTerm_sum Z R A B Q
#print axioms Paper7MomentCounts.b6SortedFastASliceRaw_eq

def b6SortedFastEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6SortedFastASliceRaw Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6SortedFastEvalASlice

theorem b6SortedFastEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6SortedFastEvalASlice sm Z Q A = b6W6FastEvalASlice sm Z Q A := by
  unfold b6SortedFastEvalASlice b6W6FastEvalASlice
  exact b6SortedFastASliceRaw_eq Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6SortedFastEvalASlice_eq

def b6SortedFastEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6BalancedRangeOffset (fun A => b6SortedFastEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6SortedFastEvalBlock

theorem b6SortedFastEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6SortedFastEvalBlock sm Z Q = b6W6FastEvalBlock sm Z Q := by
  simp only [b6SortedFastEvalBlock, b6BalancedRangeOffset_eq_range,
    b6W6FastEvalBlock, b6SortedFastEvalASlice_eq]
#print axioms Paper7MomentCounts.b6SortedFastEvalBlock_eq

def b6SortedFastEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6BalancedIccSum (fun Z => b6SortedFastEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6SortedFastEvalQSlice

theorem b6SortedFastEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6SortedFastEvalQSlice sm Q = b6W6FastEvalQSlice sm Q := by
  simp only [b6SortedFastEvalQSlice, b6BalancedIccSum_eq,
    b6W6FastEvalQSlice, b6EvalZRange, b6SortedFastEvalBlock_eq]
#print axioms Paper7MomentCounts.b6SortedFastEvalQSlice_eq

def b6SortedFastEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6BalancedRangeOffset (fun Q => b6SortedFastEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6SortedFastEvalTotal

theorem b6SortedFastEvalTotal_eq (sm : ℤ × ℤ) :
    b6SortedFastEvalTotal sm = b6W6FastEvalTotal sm := by
  simp only [b6SortedFastEvalTotal, b6BalancedRangeOffset_eq_range,
    b6W6FastEvalTotal, b6SortedFastEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6SortedFastEvalTotal_eq

theorem b6SortedFastEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6SortedFastEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6SortedFastEvalTotal_eq]
  exact b6W6FastEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6SortedFastEvalTotal_eq_original_B1_theta

theorem b6SortedFastEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6SortedFastEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6SortedFastEvalTotal_eq]
  exact b6W6FastEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6SortedFastEvalTotal_eq_original_D2_theta

theorem b6SortedFastEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6SortedFastEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6SortedFastEvalTotal_eq]
  exact b6W6FastEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6SortedFastEvalTotal_sum_eq_original_B1

theorem b6SortedFastEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6SortedFastEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6SortedFastEvalTotal_eq]
  exact b6W6FastEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6SortedFastEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
