import Research.Backfill.Paper7.MomentB6TightCResidualPruned
import Research.Backfill.Paper7.MomentB6W6LowQFiveDominantFastWeight

/-! SOURCE ONLY. All eighteen original TightC transport interfaces with the
universal Q0-through-Q5 weight and its capacity complements. The original
A/c/a/Z/Q ranges, both c inequalities, catalog/B/triple guards, multiplicities
and structural recursion are unchanged. The new weight is an uncompiled
local dependency; its imported generic DP4/DP5 sources have actual successful
compile/checker evidence. No graph premise, numerical theta source, guessed
value, native computation, budget change or execution plan is added. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6StructuralLowQFiveDominantTightFastTerm (Z R A Q B c a b : ℕ) : ℤ :=
  bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (R-B)) then
    b6StructuralIccSum (fun f =>
      bif b6EvalSortedAccept (Z-A) (R-B) f then
        (b6EvalMultiplicity c a b : ℤ) *
        (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
          (b6EvalLow (Z-A) (R-B) f) : ℤ) *
        b6W6LowQFiveDominantFastWeight
          ![c,a,b,f,b6EvalHigh (Z-A) (R-B) f,b6EvalLow (Z-A) (R-B) f] Q
      else 0)
      (((Z-A)+2)/3) (min (Z-A) (Nat.sqrt (R-B)))
  else 0
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightFastTerm

theorem b6StructuralLowQFiveDominantTightFastTerm_eq (Z R A Q B c a b : ℕ) :
    b6StructuralLowQFiveDominantTightFastTerm Z R A Q B c a b =
      b6StructuralProductFastTerm Z R A Q B c a b := by
  simp only [b6StructuralLowQFiveDominantTightFastTerm, b6StructuralProductFastTerm,
    b6W6LowQFiveDominantFastWeight_eq]
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightFastTerm_eq

def b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw (Z R A Q c : ℕ) : ℤ :=
  bif decide (R ≤ b6SortedCUpper A c+(Z-A)^2 ∧ 2*c^2+(A-c)^2 ≤ 2*R) then
    b6StructuralIccSum (fun a =>
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        b6StructuralLowQFiveDominantTightFastTerm Z R A Q (b6SortedLeftSquares A c a)
          c a (b6SortedLeftLow A c a)
      else 0) ((A-c+1)/2) (min c (A-c))
  else 0
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw

theorem b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw_eq (Z R A Q c : ℕ) :
    b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw Z R A Q c = b6StructuralTightCResidualPrunedCSliceRaw Z R A Q c := by
  simp only [b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw, b6StructuralTightCResidualPrunedCSliceRaw, b6StructuralLowQFiveDominantTightFastTerm_eq]
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw_eq

def b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw (Z R A Q : ℕ) : ℤ :=
  bif decide (R ≤ A^2 + (Z-A)^2) then
    b6StructuralIccSum (fun c => b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw Z R A Q c)
      ((A+2)/3) A
  else 0
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw

theorem b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw_eq (Z R A Q : ℕ) :
    b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw Z R A Q = b6StructuralTightCResidualPrunedASliceRaw Z R A Q := by
  simp only [b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw, b6StructuralTightCResidualPrunedASliceRaw, b6StructuralLowQFiveDominantTightCResidualPrunedCSliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw_eq

def b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice sm Z Q A = b6StructuralTightCResidualPrunedEvalASlice sm Z Q A := by
  simp only [b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice, b6StructuralTightCResidualPrunedEvalASlice, b6StructuralLowQFiveDominantTightCResidualPrunedASliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice_eq

def b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6StructuralRangeOffset (fun A => b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock sm Z Q = b6StructuralTightCResidualPrunedEvalBlock sm Z Q := by
  simp only [b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock, b6StructuralTightCResidualPrunedEvalBlock, b6StructuralLowQFiveDominantTightCResidualPrunedEvalASlice_eq]
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock_eq

def b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun Z => b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice sm Q = b6StructuralTightCResidualPrunedEvalQSlice sm Q := by
  simp only [b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice, b6StructuralTightCResidualPrunedEvalQSlice, b6StructuralLowQFiveDominantTightCResidualPrunedEvalBlock_eq]
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice_eq

def b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6StructuralRangeOffset (fun Q => b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq (sm : ℤ × ℤ) :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal sm = b6StructuralTightCResidualPrunedEvalTotal sm := by
  simp only [b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal, b6StructuralTightCResidualPrunedEvalTotal, b6StructuralLowQFiveDominantTightCResidualPrunedEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq_original_B1_theta

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq_original_D2_theta

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_sum_eq_original_B1

theorem b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6StructuralLowQFiveDominantTightCResidualPrunedEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
