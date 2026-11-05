import Research.Backfill.Paper7.MomentB6BalancedFiniteSum
import Research.Backfill.Paper7.MomentB6W6BinaryOriginalTransport

/-! Uncompiled full-domain equivalence layer over actual956 and actual949.
All six summation traversals (left/right scalar, B, A, Z, Q) are balanced.
The B parity filter and every original Boolean guard remain. The fixed six
finite differences inside FastWeight are unchanged. No numerical evaluation,
resource option or additional original-graph hypothesis is introduced.
Whether this changes actual954 kernel cost remains UNKNOWN. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6BalancedIccSum (f : ℕ → ℤ) (a b : ℕ) : ℤ :=
  b6BalancedIcoSum f a (b+1)
#print axioms Paper7MomentCounts.b6BalancedIccSum

theorem b6BalancedIccSum_eq (f : ℕ → ℤ) (a b : ℕ) :
    b6BalancedIccSum f a b = ∑ i ∈ Finset.Icc a b, f i := by
  unfold b6BalancedIccSum
  rw [b6BalancedIcoSum_eq, Finset.Ico_add_one_right_eq_Icc]
#print axioms Paper7MomentCounts.b6BalancedIccSum_eq

def b6BalancedIccBoolSum (f : ℕ → ℤ) (p : ℕ → Bool) (a b : ℕ) : ℤ :=
  b6BalancedIccSum (fun i => bif p i then f i else 0) a b
#print axioms Paper7MomentCounts.b6BalancedIccBoolSum

theorem b6BalancedIccBoolSum_eq (f : ℕ → ℤ) (p : ℕ → Bool) (a b : ℕ) :
    b6BalancedIccBoolSum f p a b =
      ∑ i ∈ (Finset.Icc a b).filter (fun i => p i = true), f i := by
  unfold b6BalancedIccBoolSum
  rw [b6BalancedIccSum_eq, Finset.sum_filter]
  simp only [Bool.cond_eq_ite]
#print axioms Paper7MomentCounts.b6BalancedIccBoolSum_eq

def b6W6BalancedEvalQSplitSum (Z R A B Q : ℕ) : ℤ :=
  b6BalancedIccSum (fun c =>
    bif b6EvalSortedAccept A B c then
      b6BalancedIccSum (fun f =>
        bif b6EvalSortedAccept (Z-A) (R-B) f then
          (b6EvalMultiplicity c (b6EvalHigh A B c) (b6EvalLow A B c) : ℤ) *
          (b6EvalMultiplicity f (b6EvalHigh (Z-A) (R-B) f)
            (b6EvalLow (Z-A) (R-B) f) : ℤ) *
          b6W6FastWeight
            ![c, b6EvalHigh A B c, b6EvalLow A B c,
              f, b6EvalHigh (Z-A) (R-B) f, b6EvalLow (Z-A) (R-B) f] Q
        else 0)
        (((Z-A)+2)/3) (min (Z-A) (Nat.sqrt (R-B)))
    else 0)
    ((A+2)/3) (min A (Nat.sqrt B))
#print axioms Paper7MomentCounts.b6W6BalancedEvalQSplitSum

def b6W6BalancedEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6BalancedIccBoolSum (fun B =>
    bif (b6EvalTripleGuard A B &&
      b6EvalTripleGuard (Z-A) (b6EvalResidual sm Z Q-B)) then
      b6W6BalancedEvalQSplitSum Z (b6EvalResidual sm Z Q) A B Q else 0)
    (fun B => decide (B%2=A%2))
    (max ((A^2+2)/3) (b6EvalResidual sm Z Q-(Z-A)^2))
    (min (A^2) (b6EvalResidual sm Z Q-((Z-A)^2+2)/3))
#print axioms Paper7MomentCounts.b6W6BalancedEvalASlice

def b6W6BalancedEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6BalancedRangeOffset (fun A => b6W6BalancedEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6W6BalancedEvalBlock

def b6W6BalancedEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6BalancedIccSum (fun Z => b6W6BalancedEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6W6BalancedEvalQSlice

def b6W6BalancedEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6BalancedRangeOffset (fun Q => b6W6BalancedEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6W6BalancedEvalTotal

theorem b6W6BalancedEvalQSplitSum_eq (Z R A B Q : ℕ) :
    b6W6BalancedEvalQSplitSum Z R A B Q = b6W6FastEvalQSplitSum Z R A B Q := by
  simp only [b6W6BalancedEvalQSplitSum, b6BalancedIccSum_eq,
    b6W6FastEvalQSplitSum, b6EvalScalarRange]
#print axioms Paper7MomentCounts.b6W6BalancedEvalQSplitSum_eq

theorem b6W6BalancedEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6W6BalancedEvalASlice sm Z Q A = b6W6FastEvalASlice sm Z Q A := by
  simp only [b6W6BalancedEvalASlice, b6BalancedIccBoolSum_eq,
    b6W6FastEvalASlice, b6EvalBRange, b6W6BalancedEvalQSplitSum_eq]
#print axioms Paper7MomentCounts.b6W6BalancedEvalASlice_eq

theorem b6W6BalancedEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6W6BalancedEvalBlock sm Z Q = b6W6FastEvalBlock sm Z Q := by
  simp only [b6W6BalancedEvalBlock, b6BalancedRangeOffset_eq_range,
    b6W6FastEvalBlock, b6W6BalancedEvalASlice_eq]
#print axioms Paper7MomentCounts.b6W6BalancedEvalBlock_eq

theorem b6W6BalancedEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6W6BalancedEvalQSlice sm Q = b6W6FastEvalQSlice sm Q := by
  simp only [b6W6BalancedEvalQSlice, b6BalancedIccSum_eq,
    b6W6FastEvalQSlice, b6EvalZRange, b6W6BalancedEvalBlock_eq]
#print axioms Paper7MomentCounts.b6W6BalancedEvalQSlice_eq

theorem b6W6BalancedEvalTotal_eq (sm : ℤ × ℤ) :
    b6W6BalancedEvalTotal sm = b6W6FastEvalTotal sm := by
  simp only [b6W6BalancedEvalTotal, b6BalancedRangeOffset_eq_range,
    b6W6FastEvalTotal, b6W6BalancedEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6W6BalancedEvalTotal_eq

theorem b6W6BalancedEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6W6BalancedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6W6BalancedEvalTotal_eq]
  exact b6W6FastEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6W6BalancedEvalTotal_eq_original_B1_theta

theorem b6W6BalancedEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6W6BalancedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6W6BalancedEvalTotal_eq]
  exact b6W6FastEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6W6BalancedEvalTotal_eq_original_D2_theta

theorem b6W6BalancedEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6W6BalancedEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6W6BalancedEvalTotal_eq]
  exact b6W6FastEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6W6BalancedEvalTotal_sum_eq_original_B1

theorem b6W6BalancedEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6W6BalancedEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6W6BalancedEvalTotal_eq]
  exact b6W6FastEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6W6BalancedEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
