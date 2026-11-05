import Research.Backfill.Paper7.MomentB6ResidualPruned
import Research.Backfill.Paper7.MomentB6SortedCArithmetic

/-! SOURCE ONLY. Both proved necessary c bounds before the unchanged a sum.
Every original A/c/a/Z/Q range, catalog/B/triple guard, multiplicity,
ProductFastTerm and structural recursion is retained. This independent
candidate does not import or alter the weaker CResidual candidate.
No original cardinality hypothesis, numeric guess or budget change. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

theorem b6SortedLeftBGuard_false_of_tightCBounds (Z R A c a : ℕ)
    (hlo : (A-c+1)/2 ≤ a) (hhi : a ≤ min c (A-c))
    (h : ¬ (R ≤ b6SortedCUpper A c+(Z-A)^2 ∧ 2*c^2+(A-c)^2 ≤ 2*R)) :
    b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) = false := by
  apply Bool.eq_false_iff.mpr
  intro hg
  simp only [b6SortedLeftBGuard, Bool.and_eq_true, decide_eq_true_eq,
    max_le_iff, le_min_iff, and_assoc] at hg
  have hlow : R-(Z-A)^2 ≤ b6SortedLeftSquares A c a := hg.2.1
  have hhigh : b6SortedLeftSquares A c a ≤ R-((Z-A)^2+2)/3 := hg.2.2.2.1
  have hR : R ≤ b6SortedLeftSquares A c a+(Z-A)^2 :=
    Nat.sub_le_iff_le_add.mp hlow
  have hB : b6SortedLeftSquares A c a ≤ R := by omega
  have hR' : R ≤ c^2+a^2+(A-c-a)^2+(Z-A)^2 := by
    simpa only [b6SortedLeftSquares, b6SortedLeftLow] using hR
  have hB' : c^2+a^2+(A-c-a)^2 ≤ R := by
    simpa only [b6SortedLeftSquares, b6SortedLeftLow] using hB
  have ha : a ≤ A-c := le_trans hhi (min_le_right _ _)
  exact h ⟨b6SortedCResidualUpper_of_leftResidual Z R A c a hlo hhi hR',
    b6SortedCResidualLower_of_leftSquares R A c a ha hB'⟩
#print axioms Paper7MomentCounts.b6SortedLeftBGuard_false_of_tightCBounds

theorem b6StructuralProductFastCSlice_eq_zero_of_tightCBounds (Z R A Q c : ℕ)
    (h : ¬ (R ≤ b6SortedCUpper A c+(Z-A)^2 ∧ 2*c^2+(A-c)^2 ≤ 2*R)) :
    b6StructuralIccSum (fun a =>
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        b6StructuralProductFastTerm Z R A Q (b6SortedLeftSquares A c a)
          c a (b6SortedLeftLow A c a)
      else 0) ((A-c+1)/2) (min c (A-c)) = 0 := by
  rw [b6StructuralIccSum_eq]
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := Finset.mem_Icc.mp ha
  simp only [b6SortedLeftBGuard_false_of_tightCBounds Z R A c a ha'.1 ha'.2 h,
    Bool.cond_false]
#print axioms Paper7MomentCounts.b6StructuralProductFastCSlice_eq_zero_of_tightCBounds

def b6StructuralTightCResidualPrunedCSliceRaw (Z R A Q c : ℕ) : ℤ :=
  bif decide (R ≤ b6SortedCUpper A c+(Z-A)^2 ∧ 2*c^2+(A-c)^2 ≤ 2*R) then
    b6StructuralIccSum (fun a =>
      bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
        b6StructuralProductFastTerm Z R A Q (b6SortedLeftSquares A c a)
          c a (b6SortedLeftLow A c a)
      else 0) ((A-c+1)/2) (min c (A-c))
  else 0
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedCSliceRaw

theorem b6StructuralTightCResidualPrunedCSliceRaw_eq (Z R A Q c : ℕ) :
    b6StructuralTightCResidualPrunedCSliceRaw Z R A Q c =
      b6StructuralIccSum (fun a =>
        bif b6SortedLeftBGuard Z R A (b6SortedLeftSquares A c a) then
          b6StructuralProductFastTerm Z R A Q (b6SortedLeftSquares A c a)
            c a (b6SortedLeftLow A c a)
        else 0) ((A-c+1)/2) (min c (A-c)) := by
  by_cases h : R ≤ b6SortedCUpper A c+(Z-A)^2 ∧ 2*c^2+(A-c)^2 ≤ 2*R
  · simp only [b6StructuralTightCResidualPrunedCSliceRaw, decide_eq_true h, Bool.cond_true]
  · rw [b6StructuralProductFastCSlice_eq_zero_of_tightCBounds Z R A Q c h]
    simp only [b6StructuralTightCResidualPrunedCSliceRaw, decide_eq_false h, Bool.cond_false]
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedCSliceRaw_eq

def b6StructuralTightCResidualPrunedASliceRaw (Z R A Q : ℕ) : ℤ :=
  bif decide (R ≤ A^2 + (Z-A)^2) then
    b6StructuralIccSum (fun c => b6StructuralTightCResidualPrunedCSliceRaw Z R A Q c)
      ((A+2)/3) A
  else 0
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedASliceRaw

theorem b6StructuralTightCResidualPrunedASliceRaw_eq (Z R A Q : ℕ) :
    b6StructuralTightCResidualPrunedASliceRaw Z R A Q =
      b6StructuralResidualPrunedASliceRaw Z R A Q := by
  simp only [b6StructuralTightCResidualPrunedASliceRaw, b6StructuralResidualPrunedASliceRaw,
    b6StructuralTightCResidualPrunedCSliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedASliceRaw_eq

def b6StructuralTightCResidualPrunedEvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  b6StructuralTightCResidualPrunedASliceRaw Z (b6EvalResidual sm Z Q) A Q
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalASlice

theorem b6StructuralTightCResidualPrunedEvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6StructuralTightCResidualPrunedEvalASlice sm Z Q A =
      b6StructuralResidualPrunedEvalASlice sm Z Q A := by
  simp only [b6StructuralTightCResidualPrunedEvalASlice, b6StructuralResidualPrunedEvalASlice,
    b6StructuralTightCResidualPrunedASliceRaw_eq]
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalASlice_eq

def b6StructuralTightCResidualPrunedEvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    b6StructuralRangeOffset (fun A => b6StructuralTightCResidualPrunedEvalASlice sm Z Q A) (Z+1) 0
  else 0
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalBlock

theorem b6StructuralTightCResidualPrunedEvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6StructuralTightCResidualPrunedEvalBlock sm Z Q =
      b6StructuralResidualPrunedEvalBlock sm Z Q := by
  simp only [b6StructuralTightCResidualPrunedEvalBlock, b6StructuralResidualPrunedEvalBlock,
    b6StructuralTightCResidualPrunedEvalASlice_eq]
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalBlock_eq

def b6StructuralTightCResidualPrunedEvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  b6StructuralIccSum (fun Z => b6StructuralTightCResidualPrunedEvalBlock sm Z Q)
    (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalQSlice

theorem b6StructuralTightCResidualPrunedEvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6StructuralTightCResidualPrunedEvalQSlice sm Q =
      b6StructuralResidualPrunedEvalQSlice sm Q := by
  simp only [b6StructuralTightCResidualPrunedEvalQSlice, b6StructuralResidualPrunedEvalQSlice,
    b6StructuralTightCResidualPrunedEvalBlock_eq]
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalQSlice_eq

def b6StructuralTightCResidualPrunedEvalTotal (sm : ℤ × ℤ) : ℤ :=
  b6StructuralRangeOffset (fun Q => b6StructuralTightCResidualPrunedEvalQSlice sm Q) 19 0
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalTotal

theorem b6StructuralTightCResidualPrunedEvalTotal_eq (sm : ℤ × ℤ) :
    b6StructuralTightCResidualPrunedEvalTotal sm = b6StructuralResidualPrunedEvalTotal sm := by
  simp only [b6StructuralTightCResidualPrunedEvalTotal, b6StructuralResidualPrunedEvalTotal,
    b6StructuralTightCResidualPrunedEvalQSlice_eq]
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalTotal_eq

theorem b6StructuralTightCResidualPrunedEvalTotal_eq_original_B1_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralTightCResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralResidualPrunedEvalTotal_eq_original_B1_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalTotal_eq_original_B1_theta

theorem b6StructuralTightCResidualPrunedEvalTotal_eq_original_D2_theta (sm : ℤ × ℤ)
    (hsm : sm ∈ b6FeatureCatalog) :
    b6StructuralTightCResidualPrunedEvalTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6StructuralTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralResidualPrunedEvalTotal_eq_original_D2_theta sm hsm
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalTotal_eq_original_D2_theta

theorem b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_B1 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralTightCResidualPrunedEvalTotal sm) =
      ((CandB1 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralResidualPrunedEvalTotal_sum_eq_original_B1
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_B1

theorem b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_D2 :
    (∑ sm ∈ b6FeatureCatalog, b6StructuralTightCResidualPrunedEvalTotal sm) =
      ((CandD2 6 42).ncard : ℤ) := by
  classical
  simp_rw [b6StructuralTightCResidualPrunedEvalTotal_eq]
  exact b6StructuralResidualPrunedEvalTotal_sum_eq_original_D2
#print axioms Paper7MomentCounts.b6StructuralTightCResidualPrunedEvalTotal_sum_eq_original_D2

end Paper7MomentCounts
