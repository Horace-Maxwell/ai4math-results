import Research.Backfill.Paper7.MomentB6BSupportPruning

/-! Uncompiled candidate. Every evaluation definition below is an ordinary
computable def, outside any Classical scope or noncomputable section. It only
uses arithmetic decisions, Boolean branches and concrete Nat finite ranges.
Original symbolic functions occur only in the subsequent equality proofs. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6EvalDiscriminant (A B c : ℕ) : ℤ :=
  2*(B : ℤ)-2*(c : ℤ)^2-((A : ℤ)-c)^2
#print axioms Paper7MomentCounts.b6EvalDiscriminant

def b6EvalRoot (A B c : ℕ) : ℕ := Nat.sqrt (b6EvalDiscriminant A B c).toNat
#print axioms Paper7MomentCounts.b6EvalRoot

def b6EvalHigh (A B c : ℕ) : ℕ := (A-c+b6EvalRoot A B c)/2
#print axioms Paper7MomentCounts.b6EvalHigh

def b6EvalLow (A B c : ℕ) : ℕ := (A-c-b6EvalRoot A B c)/2
#print axioms Paper7MomentCounts.b6EvalLow

def b6EvalSortedAccept (A B c : ℕ) : Bool :=
  decide (c≤A) && decide (b6EvalRoot A B c≤A-c) &&
    decide (A+b6EvalRoot A B c≤3*c) &&
    decide ((A-c)%2=b6EvalRoot A B c%2) &&
    decide (b6EvalRoot A B c^2+(A-c)^2+2*c^2=2*B)
#print axioms Paper7MomentCounts.b6EvalSortedAccept

def b6EvalTriangular (n : ℤ) : ℤ :=
  bif decide (n<0) then 0 else ((n.toNat+2).choose 2 : ℕ)
#print axioms Paper7MomentCounts.b6EvalTriangular

def b6EvalQWeight (a b c Q : ℕ) : ℤ :=
  b6EvalTriangular Q -
    b6EvalTriangular ((Q : ℤ)-a-1) -
    b6EvalTriangular ((Q : ℤ)-b-1) -
    b6EvalTriangular ((Q : ℤ)-c-1) +
    b6EvalTriangular ((Q : ℤ)-a-b-2) +
    b6EvalTriangular ((Q : ℤ)-a-c-2) +
    b6EvalTriangular ((Q : ℤ)-b-c-2) -
    b6EvalTriangular ((Q : ℤ)-a-b-c-3)
#print axioms Paper7MomentCounts.b6EvalQWeight

def b6EvalMultiplicity (c a b : ℕ) : ℕ :=
  bif (decide (c=a) && decide (a=b)) then 1
  else bif (decide (c=a) || decide (a=b)) then 3 else 6
#print axioms Paper7MomentCounts.b6EvalMultiplicity

def b6EvalScalarRange (A B : ℕ) : Finset ℕ :=
  Finset.Icc ((A+2)/3) (min A (Nat.sqrt B))
#print axioms Paper7MomentCounts.b6EvalScalarRange

def b6EvalKernel (A B Q : ℕ) : ℤ :=
  ∑ c ∈ b6EvalScalarRange A B,
    bif b6EvalSortedAccept A B c then
      (b6EvalMultiplicity c (b6EvalHigh A B c) (b6EvalLow A B c) : ℤ) *
        b6EvalQWeight c (b6EvalHigh A B c) (b6EvalLow A B c) Q
    else 0
#print axioms Paper7MomentCounts.b6EvalKernel

def b6EvalTripleGuard (A B : ℕ) : Bool :=
  decide (A^2≤3*B) && decide (B≤A^2) && decide (B%2=A%2)
#print axioms Paper7MomentCounts.b6EvalTripleGuard

def b6EvalResidual (sm : ℤ × ℤ) (Z Q : ℕ) : ℕ :=
  (sm.2-12-3*(Z : ℤ)-2*(Q : ℤ)).toNat
#print axioms Paper7MomentCounts.b6EvalResidual

def b6EvalCatalogAccept (sm : ℤ × ℤ) (Z Q : ℕ) : Bool :=
  decide (0<Z+Q) && decide (Z+Q≤36) && decide (Q≤Z) &&
    decide ((0 : ℤ) ≤ (sm.2 - 12 - 3*(Z : ℤ) - 2*(Q : ℤ))) &&
    decide (b6EvalResidual sm Z Q≤Z^2) && decide (Z^2≤6*b6EvalResidual sm Z Q) &&
    decide (sm.1≤(6+(Z+Q : ℕ) : ℤ)) &&
    decide ((6+(Z+Q : ℕ) : ℤ) - max (Q : ℤ) 2 ≤ (sm.1))
#print axioms Paper7MomentCounts.b6EvalCatalogAccept

def b6EvalQSplitRange (Z A Q : ℕ) : Finset ℕ :=
  Finset.Icc (Q-(Z-A)) (min Q A)
#print axioms Paper7MomentCounts.b6EvalQSplitRange

def b6EvalBRange (Z R A : ℕ) : Finset ℕ :=
  (Finset.Icc (max ((A^2+2)/3) (R-(Z-A)^2))
    (min (A^2) (R-((Z-A)^2+2)/3))).filter (fun B => decide (B%2=A%2)=true)
#print axioms Paper7MomentCounts.b6EvalBRange

def b6EvalZRange (sm : ℤ × ℤ) (Q : ℕ) : Finset ℕ :=
  Finset.Icc (max Q (sm.1-6-(Q : ℤ)).toNat)
    (min (36-Q) (sm.1-6-(Q : ℤ)+max (Q : ℤ) 2).toNat)
#print axioms Paper7MomentCounts.b6EvalZRange

def b6EvalQSplitSum (Z R A B Q : ℕ) : ℤ :=
  ∑ t ∈ b6EvalQSplitRange Z A Q,
    b6EvalKernel A B t * b6EvalKernel (Z-A) (R-B) (Q-t)
#print axioms Paper7MomentCounts.b6EvalQSplitSum

def b6EvalASlice (sm : ℤ × ℤ) (Z Q A : ℕ) : ℤ :=
  ∑ B ∈ b6EvalBRange Z (b6EvalResidual sm Z Q) A,
    bif (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (b6EvalResidual sm Z Q-B)) then
      b6EvalQSplitSum Z (b6EvalResidual sm Z Q) A B Q else 0
#print axioms Paper7MomentCounts.b6EvalASlice

def b6EvalBlock (sm : ℤ × ℤ) (Z Q : ℕ) : ℤ :=
  bif b6EvalCatalogAccept sm Z Q then
    ∑ A ∈ Finset.range (Z+1), b6EvalASlice sm Z Q A else 0
#print axioms Paper7MomentCounts.b6EvalBlock

def b6EvalQSlice (sm : ℤ × ℤ) (Q : ℕ) : ℤ :=
  ∑ Z ∈ b6EvalZRange sm Q, b6EvalBlock sm Z Q
#print axioms Paper7MomentCounts.b6EvalQSlice

def b6EvalTotal (sm : ℤ × ℤ) : ℤ :=
  ∑ Q ∈ Finset.range 19, b6EvalQSlice sm Q
#print axioms Paper7MomentCounts.b6EvalTotal

/- All definitions above are complete before any theorem-local classical
reasoning below. Equality proofs are never called by evaluation definitions. -/

theorem b6EvalDiscriminant_eq (A B c : ℕ) :
    b6EvalDiscriminant A B c = labelledTripleDiscriminant A B c := rfl
#print axioms Paper7MomentCounts.b6EvalDiscriminant_eq

theorem b6EvalRoot_eq (A B c : ℕ) : b6EvalRoot A B c = labelledTripleRoot A B c := rfl
#print axioms Paper7MomentCounts.b6EvalRoot_eq

theorem b6EvalHigh_eq (A B c : ℕ) : b6EvalHigh A B c = labelledTripleHigh A B c := rfl
#print axioms Paper7MomentCounts.b6EvalHigh_eq

theorem b6EvalLow_eq (A B c : ℕ) : b6EvalLow A B c = labelledTripleLow A B c := rfl
#print axioms Paper7MomentCounts.b6EvalLow_eq

theorem b6EvalSortedAccept_iff (A B c : ℕ) :
    b6EvalSortedAccept A B c = true ↔ B6SortedTripleDiscriminantAccept A B c := by
  unfold b6EvalSortedAccept B6SortedTripleDiscriminantAccept
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  simp only [b6EvalRoot_eq]
#print axioms Paper7MomentCounts.b6EvalSortedAccept_iff

theorem b6EvalTriangular_eq (n : ℤ) : b6EvalTriangular n = labelledPositiveTriangular n := by
  unfold b6EvalTriangular labelledPositiveTriangular
  by_cases hn : n<0
  · have hb : decide (n<0) = true := decide_eq_true hn
    rw [Bool.cond_eq_ite,ite_eq_left hb,ite_eq_left hn]
  · have hb : ¬ decide (n<0) = true := by simpa only [decide_eq_true_eq] using hn
    rw [Bool.cond_eq_ite,ite_eq_right hb,ite_eq_right hn]
#print axioms Paper7MomentCounts.b6EvalTriangular_eq

theorem b6EvalQWeight_eq (a b c Q : ℕ) :
    b6EvalQWeight a b c Q = labelledTripleQWeight a b c Q := by
  unfold b6EvalQWeight labelledTripleQWeight
  simp only [b6EvalTriangular_eq]
#print axioms Paper7MomentCounts.b6EvalQWeight_eq

theorem b6EvalMultiplicity_eq (c a b : ℕ) :
    b6EvalMultiplicity c a b = labelledSortedTripleMultiplicity c a b := by
  unfold b6EvalMultiplicity labelledSortedTripleMultiplicity
  have he : (decide (c=a) && decide (a=b)) = true ↔ c=a ∧ a=b := by
    simp only [Bool.and_eq_true,decide_eq_true_eq]
  have ho : (decide (c=a) || decide (a=b)) = true ↔ c=a ∨ a=b := by
    simp only [Bool.or_eq_true,decide_eq_true_eq]
  by_cases h : c=a ∧ a=b
  · rw [Bool.cond_eq_ite,ite_eq_left (he.mpr h),ite_eq_left h]
  · rw [Bool.cond_eq_ite,ite_eq_right (fun hb => h (he.mp hb)),ite_eq_right h]
    by_cases h' : c=a ∨ a=b
    · rw [Bool.cond_eq_ite,ite_eq_left (ho.mpr h'),ite_eq_left h']
    · rw [Bool.cond_eq_ite,ite_eq_right (fun hb => h' (ho.mp hb)),ite_eq_right h']
#print axioms Paper7MomentCounts.b6EvalMultiplicity_eq

theorem b6EvalScalarRange_eq (A B : ℕ) :
    b6EvalScalarRange A B = labelledTripleScalarRange A B := rfl
#print axioms Paper7MomentCounts.b6EvalScalarRange_eq

theorem b6EvalKernel_eq (A B Q : ℕ) :
    b6EvalKernel A B Q = labelledTripleDiscriminantKernel A B Q := by
  classical
  unfold b6EvalKernel labelledTripleDiscriminantKernel
  rw [b6EvalScalarRange_eq]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases h : B6SortedTripleDiscriminantAccept A B c
  · rw [Bool.cond_eq_ite,ite_eq_left ((b6EvalSortedAccept_iff A B c).mpr h),ite_eq_left h]
    simp only [b6EvalMultiplicity_eq,b6EvalHigh_eq,b6EvalLow_eq,b6EvalQWeight_eq]
  · have hb : ¬ b6EvalSortedAccept A B c = true := fun he => h ((b6EvalSortedAccept_iff A B c).mp he)
    rw [Bool.cond_eq_ite,ite_eq_right hb,ite_eq_right h]
#print axioms Paper7MomentCounts.b6EvalKernel_eq

theorem b6EvalTripleGuard_iff (A B : ℕ) :
    b6EvalTripleGuard A B = true ↔ B6TripleStatisticGuard A B := by
  simp only [b6EvalTripleGuard,Bool.and_eq_true,decide_eq_true_eq,B6TripleStatisticGuard,and_assoc]
#print axioms Paper7MomentCounts.b6EvalTripleGuard_iff

theorem b6EvalResidual_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6EvalResidual sm Z Q = b6CatalogResidual sm Z Q := rfl
#print axioms Paper7MomentCounts.b6EvalResidual_eq

theorem b6EvalCatalogAccept_iff (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6EvalCatalogAccept sm Z Q = true ↔ b6CatalogStatisticAccept sm Z Q := by
  unfold b6EvalCatalogAccept b6CatalogStatisticAccept
  simp only [Bool.and_eq_true, decide_eq_true_eq, and_assoc]
  simp only [b6EvalResidual_eq]
#print axioms Paper7MomentCounts.b6EvalCatalogAccept_iff

theorem b6EvalQSplitRange_eq (Z A Q : ℕ) :
    b6EvalQSplitRange Z A Q = labelledTripleQSplitRange Z A Q := rfl
#print axioms Paper7MomentCounts.b6EvalQSplitRange_eq

theorem b6EvalBRange_eq (Z R A : ℕ) :
    b6EvalBRange Z R A = labelledTripleBSplitRange Z R A := by
  classical
  ext B
  simp only [b6EvalBRange,labelledTripleBSplitRange,labelledTripleBSplitLower,
    labelledTripleBSplitUpper,Finset.mem_filter,decide_eq_true_eq]
#print axioms Paper7MomentCounts.b6EvalBRange_eq

theorem b6EvalZRange_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6EvalZRange sm Q = b6CatalogZRange sm Q := rfl
#print axioms Paper7MomentCounts.b6EvalZRange_eq

theorem b6EvalQSplitSum_eq (Z R A B Q : ℕ) :
    b6EvalQSplitSum Z R A B Q = labelledTripleKernelQSplitSum Z R A B Q := by
  unfold b6EvalQSplitSum labelledTripleKernelQSplitSum
  simp only [b6EvalQSplitRange_eq,b6EvalKernel_eq]
#print axioms Paper7MomentCounts.b6EvalQSplitSum_eq

theorem b6EvalASlice_eq (sm : ℤ × ℤ) (Z Q A : ℕ) :
    b6EvalASlice sm Z Q A = b6CatalogBSupportASlice sm Z Q A := by
  classical
  unfold b6EvalASlice b6CatalogBSupportASlice
  simp only [b6EvalResidual_eq,b6EvalBRange_eq]
  apply Finset.sum_congr rfl
  intro B _hB
  have he : (b6EvalTripleGuard A B && b6EvalTripleGuard (Z-A) (b6CatalogResidual sm Z Q-B)) = true ↔
      B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (b6CatalogResidual sm Z Q-B) := by
    simp only [Bool.and_eq_true,b6EvalTripleGuard_iff]
  by_cases h : B6TripleStatisticGuard A B ∧ B6TripleStatisticGuard (Z-A) (b6CatalogResidual sm Z Q-B)
  · rw [Bool.cond_eq_ite,ite_eq_left (he.mpr h),ite_eq_left h]
    exact b6EvalQSplitSum_eq Z (b6CatalogResidual sm Z Q) A B Q
  · rw [Bool.cond_eq_ite,ite_eq_right (fun hb => h (he.mp hb)),ite_eq_right h]
#print axioms Paper7MomentCounts.b6EvalASlice_eq

theorem b6EvalBlock_eq (sm : ℤ × ℤ) (Z Q : ℕ) :
    b6EvalBlock sm Z Q = b6CatalogConvolutionBlock sm Z Q := by
  classical
  rw [b6CatalogConvolutionBlock_eq_B_support]
  unfold b6EvalBlock
  by_cases h : b6CatalogStatisticAccept sm Z Q
  · rw [Bool.cond_eq_ite,ite_eq_left ((b6EvalCatalogAccept_iff sm Z Q).mpr h),ite_eq_left h]
    apply Finset.sum_congr rfl
    intro A _hA
    exact b6EvalASlice_eq sm Z Q A
  · have hb : ¬ b6EvalCatalogAccept sm Z Q = true := fun he => h ((b6EvalCatalogAccept_iff sm Z Q).mp he)
    rw [Bool.cond_eq_ite,ite_eq_right hb,ite_eq_right h]
#print axioms Paper7MomentCounts.b6EvalBlock_eq

theorem b6EvalQSlice_eq (sm : ℤ × ℤ) (Q : ℕ) :
    b6EvalQSlice sm Q = b6CatalogConvolutionQSlice sm Q := by
  unfold b6EvalQSlice b6CatalogConvolutionQSlice
  simp only [b6EvalZRange_eq,b6EvalBlock_eq]
#print axioms Paper7MomentCounts.b6EvalQSlice_eq

theorem b6EvalTotal_eq (sm : ℤ × ℤ) : b6EvalTotal sm = b6CatalogConvolutionTotal sm := by
  unfold b6EvalTotal b6CatalogConvolutionTotal
  simp only [b6EvalQSlice_eq]
#print axioms Paper7MomentCounts.b6EvalTotal_eq

theorem b6EvalTotal_eq_original_theta_ncard (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6EvalTotal sm = ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6EvalTotal_eq]
  exact b6CatalogConvolutionTotal_eq_theta_ncard sm hsm
#print axioms Paper7MomentCounts.b6EvalTotal_eq_original_theta_ncard

end Paper7MomentCounts
