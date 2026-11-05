import Research.Backfill.Paper7.MomentB6ComputableKernel

/-! Candidate arithmetic prefilter after actual933's whole-theta heartbeat failure.
Only necessary root-free scalar inequalities are evaluated by the added filter.
The original discriminant accept, multiplicities, signed q-weights and all outer
ranges/guards remain. No measured speed improvement is asserted. All parameters,
including Q=0/1 and Nat subtraction boundaries, are retained. -/
set_option autoImplicit false
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators

def b6ScalarArithmeticGuard (A B c : ℕ) : Bool :=
  decide (2*c^2+(A-c)^2≤2*B) &&
    decide (2*B≤2*c^2+(A-c)^2+(3*c-A)^2)
#print axioms Paper7MomentCounts.b6ScalarArithmeticGuard

theorem b6ScalarArithmeticGuard_of_sortedAccept (A B c : ℕ)
    (h : b6EvalSortedAccept A B c = true) :
    b6ScalarArithmeticGuard A B c = true := by
  have hp : c≤A ∧ b6EvalRoot A B c≤A-c ∧
      A+b6EvalRoot A B c≤3*c ∧ (A-c)%2=b6EvalRoot A B c%2 ∧
      b6EvalRoot A B c^2+(A-c)^2+2*c^2=2*B := by
    simpa only [b6EvalSortedAccept,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using h
  have hr : b6EvalRoot A B c≤3*c-A := by omega
  have hs : b6EvalRoot A B c^2≤(3*c-A)^2 := pow_le_pow_left' hr 2
  have hl : 2*c^2+(A-c)^2≤2*B := by omega
  have hu : 2*B≤2*c^2+(A-c)^2+(3*c-A)^2 := by omega
  unfold b6ScalarArithmeticGuard
  rw [decide_eq_true hl,decide_eq_true hu]
  decide
#print axioms Paper7MomentCounts.b6ScalarArithmeticGuard_of_sortedAccept

def b6ArithmeticPrunedScalarRange (A B : ℕ) : Finset ℕ :=
  (b6EvalScalarRange A B).filter (fun c => b6ScalarArithmeticGuard A B c = true)
#print axioms Paper7MomentCounts.b6ArithmeticPrunedScalarRange

def b6ArithmeticPrunedKernel (A B Q : ℕ) : ℤ :=
  ∑ c ∈ b6ArithmeticPrunedScalarRange A B,
    bif b6EvalSortedAccept A B c then
      (b6EvalMultiplicity c (b6EvalHigh A B c) (b6EvalLow A B c) : ℤ) *
        b6EvalQWeight c (b6EvalHigh A B c) (b6EvalLow A B c) Q
    else 0
#print axioms Paper7MomentCounts.b6ArithmeticPrunedKernel

theorem b6ArithmeticPrunedKernel_eq (A B Q : ℕ) :
    b6ArithmeticPrunedKernel A B Q = b6EvalKernel A B Q := by
  unfold b6ArithmeticPrunedKernel b6ArithmeticPrunedScalarRange b6EvalKernel
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases h : b6ScalarArithmeticGuard A B c = true
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    have hn : ¬ b6EvalSortedAccept A B c = true :=
      fun ha => h (b6ScalarArithmeticGuard_of_sortedAccept A B c ha)
    rw [Bool.cond_eq_ite,ite_eq_right hn]
#print axioms Paper7MomentCounts.b6ArithmeticPrunedKernel_eq

def b6ArithmeticPrunedTotal (sm : ℤ × ℤ) : ℤ :=
  ∑ Q ∈ Finset.range 19,
    ∑ Z ∈ b6EvalZRange sm Q,
      bif b6EvalCatalogAccept sm Z Q then
        ∑ A ∈ Finset.range (Z+1),
          ∑ B ∈ b6EvalBRange Z (b6EvalResidual sm Z Q) A,
            bif (b6EvalTripleGuard A B &&
                b6EvalTripleGuard (Z-A) (b6EvalResidual sm Z Q-B)) then
              ∑ t ∈ b6EvalQSplitRange Z A Q,
                b6ArithmeticPrunedKernel A B t *
                  b6ArithmeticPrunedKernel (Z-A) (b6EvalResidual sm Z Q-B) (Q-t)
            else 0
      else 0
#print axioms Paper7MomentCounts.b6ArithmeticPrunedTotal

theorem b6ArithmeticPrunedTotal_eq (sm : ℤ × ℤ) :
    b6ArithmeticPrunedTotal sm = b6EvalTotal sm := by
  unfold b6ArithmeticPrunedTotal b6EvalTotal b6EvalQSlice b6EvalBlock
    b6EvalASlice b6EvalQSplitSum
  simp only [b6ArithmeticPrunedKernel_eq]
#print axioms Paper7MomentCounts.b6ArithmeticPrunedTotal_eq

theorem b6ArithmeticPrunedTotal_eq_original_B1_theta_ncard
    (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6ArithmeticPrunedTotal sm =
      ({x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6ArithmeticPrunedTotal_eq]
  exact b6EvalTotal_eq_original_theta_ncard sm hsm
#print axioms Paper7MomentCounts.b6ArithmeticPrunedTotal_eq_original_B1_theta_ncard

theorem b6ArithmeticPrunedTotal_eq_original_D2_theta_ncard
    (sm : ℤ × ℤ) (hsm : sm ∈ b6FeatureCatalog) :
    b6ArithmeticPrunedTotal sm =
      ({x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = sm.2}.ncard : ℤ) := by
  rw [b6_candD2_theta_fibre_eq_candB1 sm.2]
  exact b6ArithmeticPrunedTotal_eq_original_B1_theta_ncard sm hsm
#print axioms Paper7MomentCounts.b6ArithmeticPrunedTotal_eq_original_D2_theta_ncard

end Paper7MomentCounts
