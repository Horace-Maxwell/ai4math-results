import Research.Backfill.Paper7.EvenMomentFeature
import Research.Backfill.Paper7.BoundedQSumDP

/-! Exact original PQ coordinates for the proposed finite coefficient certificate.
No numerical candidate data, recurrence table, or target cardinality is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev ZQCoordinates (b : ℕ) := {x : PQ b // ∀ i, x.2 i ≤ x.1 i}
#print axioms Paper7MomentCounts.ZQCoordinates

def pqToZQ {b : ℕ} (x : PQ b) : ZQCoordinates b :=
  ⟨(fun i => x.1 i + x.2 i, x.2), fun _i => Nat.le_add_left _ _⟩
#print axioms Paper7MomentCounts.pqToZQ

def zqToPQ {b : ℕ} (x : ZQCoordinates b) : PQ b :=
  (fun i => x.val.1 i - x.val.2 i, x.val.2)
#print axioms Paper7MomentCounts.zqToPQ

def pqEquivZQ (b : ℕ) : PQ b ≃ ZQCoordinates b where
  toFun := pqToZQ
  invFun := zqToPQ
  left_inv x := by
    apply Prod.ext
    · funext i
      exact Nat.add_sub_cancel_right _ _
    · rfl
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact Nat.sub_add_cancel (x.property i)
    · rfl
#print axioms Paper7MomentCounts.pqEquivZQ

theorem zq_qSum (b : ℕ) (x : ZQCoordinates b) :
    qSum (zqToPQ x) = ∑ i, x.val.2 i := rfl
#print axioms Paper7MomentCounts.zq_qSum

theorem zq_weight (b : ℕ) (x : ZQCoordinates b) :
    weight (zqToPQ x) = (∑ i, x.val.1 i) + ∑ i, x.val.2 i := by
  change (∑ i, (x.val.1 i - x.val.2 i)) + 2 * (∑ i, x.val.2 i) = _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hi := x.property i
  omega
#print axioms Paper7MomentCounts.zq_weight

theorem thetaV_zq (z q : ℕ) (hq : q ≤ z) :
    thetaV (z-q) q = (z : ℤ)^2 + 3*z + 2 + 2*q := by
  unfold thetaV
  rw [Nat.cast_sub hq]
  ring
#print axioms Paper7MomentCounts.thetaV_zq

theorem zq_theta (b : ℕ) (x : ZQCoordinates b) :
    theta (zqToPQ x) = 2*(b : ℤ) + 3*((∑ i, x.val.1 i : ℕ) : ℤ) +
      2*((∑ i, x.val.2 i : ℕ) : ℤ) + ∑ i, (x.val.1 i : ℤ)^2 := by
  have hsum : theta (zqToPQ x) =
      ∑ i, ((x.val.1 i : ℤ)^2 + 3*x.val.1 i + 2 + 2*x.val.2 i) := by
    unfold theta
    apply Finset.sum_congr rfl
    intro i _
    exact thetaV_zq _ _ (x.property i)
  rw [hsum]
  simp only [Finset.sum_add_distrib, Nat.cast_sum, Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring
#print axioms Paper7MomentCounts.zq_theta

theorem zq_budget_iff (b N : ℕ) (x : ZQCoordinates b) :
    Budget b N (zqToPQ x) ↔
      0 < (∑ i, x.val.1 i) + ∑ i, x.val.2 i ∧
        b + ((∑ i, x.val.1 i) + ∑ i, x.val.2 i) ≤ N := by
  unfold Budget
  rw [zq_weight]
#print axioms Paper7MomentCounts.zq_budget_iff

/-- No positive pendant or support hypothesis has been added. In particular,
zero entries are allowed; positive total weight is exactly the original Budget. -/
theorem zq_candB1_iff (b N : ℕ) (hb : Even b) (x : ZQCoordinates b) :
    zqToPQ x ∈ CandB1 b N ↔
      (0 < (∑ i, x.val.1 i) + ∑ i, x.val.2 i ∧
        b + ((∑ i, x.val.1 i) + ∑ i, x.val.2 i) ≤ N) ∧
      ∃ a : Counts, evenFeatureCondition b N
        ((∑ i, x.val.1 i) + ∑ i, x.val.2 i) (∑ i, x.val.2 i)
        (2*(b : ℤ) + 3*((∑ i, x.val.1 i : ℕ) : ℤ) +
          2*((∑ i, x.val.2 i : ℕ) : ℤ) + ∑ i, (x.val.1 i : ℤ)^2) a := by
  change (Budget b N (zqToPQ x) ∧ MomentPass false true false b N (zqToPQ x)) ↔ _
  rw [zq_budget_iff, momentPass_iff_evenFeature b N (zqToPQ x) hb,
    zq_weight, zq_qSum, zq_theta]
#print axioms Paper7MomentCounts.zq_candB1_iff

/-- For a fixed z-vector and Q, actual PQ rows correspond exactly to the
finite, independently bounded q-coordinates. Feature witnesses are absent
from this equivalence and cannot multiply its cardinality. -/
def zqFibreEquiv (b : ℕ) (z : Fin b → ℕ) (Q : ℕ) :
    {x : PQ b // (∀ i, x.1 i + x.2 i = z i) ∧ qSum x = Q} ≃
      {q : (i : Fin b) → Fin (z i + 1) // (∑ i, (q i).val) = Q} where
  toFun x := ⟨fun i => ⟨x.val.2 i, by
    have hi := x.property.1 i
    omega⟩, x.property.2⟩
  invFun q := ⟨(fun i => z i - (q.val i).val, fun i => (q.val i).val), by
    refine ⟨?_, q.property⟩
    intro i
    exact Nat.sub_add_cancel (Nat.le_of_lt_succ (q.val i).isLt)⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      change z i - x.val.2 i = x.val.1 i
      have hi := x.property.1 i
      omega
    · rfl
  right_inv q := by
    apply Subtype.ext
    funext i
    apply Fin.ext
    rfl
#print axioms Paper7MomentCounts.zqFibreEquiv

theorem zqFibre_card (b : ℕ) (z : Fin b → ℕ) (Q : ℕ) :
    Nat.card {x : PQ b // (∀ i, x.1 i + x.2 i = z i) ∧ qSum x = Q} =
      Nat.card {q : (i : Fin b) → Fin (z i + 1) // (∑ i, (q i).val) = Q} :=
  Nat.card_congr (zqFibreEquiv b z Q)
#print axioms Paper7MomentCounts.zqFibre_card

/-- The concrete coefficient recursion counts the original PQ fibre, rather
than a set of spectral-feature witnesses. -/
theorem zqFibre_card_eq_boundedQDP (b : ℕ) (z : Fin b → ℕ) (Q : ℕ) :
    Nat.card {x : PQ b // (∀ i, x.1 i + x.2 i = z i) ∧ qSum x = Q} =
      Paper7MomentDP.boundedQDP b z Q := by
  rw [zqFibre_card]
  exact (Paper7MomentDP.boundedQDP_eq_fibre_card b z Q).symm
#print axioms Paper7MomentCounts.zqFibre_card_eq_boundedQDP

end Paper7MomentCounts
