import Research.Backfill.Paper7.MomentB6ZQPartition

/-! Source-only candidate by /root/moment_t9_recovery_0906.
Exact finite weighted sum and37 complete total-Z certificate slices.
No row values, total cardinality, or unverified DP table are assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6ZQBlock (r : B6ZQIndex) : ℕ :=
  if b6ZQAccept r.1.val r.2.val then
    Paper7MomentDP.boundedQDP 6 r.1.val r.2.val else 0
#print axioms Paper7MomentCounts.b6ZQBlock

def b6LabelledZQSum : ℕ := ∑ r : B6ZQIndex, b6ZQBlock r
#print axioms Paper7MomentCounts.b6LabelledZQSum

theorem b6_candB1_ncard_eq_zq_sum : (CandB1 6 42).ncard = b6LabelledZQSum := by
  change Nat.card {x : PQ 6 // x ∈ CandB1 6 42} = _
  calc
    Nat.card {x : PQ 6 // x ∈ CandB1 6 42} =
        Nat.card (Σ r : B6ZQIndex, B6OriginalZQFibre r) :=
      Nat.card_congr b6CandidatePartitionEquiv
    _ = ∑ r : B6ZQIndex, Nat.card (B6OriginalZQFibre r) := Nat.card_sigma
    _ = b6LabelledZQSum :=
      Finset.sum_congr rfl (fun r _ => b6OriginalZQFibre_card r)
#print axioms Paper7MomentCounts.b6_candB1_ncard_eq_zq_sum

theorem b6_candD2_ncard_eq_zq_sum : (CandD2 6 42).ncard = b6LabelledZQSum := by
  rw [candD2_ncard_eq_candB1_of_even 6 42 (by decide)]
  exact b6_candB1_ncard_eq_zq_sum
#print axioms Paper7MomentCounts.b6_candD2_ncard_eq_zq_sum

/-- Q above the total coordinate capacity has no assignments. -/
theorem b6_boundedQDP_zero_above_capacity (z : Fin 6 → ℕ) (Q : ℕ)
    (hQ : (∑ i, z i) < Q) : Paper7MomentDP.boundedQDP 6 z Q = 0 := by
  rw [Paper7MomentDP.boundedQDP_eq_fibre_card]
  let : IsEmpty {q : (i : Fin 6) → Fin (z i + 1) // ∑ i, (q i).val = Q} := ⟨by
    rintro ⟨q,hq⟩
    have hc : (∑ i, (q i).val) ≤ ∑ i, z i :=
      Finset.sum_le_sum (fun i _ => Nat.le_of_lt_succ (q i).isLt)
    omega⟩
  exact Nat.card_of_isEmpty
#print axioms Paper7MomentCounts.b6_boundedQDP_zero_above_capacity

theorem b6ZQBlock_zero_of_Q_above_capacity (r : B6ZQIndex)
    (hQ : (∑ i, r.1.val i) < r.2.val) : b6ZQBlock r = 0 := by
  unfold b6ZQBlock
  rw [b6_boundedQDP_zero_above_capacity r.1.val r.2.val hQ]
  split_ifs <;> rfl
#print axioms Paper7MomentCounts.b6ZQBlock_zero_of_Q_above_capacity

theorem b6ZQBlock_zero_of_budget (r : B6ZQIndex)
    (hb : (∑ i, r.1.val i) + r.2.val = 0 ∨
      36 < (∑ i, r.1.val i) + r.2.val) : b6ZQBlock r = 0 := by
  have ha : ¬ b6ZQAccept r.1.val r.2.val := by
    intro hg
    have hpos := hg.1
    have hbound := hg.2.1
    omega
  exact ite_eq_right ha
#print axioms Paper7MomentCounts.b6ZQBlock_zero_of_budget

def b6TotalZTag (r : B6ZQIndex) : Fin 37 :=
  ⟨∑ i, r.1.val i, Nat.lt_succ_of_le r.1.property⟩
#print axioms Paper7MomentCounts.b6TotalZTag

def b6LabelledZSlice (Z : Fin 37) : ℕ :=
  ∑ r : B6ZQIndex, if b6TotalZTag r = Z then b6ZQBlock r else 0
#print axioms Paper7MomentCounts.b6LabelledZSlice

theorem finite_sum_eq_tagged_slices {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq β] (tag : α → β) (weight : α → ℕ) :
    (∑ a, weight a) = ∑ b, ∑ a, if tag a = b then weight a else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _ha
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
#print axioms Paper7MomentCounts.finite_sum_eq_tagged_slices

/-- Every ordered z-vector belongs to exactly one of these37 total-Z slices. -/
theorem b6LabelledZQSum_eq_slices :
    b6LabelledZQSum = ∑ Z : Fin 37, b6LabelledZSlice Z := by
  exact finite_sum_eq_tagged_slices b6TotalZTag b6ZQBlock
#print axioms Paper7MomentCounts.b6LabelledZQSum_eq_slices

/-- A concrete future certificate must discharge all37 complete slice identities. -/
def B6LabelledSliceCertificate (values : Fin 37 → ℕ) : Prop :=
  ∀ Z, b6LabelledZSlice Z = values Z
#print axioms Paper7MomentCounts.B6LabelledSliceCertificate

theorem b6_candB1_ncard_of_slice_certificate (values : Fin 37 → ℕ)
    (hvalues : B6LabelledSliceCertificate values) :
    (CandB1 6 42).ncard = ∑ Z : Fin 37, values Z := by
  rw [b6_candB1_ncard_eq_zq_sum, b6LabelledZQSum_eq_slices]
  exact Finset.sum_congr rfl (fun Z _ => hvalues Z)
#print axioms Paper7MomentCounts.b6_candB1_ncard_of_slice_certificate

theorem b6_candD2_ncard_of_slice_certificate (values : Fin 37 → ℕ)
    (hvalues : B6LabelledSliceCertificate values) :
    (CandD2 6 42).ncard = ∑ Z : Fin 37, values Z := by
  rw [candD2_ncard_eq_candB1_of_even 6 42 (by decide)]
  exact b6_candB1_ncard_of_slice_certificate values hvalues
#print axioms Paper7MomentCounts.b6_candD2_ncard_of_slice_certificate

end Paper7MomentCounts
