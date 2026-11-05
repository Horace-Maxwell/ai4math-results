import Research.Backfill.Paper7.MomentB6FeatureGuard

/-! Source-only candidate by /root/moment_t9_recovery_0906.
Partition of the complete original labelled b6,N42 predicate by its unique
ordered z-vector and total Q. No coordinate permutation quotient is taken. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

abbrev B6ZQIndex := Paper7Budget.BoundedTuple 6 36 × Fin 19
#print axioms Paper7MomentCounts.B6ZQIndex

def b6ZQAccept (z : Fin 6 → ℕ) (Q : ℕ) : Prop :=
  0 < (∑ i, z i) + Q ∧ (∑ i, z i) + Q ≤ 36 ∧
    b6FeatureGuard ((∑ i, z i) + Q) Q
      (12 + 3*((∑ i, z i : ℕ) : ℤ) + 2*(Q : ℤ) + ∑ i, (z i : ℤ)^2)
#print axioms Paper7MomentCounts.b6ZQAccept

/-- Membership is constant on each genuine z,Q fibre. -/
theorem b6_candB1_on_zq_fibre (z : Fin 6 → ℕ) (Q : ℕ) (x : PQ 6)
    (hz : ∀ i, x.1 i + x.2 i = z i) (hQ : qSum x = Q) :
    x ∈ CandB1 6 42 ↔ b6ZQAccept z Q := by
  have h := b6_zq_candB1_iff (pqToZQ x)
  have hback : zqToPQ (pqToZQ x) = x := (pqEquivZQ 6).left_inv x
  have hvec : (pqToZQ x).val.1 = z := funext hz
  have hsum : (∑ i, (pqToZQ x).val.2 i) = Q := hQ
  rw [hback, hvec, hsum] at h
  exact h
#print axioms Paper7MomentCounts.b6_candB1_on_zq_fibre

def b6CandidateIndex (x : {x : PQ 6 // x ∈ CandB1 6 42}) : B6ZQIndex :=
  (⟨fun i => x.val.1 i + x.val.2 i, by
      have hb := x.property.1.2
      change 6 + (pSum x.val + 2*qSum x.val) ≤ 42 at hb
      rw [Finset.sum_add_distrib]
      change pSum x.val + qSum x.val ≤ 36
      omega⟩,
   ⟨qSum x.val, by
      have hb := (budget_sum_bounds 6 42 x.val x.property.1).2
      omega⟩)
#print axioms Paper7MomentCounts.b6CandidateIndex

theorem b6CandidateIndex_eq_iff (x : {x : PQ 6 // x ∈ CandB1 6 42}) (r : B6ZQIndex) :
    b6CandidateIndex x = r ↔
      (∀ i, x.val.1 i + x.val.2 i = r.1.val i) ∧ qSum x.val = r.2.val := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro i
      exact congrArg (fun a : B6ZQIndex => a.1.val i) h
    · exact congrArg (fun a : B6ZQIndex => a.2.val) h
  · rintro ⟨hz, hQ⟩
    apply Prod.ext
    · apply Subtype.ext
      exact funext hz
    · exact Fin.ext hQ
#print axioms Paper7MomentCounts.b6CandidateIndex_eq_iff

abbrev B6OriginalZQFibre (r : B6ZQIndex) :=
  {x : PQ 6 // (∀ i, x.1 i + x.2 i = r.1.val i) ∧
    qSum x = r.2.val ∧ x ∈ CandB1 6 42}
#print axioms Paper7MomentCounts.B6OriginalZQFibre

def b6CandidateIndexFibreEquiv (r : B6ZQIndex) :
    {x : {x : PQ 6 // x ∈ CandB1 6 42} // b6CandidateIndex x = r} ≃
      B6OriginalZQFibre r where
  toFun x := ⟨x.val.val,
    ((b6CandidateIndex_eq_iff x.val r).mp x.property).1,
    ((b6CandidateIndex_eq_iff x.val r).mp x.property).2, x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2.2⟩,
    (b6CandidateIndex_eq_iff ⟨x.val,x.property.2.2⟩ r).mpr
      ⟨x.property.1,x.property.2.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
#print axioms Paper7MomentCounts.b6CandidateIndexFibreEquiv

instance b6OriginalZQFibreFinite (r : B6ZQIndex) : Finite (B6OriginalZQFibre r) := by
  let : Finite {x : PQ 6 // x ∈ CandB1 6 42} := candB1_finite 6 42
  apply Finite.of_injective
    (fun x : B6OriginalZQFibre r => (⟨x.val,x.property.2.2⟩ : {x : PQ 6 // x ∈ CandB1 6 42}))
  intro x y h
  apply Subtype.ext
  exact congrArg (fun a : {x : PQ 6 // x ∈ CandB1 6 42} => a.val) h
#print axioms Paper7MomentCounts.b6OriginalZQFibreFinite

/-- Full coverage and disjointness follow from a function's actual fibres. -/
def b6CandidatePartitionEquiv :
    {x : PQ 6 // x ∈ CandB1 6 42} ≃ Σ r : B6ZQIndex, B6OriginalZQFibre r :=
  (Equiv.sigmaFiberEquiv b6CandidateIndex).symm.trans
    (Equiv.sigmaCongrRight b6CandidateIndexFibreEquiv)
#print axioms Paper7MomentCounts.b6CandidatePartitionEquiv

theorem b6_zq_fibres_disjoint (r s : B6ZQIndex) (x : PQ 6)
    (hr : (∀ i, x.1 i + x.2 i = r.1.val i) ∧ qSum x = r.2.val)
    (hs : (∀ i, x.1 i + x.2 i = s.1.val i) ∧ qSum x = s.2.val) : r = s := by
  apply Prod.ext
  · apply Subtype.ext
    funext i
    exact (hr.1 i).symm.trans (hs.1 i)
  · exact Fin.ext (hr.2.symm.trans hs.2)
#print axioms Paper7MomentCounts.b6_zq_fibres_disjoint

theorem b6OriginalZQFibre_card (r : B6ZQIndex) :
    Nat.card (B6OriginalZQFibre r) =
      if b6ZQAccept r.1.val r.2.val then
        Paper7MomentDP.boundedQDP 6 r.1.val r.2.val else 0 := by
  by_cases ha : b6ZQAccept r.1.val r.2.val
  · rw [ite_eq_left ha]
    calc
      Nat.card (B6OriginalZQFibre r) =
          Nat.card {x : PQ 6 // (∀ i, x.1 i + x.2 i = r.1.val i) ∧
            qSum x = r.2.val} := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        constructor
        · intro hx
          exact ⟨hx.1,hx.2.1⟩
        · rintro ⟨hz,hQ⟩
          exact ⟨hz,hQ,(b6_candB1_on_zq_fibre r.1.val r.2.val x hz hQ).mpr ha⟩
      _ = Paper7MomentDP.boundedQDP 6 r.1.val r.2.val :=
        zqFibre_card_eq_boundedQDP 6 r.1.val r.2.val
  · let : IsEmpty (B6OriginalZQFibre r) := ⟨by
      intro x
      exact ha ((b6_candB1_on_zq_fibre r.1.val r.2.val x.val
        x.property.1 x.property.2.1).mp x.property.2.2)⟩
    rw [ite_eq_right ha, Nat.card_of_isEmpty]
#print axioms Paper7MomentCounts.b6OriginalZQFibre_card

end Paper7MomentCounts
