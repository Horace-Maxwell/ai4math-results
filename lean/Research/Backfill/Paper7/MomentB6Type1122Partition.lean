import Research.Backfill.Paper7.MomentB6Type1122Reflection

/-! UNCOMPILED exact original-fibre partition. The final finite sum is a
symbolic interface, NOT an instruction to enumerate this index or evaluate
it with decide. An analytic catalog/Q-recovery proof is still required for
a numerical endpoint. No native or other numerical certificate is present. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6Type1122Capacity : Fin 4 → ℕ := ![34,18,18,34]
#print axioms Paper7MomentCounts.b6Type1122Capacity

abbrev B6Type1122Index := ((i : Fin 4) → Fin (b6Type1122Capacity i+1)) × Fin 19
#print axioms Paper7MomentCounts.B6Type1122Index

def b6Type1122CandidateIndex
    (x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}) : B6Type1122Index := by
  refine (fun i => ⟨x.val.1 i+x.val.2 i,?_⟩,⟨b6Type1122Total x.val.2,?_⟩)
  · have hg := (b6_type1122_candB1_iff x.val).mp x.property
    have hq := b6_type1122_original_fibre_Q_le
      (fun i => x.val.1 i+x.val.2 i) (b6Type1122Total x.val.2)
      ⟨x.val,fun _ => rfl,rfl⟩
    have hb := b6_type1122_guard_budget_bounds _ _ hg hq
    have hs := b6_type1122_guard_singleton_bounds _ _ hg
    fin_cases i
    · exact Nat.lt_succ_of_le hs.1
    · exact Nat.lt_succ_of_le hb.2.2.2.2.1
    · exact Nat.lt_succ_of_le hb.2.2.2.2.2
    · exact Nat.lt_succ_of_le hs.2
  · have hg := (b6_type1122_candB1_iff x.val).mp x.property
    have hq := b6_type1122_original_fibre_Q_le
      (fun i => x.val.1 i+x.val.2 i) (b6Type1122Total x.val.2)
      ⟨x.val,fun _ => rfl,rfl⟩
    exact Nat.lt_succ_of_le (b6_type1122_guard_budget_bounds _ _ hg hq).2.1
#print axioms Paper7MomentCounts.b6Type1122CandidateIndex

theorem b6_type1122_candidate_index_eq_iff
    (x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}) (r : B6Type1122Index) :
    b6Type1122CandidateIndex x = r ↔
      (∀ i, x.val.1 i+x.val.2 i=(r.1 i).val) ∧ b6Type1122Total x.val.2=r.2.val := by
  constructor
  · intro h
    exact ⟨fun i => congrArg (fun s : B6Type1122Index => (s.1 i).val) h,
      congrArg (fun s : B6Type1122Index => s.2.val) h⟩
  · rintro ⟨hz,hQ⟩
    apply Prod.ext
    · funext i
      exact Fin.ext (hz i)
    · exact Fin.ext hQ
#print axioms Paper7MomentCounts.b6_type1122_candidate_index_eq_iff

abbrev B6Type1122AcceptedFibre (r : B6Type1122Index) :=
  {u : PQ 4 // (∀ i, u.1 i+u.2 i=(r.1 i).val) ∧
    b6Type1122Total u.2=r.2.val ∧ b6Type1122Row u ∈ CandB1 6 42}
#print axioms Paper7MomentCounts.B6Type1122AcceptedFibre

def b6Type1122IndexFibreEquiv (r : B6Type1122Index) :
    {x : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} //
      b6Type1122CandidateIndex x=r} ≃ B6Type1122AcceptedFibre r where
  toFun x := ⟨x.val.val,
    ((b6_type1122_candidate_index_eq_iff x.val r).mp x.property).1,
    ((b6_type1122_candidate_index_eq_iff x.val r).mp x.property).2,x.val.property⟩
  invFun x := ⟨⟨x.val,x.property.2.2⟩,
    (b6_type1122_candidate_index_eq_iff ⟨x.val,x.property.2.2⟩ r).mpr
      ⟨x.property.1,x.property.2.1⟩⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
#print axioms Paper7MomentCounts.b6Type1122IndexFibreEquiv

instance b6Type1122CandidateFinite :
    Finite {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} := by
  let : Finite {x : PQ 6 // x ∈ CandB1 6 42} := candB1_finite 6 42
  apply Finite.of_injective
    (fun u : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} =>
      (⟨b6Type1122Row u.val,u.property⟩ : {x : PQ 6 // x ∈ CandB1 6 42}))
  intro u v h
  apply Subtype.ext
  exact b6_type1122_row_injective (congrArg Subtype.val h)
#print axioms Paper7MomentCounts.b6Type1122CandidateFinite

instance b6Type1122AcceptedFibreFinite (r : B6Type1122Index) :
    Finite (B6Type1122AcceptedFibre r) := by
  apply Finite.of_injective
    (fun x : B6Type1122AcceptedFibre r =>
      (⟨x.val,x.property.2.2⟩ : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42}))
  intro x y h
  apply Subtype.ext
  exact congrArg (fun u : {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} => u.val) h
#print axioms Paper7MomentCounts.b6Type1122AcceptedFibreFinite

def b6Type1122PartitionEquiv :
    {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} ≃
      Σ r : B6Type1122Index, B6Type1122AcceptedFibre r :=
  (Equiv.sigmaFiberEquiv b6Type1122CandidateIndex).symm.trans
    (Equiv.sigmaCongrRight b6Type1122IndexFibreEquiv)
#print axioms Paper7MomentCounts.b6Type1122PartitionEquiv

theorem b6_type1122_accepted_fibre_card (r : B6Type1122Index) :
    Nat.card (B6Type1122AcceptedFibre r) =
      if b6Type1122Guard (fun i => (r.1 i).val) r.2.val then
        b6Type1122Coefficient (r.1 0).val (r.1 1).val (r.1 2).val (r.1 3).val r.2.val
      else 0 := by
  by_cases ha : b6Type1122Guard (fun i => (r.1 i).val) r.2.val
  · rw [ite_eq_left ha]
    calc
      Nat.card (B6Type1122AcceptedFibre r) =
          Nat.card (B6Type1122OriginalFibre (fun i => (r.1 i).val) r.2.val) := by
        apply Nat.card_congr
        apply Equiv.subtypeEquivRight
        intro x
        constructor
        · intro hx
          exact ⟨hx.1,hx.2.1⟩
        · rintro ⟨hz,hQ⟩
          exact ⟨hz,hQ,(b6_type1122_original_fibre_acceptance _ _ ⟨x,hz,hQ⟩).mpr ha⟩
      _ = b6Type1122Coefficient (r.1 0).val (r.1 1).val (r.1 2).val (r.1 3).val r.2.val :=
        b6_type1122_original_fibre_card _ _
  · let : IsEmpty (B6Type1122AcceptedFibre r) := ⟨fun x =>
      ha ((b6_type1122_original_fibre_acceptance _ _
        ⟨x.val,x.property.1,x.property.2.1⟩).mp x.property.2.2)⟩
    rw [ite_eq_right ha,Nat.card_of_isEmpty]
#print axioms Paper7MomentCounts.b6_type1122_accepted_fibre_card

/-- Symbolic only. Do not use a whole-index finite decision to evaluate this. -/
def b6Type1122CoefficientSum : ℕ :=
  ∑ r : B6Type1122Index,
    if b6Type1122Guard (fun i => (r.1 i).val) r.2.val then
      b6Type1122Coefficient (r.1 0).val (r.1 1).val (r.1 2).val (r.1 3).val r.2.val
    else 0
#print axioms Paper7MomentCounts.b6Type1122CoefficientSum

theorem b6_type1122_original_count_eq_coefficient_sum :
    Nat.card {u : PQ 4 // b6Type1122Row u ∈ CandB1 6 42} =
      b6Type1122CoefficientSum := by
  rw [Nat.card_congr b6Type1122PartitionEquiv,Nat.card_sigma]
  exact Finset.sum_congr rfl (fun r _ => b6_type1122_accepted_fibre_card r)
#print axioms Paper7MomentCounts.b6_type1122_original_count_eq_coefficient_sum

end Paper7MomentCounts

namespace Paper7MomentCanonicalSix
open Paper7MomentCounts

theorem b6_reflection_zero_count_eq_coefficient_sum :
    b6FixedCount (b6Reflection 0) = b6Type1122CoefficientSum := by
  rw [b6_reflection_zero_count_eq_original_type1122,
    b6_type1122_original_count_eq_coefficient_sum]
#print axioms Paper7MomentCanonicalSix.b6_reflection_zero_count_eq_coefficient_sum

end Paper7MomentCanonicalSix
