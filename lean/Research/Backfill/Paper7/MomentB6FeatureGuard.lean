import Research.Backfill.Paper7.MomentB6FeatureCatalog
import Research.Backfill.Paper7.MomentBudgetEncoding
import Research.Backfill.Paper7.ZQBudgetCoordinates

/-! Source-only candidate by /root/moment_t9_recovery_0906.
Exact original b6,N42 acceptance, using the complete spectral catalog once as
an existential guard. No spectral-witness multiplicity is counted. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b6FeatureGuard (W Q : ℕ) (T : ℤ) : Prop :=
  ∃ sm ∈ b6FeatureCatalog,
    sm.2 = T ∧ sm.1 ≤ (6 + W : ℤ) ∧ (6 + W : ℤ) - max (Q : ℤ) 2 ≤ sm.1
#print axioms Paper7MomentCounts.b6FeatureGuard

/-- The b=4 correction is absent in the original b=6 definition. -/
theorem b6_targetTheta_eq_m4 (s : SpectralCounts) : targetTheta 6 s = m4 6 s := by
  have he : Even (6 : ℕ) := by decide
  norm_num [targetTheta, he]
#print axioms Paper7MomentCounts.b6_targetTheta_eq_m4

theorem b6_evenFeatureCondition_iff (W Q : ℕ) (T : ℤ) (a : Counts) :
    evenFeatureCondition 6 42 W Q T a ↔
      B6FeatureCore a ∧ m4 6 (a, 0) = T ∧
        s2 6 (a, 0) ≤ (6 + W : ℤ) ∧
        (6 + W : ℤ) - max (Q : ℤ) 2 ≤ s2 6 (a, 0) := by
  norm_num [evenFeatureCondition, B6FeatureCore, and_assoc]
#print axioms Paper7MomentCounts.b6_evenFeatureCondition_iff

theorem b6_feature_guard_iff (W Q : ℕ) (T : ℤ) :
    (∃ a : Counts, evenFeatureCondition 6 42 W Q T a) ↔ b6FeatureGuard W Q T := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hcore, hM, hS, hload⟩ := (b6_evenFeatureCondition_iff W Q T a).mp ha
    exact ⟨(s2 6 (a, 0),m4 6 (a, 0)), b6Feature_mem_catalog a hcore, hM, hS, hload⟩
  · rintro ⟨⟨S,M⟩, hmem, hM, hS, hload⟩
    obtain ⟨a, hcore, hSa, hMa⟩ := (b6FeatureCatalog_iff S M).mp hmem
    refine ⟨a, (b6_evenFeatureCondition_iff W Q T a).mpr ?_⟩
    exact ⟨hcore, hMa.trans hM, hSa.symm ▸ hS, hSa.symm ▸ hload⟩
#print axioms Paper7MomentCounts.b6_feature_guard_iff

theorem b6_momentPass_iff (x : PQ 6) :
    MomentPass false true false 6 42 x ↔ b6FeatureGuard (weight x) (qSum x) (theta x) := by
  rw [momentPass_iff_evenFeature 6 42 x (by decide), b6_feature_guard_iff]
#print axioms Paper7MomentCounts.b6_momentPass_iff

def b6CandidateGuard (x : PQ 6) : Prop :=
  0 < weight x ∧ weight x ≤ 36 ∧ b6FeatureGuard (weight x) (qSum x) (theta x)
#print axioms Paper7MomentCounts.b6CandidateGuard

/-- Full original labelled predicate, including the strict positive budget. -/
theorem b6_candB1_iff_guard (x : PQ 6) :
    x ∈ CandB1 6 42 ↔ b6CandidateGuard x := by
  change (Budget 6 42 x ∧ MomentPass false true false 6 42 x) ↔ _
  rw [b6_momentPass_iff]
  unfold Budget b6CandidateGuard
  constructor
  · rintro ⟨⟨hpos, hbound⟩, hguard⟩
    exact ⟨hpos, by omega, hguard⟩
  · rintro ⟨hpos, hbound, hguard⟩
    exact ⟨⟨hpos, by omega⟩, hguard⟩
#print axioms Paper7MomentCounts.b6_candB1_iff_guard

theorem b6_candD2_iff_guard (x : PQ 6) :
    x ∈ CandD2 6 42 ↔ b6CandidateGuard x := by
  rw [candD2_eq_candB1_of_even 6 42 (by decide), b6_candB1_iff_guard]
#print axioms Paper7MomentCounts.b6_candD2_iff_guard

/-- A finite obligation for the original labelled count; no total is evaluated. -/
def b6CandidateBox : Finset (MomentBox 6 42) :=
  Finset.univ.filter (fun z => b6CandidateGuard (decodeBox z))
#print axioms Paper7MomentCounts.b6CandidateBox

theorem finite_filter_card_eq_of_map_pred_iff
    {α β : Type} [Fintype α] (f : α → β) (p q : β → Prop)
    (h : ∀ x, p x ↔ q x) :
    (Finset.univ.filter (fun x => p (f x))).card =
      (Finset.univ.filter (fun x => q (f x))).card := by
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro x _hx
  exact h (f x)
#print axioms Paper7MomentCounts.finite_filter_card_eq_of_map_pred_iff

theorem b6_candB1_ncard_eq_catalog_box :
    (CandB1 6 42).ncard = b6CandidateBox.card := by
  exact (candB1_ncard_eq_box 6 42).trans
    (finite_filter_card_eq_of_map_pred_iff decodeBox (fun x => x ∈ CandB1 6 42)
      b6CandidateGuard b6_candB1_iff_guard)
#print axioms Paper7MomentCounts.b6_candB1_ncard_eq_catalog_box

theorem b6_candD2_ncard_eq_catalog_box :
    (CandD2 6 42).ncard = b6CandidateBox.card := by
  rw [candD2_ncard_eq_candB1_of_even 6 42 (by decide)]
  exact b6_candB1_ncard_eq_catalog_box
#print axioms Paper7MomentCounts.b6_candD2_ncard_eq_catalog_box

/-- Derived from the successful generic identity for the original thetaV. -/
theorem b6_zq_theta (x : ZQCoordinates 6) :
    theta (zqToPQ x) = 12 + 3*((∑ i, x.val.1 i : ℕ) : ℤ) +
      2*((∑ i, x.val.2 i : ℕ) : ℤ) + ∑ i, (x.val.1 i : ℤ)^2 := by
  have h := zq_theta 6 x
  norm_num at h
  exact h
#print axioms Paper7MomentCounts.b6_zq_theta

theorem b6_zq_candB1_iff (x : ZQCoordinates 6) :
    zqToPQ x ∈ CandB1 6 42 ↔
      0 < (∑ i, x.val.1 i) + ∑ i, x.val.2 i ∧
      (∑ i, x.val.1 i) + ∑ i, x.val.2 i ≤ 36 ∧
      b6FeatureGuard ((∑ i, x.val.1 i) + ∑ i, x.val.2 i) (∑ i, x.val.2 i)
        (12 + 3*((∑ i, x.val.1 i : ℕ) : ℤ) +
          2*((∑ i, x.val.2 i : ℕ) : ℤ) + ∑ i, (x.val.1 i : ℤ)^2) := by
  rw [b6_candB1_iff_guard]
  unfold b6CandidateGuard
  rw [zq_weight, zq_qSum, b6_zq_theta]
#print axioms Paper7MomentCounts.b6_zq_candB1_iff

/-- These are consequences of the original budget, not support assumptions. -/
theorem b6_zq_budget_bounds (x : ZQCoordinates 6) (hx : Budget 6 42 (zqToPQ x)) :
    (∑ i, x.val.1 i) ≤ 36 ∧ (∑ i, x.val.2 i) ≤ 18 ∧
      ∀ i, x.val.1 i ≤ 36 ∧ x.val.2 i ≤ 18 := by
  have hw := hx.2
  rw [zq_weight] at hw
  have hqz : (∑ i, x.val.2 i) ≤ ∑ i, x.val.1 i :=
    Finset.sum_le_sum (fun i _ => x.property i)
  have hz : (∑ i, x.val.1 i) ≤ 36 := by omega
  have hq : (∑ i, x.val.2 i) ≤ 18 := by omega
  refine ⟨hz, hq, ?_⟩
  intro i
  have hiz : x.val.1 i ≤ ∑ j, x.val.1 j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (x.val.1 j)) (Finset.mem_univ i)
  have hiq : x.val.2 i ≤ ∑ j, x.val.2 j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (x.val.2 j)) (Finset.mem_univ i)
  exact ⟨hiz.trans hz, hiq.trans hq⟩
#print axioms Paper7MomentCounts.b6_zq_budget_bounds

end Paper7MomentCounts
