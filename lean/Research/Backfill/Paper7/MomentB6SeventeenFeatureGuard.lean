import Research.Backfill.Paper7.MomentB6FourFeatureBounds

/-! Uncompiled exact reduction of the original guard contributions.
The new 17-pair guard is proved equivalent only at actual bounded original
PQ statistics.  No arbitrary-statistic guard equivalence is claimed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped Classical

def b6RetainedFeatureCatalog : Finset (ℤ × ℤ) :=
  b6FeatureCatalog \ b6ExcludedFeatureCatalog
#print axioms Paper7MomentCounts.b6RetainedFeatureCatalog

theorem b6RetainedFeatureCatalog_card : b6RetainedFeatureCatalog.card = 17 := by
  decide
#print axioms Paper7MomentCounts.b6RetainedFeatureCatalog_card

def b6FeatureGuard17 (W Q : ℕ) (T : ℤ) : Prop :=
  ∃ sm ∈ b6RetainedFeatureCatalog,
    sm.2 = T ∧ sm.1 ≤ (6 + W : ℤ) ∧ (6 + W : ℤ) - max (Q : ℤ) 2 ≤ sm.1
#print axioms Paper7MomentCounts.b6FeatureGuard17

theorem b6_budget_feature_guard_iff17 (x : PQ 6) (hx : Budget 6 42 x) :
    b6FeatureGuard (weight x) (qSum x) (theta x) ↔
      b6FeatureGuard17 (weight x) (qSum x) (theta x) := by
  constructor
  · rintro ⟨sm, hsm, ht, hs, hl⟩
    have hn := b6_budget_feature_not_excluded x hx sm ht hl
    exact ⟨sm, Finset.mem_sdiff.mpr ⟨hsm, hn⟩, ht, hs, hl⟩
  · rintro ⟨sm, hsm, ht, hs, hl⟩
    exact ⟨sm, (Finset.mem_sdiff.mp hsm).1, ht, hs, hl⟩
#print axioms Paper7MomentCounts.b6_budget_feature_guard_iff17

def b6CandidateGuard17 (x : PQ 6) : Prop :=
  0 < weight x ∧ weight x ≤ 36 ∧ b6FeatureGuard17 (weight x) (qSum x) (theta x)
#print axioms Paper7MomentCounts.b6CandidateGuard17

theorem b6CandidateGuard_iff17 (x : PQ 6) : b6CandidateGuard x ↔ b6CandidateGuard17 x := by
  constructor
  · rintro ⟨hpos, hbound, hg⟩
    have hb : Budget 6 42 x := ⟨hpos, by omega⟩
    exact ⟨hpos, hbound, (b6_budget_feature_guard_iff17 x hb).mp hg⟩
  · rintro ⟨hpos, hbound, hg⟩
    have hb : Budget 6 42 x := ⟨hpos, by omega⟩
    exact ⟨hpos, hbound, (b6_budget_feature_guard_iff17 x hb).mpr hg⟩
#print axioms Paper7MomentCounts.b6CandidateGuard_iff17

theorem b6_candB1_iff_guard17 (x : PQ 6) : x ∈ CandB1 6 42 ↔ b6CandidateGuard17 x := by
  rw [b6_candB1_iff_guard, b6CandidateGuard_iff17]
#print axioms Paper7MomentCounts.b6_candB1_iff_guard17

theorem b6_candD2_iff_guard17 (x : PQ 6) : x ∈ CandD2 6 42 ↔ b6CandidateGuard17 x := by
  rw [b6_candD2_iff_guard, b6CandidateGuard_iff17]
#print axioms Paper7MomentCounts.b6_candD2_iff_guard17

end Paper7MomentCounts
