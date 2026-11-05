import Research.Backfill.Paper7.MomentB6SeventeenFeatureGuard

/-! Uncompiled emptiness of four original theta fibres, each convention
transported separately. No claim about canonical set equality is made. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCounts
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy
open scoped Classical

theorem b6_candidate_guard_theta_not_excluded (x : PQ 6) (hx : b6CandidateGuard x) :
    theta x ∉ b6ExcludedTheta := by
  intro htheta
  obtain ⟨sm, hsm, ht, _hs, hl⟩ := hx.2.2
  have hb : Budget 6 42 x := ⟨hx.1, by have hw := hx.2.1; omega⟩
  have he : sm ∈ b6ExcludedFeatureCatalog :=
    (b6FeatureCatalog_excludedTheta_iff sm hsm).mp (ht.symm ▸ htheta)
  exact b6_budget_feature_not_excluded x hb sm ht hl he
#print axioms Paper7MomentCounts.b6_candidate_guard_theta_not_excluded

theorem b6_candB1_excluded_theta_empty (T : ℤ) (hT : T ∈ b6ExcludedTheta) :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = T} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact b6_candidate_guard_theta_not_excluded x ((b6_candB1_iff_guard x).mp hx.1)
    (hx.2.symm ▸ hT)
#print axioms Paper7MomentCounts.b6_candB1_excluded_theta_empty

theorem b6_candD2_excluded_theta_empty (T : ℤ) (hT : T ∈ b6ExcludedTheta) :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = T} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact b6_candidate_guard_theta_not_excluded x ((b6_candD2_iff_guard x).mp hx.1)
    (hx.2.symm ▸ hT)
#print axioms Paper7MomentCounts.b6_candD2_excluded_theta_empty

theorem b6_candB1_excluded_theta_ncard (T : ℤ) (hT : T ∈ b6ExcludedTheta) :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = T}.ncard = 0 := by
  rw [b6_candB1_excluded_theta_empty T hT]
  simp
#print axioms Paper7MomentCounts.b6_candB1_excluded_theta_ncard

theorem b6_candD2_excluded_theta_ncard (T : ℤ) (hT : T ∈ b6ExcludedTheta) :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = T}.ncard = 0 := by
  rw [b6_candD2_excluded_theta_empty T hT]
  simp
#print axioms Paper7MomentCounts.b6_candD2_excluded_theta_ncard

theorem b6_candB1_four_theta_ncards :
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 72}.ncard = 0 ∧
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 240}.ncard = 0 ∧
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 600}.ncard = 0 ∧
    {x : PQ 6 | x ∈ CandB1 6 42 ∧ theta x = 1260}.ncard = 0 := by
  exact ⟨b6_candB1_excluded_theta_ncard 72 (by decide),
    b6_candB1_excluded_theta_ncard 240 (by decide),
    b6_candB1_excluded_theta_ncard 600 (by decide),
    b6_candB1_excluded_theta_ncard 1260 (by decide)⟩
#print axioms Paper7MomentCounts.b6_candB1_four_theta_ncards

theorem b6_candD2_four_theta_ncards :
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 72}.ncard = 0 ∧
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 240}.ncard = 0 ∧
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 600}.ncard = 0 ∧
    {x : PQ 6 | x ∈ CandD2 6 42 ∧ theta x = 1260}.ncard = 0 := by
  exact ⟨b6_candD2_excluded_theta_ncard 72 (by decide),
    b6_candD2_excluded_theta_ncard 240 (by decide),
    b6_candD2_excluded_theta_ncard 600 (by decide),
    b6_candD2_excluded_theta_ncard 1260 (by decide)⟩
#print axioms Paper7MomentCounts.b6_candD2_four_theta_ncards

end Paper7MomentCounts
