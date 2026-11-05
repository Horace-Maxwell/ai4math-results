import Research.Backfill.Paper7.MomentB4Type112MiddleTenSupport

/-! SOURCE ONLY. Separate small evaluations of the actual recovered-Q
fibres. All natural-number subtractions and the Fin10 weight remain. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_ten_block_eq_small_catalog (z u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) 10 (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z 10 u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) 10 (u.val-z.val) sm then
        b4Type112PlainWeight z.val 10 u.val
          (b4Type112RecoveredQ (z.val+u.val) 10 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 10 u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_ten_block_eq_small_catalog

theorem b4_type112_middle10_zero_four : b4Type112Block 0 10 4 = 3 := by
  rw [type112_ten_block_eq_small_catalog 0 4 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 0 4 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_zero_four

theorem b4_type112_middle10_zero_five : b4Type112Block 0 10 5 = 6 := by
  rw [type112_ten_block_eq_small_catalog 0 5 (by decide) {(29,324),(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 0 5 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_zero_five

theorem b4_type112_middle10_zero_six : b4Type112Block 0 10 6 = 3 := by
  rw [type112_ten_block_eq_small_catalog 0 6 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 0 6 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_zero_six

theorem b4_type112_middle10_zero_nine : b4Type112Block 0 10 9 = 7 := by
  rw [type112_ten_block_eq_small_catalog 0 9 (by decide) {(34,384),(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 0 9 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_zero_nine

theorem b4_type112_middle10_one_four : b4Type112Block 1 10 4 = 5 := by
  rw [type112_ten_block_eq_small_catalog 1 4 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 1 4 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_one_four

theorem b4_type112_middle10_one_five : b4Type112Block 1 10 5 = 6 := by
  rw [type112_ten_block_eq_small_catalog 1 5 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 1 5 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_one_five

theorem b4_type112_middle10_one_six : b4Type112Block 1 10 6 = 4 := by
  rw [type112_ten_block_eq_small_catalog 1 6 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 1 6 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_one_six

theorem b4_type112_middle10_one_nine : b4Type112Block 1 10 9 = 8 := by
  rw [type112_ten_block_eq_small_catalog 1 9 (by decide) {(34,384),(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 1 9 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_one_nine

theorem b4_type112_middle10_two_three : b4Type112Block 2 10 3 = 6 := by
  rw [type112_ten_block_eq_small_catalog 2 3 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 2 3 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_two_three

theorem b4_type112_middle10_two_five : b4Type112Block 2 10 5 = 9 := by
  rw [type112_ten_block_eq_small_catalog 2 5 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 2 5 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_two_five

theorem b4_type112_middle10_two_eight : b4Type112Block 2 10 8 = 11 := by
  rw [type112_ten_block_eq_small_catalog 2 8 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 2 8 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_two_eight

theorem b4_type112_middle10_two_nine : b4Type112Block 2 10 9 = 5 := by
  rw [type112_ten_block_eq_small_catalog 2 9 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 2 9 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_two_nine

theorem b4_type112_middle10_three_four : b4Type112Block 3 10 4 = 10 := by
  rw [type112_ten_block_eq_small_catalog 3 4 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 3 4 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_three_four

theorem b4_type112_middle10_three_five : b4Type112Block 3 10 5 = 6 := by
  rw [type112_ten_block_eq_small_catalog 3 5 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 3 5 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_three_five

theorem b4_type112_middle10_four_four : b4Type112Block 4 10 4 = 9 := by
  rw [type112_ten_block_eq_small_catalog 4 4 le_rfl {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 4 4 sm le_rfl hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_four_four

theorem b4_type112_middle10_four_eight : b4Type112Block 4 10 8 = 9 := by
  rw [type112_ten_block_eq_small_catalog 4 8 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_ten_recovered_support 4 8 sm (by decide) hm hg
      simpa [B4Type112TenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle10_four_eight

end Paper7MomentCanonicalNumeric
