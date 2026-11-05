import Research.Backfill.Paper7.MomentB4Type112MiddleSixSupport

/-! SOURCE ONLY. Thirteen ordered blocks with their actual recovered Q
and the original finite truncated weight; no numerical total is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_six_block_eq_small_catalog (z u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) 6 (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z 6 u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) 6 (u.val-z.val) sm then
        b4Type112PlainWeight z.val 6 u.val
          (b4Type112RecoveredQ (z.val+u.val) 6 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 6 u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_six_block_eq_small_catalog

theorem b4_type112_middle6_zero_twelve : b4Type112Block 0 6 12 = 7 := by
  rw [type112_six_block_eq_small_catalog 0 12 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 0 12 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_zero_twelve

theorem b4_type112_middle6_one_twelve : b4Type112Block 1 6 12 = 11 := by
  rw [type112_six_block_eq_small_catalog 1 12 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 1 12 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_one_twelve

theorem b4_type112_middle6_zero_thirteen : b4Type112Block 0 6 13 = 3 := by
  rw [type112_six_block_eq_small_catalog 0 13 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 0 13 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_zero_thirteen

theorem b4_type112_middle6_three_twelve : b4Type112Block 3 6 12 = 18 := by
  rw [type112_six_block_eq_small_catalog 3 12 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 3 12 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_three_twelve

theorem b4_type112_middle6_four_twelve : b4Type112Block 4 6 12 = 9 := by
  rw [type112_six_block_eq_small_catalog 4 12 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 4 12 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_four_twelve

theorem b4_type112_middle6_six_eleven : b4Type112Block 6 6 11 = 9 := by
  rw [type112_six_block_eq_small_catalog 6 11 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 6 11 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_six_eleven

theorem b4_type112_middle6_seven_ten : b4Type112Block 7 6 10 = 24 := by
  rw [type112_six_block_eq_small_catalog 7 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 7 10 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_seven_ten

theorem b4_type112_middle6_nine_nine : b4Type112Block 9 6 9 = 1 := by
  rw [type112_six_block_eq_small_catalog 9 9 le_rfl {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 9 9 sm le_rfl hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_nine_nine

theorem b4_type112_middle6_two_fourteen : b4Type112Block 2 6 14 = 13 := by
  rw [type112_six_block_eq_small_catalog 2 14 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 2 14 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_two_fourteen

theorem b4_type112_middle6_three_fourteen : b4Type112Block 3 6 14 = 8 := by
  rw [type112_six_block_eq_small_catalog 3 14 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 3 14 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_three_fourteen

theorem b4_type112_middle6_six_thirteen : b4Type112Block 6 6 13 = 2 := by
  rw [type112_six_block_eq_small_catalog 6 13 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 6 13 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_six_thirteen

theorem b4_type112_middle6_four_fourteen : b4Type112Block 4 6 14 = 11 := by
  rw [type112_six_block_eq_small_catalog 4 14 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 4 14 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_four_fourteen

theorem b4_type112_middle6_eight_twelve : b4Type112Block 8 6 12 = 9 := by
  rw [type112_six_block_eq_small_catalog 8 12 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_six_recovered_support 8 12 sm (by decide) hm hg
      simpa [B4Type112SixSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle6_eight_twelve

end Paper7MomentCanonicalNumeric
