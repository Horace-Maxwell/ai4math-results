import Research.Backfill.Paper7.MomentB4Type112MiddleEightSupport

/-! SOURCE ONLY. All eleven ordered blocks are evaluated using their
actual recovered Q and the unchanged Fin10 truncated weight. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_eight_block_eq_small_catalog (z u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) 8 (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z 8 u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) 8 (u.val-z.val) sm then
        b4Type112PlainWeight z.val 8 u.val
          (b4Type112RecoveredQ (z.val+u.val) 8 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 8 u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_eight_block_eq_small_catalog

theorem b4_type112_middle8_zero_ten : b4Type112Block 0 8 10 = 5 := by
  rw [type112_eight_block_eq_small_catalog 0 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 0 10 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_zero_ten

theorem b4_type112_middle8_one_ten : b4Type112Block 1 8 10 = 8 := by
  rw [type112_eight_block_eq_small_catalog 1 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 1 10 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_one_ten

theorem b4_type112_middle8_two_ten : b4Type112Block 2 8 10 = 7 := by
  rw [type112_eight_block_eq_small_catalog 2 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 2 10 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_two_ten

theorem b4_type112_middle8_three_ten : b4Type112Block 3 8 10 = 1 := by
  rw [type112_eight_block_eq_small_catalog 3 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 3 10 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_three_ten

theorem b4_type112_middle8_four_nine : b4Type112Block 4 8 9 = 14 := by
  rw [type112_eight_block_eq_small_catalog 4 9 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 4 9 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_four_nine

theorem b4_type112_middle8_five_nine : b4Type112Block 5 8 9 = 1 := by
  rw [type112_eight_block_eq_small_catalog 5 9 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 5 9 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_five_nine

theorem b4_type112_middle8_zero_twelve : b4Type112Block 0 8 12 = 5 := by
  rw [type112_eight_block_eq_small_catalog 0 12 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 0 12 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_zero_twelve

theorem b4_type112_middle8_one_twelve : b4Type112Block 1 8 12 = 7 := by
  rw [type112_eight_block_eq_small_catalog 1 12 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 1 12 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_one_twelve

theorem b4_type112_middle8_two_twelve : b4Type112Block 2 8 12 = 5 := by
  rw [type112_eight_block_eq_small_catalog 2 12 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 2 12 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_two_twelve

theorem b4_type112_middle8_three_twelve : b4Type112Block 3 8 12 = 10 := by
  rw [type112_eight_block_eq_small_catalog 3 12 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 3 12 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_three_twelve

theorem b4_type112_middle8_seven_ten : b4Type112Block 7 8 10 = 9 := by
  rw [type112_eight_block_eq_small_catalog 7 10 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_eight_recovered_support 7 10 sm (by decide) hm hg
      simpa [B4Type112EightSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle8_seven_ten

end Paper7MomentCanonicalNumeric
