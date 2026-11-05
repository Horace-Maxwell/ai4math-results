import Research.Backfill.Paper7.MomentB4Type112MiddleSevenSupport

/-! SOURCE ONLY. All twelve ordered blocks use their actual recovered
catalogue Q and the original Fin10 weight, with both truncated differences. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_seven_block_eq_small_catalog (z u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) 7 (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z 7 u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) 7 (u.val-z.val) sm then
        b4Type112PlainWeight z.val 7 u.val
          (b4Type112RecoveredQ (z.val+u.val) 7 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 7 u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_seven_block_eq_small_catalog

theorem b4_type112_middle7_zero_eleven : b4Type112Block 0 7 11 = 5 := by
  rw [type112_seven_block_eq_small_catalog 0 11 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 0 11 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_zero_eleven

theorem b4_type112_middle7_two_eleven : b4Type112Block 2 7 11 = 16 := by
  rw [type112_seven_block_eq_small_catalog 2 11 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 2 11 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_two_eleven

theorem b4_type112_middle7_three_eleven : b4Type112Block 3 7 11 = 12 := by
  rw [type112_seven_block_eq_small_catalog 3 11 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 3 11 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_three_eleven

theorem b4_type112_middle7_four_eleven : b4Type112Block 4 7 11 = 2 := by
  rw [type112_seven_block_eq_small_catalog 4 11 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 4 11 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_four_eleven

theorem b4_type112_middle7_five_ten : b4Type112Block 5 7 10 = 18 := by
  rw [type112_seven_block_eq_small_catalog 5 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 5 10 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_five_ten

theorem b4_type112_middle7_six_ten : b4Type112Block 6 7 10 = 1 := by
  rw [type112_seven_block_eq_small_catalog 6 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 6 10 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_six_ten

theorem b4_type112_middle7_two_thirteen : b4Type112Block 2 7 13 = 11 := by
  rw [type112_seven_block_eq_small_catalog 2 13 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 2 13 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_two_thirteen

theorem b4_type112_middle7_three_thirteen : b4Type112Block 3 7 13 = 6 := by
  rw [type112_seven_block_eq_small_catalog 3 13 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 3 13 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_three_thirteen

theorem b4_type112_middle7_four_thirteen : b4Type112Block 4 7 13 = 9 := by
  rw [type112_seven_block_eq_small_catalog 4 13 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 4 13 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_four_thirteen

theorem b4_type112_middle7_six_twelve : b4Type112Block 6 7 12 = 12 := by
  rw [type112_seven_block_eq_small_catalog 6 12 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 6 12 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_six_twelve

theorem b4_type112_middle7_eight_eleven : b4Type112Block 8 7 11 = 2 := by
  rw [type112_seven_block_eq_small_catalog 8 11 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 8 11 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_eight_eleven

theorem b4_type112_middle7_nine_ten : b4Type112Block 9 7 10 = 6 := by
  rw [type112_seven_block_eq_small_catalog 9 10 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_seven_recovered_support 9 10 sm (by decide) hm hg
      simpa [B4Type112SevenSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle7_nine_ten

end Paper7MomentCanonicalNumeric
