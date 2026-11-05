import Research.Backfill.Paper7.MomentB4Type112MiddleFiveSupport

/-! SOURCE ONLY. Original Q recovery and truncated Fin10 weights.
The k<=5 guard is retained, and both catalogue fibres are counted in
the two blocks that have different accepted recovered Q values. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_five_block_eq_small_catalog (z u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) 5 (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z 5 u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) 5 (u.val-z.val) sm then
        b4Type112PlainWeight z.val 5 u.val
          (b4Type112RecoveredQ (z.val+u.val) 5 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 5 u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_five_block_eq_small_catalog

theorem b4_type112_middle5_zero_thirteen : b4Type112Block 0 5 13 = 6 := by
  rw [type112_five_block_eq_small_catalog 0 13 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 0 13 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_zero_thirteen

theorem b4_type112_middle5_one_thirteen : b4Type112Block 1 5 13 = 11 := by
  rw [type112_five_block_eq_small_catalog 1 13 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 1 13 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_one_thirteen

theorem b4_type112_middle5_two_thirteen : b4Type112Block 2 5 13 = 11 := by
  rw [type112_five_block_eq_small_catalog 2 13 (by decide) {(29,324)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 2 13 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_two_thirteen

theorem b4_type112_middle5_three_thirteen : b4Type112Block 3 5 13 = 18 := by
  rw [type112_five_block_eq_small_catalog 3 13 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 3 13 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_three_thirteen

theorem b4_type112_middle5_four_thirteen : b4Type112Block 4 5 13 = 9 := by
  rw [type112_five_block_eq_small_catalog 4 13 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 4 13 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_four_thirteen

theorem b4_type112_middle5_six_twelve : b4Type112Block 6 5 12 = 12 := by
  rw [type112_five_block_eq_small_catalog 6 12 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 6 12 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_six_twelve

theorem b4_type112_middle5_eight_eleven : b4Type112Block 8 5 11 = 2 := by
  rw [type112_five_block_eq_small_catalog 8 11 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 8 11 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_eight_eleven

theorem b4_type112_middle5_nine_ten : b4Type112Block 9 5 10 = 6 := by
  rw [type112_five_block_eq_small_catalog 9 10 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 9 10 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_nine_ten

theorem b4_type112_middle5_zero_fifteen : b4Type112Block 0 5 15 = 6 := by
  rw [type112_five_block_eq_small_catalog 0 15 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 0 15 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_zero_fifteen

theorem b4_type112_middle5_one_fifteen : b4Type112Block 1 5 15 = 10 := by
  rw [type112_five_block_eq_small_catalog 1 15 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 1 15 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_one_fifteen

theorem b4_type112_middle5_two_fifteen : b4Type112Block 2 5 15 = 10 := by
  rw [type112_five_block_eq_small_catalog 2 15 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 2 15 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_two_fifteen

theorem b4_type112_middle5_three_fifteen : b4Type112Block 3 5 15 = 20 := by
  rw [type112_five_block_eq_small_catalog 3 15 (by decide) {(34,384),(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 3 15 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_three_fifteen

theorem b4_type112_middle5_five_fourteen : b4Type112Block 5 5 14 = 18 := by
  rw [type112_five_block_eq_small_catalog 5 14 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 5 14 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_five_fourteen

theorem b4_type112_middle5_six_fourteen : b4Type112Block 6 5 14 = 17 := by
  rw [type112_five_block_eq_small_catalog 6 14 (by decide) {(34,384),(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 6 14 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_six_fourteen

theorem b4_type112_middle5_seven_thirteen : b4Type112Block 7 5 13 = 20 := by
  rw [type112_five_block_eq_small_catalog 7 13 (by decide) {(34,384)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 7 13 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_seven_thirteen

theorem b4_type112_middle5_eight_thirteen : b4Type112Block 8 5 13 = 9 := by
  rw [type112_five_block_eq_small_catalog 8 13 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_five_recovered_support 8 13 sm (by decide) hm hg
      simpa [B4Type112FiveSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle5_eight_thirteen

end Paper7MomentCanonicalNumeric
