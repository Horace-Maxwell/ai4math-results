import Research.Backfill.Paper7.MomentB4Type112MiddleNineSupport

/-! SOURCE ONLY. Exact recovered-Q evaluations of all fifteen ordered
blocks. The original Fin10 weight and both natural subtractions remain.
At (0,11), two distinct original catalogue fibres both contribute. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_nine_block_eq_small_catalog (z u : Fin 38)
    (hzu : z ≤ u) (s : Finset (ℤ × ℤ)) (hsub : s ⊆ b4FeatureCatalog)
    (hcover : ∀ sm ∈ b4FeatureCatalog,
      b4Type112RecoveredGuard (z.val+u.val) 9 (u.val-z.val) sm → sm ∈ s) :
    b4Type112Block z 9 u = ∑ sm ∈ s,
      if b4Type112RecoveredGuard (z.val+u.val) 9 (u.val-z.val) sm then
        b4Type112PlainWeight z.val 9 u.val
          (b4Type112RecoveredQ (z.val+u.val) 9 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 9 u hzu]
  unfold b4Type112RecoveredBlock
  symm
  apply Finset.sum_subset hsub
  intro sm hm hnot
  apply ite_eq_right
  exact fun hg => hnot (hcover sm hm hg)
#print axioms Paper7MomentCanonicalNumeric.type112_nine_block_eq_small_catalog

theorem b4_type112_middle9_zero_zero : b4Type112Block 0 9 0 = 1 := by
  rw [type112_nine_block_eq_small_catalog 0 0 le_rfl {(24,264)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 0 0 sm le_rfl hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_zero_zero

theorem b4_type112_middle9_zero_one : b4Type112Block 0 9 1 = 1 := by
  rw [type112_nine_block_eq_small_catalog 0 1 (by decide) {(24,264)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 0 1 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_zero_one

theorem b4_type112_middle9_zero_two : b4Type112Block 0 9 2 = 1 := by
  rw [type112_nine_block_eq_small_catalog 0 2 (by decide) {(24,264)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 0 2 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_zero_two

theorem b4_type112_middle9_one_one : b4Type112Block 1 9 1 = 2 := by
  rw [type112_nine_block_eq_small_catalog 1 1 le_rfl {(24,264)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 1 1 sm le_rfl hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_one_one

theorem b4_type112_middle9_zero_eight : b4Type112Block 0 9 8 = 5 := by
  rw [type112_nine_block_eq_small_catalog 0 8 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 0 8 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_zero_eight

theorem b4_type112_middle9_one_eight : b4Type112Block 1 9 8 = 9 := by
  rw [type112_nine_block_eq_small_catalog 1 8 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 1 8 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_one_eight

theorem b4_type112_middle9_two_eight : b4Type112Block 2 9 8 = 8 := by
  rw [type112_nine_block_eq_small_catalog 2 8 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 2 8 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_two_eight

theorem b4_type112_middle9_three_eight : b4Type112Block 3 9 8 = 2 := by
  rw [type112_nine_block_eq_small_catalog 3 8 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 3 8 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_three_eight

theorem b4_type112_middle9_four_seven : b4Type112Block 4 9 7 = 11 := by
  rw [type112_nine_block_eq_small_catalog 4 7 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 4 7 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_four_seven

theorem b4_type112_middle9_five_six : b4Type112Block 5 9 6 = 17 := by
  rw [type112_nine_block_eq_small_catalog 5 6 (by decide) {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 5 6 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_five_six

theorem b4_type112_middle9_six_six : b4Type112Block 6 9 6 = 1 := by
  rw [type112_nine_block_eq_small_catalog 6 6 le_rfl {(33,336)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 6 6 sm le_rfl hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_six_six

theorem b4_type112_middle9_zero_eleven : b4Type112Block 0 9 11 = 5 := by
  rw [type112_nine_block_eq_small_catalog 0 11 (by decide) {(34,384),(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 0 11 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_zero_eleven

theorem b4_type112_middle9_one_eleven : b4Type112Block 1 9 11 = 6 := by
  rw [type112_nine_block_eq_small_catalog 1 11 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 1 11 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_one_eleven

theorem b4_type112_middle9_four_ten : b4Type112Block 4 9 10 = 11 := by
  rw [type112_nine_block_eq_small_catalog 4 10 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 4 10 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_four_ten

theorem b4_type112_middle9_six_nine : b4Type112Block 6 9 9 = 6 := by
  rw [type112_nine_block_eq_small_catalog 6 9 (by decide) {(38,396)}
    (by decide +kernel) (by
      intro sm hm hg
      have hs := type112_nine_recovered_support 6 9 sm (by decide) hm hg
      simpa [B4Type112NineSupport] using hs)]
  norm_num [b4Type112RecoveredGuard,b4Type112RecoveredQ,b4Type112CatalogResidual,
    b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle9_six_nine

end Paper7MomentCanonicalNumeric
