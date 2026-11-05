import Research.Backfill.Paper7.MomentB4Type112MiddleTwoSupport

/-! SOURCE ONLY. Original recovered Q and Fin10 weights with k<=2.
Three triple-fibre and five double-fibre blocks are counted in full.
The explicit change records the complete sum with literal t=2. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_two_block_eq_support_sum (z u : Fin 38)
    (hzu : z ≤ u) (hz : z.val < 19) (hu : u.val < 27) :
    b4Type112Block z 2 u = ∑ sm ∈ b4FeatureCatalog,
      if B4Type112TwoSupport z.val u.val sm then
        b4Type112PlainWeight z.val 2 u.val
          (b4Type112RecoveredQ (z.val+u.val) 2 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 2 u hzu]
  unfold b4Type112RecoveredBlock
  change (∑ sm ∈ b4FeatureCatalog,
    if b4Type112RecoveredGuard (z.val+u.val) 2 (u.val-z.val) sm then
      b4Type112PlainWeight z.val 2 u.val
        (b4Type112RecoveredQ (z.val+u.val) 2 (u.val-z.val) sm.2) else 0) = _
  apply Finset.sum_congr rfl
  intro sm hm
  have he := type112_two_small_catalog_certificate
    (⟨z.val,hz⟩ : Fin 19) (⟨u.val,hu⟩ : Fin 27) sm hm
  by_cases hg : b4Type112RecoveredGuard (z.val+u.val) 2 (u.val-z.val) sm
  · have hs : B4Type112TwoSupport z.val u.val sm := he.mp ⟨hzu,hg⟩
    simp only [hg,hs,ite_true]
  · have hs : ¬ B4Type112TwoSupport z.val u.val sm := fun h => hg (he.mpr h).2
    simp only [hg,hs,ite_false]
#print axioms Paper7MomentCanonicalNumeric.type112_two_block_eq_support_sum

theorem b4_type112_middle2_zero_five : b4Type112Block 0 2 5 = 2 := by
  rw [type112_two_block_eq_support_sum 0 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_zero_five

theorem b4_type112_middle2_zero_six : b4Type112Block 0 2 6 = 3 := by
  rw [type112_two_block_eq_support_sum 0 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_zero_six

theorem b4_type112_middle2_one_six : b4Type112Block 1 2 6 = 4 := by
  rw [type112_two_block_eq_support_sum 1 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_one_six

theorem b4_type112_middle2_one_five : b4Type112Block 1 2 5 = 1 := by
  rw [type112_two_block_eq_support_sum 1 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_one_five

theorem b4_type112_middle2_two_five : b4Type112Block 2 2 5 = 7 := by
  rw [type112_two_block_eq_support_sum 2 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_two_five

theorem b4_type112_middle2_three_five : b4Type112Block 3 2 5 = 6 := by
  rw [type112_two_block_eq_support_sum 3 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_three_five

theorem b4_type112_middle2_three_four : b4Type112Block 3 2 4 = 4 := by
  rw [type112_two_block_eq_support_sum 3 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_three_four

theorem b4_type112_middle2_four_four : b4Type112Block 4 2 4 = 9 := by
  rw [type112_two_block_eq_support_sum 4 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_four_four

theorem b4_type112_middle2_zero_thirteen : b4Type112Block 0 2 13 = 3 := by
  rw [type112_two_block_eq_support_sum 0 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_zero_thirteen

theorem b4_type112_middle2_one_thirteen : b4Type112Block 1 2 13 = 6 := by
  rw [type112_two_block_eq_support_sum 1 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_one_thirteen

theorem b4_type112_middle2_two_thirteen : b4Type112Block 2 2 13 = 9 := by
  rw [type112_two_block_eq_support_sum 2 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_two_thirteen

theorem b4_type112_middle2_three_thirteen : b4Type112Block 3 2 13 = 6 := by
  rw [type112_two_block_eq_support_sum 3 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_three_thirteen

theorem b4_type112_middle2_three_twelve : b4Type112Block 3 2 12 = 4 := by
  rw [type112_two_block_eq_support_sum 3 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_three_twelve

theorem b4_type112_middle2_four_twelve : b4Type112Block 4 2 12 = 15 := by
  rw [type112_two_block_eq_support_sum 4 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_four_twelve

theorem b4_type112_middle2_zero_fifteen : b4Type112Block 0 2 15 = 8 := by
  rw [type112_two_block_eq_support_sum 0 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_zero_fifteen

theorem b4_type112_middle2_one_fifteen : b4Type112Block 1 2 15 = 16 := by
  rw [type112_two_block_eq_support_sum 1 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_one_fifteen

theorem b4_type112_middle2_two_fifteen : b4Type112Block 2 2 15 = 19 := by
  rw [type112_two_block_eq_support_sum 2 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_two_fifteen

theorem b4_type112_middle2_two_fourteen : b4Type112Block 2 2 14 = 7 := by
  rw [type112_two_block_eq_support_sum 2 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_two_fourteen

theorem b4_type112_middle2_three_fourteen : b4Type112Block 3 2 14 = 12 := by
  rw [type112_two_block_eq_support_sum 3 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_three_fourteen

theorem b4_type112_middle2_four_fourteen : b4Type112Block 4 2 14 = 15 := by
  rw [type112_two_block_eq_support_sum 4 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_four_fourteen

theorem b4_type112_middle2_five_fourteen : b4Type112Block 5 2 14 = 34 := by
  rw [type112_two_block_eq_support_sum 5 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_five_fourteen

theorem b4_type112_middle2_seven_thirteen : b4Type112Block 7 2 13 = 42 := by
  rw [type112_two_block_eq_support_sum 7 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_seven_thirteen

theorem b4_type112_middle2_eight_twelve : b4Type112Block 8 2 12 = 27 := by
  rw [type112_two_block_eq_support_sum 8 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_eight_twelve

theorem b4_type112_middle2_nine_twelve : b4Type112Block 9 2 12 = 25 := by
  rw [type112_two_block_eq_support_sum 9 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_nine_twelve

theorem b4_type112_middle2_ten_eleven : b4Type112Block 10 2 11 = 36 := by
  rw [type112_two_block_eq_support_sum 10 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_ten_eleven

theorem b4_type112_middle2_three_fifteen : b4Type112Block 3 2 15 = 12 := by
  rw [type112_two_block_eq_support_sum 3 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_three_fifteen

theorem b4_type112_middle2_six_fourteen : b4Type112Block 6 2 14 = 15 := by
  rw [type112_two_block_eq_support_sum 6 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_six_fourteen

theorem b4_type112_middle2_eight_thirteen : b4Type112Block 8 2 13 = 9 := by
  rw [type112_two_block_eq_support_sum 8 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_eight_thirteen

theorem b4_type112_middle2_four_sixteen : b4Type112Block 4 2 16 = 15 := by
  rw [type112_two_block_eq_support_sum 4 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_four_sixteen

theorem b4_type112_middle2_seven_fifteen : b4Type112Block 7 2 15 = 15 := by
  rw [type112_two_block_eq_support_sum 7 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_seven_fifteen

theorem b4_type112_middle2_nine_fourteen : b4Type112Block 9 2 14 = 30 := by
  rw [type112_two_block_eq_support_sum 9 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_nine_fourteen

theorem b4_type112_middle2_ten_thirteen : b4Type112Block 10 2 13 = 18 := by
  rw [type112_two_block_eq_support_sum 10 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_ten_thirteen

theorem b4_type112_middle2_eleven_twelve : b4Type112Block 11 2 12 = 24 := by
  rw [type112_two_block_eq_support_sum 11 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_eleven_twelve

theorem b4_type112_middle2_five_sixteen : b4Type112Block 5 2 16 = 18 := by
  rw [type112_two_block_eq_support_sum 5 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112TwoSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle2_five_sixteen

end Paper7MomentCanonicalNumeric
