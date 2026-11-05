import Research.Backfill.Paper7.MomentB4Type112MiddleOneSupport

/-! SOURCE ONLY mathematical correction. Original recovered Q, full catalogue,
and Fin10 sum with k<=1. The omitted (9,9,Q=14) fibre has weight5+7=12. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_one_block_eq_support_sum (z u : Fin 38)
    (hzu : z ≤ u) (hz : z.val < 19) (hu : u.val < 27) :
    b4Type112Block z 1 u = ∑ sm ∈ b4FeatureCatalog,
      if B4Type112OneSupport z.val u.val sm then
        b4Type112PlainWeight z.val 1 u.val
          (b4Type112RecoveredQ (z.val+u.val) 1 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 1 u hzu]
  unfold b4Type112RecoveredBlock
  change (∑ sm ∈ b4FeatureCatalog,
    if b4Type112RecoveredGuard (z.val+u.val) 1 (u.val-z.val) sm then
      b4Type112PlainWeight z.val 1 u.val
        (b4Type112RecoveredQ (z.val+u.val) 1 (u.val-z.val) sm.2) else 0) = _
  apply Finset.sum_congr rfl
  intro sm hm
  have he := type112_one_small_catalog_certificate
    (⟨z.val,hz⟩ : Fin 19) (⟨u.val,hu⟩ : Fin 27) sm hm
  by_cases hg : b4Type112RecoveredGuard (z.val+u.val) 1 (u.val-z.val) sm
  · have hs : B4Type112OneSupport z.val u.val sm := he.mp ⟨hzu,hg⟩
    simp only [hg,hs,ite_true]
  · have hs : ¬ B4Type112OneSupport z.val u.val sm := fun h => hg (he.mpr h).2
    simp only [hg,hs,ite_false]
#print axioms Paper7MomentCanonicalNumeric.type112_one_block_eq_support_sum

theorem b4_type112_middle1_zero_six : b4Type112Block 0 1 6 = 2 := by
  rw [type112_one_block_eq_support_sum 0 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_zero_six

theorem b4_type112_middle1_one_six : b4Type112Block 1 1 6 = 5 := by
  rw [type112_one_block_eq_support_sum 1 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_one_six

theorem b4_type112_middle1_two_six : b4Type112Block 2 1 6 = 7 := by
  rw [type112_one_block_eq_support_sum 2 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_two_six

theorem b4_type112_middle1_two_five : b4Type112Block 2 1 5 = 4 := by
  rw [type112_one_block_eq_support_sum 2 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_two_five

theorem b4_type112_middle1_three_four : b4Type112Block 3 1 4 = 1 := by
  rw [type112_one_block_eq_support_sum 3 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_three_four

theorem b4_type112_middle1_three_six : b4Type112Block 3 1 6 = 4 := by
  rw [type112_one_block_eq_support_sum 3 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_three_six

theorem b4_type112_middle1_three_five : b4Type112Block 3 1 5 = 2 := by
  rw [type112_one_block_eq_support_sum 3 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_three_five

theorem b4_type112_middle1_four_five : b4Type112Block 4 1 5 = 8 := by
  rw [type112_one_block_eq_support_sum 4 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_four_five

theorem b4_type112_middle1_four_four : b4Type112Block 4 1 4 = 1 := by
  rw [type112_one_block_eq_support_sum 4 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_four_four

theorem b4_type112_middle1_zero_thirteen : b4Type112Block 0 1 13 = 2 := by
  rw [type112_one_block_eq_support_sum 0 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_zero_thirteen

theorem b4_type112_middle1_one_thirteen : b4Type112Block 1 1 13 = 5 := by
  rw [type112_one_block_eq_support_sum 1 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_one_thirteen

theorem b4_type112_middle1_two_thirteen : b4Type112Block 2 1 13 = 6 := by
  rw [type112_one_block_eq_support_sum 2 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_two_thirteen

theorem b4_type112_middle1_three_thirteen : b4Type112Block 3 1 13 = 8 := by
  rw [type112_one_block_eq_support_sum 3 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_three_thirteen

theorem b4_type112_middle1_four_thirteen : b4Type112Block 4 1 13 = 8 := by
  rw [type112_one_block_eq_support_sum 4 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_four_thirteen

theorem b4_type112_middle1_four_twelve : b4Type112Block 4 1 12 = 1 := by
  rw [type112_one_block_eq_support_sum 4 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_four_twelve

theorem b4_type112_middle1_five_twelve : b4Type112Block 5 1 12 = 12 := by
  rw [type112_one_block_eq_support_sum 5 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_five_twelve

theorem b4_type112_middle1_six_twelve : b4Type112Block 6 1 12 = 10 := by
  rw [type112_one_block_eq_support_sum 6 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_six_twelve

theorem b4_type112_middle1_six_eleven : b4Type112Block 6 1 11 = 2 := by
  rw [type112_one_block_eq_support_sum 6 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_six_eleven

theorem b4_type112_middle1_seven_eleven : b4Type112Block 7 1 11 = 16 := by
  rw [type112_one_block_eq_support_sum 7 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_seven_eleven

theorem b4_type112_middle1_eight_eleven : b4Type112Block 8 1 11 = 2 := by
  rw [type112_one_block_eq_support_sum 8 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_eight_eleven

theorem b4_type112_middle1_eight_ten : b4Type112Block 8 1 10 = 14 := by
  rw [type112_one_block_eq_support_sum 8 10 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_eight_ten

theorem b4_type112_middle1_zero_fifteen : b4Type112Block 0 1 15 = 3 := by
  rw [type112_one_block_eq_support_sum 0 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_zero_fifteen

theorem b4_type112_middle1_one_fifteen : b4Type112Block 1 1 15 = 8 := by
  rw [type112_one_block_eq_support_sum 1 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_one_fifteen

theorem b4_type112_middle1_two_fifteen : b4Type112Block 2 1 15 = 14 := by
  rw [type112_one_block_eq_support_sum 2 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_two_fifteen

theorem b4_type112_middle1_three_fifteen : b4Type112Block 3 1 15 = 20 := by
  rw [type112_one_block_eq_support_sum 3 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_three_fifteen

theorem b4_type112_middle1_three_fourteen : b4Type112Block 3 1 14 = 2 := by
  rw [type112_one_block_eq_support_sum 3 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_three_fourteen

theorem b4_type112_middle1_four_fourteen : b4Type112Block 4 1 14 = 10 := by
  rw [type112_one_block_eq_support_sum 4 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_four_fourteen

theorem b4_type112_middle1_five_fourteen : b4Type112Block 5 1 14 = 24 := by
  rw [type112_one_block_eq_support_sum 5 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_five_fourteen

theorem b4_type112_middle1_six_fourteen : b4Type112Block 6 1 14 = 27 := by
  rw [type112_one_block_eq_support_sum 6 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_six_fourteen

theorem b4_type112_middle1_six_thirteen : b4Type112Block 6 1 13 = 12 := by
  rw [type112_one_block_eq_support_sum 6 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_six_thirteen

theorem b4_type112_middle1_seven_thirteen : b4Type112Block 7 1 13 = 16 := by
  rw [type112_one_block_eq_support_sum 7 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_seven_thirteen

theorem b4_type112_middle1_eight_thirteen : b4Type112Block 8 1 13 = 26 := by
  rw [type112_one_block_eq_support_sum 8 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_eight_thirteen

theorem b4_type112_middle1_nine_twelve : b4Type112Block 9 1 12 = 34 := by
  rw [type112_one_block_eq_support_sum 9 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_nine_twelve

theorem b4_type112_middle1_ten_eleven : b4Type112Block 10 1 11 = 20 := by
  rw [type112_one_block_eq_support_sum 10 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_ten_eleven

theorem b4_type112_middle1_four_fifteen : b4Type112Block 4 1 15 = 10 := by
  rw [type112_one_block_eq_support_sum 4 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_four_fifteen

theorem b4_type112_middle1_zero_seventeen : b4Type112Block 0 1 17 = 3 := by
  rw [type112_one_block_eq_support_sum 0 17 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_zero_seventeen

theorem b4_type112_middle1_one_seventeen : b4Type112Block 1 1 17 = 8 := by
  rw [type112_one_block_eq_support_sum 1 17 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_one_seventeen

theorem b4_type112_middle1_five_sixteen : b4Type112Block 5 1 16 = 12 := by
  rw [type112_one_block_eq_support_sum 5 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_five_sixteen

theorem b4_type112_middle1_seven_fifteen : b4Type112Block 7 1 15 = 16 := by
  rw [type112_one_block_eq_support_sum 7 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_seven_fifteen

theorem b4_type112_middle1_nine_fourteen : b4Type112Block 9 1 14 = 18 := by
  rw [type112_one_block_eq_support_sum 9 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_nine_fourteen

theorem b4_type112_middle1_two_seventeen : b4Type112Block 2 1 17 = 6 := by
  rw [type112_one_block_eq_support_sum 2 17 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_two_seventeen

theorem b4_type112_middle1_eight_fifteen : b4Type112Block 8 1 15 = 17 := by
  rw [type112_one_block_eq_support_sum 8 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_eight_fifteen

theorem b4_type112_middle1_twelve_twelve : b4Type112Block 12 1 12 = 16 := by
  rw [type112_one_block_eq_support_sum 12 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_twelve_twelve

theorem b4_type112_middle1_five_twentytwo : b4Type112Block 5 1 22 = 12 := by
  rw [type112_one_block_eq_support_sum 5 22 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_five_twentytwo

theorem b4_type112_middle1_six_twentytwo : b4Type112Block 6 1 22 = 1 := by
  rw [type112_one_block_eq_support_sum 6 22 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_six_twentytwo

theorem b4_type112_middle1_five_twentythree : b4Type112Block 5 1 23 = 12 := by
  rw [type112_one_block_eq_support_sum 5 23 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_five_twentythree

theorem b4_type112_middle1_six_twentythree : b4Type112Block 6 1 23 = 13 := by
  rw [type112_one_block_eq_support_sum 6 23 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_six_twentythree

theorem b4_type112_middle1_zero_twentyfour : b4Type112Block 0 1 24 = 2 := by
  rw [type112_one_block_eq_support_sum 0 24 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_zero_twentyfour

theorem b4_type112_middle1_nine_twentytwo : b4Type112Block 9 1 22 = 6 := by
  rw [type112_one_block_eq_support_sum 9 22 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_nine_twentytwo

theorem b4_type112_middle1_eleven_twentyone : b4Type112Block 11 1 21 = 6 := by
  rw [type112_one_block_eq_support_sum 11 21 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_eleven_twentyone

theorem b4_type112_middle1_nine_nine : b4Type112Block 9 1 9 = 12 := by
  rw [type112_one_block_eq_support_sum 9 9 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112OneSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle1_nine_nine

end Paper7MomentCanonicalNumeric
