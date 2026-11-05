import Research.Backfill.Paper7.MomentB4Type112MiddleZeroSupport

/-! SOURCE ONLY. Entire original recovered catalogue sum and Fin10 weight
with k<=0. All double/triple fibres and Q=0/1 boundary cases are retained. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_zero_block_eq_support_sum (z u : Fin 38)
    (hzu : z ≤ u) (hz : z.val < 19) (hu : u.val < 27) :
    b4Type112Block z 0 u = ∑ sm ∈ b4FeatureCatalog,
      if B4Type112ZeroSupport z.val u.val sm then
        b4Type112PlainWeight z.val 0 u.val
          (b4Type112RecoveredQ (z.val+u.val) 0 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 0 u hzu]
  unfold b4Type112RecoveredBlock
  change (∑ sm ∈ b4FeatureCatalog,
    if b4Type112RecoveredGuard (z.val+u.val) 0 (u.val-z.val) sm then
      b4Type112PlainWeight z.val 0 u.val
        (b4Type112RecoveredQ (z.val+u.val) 0 (u.val-z.val) sm.2) else 0) = _
  apply Finset.sum_congr rfl
  intro sm hm
  have he := type112_zero_small_catalog_certificate
    (⟨z.val,hz⟩ : Fin 19) (⟨u.val,hu⟩ : Fin 27) sm hm
  by_cases hg : b4Type112RecoveredGuard (z.val+u.val) 0 (u.val-z.val) sm
  · have hs : B4Type112ZeroSupport z.val u.val sm := he.mp ⟨hzu,hg⟩
    simp only [hg,hs,ite_true]
  · have hs : ¬ B4Type112ZeroSupport z.val u.val sm := fun h => hg (he.mpr h).2
    simp only [hg,hs,ite_false]
#print axioms Paper7MomentCanonicalNumeric.type112_zero_block_eq_support_sum

theorem b4_type112_middle0_one_six : b4Type112Block 1 0 6 = 1 := by
  rw [type112_zero_block_eq_support_sum 1 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_six

theorem b4_type112_middle0_two_six : b4Type112Block 2 0 6 = 3 := by
  rw [type112_zero_block_eq_support_sum 2 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_two_six

theorem b4_type112_middle0_three_six : b4Type112Block 3 0 6 = 5 := by
  rw [type112_zero_block_eq_support_sum 3 6 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_three_six

theorem b4_type112_middle0_three_five : b4Type112Block 3 0 5 = 2 := by
  rw [type112_zero_block_eq_support_sum 3 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_three_five

theorem b4_type112_middle0_four_five : b4Type112Block 4 0 5 = 5 := by
  rw [type112_zero_block_eq_support_sum 4 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_four_five

theorem b4_type112_middle0_four_four : b4Type112Block 4 0 4 = 1 := by
  rw [type112_zero_block_eq_support_sum 4 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_four_four

theorem b4_type112_middle0_zero_seven : b4Type112Block 0 0 7 = 1 := by
  rw [type112_zero_block_eq_support_sum 0 7 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_zero_seven

theorem b4_type112_middle0_one_seven : b4Type112Block 1 0 7 = 2 := by
  rw [type112_zero_block_eq_support_sum 1 7 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_seven

theorem b4_type112_middle0_one_thirteen : b4Type112Block 1 0 13 = 1 := by
  rw [type112_zero_block_eq_support_sum 1 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_thirteen

theorem b4_type112_middle0_two_thirteen : b4Type112Block 2 0 13 = 3 := by
  rw [type112_zero_block_eq_support_sum 2 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_two_thirteen

theorem b4_type112_middle0_three_thirteen : b4Type112Block 3 0 13 = 8 := by
  rw [type112_zero_block_eq_support_sum 3 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_three_thirteen

theorem b4_type112_middle0_four_twelve : b4Type112Block 4 0 12 = 1 := by
  rw [type112_zero_block_eq_support_sum 4 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_four_twelve

theorem b4_type112_middle0_zero_fourteen : b4Type112Block 0 0 14 = 1 := by
  rw [type112_zero_block_eq_support_sum 0 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_zero_fourteen

theorem b4_type112_middle0_one_fourteen : b4Type112Block 1 0 14 = 2 := by
  rw [type112_zero_block_eq_support_sum 1 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_fourteen

theorem b4_type112_middle0_four_thirteen : b4Type112Block 4 0 13 = 5 := by
  rw [type112_zero_block_eq_support_sum 4 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_four_thirteen

theorem b4_type112_middle0_five_thirteen : b4Type112Block 5 0 13 = 3 := by
  rw [type112_zero_block_eq_support_sum 5 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_five_thirteen

theorem b4_type112_middle0_five_twelve : b4Type112Block 5 0 12 = 2 := by
  rw [type112_zero_block_eq_support_sum 5 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_five_twelve

theorem b4_type112_middle0_six_twelve : b4Type112Block 6 0 12 = 7 := by
  rw [type112_zero_block_eq_support_sum 6 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_six_twelve

theorem b4_type112_middle0_seven_twelve : b4Type112Block 7 0 12 = 2 := by
  rw [type112_zero_block_eq_support_sum 7 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_seven_twelve

theorem b4_type112_middle0_seven_eleven : b4Type112Block 7 0 11 = 5 := by
  rw [type112_zero_block_eq_support_sum 7 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_seven_eleven

theorem b4_type112_middle0_eight_eleven : b4Type112Block 8 0 11 = 6 := by
  rw [type112_zero_block_eq_support_sum 8 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_eight_eleven

theorem b4_type112_middle0_eight_ten : b4Type112Block 8 0 10 = 2 := by
  rw [type112_zero_block_eq_support_sum 8 10 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_eight_ten

theorem b4_type112_middle0_nine_ten : b4Type112Block 9 0 10 = 8 := by
  rw [type112_zero_block_eq_support_sum 9 10 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_nine_ten

theorem b4_type112_middle0_nine_nine : b4Type112Block 9 0 9 = 1 := by
  rw [type112_zero_block_eq_support_sum 9 9 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_nine_nine

theorem b4_type112_middle0_zero_fifteen : b4Type112Block 0 0 15 = 1 := by
  rw [type112_zero_block_eq_support_sum 0 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_zero_fifteen

theorem b4_type112_middle0_one_fifteen : b4Type112Block 1 0 15 = 2 := by
  rw [type112_zero_block_eq_support_sum 1 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_fifteen

theorem b4_type112_middle0_two_fifteen : b4Type112Block 2 0 15 = 5 := by
  rw [type112_zero_block_eq_support_sum 2 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_two_fifteen

theorem b4_type112_middle0_three_fifteen : b4Type112Block 3 0 15 = 9 := by
  rw [type112_zero_block_eq_support_sum 3 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_three_fifteen

theorem b4_type112_middle0_four_fourteen : b4Type112Block 4 0 14 = 2 := by
  rw [type112_zero_block_eq_support_sum 4 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_four_fourteen

theorem b4_type112_middle0_five_fourteen : b4Type112Block 5 0 14 = 9 := by
  rw [type112_zero_block_eq_support_sum 5 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_five_fourteen

theorem b4_type112_middle0_six_fourteen : b4Type112Block 6 0 14 = 17 := by
  rw [type112_zero_block_eq_support_sum 6 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_six_fourteen

theorem b4_type112_middle0_seven_thirteen : b4Type112Block 7 0 13 = 12 := by
  rw [type112_zero_block_eq_support_sum 7 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_seven_thirteen

theorem b4_type112_middle0_eight_thirteen : b4Type112Block 8 0 13 = 20 := by
  rw [type112_zero_block_eq_support_sum 8 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_eight_thirteen

theorem b4_type112_middle0_eight_twelve : b4Type112Block 8 0 12 = 5 := by
  rw [type112_zero_block_eq_support_sum 8 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_eight_twelve

theorem b4_type112_middle0_nine_twelve : b4Type112Block 9 0 12 = 17 := by
  rw [type112_zero_block_eq_support_sum 9 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_nine_twelve

theorem b4_type112_middle0_ten_eleven : b4Type112Block 10 0 11 = 17 := by
  rw [type112_zero_block_eq_support_sum 10 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_ten_eleven

theorem b4_type112_middle0_four_fifteen : b4Type112Block 4 0 15 = 10 := by
  rw [type112_zero_block_eq_support_sum 4 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_four_fifteen

theorem b4_type112_middle0_seven_fourteen : b4Type112Block 7 0 14 = 8 := by
  rw [type112_zero_block_eq_support_sum 7 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_seven_fourteen

theorem b4_type112_middle0_ten_twelve : b4Type112Block 10 0 12 = 8 := by
  rw [type112_zero_block_eq_support_sum 10 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_ten_twelve

theorem b4_type112_middle0_eleven_eleven : b4Type112Block 11 0 11 = 9 := by
  rw [type112_zero_block_eq_support_sum 11 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_eleven_eleven

theorem b4_type112_middle0_zero_seventeen : b4Type112Block 0 0 17 = 1 := by
  rw [type112_zero_block_eq_support_sum 0 17 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_zero_seventeen

theorem b4_type112_middle0_one_seventeen : b4Type112Block 1 0 17 = 2 := by
  rw [type112_zero_block_eq_support_sum 1 17 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_seventeen

theorem b4_type112_middle0_two_seventeen : b4Type112Block 2 0 17 = 6 := by
  rw [type112_zero_block_eq_support_sum 2 17 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_two_seventeen

theorem b4_type112_middle0_five_sixteen : b4Type112Block 5 0 16 = 6 := by
  rw [type112_zero_block_eq_support_sum 5 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_five_sixteen

theorem b4_type112_middle0_eight_fifteen : b4Type112Block 8 0 15 = 17 := by
  rw [type112_zero_block_eq_support_sum 8 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_eight_fifteen

theorem b4_type112_middle0_nine_fourteen : b4Type112Block 9 0 14 = 10 := by
  rw [type112_zero_block_eq_support_sum 9 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_nine_fourteen

theorem b4_type112_middle0_twelve_twelve : b4Type112Block 12 0 12 = 20 := by
  rw [type112_zero_block_eq_support_sum 12 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_twelve_twelve

theorem b4_type112_middle0_six_sixteen : b4Type112Block 6 0 16 = 7 := by
  rw [type112_zero_block_eq_support_sum 6 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_six_sixteen

theorem b4_type112_middle0_eleven_thirteen : b4Type112Block 11 0 13 = 12 := by
  rw [type112_zero_block_eq_support_sum 11 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_eleven_thirteen

theorem b4_type112_middle0_zero_twentythree : b4Type112Block 0 0 23 = 1 := by
  rw [type112_zero_block_eq_support_sum 0 23 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_zero_twentythree

theorem b4_type112_middle0_one_twentythree : b4Type112Block 1 0 23 = 2 := by
  rw [type112_zero_block_eq_support_sum 1 23 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_twentythree

theorem b4_type112_middle0_six_twentytwo : b4Type112Block 6 0 22 = 5 := by
  rw [type112_zero_block_eq_support_sum 6 22 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_six_twentytwo

theorem b4_type112_middle0_nine_twentyone : b4Type112Block 9 0 21 = 1 := by
  rw [type112_zero_block_eq_support_sum 9 21 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_nine_twentyone

theorem b4_type112_middle0_zero_twentyfour : b4Type112Block 0 0 24 = 2 := by
  rw [type112_zero_block_eq_support_sum 0 24 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_zero_twentyfour

theorem b4_type112_middle0_six_twentythree : b4Type112Block 6 0 23 = 5 := by
  rw [type112_zero_block_eq_support_sum 6 23 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_six_twentythree

theorem b4_type112_middle0_nine_twentytwo : b4Type112Block 9 0 22 = 2 := by
  rw [type112_zero_block_eq_support_sum 9 22 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_nine_twentytwo

theorem b4_type112_middle0_one_twentyfour : b4Type112Block 1 0 24 = 2 := by
  rw [type112_zero_block_eq_support_sum 1 24 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_one_twentyfour

theorem b4_type112_middle0_thirteen_twenty : b4Type112Block 13 0 20 = 3 := by
  rw [type112_zero_block_eq_support_sum 13 20 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ZeroSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle0_thirteen_twenty

end Paper7MomentCanonicalNumeric
