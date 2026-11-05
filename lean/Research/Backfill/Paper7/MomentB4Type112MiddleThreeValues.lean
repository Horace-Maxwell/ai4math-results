import Research.Backfill.Paper7.MomentB4Type112MiddleThreeSupport

/-! SOURCE ONLY. Original catalogue Q recovery and Fin10 weights with
k<=3. Both fibres of (4,14) and (11,12) remain in the catalogue sum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_three_block_eq_support_sum (z u : Fin 38)
    (hzu : z ≤ u) (hz : z.val < 19) (hu : u.val < 27) :
    b4Type112Block z 3 u = ∑ sm ∈ b4FeatureCatalog,
      if B4Type112ThreeSupport z.val u.val sm then
        b4Type112PlainWeight z.val 3 u.val
          (b4Type112RecoveredQ (z.val+u.val) 3 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 3 u hzu]
  unfold b4Type112RecoveredBlock
  change (∑ sm ∈ b4FeatureCatalog,
    if b4Type112RecoveredGuard (z.val+u.val) 3 (u.val-z.val) sm then
      b4Type112PlainWeight z.val 3 u.val
        (b4Type112RecoveredQ (z.val+u.val) 3 (u.val-z.val) sm.2) else 0) = _
  apply Finset.sum_congr rfl
  intro sm hm
  have he := type112_three_small_catalog_certificate
    (⟨z.val,hz⟩ : Fin 19) (⟨u.val,hu⟩ : Fin 27) sm hm
  by_cases hg : b4Type112RecoveredGuard (z.val+u.val) 3 (u.val-z.val) sm
  · have hs : B4Type112ThreeSupport z.val u.val sm := he.mp ⟨hzu,hg⟩
    simp only [hg,hs,ite_true]
  · have hs : ¬ B4Type112ThreeSupport z.val u.val sm := fun h => hg (he.mpr h).2
    simp only [hg,hs,ite_false]
#print axioms Paper7MomentCanonicalNumeric.type112_three_block_eq_support_sum

theorem b4_type112_middle3_zero_three : b4Type112Block 0 3 3 = 1 := by
  rw [type112_three_block_eq_support_sum 0 3 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_zero_three

theorem b4_type112_middle3_zero_five : b4Type112Block 0 3 5 = 3 := by
  rw [type112_three_block_eq_support_sum 0 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_zero_five

theorem b4_type112_middle3_one_five : b4Type112Block 1 3 5 = 3 := by
  rw [type112_three_block_eq_support_sum 1 5 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_one_five

theorem b4_type112_middle3_zero_four : b4Type112Block 0 3 4 = 1 := by
  rw [type112_three_block_eq_support_sum 0 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_zero_four

theorem b4_type112_middle3_one_four : b4Type112Block 1 3 4 = 4 := by
  rw [type112_three_block_eq_support_sum 1 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_one_four

theorem b4_type112_middle3_two_four : b4Type112Block 2 3 4 = 7 := by
  rw [type112_three_block_eq_support_sum 2 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_two_four

theorem b4_type112_middle3_three_four : b4Type112Block 3 3 4 = 2 := by
  rw [type112_three_block_eq_support_sum 3 4 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_three_four

theorem b4_type112_middle3_two_three : b4Type112Block 2 3 3 = 2 := by
  rw [type112_three_block_eq_support_sum 2 3 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_two_three

theorem b4_type112_middle3_three_three : b4Type112Block 3 3 3 = 8 := by
  rw [type112_three_block_eq_support_sum 3 3 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_three_three

theorem b4_type112_middle3_zero_thirteen : b4Type112Block 0 3 13 = 3 := by
  rw [type112_three_block_eq_support_sum 0 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_zero_thirteen

theorem b4_type112_middle3_one_thirteen : b4Type112Block 1 3 13 = 3 := by
  rw [type112_three_block_eq_support_sum 1 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_one_thirteen

theorem b4_type112_middle3_zero_twelve : b4Type112Block 0 3 12 = 1 := by
  rw [type112_three_block_eq_support_sum 0 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_zero_twelve

theorem b4_type112_middle3_one_twelve : b4Type112Block 1 3 12 = 4 := by
  rw [type112_three_block_eq_support_sum 1 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_one_twelve

theorem b4_type112_middle3_two_twelve : b4Type112Block 2 3 12 = 11 := by
  rw [type112_three_block_eq_support_sum 2 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_two_twelve

theorem b4_type112_middle3_zero_fourteen : b4Type112Block 0 3 14 = 4 := by
  rw [type112_three_block_eq_support_sum 0 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_zero_fourteen

theorem b4_type112_middle3_one_fourteen : b4Type112Block 1 3 14 = 8 := by
  rw [type112_three_block_eq_support_sum 1 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_one_fourteen

theorem b4_type112_middle3_two_fourteen : b4Type112Block 2 3 14 = 12 := by
  rw [type112_three_block_eq_support_sum 2 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_two_fourteen

theorem b4_type112_middle3_three_fourteen : b4Type112Block 3 3 14 = 16 := by
  rw [type112_three_block_eq_support_sum 3 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_three_fourteen

theorem b4_type112_middle3_four_fourteen : b4Type112Block 4 3 14 = 31 := by
  rw [type112_three_block_eq_support_sum 4 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_four_fourteen

theorem b4_type112_middle3_six_thirteen : b4Type112Block 6 3 13 = 19 := by
  rw [type112_three_block_eq_support_sum 6 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_six_thirteen

theorem b4_type112_middle3_zero_fifteen : b4Type112Block 0 3 15 = 4 := by
  rw [type112_three_block_eq_support_sum 0 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_zero_fifteen

theorem b4_type112_middle3_one_fifteen : b4Type112Block 1 3 15 = 8 := by
  rw [type112_three_block_eq_support_sum 1 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_one_fifteen

theorem b4_type112_middle3_five_fourteen : b4Type112Block 5 3 14 = 12 := by
  rw [type112_three_block_eq_support_sum 5 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_five_fourteen

theorem b4_type112_middle3_seven_thirteen : b4Type112Block 7 3 13 = 12 := by
  rw [type112_three_block_eq_support_sum 7 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_seven_thirteen

theorem b4_type112_middle3_eight_twelve : b4Type112Block 8 3 12 = 30 := by
  rw [type112_three_block_eq_support_sum 8 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_eight_twelve

theorem b4_type112_middle3_ten_eleven : b4Type112Block 10 3 11 = 4 := by
  rw [type112_three_block_eq_support_sum 10 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_ten_eleven

theorem b4_type112_middle3_one_sixteen : b4Type112Block 1 3 16 = 8 := by
  rw [type112_three_block_eq_support_sum 1 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_one_sixteen

theorem b4_type112_middle3_two_sixteen : b4Type112Block 2 3 16 = 12 := by
  rw [type112_three_block_eq_support_sum 2 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_two_sixteen

theorem b4_type112_middle3_three_sixteen : b4Type112Block 3 3 16 = 14 := by
  rw [type112_three_block_eq_support_sum 3 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_three_sixteen

theorem b4_type112_middle3_six_fifteen : b4Type112Block 6 3 15 = 16 := by
  rw [type112_three_block_eq_support_sum 6 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_six_fifteen

theorem b4_type112_middle3_eight_fourteen : b4Type112Block 8 3 14 = 12 := by
  rw [type112_three_block_eq_support_sum 8 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_eight_fourteen

theorem b4_type112_middle3_eleven_twelve : b4Type112Block 11 3 12 = 22 := by
  rw [type112_three_block_eq_support_sum 11 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_eleven_twelve

theorem b4_type112_middle3_four_sixteen : b4Type112Block 4 3 16 = 18 := by
  rw [type112_three_block_eq_support_sum 4 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_four_sixteen

theorem b4_type112_middle3_ten_thirteen : b4Type112Block 10 3 13 = 12 := by
  rw [type112_three_block_eq_support_sum 10 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112ThreeSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle3_ten_thirteen

end Paper7MomentCanonicalNumeric
