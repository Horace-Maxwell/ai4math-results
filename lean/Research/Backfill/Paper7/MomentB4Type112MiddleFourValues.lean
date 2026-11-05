import Research.Backfill.Paper7.MomentB4Type112MiddleFourSupport

/-! SOURCE ONLY. Complete catalogue fibres are retained in the support
sum. The original Fin10 weight has k<=t, hence k<=4 in this layer.
Seven endpoint blocks have two distinct accepted catalogue fibres. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem type112_four_block_eq_support_sum (z u : Fin 38)
    (hzu : z ≤ u) (hz : z.val < 19) (hu : u.val < 27) :
    b4Type112Block z 4 u = ∑ sm ∈ b4FeatureCatalog,
      if B4Type112FourSupport z.val u.val sm then
        b4Type112PlainWeight z.val 4 u.val
          (b4Type112RecoveredQ (z.val+u.val) 4 (u.val-z.val) sm.2) else 0 := by
  rw [type112_block_eq_recovered_catalog_sum z 4 u hzu]
  unfold b4Type112RecoveredBlock
  change (∑ sm ∈ b4FeatureCatalog,
    if b4Type112RecoveredGuard (z.val+u.val) 4 (u.val-z.val) sm then
      b4Type112PlainWeight z.val 4 u.val
        (b4Type112RecoveredQ (z.val+u.val) 4 (u.val-z.val) sm.2) else 0) = _
  apply Finset.sum_congr rfl
  intro sm hm
  have he := type112_four_small_catalog_certificate
    (⟨z.val,hz⟩ : Fin 19) (⟨u.val,hu⟩ : Fin 27) sm hm
  by_cases hg : b4Type112RecoveredGuard (z.val+u.val) 4 (u.val-z.val) sm
  · have hs : B4Type112FourSupport z.val u.val sm := he.mp ⟨hzu,hg⟩
    simp only [hg,hs,ite_true]
  · have hs : ¬ B4Type112FourSupport z.val u.val sm := fun h => hg (he.mpr h).2
    simp only [hg,hs,ite_false]
#print axioms Paper7MomentCanonicalNumeric.type112_four_block_eq_support_sum

theorem b4_type112_middle4_zero_zero : b4Type112Block 0 4 0 = 1 := by
  rw [type112_four_block_eq_support_sum 0 0 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_zero_zero

theorem b4_type112_middle4_zero_one : b4Type112Block 0 4 1 = 1 := by
  rw [type112_four_block_eq_support_sum 0 1 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_zero_one

theorem b4_type112_middle4_zero_three : b4Type112Block 0 4 3 = 2 := by
  rw [type112_four_block_eq_support_sum 0 3 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_zero_three

theorem b4_type112_middle4_one_three : b4Type112Block 1 4 3 = 4 := by
  rw [type112_four_block_eq_support_sum 1 3 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_one_three

theorem b4_type112_middle4_two_three : b4Type112Block 2 4 3 = 1 := by
  rw [type112_four_block_eq_support_sum 2 3 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_two_three

theorem b4_type112_middle4_zero_two : b4Type112Block 0 4 2 = 1 := by
  rw [type112_four_block_eq_support_sum 0 2 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_zero_two

theorem b4_type112_middle4_one_two : b4Type112Block 1 4 2 = 3 := by
  rw [type112_four_block_eq_support_sum 1 2 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_one_two

theorem b4_type112_middle4_two_two : b4Type112Block 2 4 2 = 5 := by
  rw [type112_four_block_eq_support_sum 2 2 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_two_two

theorem b4_type112_middle4_one_one : b4Type112Block 1 4 1 = 1 := by
  rw [type112_four_block_eq_support_sum 1 1 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_one_one

theorem b4_type112_middle4_zero_twelve : b4Type112Block 0 4 12 = 5 := by
  rw [type112_four_block_eq_support_sum 0 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_zero_twelve

theorem b4_type112_middle4_zero_fourteen : b4Type112Block 0 4 14 = 9 := by
  rw [type112_four_block_eq_support_sum 0 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_zero_fourteen

theorem b4_type112_middle4_one_fourteen : b4Type112Block 1 4 14 = 18 := by
  rw [type112_four_block_eq_support_sum 1 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_one_fourteen

theorem b4_type112_middle4_two_fourteen : b4Type112Block 2 4 14 = 22 := by
  rw [type112_four_block_eq_support_sum 2 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_two_fourteen

theorem b4_type112_middle4_three_fourteen : b4Type112Block 3 4 14 = 13 := by
  rw [type112_four_block_eq_support_sum 3 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_three_fourteen

theorem b4_type112_middle4_four_thirteen : b4Type112Block 4 4 13 = 23 := by
  rw [type112_four_block_eq_support_sum 4 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_four_thirteen

theorem b4_type112_middle4_five_thirteen : b4Type112Block 5 4 13 = 26 := by
  rw [type112_four_block_eq_support_sum 5 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_five_thirteen

theorem b4_type112_middle4_six_thirteen : b4Type112Block 6 4 13 = 6 := by
  rw [type112_four_block_eq_support_sum 6 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_six_thirteen

theorem b4_type112_middle4_seven_twelve : b4Type112Block 7 4 12 = 28 := by
  rw [type112_four_block_eq_support_sum 7 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_seven_twelve

theorem b4_type112_middle4_nine_eleven : b4Type112Block 9 4 11 = 6 := by
  rw [type112_four_block_eq_support_sum 9 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_nine_eleven

theorem b4_type112_middle4_ten_ten : b4Type112Block 10 4 10 = 9 := by
  rw [type112_four_block_eq_support_sum 10 10 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_ten_ten

theorem b4_type112_middle4_zero_sixteen : b4Type112Block 0 4 16 = 9 := by
  rw [type112_four_block_eq_support_sum 0 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_zero_sixteen

theorem b4_type112_middle4_four_fifteen : b4Type112Block 4 4 15 = 21 := by
  rw [type112_four_block_eq_support_sum 4 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_four_fifteen

theorem b4_type112_middle4_five_fifteen : b4Type112Block 5 4 15 = 30 := by
  rw [type112_four_block_eq_support_sum 5 15 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_five_fifteen

theorem b4_type112_middle4_seven_fourteen : b4Type112Block 7 4 14 = 9 := by
  rw [type112_four_block_eq_support_sum 7 14 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_seven_fourteen

theorem b4_type112_middle4_nine_thirteen : b4Type112Block 9 4 13 = 17 := by
  rw [type112_four_block_eq_support_sum 9 13 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_nine_thirteen

theorem b4_type112_middle4_ten_twelve : b4Type112Block 10 4 12 = 6 := by
  rw [type112_four_block_eq_support_sum 10 12 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_ten_twelve

theorem b4_type112_middle4_eleven_eleven : b4Type112Block 11 4 11 = 9 := by
  rw [type112_four_block_eq_support_sum 11 11 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_eleven_eleven

theorem b4_type112_middle4_one_sixteen : b4Type112Block 1 4 16 = 10 := by
  rw [type112_four_block_eq_support_sum 1 16 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_one_sixteen

theorem b4_type112_middle4_two_twentythree : b4Type112Block 2 4 23 = 7 := by
  rw [type112_four_block_eq_support_sum 2 23 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_two_twentythree

theorem b4_type112_middle4_three_twentythree : b4Type112Block 3 4 23 = 1 := by
  rw [type112_four_block_eq_support_sum 3 23 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_three_twentythree

theorem b4_type112_middle4_three_twentysix : b4Type112Block 3 4 26 = 1 := by
  rw [type112_four_block_eq_support_sum 3 26 (by decide) (by decide) (by decide)]
  norm_num [b4FeatureCatalog,B4Type112FourSupport,b4Type112RecoveredQ,
    b4Type112CatalogResidual,b4Type112DoubleBase,b4Type112PlainWeight,Fin.sum_univ_succ]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_middle4_three_twentysix

end Paper7MomentCanonicalNumeric
