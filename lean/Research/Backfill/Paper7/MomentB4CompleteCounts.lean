import Research.Backfill.Paper7.MomentB4Type112MiddleZeroSum
import Research.Backfill.Paper7.MomentB4Type112MiddleOneSum
import Research.Backfill.Paper7.MomentB4Type112MiddleTwoSum
import Research.Backfill.Paper7.MomentB4Type112MiddleThreeSum
import Research.Backfill.Paper7.MomentB4Type112MiddleFourSum
import Research.Backfill.Paper7.MomentB4Type112MiddleFiveSum
import Research.Backfill.Paper7.MomentB4Type112MiddleSixSum
import Research.Backfill.Paper7.MomentB4Type112MiddleSevenSum
import Research.Backfill.Paper7.MomentB4Type112MiddleEightSum
import Research.Backfill.Paper7.MomentB4Type112MiddleNineSum
import Research.Backfill.Paper7.MomentB4Type112MiddleTenSum
import Research.Backfill.Paper7.MomentB4Type112MiddleElevenCount
import Research.Backfill.Paper7.MomentB4Type112MiddleTwelveCount
import Research.Backfill.Paper7.MomentB4Type22Count

/-! SOURCE ONLY. Original complete b4 counts, pending the four t0 modules.
The successful t1 dependency is the corrected actual606 source with983.
No numerical target or support assumption is added to any theorem header.
These two original canonical sets receive separate cardinality conclusions;
their equality is not asserted. The four b6 numbers remain outside this file. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy Paper7MomentCounts Paper7MomentCertificate
open scoped BigOperators Classical

theorem b4_type112_finite_sum_eq_5226 : b4Type112FiniteSum = 5226 := by
  rw [b4_type112_finite_sum_eq_first_twelve_add_six,
    b4_type112_first_twelve_eq_first_eleven_add_ninety_six,
    b4_type112_first_eleven_eq_first_ten_add_205,
    b4_type112_first_ten_eq_first_nine_add_168,
    b4_type112_first_nine_eq_first_eight_add_144,
    b4_type112_first_eight_eq_first_seven_add_200,
    b4_type112_first_seven_eq_first_six_add_249,
    b4_type112_first_six_eq_first_five_add_370,
    b4_type112_first_five_eq_first_four_add_583,
    b4_type112_first_four_eq_first_three_add_646,
    b4_type112_first_three_eq_first_two_add_943,
    b4_type112_first_two_eq_first_one_add_983,
    b4_type112_first_one_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_finite_sum_eq_5226

theorem b4_type112_card_eq_5226 : Fintype.card B4Type112 = 5226 := by
  rw [b4_type112_card_eq_finite_sum,b4_type112_finite_sum_eq_5226]
#print axioms Paper7MomentCanonicalNumeric.b4_type112_card_eq_5226

theorem b4_two_fixed_type_card_sum_eq_10584 :
    3 * Fintype.card B4Type22 + 2 * Fintype.card B4Type112 = 10584 := by
  norm_num [b4_type22_card_eq_forty_four,b4_type112_card_eq_5226]
#print axioms Paper7MomentCanonicalNumeric.b4_two_fixed_type_card_sum_eq_10584

theorem b4_nonidentity_fixed_sum_eq_10584 : b4NonidentityFixedSum = 10584 := by
  rw [b4_nonidentity_cycle_type_sum,b4_type4_card]
  simpa only [mul_zero,zero_add] using b4_two_fixed_type_card_sum_eq_10584
#print axioms Paper7MomentCanonicalNumeric.b4_nonidentity_fixed_sum_eq_10584

theorem b4_original_canonical_clauses :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) := by
  exact b4_canonical_clauses_iff_type112_5226.mpr b4_type112_finite_sum_eq_5226
#print axioms Paper7MomentCanonicalNumeric.b4_original_canonical_clauses

theorem canonB1_b4_original_finite : (canonB1 4 41).Finite := by
  exact b4_original_canonical_clauses.1.1
#print axioms Paper7MomentCanonicalNumeric.canonB1_b4_original_finite

theorem canonB1_b4_original_ncard : (canonB1 4 41).ncard = 52641 := by
  exact b4_original_canonical_clauses.1.2
#print axioms Paper7MomentCanonicalNumeric.canonB1_b4_original_ncard

theorem canonD2_b4_original_finite : (canonD2 4 41).Finite := by
  exact b4_original_canonical_clauses.2.1
#print axioms Paper7MomentCanonicalNumeric.canonD2_b4_original_finite

theorem canonD2_b4_original_ncard : (canonD2 4 41).ncard = 52641 := by
  exact b4_original_canonical_clauses.2.2
#print axioms Paper7MomentCanonicalNumeric.canonD2_b4_original_ncard

end Paper7MomentCanonicalNumeric
