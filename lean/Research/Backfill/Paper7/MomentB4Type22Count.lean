import Research.Backfill.Paper7.MomentB4Type22RemainingStrips
import Research.Backfill.Paper7.MomentB4Type22SDStripPilots
import Research.Backfill.Paper7.MomentB4Type22SDSum
import Research.Backfill.Paper7.MomentB4Type22Diagonal

/-! SOURCE ONLY. Full assembly of nineteen exact strip obligations, using
already successful strips4/5/6 and the successful diagonal4. The complete
Type22 value44 is a proposed conclusion; no numeral is an added premise.
The Type112 value5226 and both original52641 clauses remain unproved. -/
set_option autoImplicit false
noncomputable section
namespace Paper7MomentCanonicalNumeric
open BackfillPaper7.Challenge.Legacy
open scoped BigOperators Classical

def b4Type22StripValues : Fin 19 → ℕ :=
  ![0,0,0,0,1,1,3,0,0,1,2,1,2,2,3,4,0,0,0]
#print axioms Paper7MomentCanonicalNumeric.b4Type22StripValues

theorem b4_type22_all_strip_values (S : Fin 19) :
    b4Type22SDStrip S = b4Type22StripValues S := by
  fin_cases S
  · exact b4_type22_strip_zero_low 0 (by decide)
  · exact b4_type22_strip_zero_low 1 (by decide)
  · exact b4_type22_strip_zero_low 2 (by decide)
  · exact b4_type22_strip_zero_low 3 (by decide)
  · exact b4_type22_sd_strip_four
  · exact b4_type22_sd_strip_five
  · exact b4_type22_sd_strip_six
  · exact b4_type22_strip_zero_middle 7 (by decide)
  · exact b4_type22_strip_zero_middle 8 (by decide)
  · exact b4_type22_strip_nine
  · exact b4_type22_strip_ten
  · exact b4_type22_strip_eleven
  · exact b4_type22_strip_twelve
  · exact b4_type22_strip_thirteen
  · exact b4_type22_strip_fourteen
  · exact b4_type22_strip_fifteen
  · exact b4_type22_strip_zero_high 16 (by decide)
  · exact b4_type22_strip_zero_high 17 (by decide)
  · exact b4_type22_strip_zero_high 18 (by decide)
#print axioms Paper7MomentCanonicalNumeric.b4_type22_all_strip_values

theorem b4_type22_strip_values_sum : (∑ S : Fin 19, b4Type22StripValues S) = 20 := by
  decide +kernel
#print axioms Paper7MomentCanonicalNumeric.b4_type22_strip_values_sum

theorem b4_type22_all_strips_sum : (∑ S : Fin 19, b4Type22SDStrip S) = 20 := by
  simp_rw [b4_type22_all_strip_values]
  exact b4_type22_strip_values_sum
#print axioms Paper7MomentCanonicalNumeric.b4_type22_all_strips_sum

theorem b4_type22_finite_sum_eq_forty_four : b4Type22FiniteSum = 44 := by
  rw [b4_type22_finite_sum_eq_diagonal_and_SD,b4_type22_diagonal_budget_sum,
    b4_type22_SD_sum_eq_strips,b4_type22_all_strips_sum]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_finite_sum_eq_forty_four

theorem b4_type22_card_eq_forty_four : Fintype.card B4Type22 = 44 := by
  rw [b4_type22_card_eq_finite_sum,b4_type22_finite_sum_eq_forty_four]
#print axioms Paper7MomentCanonicalNumeric.b4_type22_card_eq_forty_four

theorem b4_canonical_clauses_iff_type112_5226 :
    ((canonB1 4 41).Finite ∧ (canonB1 4 41).ncard = 52641) ∧
      ((canonD2 4 41).Finite ∧ (canonD2 4 41).ncard = 52641) ↔
        b4Type112FiniteSum = 5226 := by
  rw [b4_canonical_clauses_iff_two_finite_sums,b4_type22_finite_sum_eq_forty_four]
  omega
#print axioms Paper7MomentCanonicalNumeric.b4_canonical_clauses_iff_type112_5226

end Paper7MomentCanonicalNumeric
