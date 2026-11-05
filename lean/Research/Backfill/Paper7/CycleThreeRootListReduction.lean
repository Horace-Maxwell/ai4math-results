import Research.Backfill.Paper7.CycleThreeCoefficientRecovery
import Research.Backfill.Paper7.CycleThreeLowDegreeReduction

/-! Actual complete factorizations have exactly eight integer roots counted
with multiplicity; no root search result is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThree
open Polynomial BackfillPaper7.Challenge.Legacy.Algebra

theorem factorization_length_eq_natDegree {H : Polynomial ℤ} {S : Finset ℤ}
    (hF : IntegerFactorizationOn H S) :
    ∃ a : List ℤ, (∀ z ∈ a, z ∈ S) ∧ a.length = H.natDegree ∧
      H = (a.map (fun z => X-C z)).prod := by
  obtain ⟨a, ha, hpoly⟩ := hF
  refine ⟨a, ha, ?_, hpoly⟩
  have hdeg : ((a.map (fun z : ℤ => (X-C z : Polynomial ℤ))).prod).natDegree = a.length := by
    simpa using Polynomial.natDegree_multiset_prod_X_sub_C_eq_card (a : Multiset ℤ)
  rw [← hpoly] at hdeg
  exact hdeg.symm
#print axioms Paper7CycleThree.factorization_length_eq_natDegree

theorem degree_eight_factorization_sum_zero {H : Polynomial ℤ}
    (hF : IntegerFactorizationOn H (integerWindow 9)) (hdeg : H.natDegree = 8)
    (h7 : H.coeff 7 = 0) :
    ∃ a : List ℤ, (∀ z ∈ a, z ∈ integerWindow 9) ∧ a.length = 8 ∧ a.sum = 0 ∧
      H = (a.map (fun z => X-C z)).prod := by
  obtain ⟨a, ha, hlen, hpoly⟩ := factorization_length_eq_natDegree hF
  rw [hdeg] at hlen
  have hpos : 0 < (a : Multiset ℤ).card := by simpa using (by omega : 0 < a.length)
  have hcoeff : ((a.map (fun z : ℤ => (X-C z : Polynomial ℤ))).prod).coeff (a.length-1) = -a.sum := by
    simpa using Polynomial.multiset_prod_X_sub_C_coeff_card_pred (a : Multiset ℤ) hpos
  rw [← hpoly, hlen] at hcoeff
  change H.coeff 7 = -a.sum at hcoeff
  rw [h7] at hcoeff
  exact ⟨a, ha, hlen, by omega, hpoly⟩
#print axioms Paper7CycleThree.degree_eight_factorization_sum_zero

end Paper7CycleThree
