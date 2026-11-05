import Research.Backfill.Paper7.RootDomainCoverage
import Research.Backfill.Paper7.CycleThreeRootListReduction

/-! Transport an actual integer factorization to a sorted row and then into a
kernel-checked table. No concrete table or successful check is asserted here. -/
set_option autoImplicit false
noncomputable section
namespace Paper7CycleThreeCertificate
open Polynomial BackfillPaper7.Challenge.Legacy.Algebra

def coefficientPattern (H : Polynomial ℤ) : Prop :=
  H.coeff 7 = 0 ∧ H.coeff 5 = -2 ∧ 0 ≤ H.coeff 0 ∧
    ((H.coeff 3 = 2 ∧ H.coeff 1 = 0 ∧ 0 ≤ -H.coeff 6 - 4 ∧ -H.coeff 6 - 4 ≤ 46) ∨
     (H.coeff 3 = 4 ∧ H.coeff 1 = -2 ∧ 0 ≤ -H.coeff 6 - 5 ∧ -H.coeff 6 - 5 ≤ 46))
#print axioms Paper7CycleThreeCertificate.coefficientPattern

theorem sorted_factorization (H : Polynomial ℤ)
    (hF : IntegerFactorizationOn H (integerWindow 9)) (hdeg : H.natDegree = 8)
    (h7 : H.coeff 7 = 0) :
    ∃ a : List ℤ, a.Pairwise (· ≤ ·) ∧ (∀ z ∈ a, -9 ≤ z ∧ z ≤ 9) ∧
      a.length = 8 ∧ a.sum = 0 ∧ H = (a.map (fun z => X-C z)).prod := by
  obtain ⟨w, hw, hwlen, hwsum, hwpoly⟩ :=
    Paper7CycleThree.degree_eight_factorization_sum_zero hF hdeg h7
  let a := (w : Multiset ℤ).sort (· ≤ ·)
  have haeq : (a : Multiset ℤ) = (w : Multiset ℤ) := Multiset.sort_eq _ _
  have hasum : a.sum = w.sum := by
    simpa only [Multiset.sum_coe] using congrArg Multiset.sum haeq
  have hapoly : (a.map (fun z => (X-C z : Polynomial ℤ))).prod =
      (w.map (fun z => (X-C z : Polynomial ℤ))).prod := by
    have h := congrArg Multiset.prod
      (congrArg (Multiset.map (fun z => (X-C z : Polynomial ℤ))) haeq)
    simpa only [Multiset.map_coe, Multiset.prod_coe] using h
  refine ⟨a, Multiset.pairwise_sort _ _, ?_, ?_, hasum.trans hwsum, hwpoly.trans hapoly.symm⟩
  · intro z hz
    have hzw : z ∈ w := by
      have hzm : z ∈ (a : Multiset ℤ) := by simpa using hz
      rw [haeq] at hzm
      simpa using hzm
    have hwin := hw z hzw
    exact Finset.mem_Icc.mp hwin
  · simpa only [a, Multiset.length_sort, Multiset.coe_card] using hwlen
#print axioms Paper7CycleThreeCertificate.sorted_factorization

theorem rootPattern_of_factorization (H : Polynomial ℤ) (a : List ℤ)
    (hlen : a.length = 8) (hsum : a.sum = 0)
    (hpoly : H = (a.map (fun z => X-C z)).prod) (hpattern : coefficientPattern H) :
    rootPattern a := by
  have hcoeff (n : ℕ) : rootCoefficient a n = H.coeff n := by
    rw [rootCoefficient_eq, ← hpoly]
  unfold rootPattern
  simp only [hcoeff]
  exact ⟨hlen, hsum, hpattern⟩
#print axioms Paper7CycleThreeCertificate.rootPattern_of_factorization

theorem checked_table_covers_factorization (rows : List (List ℤ))
    (hcheck : rootCoverageCheck rows [] 8 (-9) = true) (H : Polynomial ℤ)
    (hF : IntegerFactorizationOn H (integerWindow 9)) (hdeg : H.natDegree = 8)
    (hpattern : coefficientPattern H) :
    ∃ a ∈ rows, H = (a.map (fun z => X-C z)).prod := by
  obtain ⟨a, hsort, hrange, hlen, hsum, hpoly⟩ := sorted_factorization H hF hdeg hpattern.1
  have hp := rootPattern_of_factorization H a hlen hsum hpoly hpattern
  have hm := rootCoverageCheck_sound rows [] 8 (-9) hcheck a hlen hsort hrange
    (fun z hz => (hrange z hz).1) hp
  exact ⟨a, hm, hpoly⟩
#print axioms Paper7CycleThreeCertificate.checked_table_covers_factorization

/-- Both proof inputs must be discharged by future concrete certificates.
This is a checker-soundness theorem, not a conditional frozen-contract check. -/
theorem checked_table_and_rows_reject_factorization (rows : List (List ℤ))
    (hcheck : rootCoverageCheck rows [] 8 (-9) = true) (H : Polynomial ℤ)
    (hdeg : H.natDegree = 8) (hpattern : coefficientPattern H)
    (hrows : ∀ a ∈ rows, H ≠ (a.map (fun z => X-C z)).prod) :
    ¬ IntegerFactorizationOn H (integerWindow 9) := by
  intro hF
  obtain ⟨a, ha, hpoly⟩ := checked_table_covers_factorization rows hcheck H hF hdeg hpattern
  exact hrows a ha hpoly
#print axioms Paper7CycleThreeCertificate.checked_table_and_rows_reject_factorization

end Paper7CycleThreeCertificate
