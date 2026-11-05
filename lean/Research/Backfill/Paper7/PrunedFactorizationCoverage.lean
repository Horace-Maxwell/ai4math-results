import Research.Backfill.Paper7.PrunedRootCoverage
import Research.Backfill.Paper7.RootFactorizationCoverage

set_option autoImplicit false
noncomputable section
namespace Paper7CycleThreeCertificate
open Polynomial BackfillPaper7.Challenge.Legacy.Algebra

theorem checked_pruned_table_covers_factorization (rows : List (List ℤ))
    (hcheck : prunedRootCheck rows [] 8 (-9) = true) (H : Polynomial ℤ)
    (hF : IntegerFactorizationOn H (integerWindow 9)) (hdeg : H.natDegree = 8)
    (hpattern : coefficientPattern H) :
    ∃ a ∈ rows, H = (a.map (fun z => X-C z)).prod := by
  obtain ⟨a, hsort, hrange, hlen, hsum, hpoly⟩ := sorted_factorization H hF hdeg hpattern.1
  have hp := rootPattern_of_factorization H a hlen hsum hpoly hpattern
  have hm := prunedRootCheck_sound rows [] 8 (-9) hcheck a hlen hsort hrange
    (fun z hz => (hrange z hz).1) hp
  exact ⟨a, hm, hpoly⟩
#print axioms Paper7CycleThreeCertificate.checked_pruned_table_covers_factorization

end Paper7CycleThreeCertificate
