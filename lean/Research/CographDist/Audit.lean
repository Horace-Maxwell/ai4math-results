import Research.CographDist.Main
import Research.CographDist.ChallengeTests

/-! Final audit: restates the frozen statement and prints the axioms. -/

set_option autoImplicit false

namespace CographDist.Audit

theorem check_OpenProblemI_negative : CographDist.OpenProblemI_negative :=
  CographDist.openProblemI_negative

theorem check_family (m : ℕ) (hm : 1 ≤ m) :
    (CographDist.fam m).Connected ∧ CographDist.IsCograph (CographDist.fam m) ∧
      ∃ l : ℝ, -2 - 1 / (2 * (m : ℝ)) < l ∧ l < -2 ∧
        CographDist.IsDistEigenvalue (CographDist.fam m) l :=
  CographDist.family_theorem m hm

end CographDist.Audit

#print axioms CographDist.Audit.check_OpenProblemI_negative
#print axioms CographDist.Audit.check_family
#print axioms CographDist.Tests.pathGraph_four_not_cograph
#print axioms CographDist.Tests.complete_two_distEigenvalue_one
#print axioms CographDist.Tests.complete_two_not_distEigenvalue_two
#print axioms CographDist.Tests.complete_two_connected
#print axioms CographDist.Tests.complete_two_isCograph
