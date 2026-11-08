import Research.Backfill.Paper1.PathLinearConvex
import Research.Backfill.Paper1.GeneralEqualityBase

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1 ICGGeneral

theorem check_AlternatingPath : NarrowSupplement.AlternatingPath := by
  intro x hx k _hk j hj hjk
  have hr : (j + 1).toNat ≤ k := by omega
  rw [NarrowPath.z_eq_Zp (by linarith) k j hj hjk]
  change |Zp x k sgnv (j + 1).toNat| = _
  rw [ICGEqualParityB.Zp_sgnv_eq hx hr, abs_mul, GeneralEquality.sign_abs, one_mul,
    abs_of_nonneg (nu_pos hx _).le, Challenge.mu, Additional.muSeq_eq_nu]
  congr 1
  omega

#print axioms check_AlternatingPath
end CodexPaper1
