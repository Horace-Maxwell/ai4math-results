import Research.Backfill.Paper1.PathLinearConvex

set_option autoImplicit false
noncomputable section
namespace CodexPaper1
open BackfillPaper1

theorem check_PathCoordinates : NarrowSupplement.PathCoordinates := by
  intro x hx k hk w
  have hx0 : x ≠ 0 := by linarith
  constructor
  · rw [Additional.tMulVec_eq_Tv x k w k le_rfl,
      NarrowPath.z_eq_Zp hx0 k (-1) (by omega) (by omega)]
    norm_num only [neg_add_cancel, Int.toNat_zero]
    exact ICGGeneral.Tv_last hx0 k w
  · intro u hu
    have hk1 : k - 1 - u + u + 1 = k := by omega
    have hi1 : k - 1 - u + 1 = k - u := by omega
    have hz : Challenge.z x k w ((k : ℤ) - 1 - u) =
        ICGGeneral.Zp x k w (k - u) := by
      rw [NarrowPath.z_eq_Zp hx0 k _ (by omega) (by omega)]
      congr 1
      omega
    have hr := ICGGeneral.Tv_row hx0 (k - 1 - u) u w
    rw [hk1, hi1] at hr
    rw [Additional.tMulVec_eq_Tv x k w u hu.le, hr, hz,
      ICGGeneral.Zp_rec hx0 k w (k := k - 1 - u) (by omega), hi1]
    have hp : x ^ k = x ^ (k - 1) * x := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    rw [hp]
    field_simp
    ring

#print axioms check_PathCoordinates
end CodexPaper1
