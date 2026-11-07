import Research.Backfill.Paper2.CatalanComposition
import Research.Backfill.Paper2.EntryRemark6

/-! Two full original existence-and-uniqueness contracts, over integers throughout. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceExplicit
open PowerSeries BackfillPaper2.Challenge

private theorem shift_mul_X (V : PowerSeries ℤ) (h0 : constantCoeff V = 0) :
    X * (PowerSeries.mk fun n => coeff (n + 1) V) = V := by
  ext n
  rcases n with _ | n
  · simp [coeff_zero_eq_constantCoeff_apply, h0]
  · rw [coeff_succ_X_mul, coeff_mk]

theorem check_EX_A273958 : EX_A273958 := by
  let Cs := catalanC
  have hc : Cs = X + Cs ^ 2 := CatalanCore.check_CatalanEq
  have hc0 : constantCoeff Cs = 0 := by simp [Cs, catalanC]
  let V := -(Cs.subst (-(Cs ^ 2)))
  have hi0 : constantCoeff (-(Cs ^ 2)) = 0 := by simp [hc0]
  have hs := HasSubst.of_constantCoeff_zero' hi0
  have hv0 : constantCoeff V = 0 := by
    have ht : constantCoeff (Cs.subst (-(Cs ^ 2))) = 0 := constantCoeff_subst_eq_zero hi0 Cs hc0
    dsimp only [V]
    rw [map_neg, ht, neg_zero]
  let A : PowerSeries ℤ := PowerSeries.mk fun n => coeff (n + 1) V
  have hXA : X * A = V := shift_mul_X V hv0
  have hv : V + V ^ 2 = Cs ^ 2 := by
    have he := congrArg (fun F : PowerSeries ℤ => F.subst (-(Cs ^ 2))) hc
    rw [subst_add hs, subst_X hs, subst_pow hs] at he
    dsimp only [V]
    linear_combination -he
  have heq : Eq273958 Cs A := by
    refine ⟨hc, ?_⟩
    calc
      X * A + X ^ 2 * A ^ 2 = X * A + (X * A) ^ 2 := by ring
      _ = Cs ^ 2 := by rw [hXA]; exact hv
  refine ⟨(Cs, A), heq, ?_⟩
  rintro ⟨D, B⟩ hDB
  have hd0 : constantCoeff D = 0 := by
    have hz : constantCoeff D ^ 2 = 0 := by
      rw [← map_pow, ← hDB.2]
      simp
    exact (pow_eq_zero_iff two_ne_zero).mp hz
  have hu : IsUnit (1 - D - Cs) := isUnit_iff_constantCoeff.mpr (by simp [hd0, hc0])
  have hDC : D = Cs := by
    have hz : (1 - D - Cs) * (D - Cs) = 0 := by linear_combination hDB.1 - hc
    exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hz)
  have hBX : X * B = V := by
    have he := CatalanComposition.check_RC_A273958_closedForm D B hDB
    rw [hDC] at he
    exact he
  have hBA : B = A := mul_left_cancel₀ (X_ne_zero (R := ℤ)) (hBX.trans hXA.symm)
  exact Prod.ext hDC hBA

theorem check_EX_A388734 : EX_A388734 := by
  have hp0 : constantCoeff phi388734 = 0 := by simp [phi388734]
  have hp1 : coeff 1 phi388734 = 1 := by
    rw [phi388734, mul_assoc]
    change coeff (0 + 1) (X * _) = 1
    rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
    simp
  have hu : IsUnit (coeff 1 phi388734) := by rw [hp1]; exact isUnit_one
  let P := substInvOfIsUnit phi388734 hu
  have hs : HasSubst P := HasSubst.substInvOfIsUnit phi388734 hu
  have hP : phi388734.subst P = X := subst_substInvOfIsUnit_right phi388734 hp0 hu
  let A : PowerSeries ℤ := PowerSeries.subst P B388734
  have hOne : (1 : PowerSeries ℤ).subst P = 1 := by rw [← coe_substAlgHom hs, map_one]
  have hA : Eq388734 A := by
    have hb : B388734 = 1 + phi388734 * B388734 ^ 2 +
        phi388734 ^ 2 * (1 - phi388734) * B388734 ^ 3 := EntryRemark6.check_Rem6.1.1
    have he := congrArg (fun F : PowerSeries ℤ => PowerSeries.subst P F) hb
    change A = 1 + X * A ^ 2 + X ^ 2 * (1 - X) * A ^ 3
    simpa only [subst_add hs, subst_mul hs, subst_pow hs, subst_sub hs, hOne, hP] using he
  refine ⟨A, hA, ?_⟩
  intro B hB
  let Q := B + A + X * (1 - X) * (B ^ 2 + B * A + A ^ 2)
  have hQ : IsUnit (1 - X * Q) := isUnit_iff_constantCoeff.mpr (by simp)
  have hz : (1 - X * Q) * (B - A) = 0 := by
    change B = 1 + X * B ^ 2 + X ^ 2 * (1 - X) * B ^ 3 at hB
    change A = 1 + X * A ^ 2 + X ^ 2 * (1 - X) * A ^ 3 at hA
    dsimp only [Q]
    linear_combination hB - hA
  exact sub_eq_zero.mp (hQ.mul_right_eq_zero.mp hz)

end BackfillPaper2.ExistenceExplicit
#print axioms BackfillPaper2.ExistenceExplicit.check_EX_A273958
#print axioms BackfillPaper2.ExistenceExplicit.check_EX_A388734
