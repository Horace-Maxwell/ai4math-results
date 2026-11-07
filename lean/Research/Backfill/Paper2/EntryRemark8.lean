import Research.Backfill.Paper2.Challenge

/-! The two full integer and mod-three rational-series identities of Remark 8. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.EntryRemark8
open PowerSeries BackfillPaper2.Challenge

private theorem one_sub_mul (R : Type*) [CommRing R] :
    (X * invOfUnit (1 - X) 1 : PowerSeries R) * (1 - X) = X := by
  rw [mul_assoc, invOfUnit_mul]
  · simp
  · simp

theorem check_Rem8 : Rem8 := by
  constructor
  · let F : PowerSeries ℤ := X * invOfUnit (1 - X) 1
    let D : PowerSeries ℤ := 1 - 2 * X + 2 * X ^ 2
    let h : PowerSeries ℤ := X ^ 2 * invOfUnit D 1
    have hD0 : constantCoeff D = 1 := by simp [D]
    have hh : h * D = X ^ 2 := by
      dsimp only [h]
      rw [mul_assoc, invOfUnit_mul D 1 hD0, mul_one]
    have hf : F * (1 - X) = X := one_sub_mul ℤ
    have h0 : constantCoeff h = 0 := by simp [h]
    have hs : HasSubst h := HasSubst.of_constantCoeff_zero' h0
    have hsub := congrArg (fun G : PowerSeries ℤ => G.subst h) hf
    have hOne : (1 : PowerSeries ℤ).subst h = 1 := by
      rw [← coe_substAlgHom hs, map_one]
    simp only [subst_mul hs, subst_sub hs, subst_X hs, hOne] at hsub
    have hf2 : F ^ 2 * (1 - X) ^ 2 = X ^ 2 := by
      calc
        F ^ 2 * (1 - X) ^ 2 = (F * (1 - X)) ^ 2 := by ring
        _ = X ^ 2 := congrArg (fun G : PowerSeries ℤ => G ^ 2) hf
    have hd : D = (1 - X) ^ 2 + X ^ 2 := by dsimp [D]; ring
    have hprod : (F ^ 2 * (1 - h) - h) * (1 - X) ^ 2 = 0 := by
      rw [hd] at hh
      linear_combination -hh + (1 - h) * hf2
    have hq : IsUnit ((1 - X : PowerSeries ℤ) ^ 2) :=
      (isUnit_iff_constantCoeff.mpr (by simp : IsUnit (constantCoeff (1 - X : PowerSeries ℤ)))).pow 2
    have heq : F ^ 2 * (1 - h) = h := sub_eq_zero.mp (hq.mul_left_eq_zero.mp hprod)
    have hu : IsUnit (1 - h) := isUnit_iff_constantCoeff.mpr (by simp [h0])
    exact hu.mul_left_injective (heq.trans hsub.symm)
  · let D : PowerSeries ℤ := 1 - 2 * X + 2 * X ^ 2
    let h : PowerSeries ℤ := X ^ 2 * invOfUnit D 1
    have hD0 : constantCoeff D = 1 := by simp [D]
    have hh : h * D = X ^ 2 := by
      dsimp only [h]
      rw [mul_assoc, invOfUnit_mul D 1 hD0, mul_one]
    have ho : h274479 * (1 - 2 * X - 4 * X ^ 2) = X ^ 2 := by
      rw [h274479, mul_assoc, invOfUnit_mul]
      · simp
      · simp
    have he : red 3 (1 - 2 * X - 4 * X ^ 2) = red 3 D := by
      simp only [red, D, map_sub, map_add, map_mul, map_pow, map_one, map_X, map_ofNat]
      have h4 : (4 : PowerSeries (ZMod 3)) = -2 := by
        simpa only [map_ofNat, map_neg] using
          congrArg (C : ZMod 3 →+* PowerSeries (ZMod 3))
            (show (4 : ZMod 3) = -2 by decide)
      rw [h4]
      ring
    have hr := congrArg (red 3) ho
    have hn := congrArg (red 3) hh
    simp only [red, map_mul, map_pow, map_X] at hr hn
    change red 3 h274479 * red 3 (1 - 2 * X - 4 * X ^ 2) = X ^ 2 at hr
    change red 3 h * red 3 D = X ^ 2 at hn
    rw [he] at hr
    have hu : IsUnit (red 3 D) := by
      apply isUnit_iff_constantCoeff.mpr
      have hc : constantCoeff (red 3 D) = 1 := by simp [red, D]
      rw [hc]
      exact isUnit_one
    exact hu.mul_left_injective (hr.trans hn.symm)

end BackfillPaper2.EntryRemark8
#print axioms BackfillPaper2.EntryRemark8.check_Rem8
