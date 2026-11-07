import Research.Backfill.Paper2.Challenge
import Research.Backfill.Paper2.EntryA388734

/-! Complete integer reversion and mod-two identities from the remark after Theorem 6. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.EntryRemark6
open PowerSeries BackfillPaper2.Challenge

private theorem phi_zero : constantCoeff phi388734 = 0 := by simp [phi388734]

private theorem phi_one : coeff 1 phi388734 = 1 := by
  rw [phi388734, mul_assoc]
  change coeff (0 + 1) (X * _) = 1
  rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  simp

private theorem B_mul : B388734 * (1 - X - X ^ 2) = 1 - X ^ 3 := by
  rw [B388734, mul_assoc, invOfUnit_mul]
  · simp
  · simp

private theorem phi_mul_B : phi388734 * B388734 = X := by
  have hn : (1 - X - X ^ 2 : PowerSeries ℤ) * invOfUnit (1 - X - X ^ 2) 1 = 1 :=
    mul_invOfUnit _ _ (by simp)
  have hd : (1 - X ^ 3 : PowerSeries ℤ) * invOfUnit (1 - X ^ 3) 1 = 1 :=
    mul_invOfUnit _ _ (by simp)
  calc
    phi388734 * B388734 = X * ((1 - X - X ^ 2) * invOfUnit (1 - X - X ^ 2) 1) *
        ((1 - X ^ 3) * invOfUnit (1 - X ^ 3) 1) := by dsimp [phi388734, B388734]; ring
    _ = X := by rw [hn, hd]; ring

private theorem B_equation :
    B388734 = 1 + phi388734 * B388734 ^ 2 +
      phi388734 ^ 2 * (1 - phi388734) * B388734 ^ 3 := by
  symm
  calc
    _ = 1 + (phi388734 * B388734) * B388734 +
        (phi388734 * B388734) ^ 2 * B388734 - (phi388734 * B388734) ^ 3 := by ring
    _ = 1 + X * B388734 + X ^ 2 * B388734 - X ^ 3 := by rw [phi_mul_B]
    _ = B388734 := by linear_combination -B_mul

private theorem unique (Y Z : PowerSeries ℤ)
    (hY : Y = 1 + phi388734 * Y ^ 2 + phi388734 ^ 2 * (1 - phi388734) * Y ^ 3)
    (hZ : Z = 1 + phi388734 * Z ^ 2 + phi388734 ^ 2 * (1 - phi388734) * Z ^ 3) : Y = Z := by
  let Q := Y + Z + phi388734 * (1 - phi388734) * (Y ^ 2 + Y * Z + Z ^ 2)
  have hu : IsUnit (1 - phi388734 * Q) := isUnit_iff_constantCoeff.mpr (by simp [phi_zero])
  have hz : (1 - phi388734 * Q) * (Y - Z) = 0 := by
    dsimp only [Q]
    linear_combination hY - hZ
  exact sub_eq_zero.mp (hu.mul_right_eq_zero.mp hz)

private theorem subst_equation (A : PowerSeries ℤ) (hA : Eq388734 A) :
    A.subst phi388734 = 1 + phi388734 * (A.subst phi388734) ^ 2 +
      phi388734 ^ 2 * (1 - phi388734) * (A.subst phi388734) ^ 3 := by
  have hs := HasSubst.of_constantCoeff_zero' phi_zero
  have ho : (1 : PowerSeries ℤ).subst phi388734 = 1 := by
    rw [← coe_substAlgHom hs, map_one]
  have h := congrArg (fun F : PowerSeries ℤ => F.subst phi388734) hA
  simpa only [subst_add hs, subst_mul hs, subst_pow hs, subst_sub hs, subst_X hs, ho] using h

private theorem reduced_phi : red 2 phi388734 =
    (X * invOfUnit (1 + X) 1 : PowerSeries (ZMod 2)) := by
  let N : PowerSeries ℤ := 1 - X - X ^ 2
  let D : PowerSeries ℤ := 1 - X ^ 3
  have hp : phi388734 * D = X * N := by
    dsimp only [phi388734, D, N]
    rw [mul_assoc, invOfUnit_mul]
    · simp
    · simp
  have two_zero : (2 : PowerSeries (ZMod 2)) = 0 := EntryA388734.two_eq_zero
  have hrel : red 2 D = red 2 N * (1 + X) := by
    simp only [red, N, D, map_sub, map_pow, map_one, map_X]
    linear_combination (X ^ 2) * two_zero
  have hm : red 2 phi388734 * red 2 D = X * red 2 N := by
    simpa only [red, map_mul, map_X] using congrArg (PowerSeries.map (Int.castRingHom (ZMod 2))) hp
  have hnU : IsUnit (red 2 N) := isUnit_iff_constantCoeff.mpr (by simp [red, N])
  have hf : red 2 phi388734 * (1 + X) = X := by
    apply hnU.mul_left_injective
    change (red 2 phi388734 * (1 + X)) * red 2 N = X * red 2 N
    rw [mul_assoc, mul_comm (1 + X) (red 2 N), ← hrel]
    exact hm
  have hg : (X * invOfUnit (1 + X) 1 : PowerSeries (ZMod 2)) * (1 + X) = X := by
    rw [mul_assoc, invOfUnit_mul]
    · simp
    · simp
  have hu : IsUnit (1 + X : PowerSeries (ZMod 2)) := isUnit_iff_constantCoeff.mpr (by simp)
  exact hu.mul_left_injective (hf.trans hg.symm)

private theorem reduced_A (A : PowerSeries ℤ) (hA : Eq388734 A) :
    red 2 A = invOfUnit (1 - X) 1 := by
  have hr : red 2 A = EntryA388734.U := by
    apply EntryA388734.residue
    have h := congrArg (red 2) hA
    simpa only [red, map_add, map_mul, map_pow, map_sub, map_one, map_X] using h
  rw [hr]
  have hu : IsUnit (1 - X : PowerSeries (ZMod 2)) := isUnit_iff_constantCoeff.mpr (by simp)
  apply hu.mul_left_injective
  change EntryA388734.U * (1 - X) = invOfUnit (1 - X) 1 * (1 - X)
  rw [EntryA388734.U_mul, invOfUnit_mul _ _ (by simp)]

theorem check_Rem6 : Rem6 := by
  refine ⟨⟨B_equation, phi_mul_B⟩, unique, ?_, ?_, reduced_phi, ?_, reduced_A⟩
  · intro A hA
    exact unique _ _ (subst_equation A hA) B_equation
  · intro A hA
    have hsP := HasSubst.of_constantCoeff_zero' phi_zero
    have hAB : A.subst phi388734 = B388734 := unique _ _ (subst_equation A hA) B_equation
    have hr : (X * A).subst phi388734 = X := by
      rw [subst_mul hsP, subst_X hsP, hAB, phi_mul_B]
    have h0 : constantCoeff (X * A) = 0 := by simp
    have hc0 : constantCoeff A = 1 := by
      have h := congrArg constantCoeff hA
      simpa [Eq388734] using h
    have h1 : coeff 1 (X * A) = 1 := by
      change coeff (0 + 1) (X * A) = 1
      rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, hc0]
    exact ⟨hr, subst_eq_X_of_subst_eq_X (X * A) h0 (by rw [h1]; exact isUnit_one) hsP hr⟩
  · let E : PowerSeries (ZMod 2) := X * invOfUnit (1 - X) 1
    have eqpm : (1 + X : PowerSeries (ZMod 2)) = 1 - X := by
      linear_combination X * EntryA388734.two_eq_zero
    have he0 : constantCoeff E = 0 := by simp [E]
    have hs := HasSubst.of_constantCoeff_zero' he0
    have he : E * (1 - X) = X := by
      dsimp only [E]
      rw [mul_assoc, invOfUnit_mul]
      · simp
      · simp
    have hh := congrArg (fun F : PowerSeries (ZMod 2) => F.subst E) he
    have ho : (1 : PowerSeries (ZMod 2)).subst E = 1 := by rw [← coe_substAlgHom hs, map_one]
    simp only [subst_mul hs, subst_sub hs, subst_X hs, ho] at hh
    have hEE : E.subst E = X := by
      linear_combination (1 - X) * hh + (E.subst E + 1) * he +
        (E.subst E * X) * EntryA388734.two_eq_zero
    change (X * invOfUnit (1 + X) 1 : PowerSeries (ZMod 2)).subst E = X ∧
      E.subst (X * invOfUnit (1 + X) 1) = X
    rw [eqpm]
    exact ⟨hEE, hEE⟩

end BackfillPaper2.EntryRemark6
#print axioms BackfillPaper2.EntryRemark6.check_Rem6
