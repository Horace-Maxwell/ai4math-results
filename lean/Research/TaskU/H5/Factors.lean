import Research.TaskU.H5.Blocks
import Mathlib.Algebra.Field.ZMod

namespace TaskU.H5
noncomputable section
open Finset Matrix
open scoped BigOperators

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def linearFactor (f : H → ℤ) (u v : F) : ℂ :=
  ∑ g : H, (f g : ℂ) * ch (u*g.a+v*g.b)

theorem shift_det (f : H → ℤ) (v w : F) (hw : w ≠ 0) :
    (frequencyBlock f v w).det = (frequencyBlock f 0 w).det := by
  let e := Equiv.addRight (v / w)
  have hb : frequencyBlock f v w = Matrix.reindex e.symm e.symm (frequencyBlock f 0 w) := by
    ext i j : 1
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm,
      e, Equiv.coe_addRight, frequencyBlock, Matrix.of_apply, zero_mul, zero_add]
    apply sum_congr rfl
    intro g _
    have he : w*(g.c+g.b*(j+v/w)) = v*g.b+w*(g.c+g.b*j) := by
      field_simp
      ring
    simp [he, ← add_assoc]
  rw [hb, Matrix.det_reindex_self]

private def W : Matrix F F ℂ := Matrix.of fun u j => ch (u*j)
private def V : Matrix F F ℂ := Matrix.of fun i u => ch (-(u*i))

private theorem Wdet : W.det ≠ 0 := by
  have hi : V*W = 5 • (1 : Matrix F F ℂ) := by
    ext i j : 1
    simp only [V, W, Matrix.mul_apply, Matrix.of_apply, ← AddChar.map_add_eq_mul,
      Matrix.smul_apply, nsmul_eq_mul, Matrix.one_apply]
    have he (u : F) : -(u*i)+u*j=(j-i)*u := by ring
    simp only [he, orthog, sub_eq_zero]
    by_cases h : i=j <;> simp [h, Ne.symm]
  intro h
  have hh := congrArg Matrix.det hi
  rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul_of_tower, Matrix.det_one, nsmul_eq_mul, mul_one] at hh
  exact (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide : (5:ℕ) ≠ 0))) hh.symm

theorem abelian_det (f : H → ℤ) (v : F) :
    (frequencyBlock f v 0).det = ∏ u : F, linearFactor f u v := by
  let diag := Matrix.diagonal (fun u => linearFactor f u v)
  have he : W * frequencyBlock f v 0 = diag * W := by
    ext u j : 1
    rw [Matrix.mul_apply, Matrix.diagonal_mul]
    simp only [W, frequencyBlock, Matrix.of_apply, zero_mul, add_zero,
      linearFactor, mul_sum, sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro g _
    simp only [mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
    rw [mul_left_comm, mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  have hd := congrArg Matrix.det he
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm diag.det, Matrix.det_diagonal] at hd
  exact mul_left_cancel₀ Wdet hd

theorem factorization (f : H → ℤ) :
    (groupDet f : ℂ) = (∏ v : F, ∏ u : F, linearFactor f u v) *
      (∏ w ∈ (Finset.univ : Finset F).erase 0, (frequencyBlock f 0 w).det)^5 := by
  rw [det_fourier]
  have hv (v : F) : ∏ w : F, (frequencyBlock f v w).det =
      (∏ u : F, linearFactor f u v) *
      ∏ w ∈ (Finset.univ : Finset F).erase 0, (frequencyBlock f 0 w).det := by
    calc
      _ = (frequencyBlock f v 0).det * ∏ w ∈ (Finset.univ : Finset F).erase 0,
          (frequencyBlock f v w).det :=
        (Finset.mul_prod_erase _ (fun w => (frequencyBlock f v w).det) (Finset.mem_univ (0:F))).symm
      _ = _ := ?_
    apply congrArg₂ (· * ·) (abelian_det f v)
    exact Finset.prod_congr rfl (fun w hw => shift_det f v w (Finset.ne_of_mem_erase hw))
  simp only [hv, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ZMod.card]

end
end TaskU.H5
