import Research.TaskU.H5.Fourier

namespace TaskU.H5
noncomputable section
open Finset Matrix
open scoped BigOperators

def regular (f : H → ℤ) : Matrix H H ℂ :=
  Matrix.of fun g h => (f (g*h⁻¹) : ℂ)

theorem regular_det (f : H → ℤ) : (regular f).det = (groupDet f : ℂ) := by
  symm
  exact (Int.castRingHom ℂ).map_det _

theorem block_transform (f : H → ℤ) :
    Matrix.of T * regular f = blocks f * Matrix.of T := by
  ext i h : 1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  conv_lhs => rw [← Equiv.sum_comp (Equiv.mulRight h) (fun k => Matrix.of T i k * regular f k h)]
  simp only [Equiv.coe_mulRight, regular, Matrix.of_apply, mul_inv_cancel_right]
  rw [Finset.sum_eq_single_of_mem (⟨h.a,i.b,i.c⟩ : H) (Finset.mem_univ _) (s := Finset.univ)
       (f := fun j => blocks f i j * T j h) (by
         intro k _ hk
         by_cases he : (i.b,i.c)=(k.b,k.c)
         · have hne : h.a ≠ k.a := by
             intro hh
             apply hk
             cases k
             simp_all
           simp [T, hne]
         · simp only [blocks, Matrix.of_apply, ite_eq_right he, zero_mul])]
  simp only [blocks, Matrix.of_apply, T, eq_self, ite_true, frequencyBlock, sum_mul]
  apply Finset.sum_congr rfl
  intro g _
  change (if g.a+h.a=i.a then ch (i.b*(g.b+h.b)+i.c*(g.c+h.c+g.b*h.a)) else 0) *
    (f g : ℂ) = _
  by_cases hp : i.a = g.a + h.a
  · simp only [hp, eq_self, ite_true]
    rw [mul_comm _ (f g : ℂ), mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  · simp [hp, Ne.symm hp]

theorem blocks_det (f : H → ℤ) :
    (blocks f).det = ∏ v : F, ∏ w : F, (frequencyBlock f v w).det := by
  let B := Matrix.blockDiagonal (fun vw : F × F => frequencyBlock f vw.1 vw.2)
  have hb : blocks f = Matrix.reindex coords.symm coords.symm B := by
    ext i j : 1
    simp [blocks, B, Matrix.blockDiagonal, Matrix.reindex_apply, coords]
  rw [hb, Matrix.det_reindex_self, Matrix.det_blockDiagonal, Fintype.prod_prod_type]

theorem det_fourier (f : H → ℤ) :
    (groupDet f : ℂ) = ∏ v : F, ∏ w : F, (frequencyBlock f v w).det := by
  have ht : (Matrix.of T : Matrix H H ℂ).det ≠ 0 := by
    intro h
    have hh := congrArg Matrix.det inverseFourier
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_smul_of_tower, Matrix.det_one, nsmul_eq_mul, mul_one] at hh
    exact (Nat.cast_ne_zero.mpr (pow_ne_zero _ (by decide : (25:ℕ) ≠ 0))) hh.symm
  have he := congrArg Matrix.det (block_transform f)
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm (blocks f).det, regular_det, blocks_det] at he
  exact mul_left_cancel₀ ht he

end
end TaskU.H5
