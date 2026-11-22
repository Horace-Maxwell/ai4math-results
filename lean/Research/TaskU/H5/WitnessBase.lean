import Research.TaskU.H5.Challenge
import Research.TaskU.H5.WitnessRows
import Mathlib.LinearAlgebra.Matrix.Block
import Lean.Elab.Tactic.Omega

namespace TaskU.H5.WitnessCertificate

/-- Simultaneous lexicographic reordering of the rows and columns. -/
def encode (h : H) : Fin 125 :=
  ⟨25 * h.a.val + 5 * h.b.val + h.c.val, by
    have ha := ZMod.val_lt h.a
    have hb := ZMod.val_lt h.b
    have hc := ZMod.val_lt h.c
    omega⟩

def decode (i : Fin 125) : H :=
  ⟨(i.val / 25 : ℕ), (i.val / 5 : ℕ), (i.val : ℕ)⟩

def orderEquiv : H ≃ Fin 125 where
  toFun := encode
  invFun := decode
  left_inv := by
    change ∀ h : H, decode (encode h) = h
    decide +kernel
  right_inv := by
    change ∀ i : Fin 125, encode (decode i) = i
    decide +kernel

abbrev Square := Matrix (Fin 125) (Fin 125) ℤ

def left : Square := Matrix.of fun i j =>
  if i.val < j.val then 0 else
    (((packedRows.getD i.val 0 >>> (18 * j.val)) % 262144 : ℕ) : ℤ) - 131072

def target (g : H) (j : Fin 125) : Fin 125 := encode (g * decode j)

def transformed : Square := Matrix.of fun i j =>
  left i j + left i (target x j) + left i (target y j) +
  left i (target (y ^ 2) j) + left i (target (x * y ^ 2) j)

def regular : Square :=
  (Matrix.of fun g h : H => witness (g * h⁻¹)).submatrix orderEquiv.symm orderEquiv.symm

private theorem coeff_test (i j : Fin 125) (g : H) :
    decode i * (decode j)⁻¹ = g ↔ i = target g j := by
  rw [mul_inv_eq_iff_eq_mul]
  change orderEquiv.symm i = g * decode j ↔ i = orderEquiv (g * decode j)
  exact orderEquiv.symm_apply_eq

private theorem target_one (j : Fin 125) : target 1 j = j := by
  change encode (1 * decode j) = j
  rw [one_mul]
  exact orderEquiv.apply_symm_apply j

theorem transformed_eq : left * regular = transformed := by
  ext i j
  rw [Matrix.mul_apply]
  change ∑ k : Fin 125, left i k * witness (decode k * (decode j)⁻¹) = _
  simp only [witness, coeff_test, target_one, mul_add, mul_ite, mul_one, mul_zero,
    Finset.sum_add_distrib, transformed, Matrix.of_apply]
  simp

theorem left_lower : left.IsLowerTriangular := by
  intro i j h
  change i.val < j.val at h
  exact ite_eq_left h

theorem regular_det : regular.det = groupDet witness := by
  exact Matrix.det_submatrix_equiv_self orderEquiv.symm _

end TaskU.H5.WitnessCertificate
