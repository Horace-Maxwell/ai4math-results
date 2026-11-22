import Research.TaskU.H5.Fourier
import Mathlib.Algebra.Field.ZMod

namespace TaskU.H5
noncomputable section
open Finset Matrix
open scoped BigOperators

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

def mx (f : H → ℤ) : F := ∑ g : H, (f g : F)*g.a
def my (f : H → ℤ) : F := ∑ g : H, (f g : F)*g.b

private def switchAxes (k : F) : H ≃* H where
  toFun g := ⟨g.b-k*g.a, g.a, -g.c+g.a*g.b-(k * (3:F))*g.a^2⟩
  invFun g := ⟨g.b, g.a+k*g.b, -g.c+g.b*g.a+(k * (3:F))*g.b^2⟩
  left_inv g := by
    cases g with
    | mk a b c =>
      rw [H.mk.injEq]
      refine ⟨rfl, by ring, ?_⟩
      linear_combination (norm := ring) (by decide : (2:F) * 3 = 1) * (k * a^2)
  right_inv g := by
    cases g with
    | mk a b c =>
      rw [H.mk.injEq]
      refine ⟨by ring, rfl, ?_⟩
      linear_combination (norm := ring) - (by decide : (2:F) * 3 = 1) * (k * b^2)
  map_mul' g h := by
    change H.mk _ _ _ = H.mk _ _ _
    rw [H.mk.injEq]
    change (g.b+h.b - k*(g.a+h.a) = (g.b-k*g.a)+(h.b-k*h.a)) ∧ (_ = _) ∧
      (-(g.c+h.c+g.b*h.a)+(g.a+h.a)*(g.b+h.b)-
          k*(3:F)*(g.a+h.a)^2 = _+_+_*_)
    refine ⟨by ring, rfl, ?_⟩
    linear_combination (norm := ring) -(by decide : (2:F) * 3 = 1) * (k * g.a*h.a)

def transport (e : H ≃* H) (f : H → ℤ) (h : H) := f (e.symm h)

theorem transport_det (e : H ≃* H) (f : H → ℤ) :
    groupDet (transport e f) = groupDet f := by
  unfold groupDet
  let A : Matrix H H ℤ := Matrix.of fun g h => f (g * h⁻¹)
  have he : Matrix.of (fun g h : H => transport e f (g*h⁻¹)) =
      Matrix.reindex e.toEquiv e.toEquiv A := by
    ext g h : 1
    simp [transport, A, Matrix.reindex_apply]
  rw [he, Matrix.det_reindex_self]

theorem normalize (f : H → ℤ) : ∃ f' : H → ℤ, groupDet f' = groupDet f ∧ mx f' = 0 := by
  by_cases hz : mx f = 0
  · exact ⟨f,rfl,hz⟩
  let k := my f / mx f
  let e := switchAxes k
  refine ⟨transport e f, transport_det e f, ?_⟩
  unfold mx
  rw [← Equiv.sum_comp e.toEquiv (fun g => (transport e f g : F)*g.a)]
  change (∑ g : H, (f (e.symm (e g)) : F) * (e g).a) = 0
  simp only [MulEquiv.symm_apply_apply]
  change (∑ g : H, (f g : F)*(g.b-k*g.a))=0
  simp_rw [mul_sub, mul_left_comm (f _ : F) k]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  change my f - (my f / mx f)*mx f = 0
  field_simp
  ring

end
end TaskU.H5
