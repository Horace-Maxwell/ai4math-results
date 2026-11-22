import Research.TaskU.H5.Cyc5
import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.Tactic

namespace TaskU.H5.PrimeBasis
open NumberField IsCyclotomicExtension
open Cyc5
noncomputable section

abbrev K := CyclotomicField 5 ℚ
abbrev O := 𝓞 K
instance cyclo : IsCyclotomicExtension ({5} : Set ℕ) ℚ K := CyclotomicField.isCyclotomicExtension 5 ℚ
def pb : PowerBasis ℤ O := (zeta_spec 5 ℚ K).integralPowerBasis

lemma dim_four : pb.dim = 4 := by
  simp only [pb, IsPrimitiveRoot.integralPowerBasis_dim]
  decide

def ib : Module.Basis (Fin 4) ℤ O := pb.basis.reindex (finCongr dim_four)

lemma ib_pow (i : Fin 4) : ib i = pb.gen ^ i.val := by
  simp [ib]

def toO (v : V) : O := v.a + v.b*pb.gen + v.c*pb.gen^2 + v.d*pb.gen^3

def fromO (x : O) : V :=
  ⟨ib.repr x 0, ib.repr x 1, ib.repr x 2, ib.repr x 3⟩

private def tuple (v : V) : Fin 4 → ℤ := ![v.a,v.b,v.c,v.d]

private lemma repr_toO (v : V) (i : Fin 4) : ib.repr (toO v) i = tuple v i := by
  have hs : ∑ j : Fin 4, tuple v j • ib j = toO v := by
    rw [Fin.sum_univ_four]
    simp [tuple, ib_pow, toO, zsmul_eq_mul]
  rw [← hs]
  exact congrFun (ib.repr_sum_self (tuple v)) i

lemma left_inv : Function.LeftInverse fromO toO := by
  intro v
  ext <;> simp [fromO,repr_toO,tuple]

lemma right_inv : Function.RightInverse fromO toO := by
  intro x
  apply ib.repr.injective
  ext i
  rw [repr_toO]
  fin_cases i <;> rfl

lemma gen_five : pb.gen ^ 5 = 1 := by
  rw [pb, IsPrimitiveRoot.integralPowerBasis_gen]
  apply Subtype.ext
  exact (zeta_spec 5 ℚ K).pow_eq_one

lemma phi : 1 + pb.gen + pb.gen^2+pb.gen^3+pb.gen^4 = 0 := by
  have hn : pb.gen ≠ 1 := by
    intro h
    have hh : IsCyclotomicExtension.zeta 5 ℚ K = 1 := by
      rw [pb, IsPrimitiveRoot.integralPowerBasis_gen] at h
      exact (congrArg (algebraMap O K) h).trans (map_one _)
    exact ((zeta_spec 5 ℚ K).ne_one (by decide)) hh
  have h : (pb.gen-1)*(1+pb.gen+pb.gen^2+pb.gen^3+pb.gen^4)=0 := by
    linear_combination gen_five
  exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hn)

lemma toO_mul (v w : V) : toO (mul v w) = toO v * toO w := by
  simp only [toO,mul,Int.cast_sub,Int.cast_mul,Int.cast_add]
  linear_combination (-(v.b:O)*(w.d:O) - (v.c:O)*(w.c:O) + (v.c:O)*(w.d:O) - (v.d:O)*(w.b:O) + (v.d:O)*(w.c:O) - (v.d:O)*(w.d:O)*pb.gen^2 - pb.gen*((v.c:O)*(w.d:O) + (v.d:O)*(w.c:O) - (v.d:O)*(w.d:O))) * phi

end
end TaskU.H5.PrimeBasis
