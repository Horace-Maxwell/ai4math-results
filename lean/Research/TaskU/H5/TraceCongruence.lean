import Research.TaskU.H5.TraceOrbit

namespace TaskU.H5.TraceWords
noncomputable section
open Finset

theorem sum_by_phase (f : H → ℤ) (k : K → ℂ) :
    ∑ e : K, (binWeight f e : ℂ) * k e =
      ∑ q : Word, if mass q=0 then (weight f q:ℂ)*k (phase q) else 0 := by
  classical
  simp only [binWeight, Int.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro q _
  by_cases hb : mass q=0
  · simp [hb, ite_mul]
  · simp [hb]

theorem nonlinear_congruence (f : H → ℤ) :
    (wordMatrix f 0 1).det - (integerAverage f : ℂ) =
      5*∑ e : K, (anchoredWeight f e : ℂ)*(χ e-1) := by
  classical
  rw [projected_expansion, ← sum_by_phase]
  have avg := sum_by_phase f (fun _ => (1:ℂ))
  have avg' : ∑ e : K, (binWeight f e:ℂ) = (integerAverage f:ℂ) := by
    simpa [integerAverage] using avg
  rw [← avg', ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply sum_congr rfl
  intro e _
  by_cases h : e=0
  · simp [h]
  · rw [binWeight_eq_five f h]
    push_cast
    ring

#print axioms nonlinear_congruence
#print axioms average_eq
end
end TaskU.H5.TraceWords
