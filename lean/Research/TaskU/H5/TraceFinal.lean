import Research.TaskU.H5.TraceLower
import Research.TaskU.H5.Divisibility

namespace TaskU.H5.TraceFinal
noncomputable section
open Finset

theorem deep_average (f : H → ℤ) (hx : mx f = 0) (hy : my f ≠ 0)
    (ha : 5 ∣ aug f) (hN : ∀ j, Cyc5.norm (ray f j 1) = 5) :
    25 ∣ TraceWords.integerAverage f := by
  obtain ⟨a,ha'⟩ := ha
  obtain ⟨b,hb⟩ := exceptional_norm f hx ⟨a,ha'⟩
  have ht := ordinary_trace_zero f hx hy ⟨a,ha'⟩ hN
  have h := TraceWords.average_eq f
  change (∑ v : F, (frequencyBlock f v 0).det) = _ at h
  simp_rw [abelian_det] at h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0:F)), ht, add_zero, horizontal] at h
  have hℤ : aug f * Cyc5.norm (ray f 1 0) = 5 * TraceWords.integerAverage f := by
    exact_mod_cast h
  refine ⟨a*b, ?_⟩
  rw [ha',hb] at hℤ
  nlinarith only [hℤ]

end
end TaskU.H5.TraceFinal
