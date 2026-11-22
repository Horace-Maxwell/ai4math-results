import Research.TaskU.H5.RayCancellation

namespace TaskU.H5
noncomputable section
open Finset

theorem ordinary_trace_zero (f : H → ℤ) (hx : mx f = 0) (hy : my f ≠ 0)
    (ha : 5 ∣ aug f) (hN : ∀ j, Cyc5.norm (ray f j 1) = 5) :
    (∑ v ∈ (univ : Finset F).erase 0, ∏ u : F, linearFactor f u v) = 0 := by
  have units (j : F) : ∃ u, ray f j 1 = Cyc5.mul Cyc5.pi u ∧ Cyc5.norm u = 1 := by
    obtain ⟨u,hu⟩ := ray_pi ha j 1
    refine ⟨u, hu, ?_⟩
    have h := hN j
    rw [hu, Cyc5.norm_mul, Cyc5.norm_pi] at h
    omega
  have h := cancel_nonzero_rows f hx hy units
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0:F))] at h
  simp only [ite_true, zero_add] at h
  calc
    _ = ∑ v ∈ (univ : Finset F).erase 0, (if v=0 then 0 else ∏ u : F, linearFactor f u v) := by
      apply sum_congr rfl
      intro v hv
      simp [ne_of_mem_erase hv]
    _ = 0 := h

end
end TaskU.H5
