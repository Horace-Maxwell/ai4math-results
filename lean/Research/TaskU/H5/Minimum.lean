import Research.TaskU.H5.TraceFinal
import Research.TaskU.H5.TraceAugment
import Research.TaskU.H5.Divisibility

namespace TaskU.H5.Proof
noncomputable section

private theorem normalized_layers (f : H → ℤ) (hx : mx f = 0) (hd : 5 ∣ groupDet f) :
    5 ∣ aug f ∧ Nonempty (Layers f) := by
  have ha := aug_necessary f ((Cyc5.five_dvd_norm_iff _).trans (TraceWords.profile_dvd_iff_aug f)) hd
  exact ⟨ha,layers_exist f hx ha (TraceWords.norm_divisibility f ((TraceWords.average_dvd_iff_aug f).mpr ha))⟩

theorem baseline (f : H → ℤ) (hd : 5 ∣ groupDet f) : 5^28 ∣ groupDet f := by
  obtain ⟨g,hg,hx⟩ := normalize f
  rw [← hg] at hd ⊢
  obtain ⟨_,⟨c⟩⟩ := normalized_layers g hx hd
  exact ⟨_,c.value⟩

theorem small (f : H → ℤ) (m : ℤ) (hm : 1 ≤ m) (hm' : m ≤ 10)
    (he : groupDet f = 5^28*m) : 5^33 ∣ groupDet f := by
  obtain ⟨g,hg,hx⟩ := normalize f
  rw [← hg] at he ⊢
  have hd : 5 ∣ groupDet g := ⟨5^27*m, by rw [he]; ring⟩
  obtain ⟨ha,⟨c⟩⟩ := normalized_layers g hx hd
  by_cases hy : my g = 0
  · exact c.deep_zero hx hy
  · exact c.deep_nonlin (TraceFinal.deep_average g hx hy ha (c.small_norm hx hy hm hm' he))

theorem leastPositiveMultiple : Challenge.leastPositiveMultiple :=
  SmallMultiples.least_from_small baseline small

#print axioms leastPositiveMultiple
end
end TaskU.H5.Proof
