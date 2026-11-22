import Research.TaskU.H5B.UnitResidues
import Research.TaskU.H5B.BTrace
import Research.TaskU.H5.Divisibility
import Research.TaskU.H5.TraceFinal

namespace TaskU.H5.Spectrum
noncomputable section
open Finset
open Cyc5 (V)
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem moments_eq {x y : V} (h : red x = red y) :
    Cyc5.first x = Cyc5.first y ∧ Cyc5.second x = Cyc5.second y := by
  simp only [red,Prod.mk.injEq] at h
  simp [Cyc5.first,Cyc5.second,h.2.1,h.2.2.1,h.2.2.2]

private theorem replacements (f : H → ℤ) (c : Layers f) (hu : ∀j, ChallengeB.unitImage (c.q j)) :
    ∃ u : F → V, (∀j, Cyc5.norm (u j) = 1) ∧
      (∀j, red (Cyc5.mul Cyc5.pi (u j)) = red (ray f j 1)) ∧
      (∀j, ∃ a : V, c.q j = u j + 5*a) := by
  choose u v h1 h2 using hu
  refine ⟨u,fun j => norm_of_unit (h1 j),?_,fun j => red_difference (h2 j)⟩
  intro j
  rw [c.ordinary j, red_mul,red_mul,(red_congr.mp (h2 j))]

theorem deep_of_images (f : H → ℤ) (hx : mx f = 0) (hy : my f ≠ 0)
    (ha : 5 ∣ aug f) (c : Layers f) (hu : ∀j,ChallengeB.unitImage (c.q j)) :
    25 ∣ TraceWords.integerAverage f := by
  obtain ⟨u,hn,hr,he⟩ := replacements f c hu
  let y (j : F) := Cyc5.mul Cyc5.pi (u j)
  choose k hk using fun j => Cyc5.ordinary_phase (y j) (u j) rfl (hn j)
  have hs : ∑ j, k j = 0 := by
    apply Phase.sum_phase f (-my f)
    intro j
    have hm := Cyc5.phase_moment _ _ ((Cyc5.pi_dvd_iff (y j)).mp ⟨u j,rfl⟩) (hk j)
    obtain ⟨h1,h2⟩ := moments_eq (hr j)
    change Cyc5.first (y j) = _ at h1
    change Cyc5.second (y j) = _ at h2
    rw [h1,h2,ray_first _ _ hx,ray_second] at hm
    field_simp
    linear_combination -hm
  have hz := BTrace.exact_trace_zero y k hs hk
  have hd := BTrace.trace_replacement (c.q) u he
  have hg (j : F) : Cyc5.pi * c.q j = ray f j 1 := (c.ordinary j).symm
  simp only [hg] at hd
  change (125:ℤ) ∣ BTrace.tr (∏j,ray f j 1)-BTrace.tr (∏j,y j) at hd
  rw [hz,sub_zero] at hd
  obtain ⟨z,hz⟩ := hd
  have hh := TraceWords.average_eq f
  change (∑ v : F, (frequencyBlock f v 0).det) = _ at hh
  simp_rw [abelian_det] at hh
  rw [←Finset.add_sum_erase _ _ (mem_univ (0:F)),horizontal,BTrace.trace_row,hz] at hh
  have hh' : aug f * Cyc5.norm (ray f 1 0) + 125*z = 5 * TraceWords.integerAverage f := by exact_mod_cast hh
  obtain ⟨a,ha⟩ := ha
  obtain ⟨b,hb⟩ := exceptional_norm f hx ⟨a,ha⟩
  exact ⟨a*b+z,by rw [ha,hb] at hh'; nlinarith only [hh']⟩

end
end TaskU.H5.Spectrum
