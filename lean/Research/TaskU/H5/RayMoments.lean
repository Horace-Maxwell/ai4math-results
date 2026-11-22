import Research.TaskU.H5.CycMoments
import Research.TaskU.H5.Profile
import Research.TaskU.H5.Normalize
import Research.TaskU.H5.Phase

namespace TaskU.H5
noncomputable section
open Finset
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem ray_first (f : H → ℤ) (j : F) (hx : mx f = 0) :
    Cyc5.first (ray f j 1) = -my f := by
  have same (v : Cyc5.V) : Cyc5.first v = -slope v := by simp [Cyc5.first, slope]
  rw [same, ray_slope]
  change -(j * mx f + 1 * my f) = -my f
  simp [hx]

theorem profile_second (p : F → ℤ) :
    Cyc5.second (profile p) = ∑ j, (p j : F) * (j*(j-1)/2) := by
  rw [sum_five]
  have coeff : ∀ j : F, j*(j-1)/2 =
      (if j=2 then 1 else if j=3 then 3 else if j=4 then 1 else 0) := by decide +kernel
  simp only [coeff]
  simp +decide [Cyc5.second, profile]
  linear_combination (norm := ring) -(p 4 : F) * (by decide : (5:F)=0)

theorem ray_second (f : H → ℤ) (j : F) :
    Cyc5.second (ray f j 1) = Phase.moment f j := by
  rw [ray, profile_second, counts_weight]
  simp only [Phase.moment, one_mul, mul_comm j]

theorem phases_vanish (f : H → ℤ) (hx : mx f = 0) (hy : my f ≠ 0)
    (units : ∀ j, ∃ u, ray f j 1 = Cyc5.mul Cyc5.pi u ∧ Cyc5.norm u = 1) :
    ∃ k : F → F, (∑ j, k j) = 0 ∧
      ∀ j, Cyc5.conj (ray f j 1) = Cyc5.neg (Cyc5.mul (Cyc5.rootAt (k j)) (ray f j 1)) := by
  choose u hu hn using units
  choose k hk using fun j => Cyc5.ordinary_phase (ray f j 1) (u j) (hu j) (hn j)
  refine ⟨k, Phase.sum_phase f (-my f) k ?_, hk⟩
  intro j
  have hm := Cyc5.phase_moment _ _ ((Cyc5.pi_dvd_iff _).mp ⟨u j,hu j⟩) (hk j)
  rw [ray_first f j hx, ray_second] at hm
  field_simp
  linear_combination -hm

end
end TaskU.H5
