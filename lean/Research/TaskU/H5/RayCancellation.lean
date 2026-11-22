import Research.TaskU.H5.RayMoments
import Research.TaskU.H5.IntegerFactors
import Research.TaskU.H5.CycRoots

namespace TaskU.H5
noncomputable section
open Finset
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem cancel_nonzero_rows (f : H → ℤ) (hx : mx f = 0) (hy : my f ≠ 0)
    (units : ∀ j, ∃ u, ray f j 1 = Cyc5.mul Cyc5.pi u ∧ Cyc5.norm u = 1) :
    (∑ r : F, if r=0 then 0 else ∏ j : F, linearFactor f j r) = 0 := by
  obtain ⟨k,hs,hk⟩ := phases_vanish f hx hy units
  apply Phase.row_trace _ k hs
  intro j r hr
  have h := Cyc5.phase_character _ _ (hk j) r hr
  simpa only [val_ray f j 1 _ hr, val_ray f j 1 _ (neg_ne_zero.mpr hr), mul_one,
    mul_comm (k j) r] using h

end
end TaskU.H5
