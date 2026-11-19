import Research.TaskJ.Rank.Challenge

namespace TaskJ.Rank.Parameters

open Challenge

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem twoAction : ActionLaws twoSwap := by
  unfold ActionLaws
  decide +kernel

theorem fiveAction : ActionLaws fiveSwap := by
  unfold ActionLaws
  decide +kernel

/-- Commuting with the generator is precisely equivariance on both elements. -/
theorem equivariance {n : ℕ} (t : Equiv.Perm (Fin n)) : EquivarianceMeaning t := by
  intro p
  rw [equivariantGroup, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro comm g x
    by_cases hg : g = 0
    · simp [act, hg]
    · simpa [act, hg, Equiv.Perm.mul_apply] using
        congrArg (fun q : Equiv.Perm (Fin n) => q x) comm
  · intro h
    apply Equiv.ext
    intro x
    simpa [act, Equiv.Perm.mul_apply] using h 1 x

theorem twoBases : BasesValid twoSwap := by
  unfold BasesValid
  decide +kernel

theorem fiveBases : BasesValid fiveSwap := by
  unfold BasesValid
  decide +kernel

theorem two : TwoPointParameters := by
  unfold TwoPointParameters
  decide +kernel

theorem five : FivePointParameters := by
  unfold FivePointParameters
  decide +kernel

end TaskJ.Rank.Parameters
