import Research.Backfill.Paper7.ChallengeV3

set_option autoImplicit false

noncomputable section

namespace Paper7Reduced

open Finset

def sumCoordinates (K : Type*) [Field K] (ι : Type*) [Fintype ι] :
    (ι → K) →ₗ[K] K where
  toFun v := ∑ i, v i
  map_add' u v := Finset.sum_add_distrib
  map_smul' c v := by simp [Finset.mul_sum]

#print axioms Paper7Reduced.sumCoordinates

theorem sumCoordinates_surjective (K : Type*) [Field K]
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    Function.Surjective (sumCoordinates K ι) := by
  classical
  intro c
  let i : ι := Classical.arbitrary ι
  refine ⟨Pi.single i c, ?_⟩
  exact Fintype.sum_pi_single' i c

#print axioms Paper7Reduced.sumCoordinates_surjective

theorem finrank_ker_sumCoordinates (K : Type*) [Field K]
    (ι : Type*) [Fintype ι] :
    Module.finrank K (LinearMap.ker (sumCoordinates K ι)) = Fintype.card ι - 1 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hempty =>
    let : IsEmpty ι := hempty
    have hle := (LinearMap.ker (sumCoordinates K ι)).finrank_le
    have hzero : Module.finrank K (LinearMap.ker (sumCoordinates K ι)) ≤ 0 := by
      simpa using hle
    simpa using Nat.eq_zero_of_le_zero hzero
  | inr hnonempty =>
    let : Nonempty ι := hnonempty
    have hdim := (sumCoordinates K ι).finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr (sumCoordinates_surjective K ι),
      finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at hdim
    omega

#print axioms Paper7Reduced.finrank_ker_sumCoordinates

theorem finrank_zeroSumBundles (K : Type*) [Field K]
    (κ : Type*) [Fintype κ] (ι : κ → Type*) [∀ k, Fintype (ι k)] :
    Module.finrank K (∀ k, LinearMap.ker (sumCoordinates K (ι k))) =
      ∑ k, (Fintype.card (ι k) - 1) := by
  rw [Module.finrank_pi_fintype]
  exact Finset.sum_congr rfl (fun k _ => finrank_ker_sumCoordinates K (ι k))

#print axioms Paper7Reduced.finrank_zeroSumBundles

end Paper7Reduced
