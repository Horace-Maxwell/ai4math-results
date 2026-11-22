import Research.TaskU.H5.Factors
import Research.TaskU.H5.ProfileEval
import Research.TaskU.H5.TraceProfile

namespace TaskU.H5
noncomputable section
open Finset Matrix
open scoped BigOperators
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem val_ray (f : H → ℤ) (u v r : F) (hr : r ≠ 0) :
    Cyc5.val (ray f u v) (ch r) = linearFactor f (r*u) (r*v) := by
  rw [ray, evalProfile _ _ hr, counts_weight]
  unfold linearFactor
  apply sum_congr rfl
  intro g _
  congr 2
  ring

theorem val_nonlinear (f : H → ℤ) (r : F) (hr : r ≠ 0) :
    Cyc5.val (TraceWords.nonlinear f) (ch r) = (frequencyBlock f 0 r).det := by
  change Cyc5.val (profile (counts (TraceWords.weight f) TraceWords.phase)) (ch r) =
    (TraceWords.wordMatrix f 0 r).det
  rw [evalProfile _ _ hr, counts_weight, TraceWords.word_expansion]
  simp

theorem horizontal (f : H → ℤ) :
    ∏ u : F, linearFactor f u 0 = ((aug f * Cyc5.norm (ray f 1 0) : ℤ):ℂ) := by
  rw [Int.cast_mul, norm_values]
  rw [← Finset.mul_prod_erase _ (fun u : F => linearFactor f u 0) (Finset.mem_univ (0:F))]
  apply congrArg₂ (· * ·)
  · simp [linearFactor, aug]
  · apply Finset.prod_congr rfl
    intro u hu
    simpa using (val_ray f 1 0 u (Finset.ne_of_mem_erase hu)).symm

theorem abelianProduct (f : H → ℤ) :
    (∏ v : F, ∏ u : F, linearFactor f u v) =
      ((aug f * Cyc5.norm (ray f 1 0) * ∏ j : F, Cyc5.norm (ray f j 1) : ℤ):ℂ) := by
  rw [Int.cast_mul, Int.cast_prod,
    ← Finset.mul_prod_erase _ (fun v : F => ∏ u : F, linearFactor f u v) (Finset.mem_univ (0:F)),
    horizontal]
  apply congrArg (fun x : ℂ => ((aug f * Cyc5.norm (ray f 1 0) : ℤ):ℂ) * x)
  simp_rw [norm_values]
  rw [Finset.prod_comm (s := (Finset.univ : Finset F))]
  apply Finset.prod_congr rfl
  intro v hv
  have h := Finset.ne_of_mem_erase hv
  calc
    _ = ∏ j : F, linearFactor f (v*j) v :=
      (Equiv.prod_comp (Equiv.mulLeft₀ v h) (fun t => linearFactor f t v)).symm
    _ = _ := Finset.prod_congr rfl (fun j _ => by simpa using (val_ray f j 1 v h).symm)

theorem integerFactorization (f : H → ℤ) :
    groupDet f = aug f * Cyc5.norm (ray f 1 0) * (∏ j : F, Cyc5.norm (ray f j 1)) *
      Cyc5.norm (TraceWords.nonlinear f)^5 := by
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_mul, Int.cast_pow, ← abelianProduct, factorization, norm_values]
  apply congrArg (fun x : ℂ => (∏ v : F, ∏ u : F, linearFactor f u v) * x^5)
  apply Finset.prod_congr rfl
  exact fun r hr => (val_nonlinear f r (Finset.ne_of_mem_erase hr)).symm

end
end TaskU.H5
