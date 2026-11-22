import Research.TaskU.H5.TraceIntegral
import Research.TaskU.H5.Factors
import Research.TaskU.H5.ProfileEval

namespace TaskU.H5.TraceWords
noncomputable section
open Finset

theorem horizontal_value (f : H → ℤ) {s : F} (hs : s ≠ 0) :
    Cyc5.val (ray f 1 0) (ch s) = linearFactor f s 0 := by
  rw [ray, evalProfile _ _ hs, counts_weight]
  simp [linearFactor]

theorem horizontal_norm (f : H → ℤ) :
    ∏ u : F, linearFactor f u 0 = (aug f:ℂ)*Cyc5.norm (ray f 1 0) := by
  rw [← Finset.mul_prod_erase _ _ (mem_univ (0:F)), norm_values]
  have h : linearFactor f 0 0 = (aug f : ℂ) := by simp [linearFactor,aug]
  rw [h]
  congr 1
  exact prod_congr rfl (fun s hs => (horizontal_value f (ne_of_mem_erase hs)).symm)

theorem total_weight (f : H → ℤ) :
    ∑ q : Word, weight f q = aug f * Cyc5.norm (ray f 1 0) := by
  have h := word_expansion f 0 0
  change (frequencyBlock f 0 0).det = _ at h
  rw [abelian_det, horizontal_norm] at h
  simp only [zero_mul, add_zero, AddChar.map_zero_eq_one, mul_one] at h
  exact_mod_cast h.symm

theorem profile_dvd_iff_aug (f : H → ℤ) :
    5 ∣ Cyc5.sumCoeff (nonlinear f) ↔ 5 ∣ aug f := by
  rw [nonlinear, profile_mass, counts_total, total_weight]
  have hv : Cyc5.sumCoeff (ray f 1 0) = aug f - 5*counts f (fun g => 1*g.a+0*g.b) 4 := by
    rw [ray, profile_mass, counts_total]; rfl
  have ray5 : (5:ℤ) ∣ Cyc5.norm (ray f 1 0) ↔ 5 ∣ aug f := by
    rw [Cyc5.five_dvd_norm_iff, hv]
    omega
  have hprime : Prime (5:ℤ) := by norm_num
  constructor
  · intro h
    have hprod : (5:ℤ) ∣ aug f * Cyc5.norm (ray f 1 0) := by omega
    rcases hprime.dvd_mul.mp hprod with hg | hn
    · exact hg
    · exact ray5.mp hn
  · intro hg
    have hprod := dvd_mul_of_dvd_left hg (Cyc5.norm (ray f 1 0))
    omega

theorem average_dvd_iff_aug (f : H → ℤ) : 5 ∣ integerAverage f ↔ 5 ∣ aug f :=
  (average_dvd_iff_profile f).trans (profile_dvd_iff_aug f)

#print axioms average_dvd_iff_aug
#print axioms norm_deep
end
end TaskU.H5.TraceWords
