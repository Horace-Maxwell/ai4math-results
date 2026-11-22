import Research.TaskU.H5B.UnitResidues
import Research.TaskU.H5B.PrimeExtract
import Research.TaskU.H5B.BTraceImage
import Research.TaskU.H5.TraceAugment

namespace TaskU.H5.Spectrum
open Finset

theorem divisible_necessary (f : H → ℤ) (hd : (5:ℤ) ∣ groupDet f) :
    (5^33 : ℤ) ∣ groupDet f ∨ ∃ n : ℤ, n≠0 ∧ groupDet f=5^28*n ∧
      ∃ q : ℕ, ChallengeB.visible q ∧ (q:ℤ) ∣ n := by
  classical
  obtain ⟨g,hg,hx⟩ := normalize f
  rw [← hg] at hd ⊢
  have ha := aug_necessary g ((Cyc5.five_dvd_norm_iff _).trans (TraceWords.profile_dvd_iff_aug g)) hd
  obtain ⟨c⟩ := layers_exist g hx ha (TraceWords.norm_divisibility g ((TraceWords.average_dvd_iff_aug g).mpr ha))
  by_cases hy : my g = 0
  · exact Or.inl (c.deep_zero hx hy)
  by_cases hall : ∀ j, ChallengeB.unitImage (c.q j)
  · exact Or.inl (c.deep_nonlin (deep_of_images g hx hy ha c hall))
  push Not at hall
  obtain ⟨j,hj⟩ := hall
  have hz : ¬ (5:ℤ) ∣ Cyc5.norm (c.q j) := by
    intro he
    obtain ⟨w,hw⟩ := (Cyc5.pi_dvd_iff _).mpr ((Cyc5.five_dvd_norm_iff _).mp he)
    have hs := (two_pi (c.ordinary j)).mp ⟨w,hw⟩
    rw [ray_slope] at hs
    change j * mx g + 1 * my g = 0 at hs
    exact hy (by simpa [hx] using hs)
  obtain ⟨q,hq,hqd⟩ := PrimeExtract.visible_dvd_of_not_unitImage (c.q j) hz hj
  let n := c.a*c.e*(∏ t, Cyc5.norm (c.q t))*c.d^5
  by_cases hn : n=0
  · left
    rw [show groupDet g=5^28*n from c.value,hn,mul_zero]; exact dvd_zero _
  · exact Or.inr ⟨n,hn,c.value,q,hq,hqd.trans (SmallMultiples.each_dvd _ _ _ _ _ rfl j)⟩

end TaskU.H5.Spectrum
