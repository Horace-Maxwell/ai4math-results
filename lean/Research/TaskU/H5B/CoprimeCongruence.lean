import Research.TaskU.H5.IntegerFactors
import Research.TaskU.H5.TraceIntegral
import Research.TaskU.H5B.ChallengeB

namespace TaskU.H5.Coprime
noncomputable section

open Finset
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
open TraceWords

def massBin (f : H → ℤ) (b : F) : ℤ := counts (weight f) mass b

private def bothBins (f : H → ℤ) (b e : F) : ℤ :=
  ∑ q : Word, if mass q = b ∧ phase q = e then weight f q else 0

private theorem sameBin (f : H → ℤ) {b : F} (hb : b ≠ 0) (e : F) :
    bothBins f b e = bothBins f b 0 := by
  let t := -e/b
  let h (q : Word) := if mass q = b ∧ phase q = e then weight f q else 0
  change ∑ q, h q = _
  rw [← Equiv.sum_comp (spin t) h]
  apply sum_congr rfl
  intro q _
  by_cases hq : mass q = b
  · have ht : t*b = -e := div_mul_cancel₀ _ hb
    change h (translate t q) = _
    simp [h, mass_translate, phase_translate, weight_translate, hq, ht]
  · change h (translate t q) = _
    simp [h, mass_translate, hq]

theorem five_dvd_massBin (f : H → ℤ) {b : F} (hb : b ≠ 0) : 5 ∣ massBin f b := by
  have hs : massBin f b = ∑ e : F, bothBins f b e := by
    simp only [massBin, counts, bothBins]
    rw [sum_comm]
    apply sum_congr rfl
    intro q _
    by_cases hq : mass q = b <;> simp [hq]
  rw [hs]
  simp_rw [sameBin f hb]
  simp [ZMod.card]

private theorem row (f : H → ℤ) (v : F) :
    (frequencyBlock f v 0).det = ∑ i, (massBin f i : ℂ)*ch (v*i) := by
  change (wordMatrix f v 0).det = _
  simp only [massBin, counts_weight, word_expansion]
  simp

private theorem linearProduct (f : H → ℤ) :
    (∏ v : F, ∏ u : F, linearFactor f u v) =
    ((∑ i, massBin f i) * Cyc5.norm (profile (massBin f)) : ℤ) := by
  simp_rw [← abelian_det, row]
  rw [← Finset.mul_prod_erase _ (fun v : F => ∑ i, (massBin f i : ℂ)*ch (v*i)) (mem_univ (0:F))]
  push_cast
  rw [norm_values]
  congr 1
  · simp
  · exact Finset.prod_congr rfl (fun v hv => (evalProfile _ v (ne_of_mem_erase hv)).symm)

private theorem fullProduct (f : H → ℤ) :
    groupDet f = ((∑ i, massBin f i) * Cyc5.norm (profile (massBin f))) *
      Cyc5.norm (nonlinear f)^5 := by
  rw [integerFactorization]
  apply congrArg (fun a : ℤ => a * Cyc5.norm (nonlinear f)^5)
  exact_mod_cast (abelianProduct f).symm.trans (linearProduct f)

private theorem quartic (a b c d e : ℤ) :
    125 ∣ (a + 5*b + 5*c + 5*d + 5*e) *
      Cyc5.normForm (a-5*e) (5*b-5*e) (5*c-5*e) (5*d-5*e) - a^5 := by
  unfold Cyc5.normForm
  ring_nf
  omega

private theorem nonlinearNorm (f : H → ℤ) :
    25 ∣ Cyc5.norm (nonlinear f) - (integerAverage f)^4 := by
  obtain ⟨u,h,⟨j,hj⟩⟩ := integral_congruence f
  simp only [Cyc5.sumCoeff] at hj
  have ha : u.a = 5*j-u.b-u.c-u.d := by omega
  rw [h]
  simp [Cyc5.add,Cyc5.scalar,Cyc5.mul,Cyc5.norm,Cyc5.normForm,ha]
  ring_nf
  omega

theorem determinant_congruence (f : H → ℤ) :
    groupDet f ≡ (integerAverage f)^25 [ZMOD 125] := by
  obtain ⟨b,hb⟩ := five_dvd_massBin f (show (1:F)≠0 by decide)
  obtain ⟨c,hc⟩ := five_dvd_massBin f (show (2:F)≠0 by decide)
  obtain ⟨d,hd⟩ := five_dvd_massBin f (show (3:F)≠0 by decide)
  obtain ⟨e,he⟩ := five_dvd_massBin f (show (4:F)≠0 by decide)
  have h0 : massBin f 0 = integerAverage f := rfl
  have hlin : 125 ∣ (∑ i, massBin f i) * Cyc5.norm (profile (massBin f)) - (integerAverage f)^5 := by
    simp only [sum_five, profile, Cyc5.norm, h0,hb,hc,hd,he]
    exact quartic _ b c d e
  obtain ⟨v,hv⟩ := hlin
  obtain ⟨w,hw⟩ := nonlinearNorm f
  have hL : (∑ i, massBin f i) * Cyc5.norm (profile (massBin f)) = (integerAverage f)^5+125*v := by omega
  have hN : Cyc5.norm (nonlinear f) = (integerAverage f)^4+25*w := by omega
  rw [Int.modEq_iff_dvd,fullProduct,hL,hN]
  ring_nf
  omega

theorem coprime_necessary (f : H → ℤ) (h : ¬(5:ℤ) ∣ groupDet f) :
    (groupDet f)^4 ≡ 1 [ZMOD 125] := by
  have he := (ZMod.intCast_eq_intCast_iff _ _ 125).mpr (determinant_congruence f)
  push_cast at he
  apply (ZMod.intCast_eq_intCast_iff _ _ 125).mp
  push_cast
  rw [he]
  have small : ∀ x : ZMod 125, (x^25)^4 = 1 ∨ x^25 = 0 := by decide +kernel
  rcases small (integerAverage f) with hgood | hzero
  · exact hgood
  · have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp (he.trans hzero)
    exact (h (dvd_trans (by decide : (5:ℤ) ∣ 125) hd)).elim

end
end TaskU.H5.Coprime
