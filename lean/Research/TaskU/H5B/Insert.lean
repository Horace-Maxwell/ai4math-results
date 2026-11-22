import Research.TaskU.H5B.UnitResidues
import Research.TaskU.H5B.SeedMarginals

namespace TaskU.H5.Spectrum
open Cyc5 (V)
open Finset

def divFive (x : V) : V := ⟨x.a / 5, x.b / 5, x.c / 5, x.d / 5⟩
def seedQuot (s : Fin 5) := divFive (Cyc5.mul p3 (baseRay s))

theorem seed_quot_spec : ∀ s : Fin 5,
    Cyc5.mul p3 (baseRay s) = Cyc5.mul (Cyc5.scalar 5) (seedQuot s) ∧
    (Cyc5.sumCoeff (seedQuot s) : F) = -1 ∧ (Cyc5.sumCoeff (baseRay s) : F) = 0 := by
  decide +kernel

theorem profile_surj (W : V) (t : ℤ) (h : (t:F)=(Cyc5.sumCoeff W:F)) :
    ∃ q : F → ℤ, profile q = W ∧ ∑ a, q a = t := by
  have hdiv : (5:ℤ) ∣ t-Cyc5.sumCoeff W := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp
    push_cast
    rw [h,sub_self]
  obtain ⟨v,hv⟩ := hdiv
  let q : F → ℤ := fun j => ![W.a+v,W.b+v,W.c+v,W.d+v,v] (j : Fin 5)
  refine ⟨q,?_,?_⟩
  · ext <;> simp [profile,q]
  · rw [sum_five]
    simp [q,Cyc5.sumCoeff] at hv ⊢
    omega

theorem insert_rows {ℓ : ℕ} (hl : ChallengeB.visible ℓ) (k : ℤ) :
    ∃ s : Fin 5, ∃ q : F → ℤ, (∑ a, q a)=k-seedA s ∧
      (∑ a, (q a : F)) ≠ 0 ∧
      Cyc5.norm (Cyc5.add (baseRay s) (Cyc5.mul (Cyc5.scalar 5) (profile q))) = 5*(ℓ:ℤ) := by
  obtain ⟨η,d,w,hd,hn,he⟩ := visible_normalized hl
  obtain ⟨s,hs⟩ := seed_residues ((k:F)+d)
  let b := baseRay s
  let W := (d.val : V) * seedQuot s + w * b
  obtain ⟨hb,hq0,hb0⟩ := seed_quot_spec s
  have hmass : (Cyc5.sumCoeff W:F) = -d := by
    change Cyc5.residue (Cyc5.add (Cyc5.mul (Cyc5.scalar d.val) (seedQuot s)) (Cyc5.mul w b)) = _
    have hadd (x y : V) : Cyc5.residue (Cyc5.add x y) = Cyc5.residue x + Cyc5.residue y := by
      simp [Cyc5.residue,Cyc5.sumCoeff,Cyc5.add]; ring
    rw [hadd,Cyc5.residue_mul,Cyc5.residue_mul]
    change _ * (Cyc5.sumCoeff (seedQuot s):F) + _ * (Cyc5.sumCoeff (baseRay s):F) = _
    rw [hq0,hb0,mul_zero,add_zero,mul_neg_one]
    simp [Cyc5.residue,Cyc5.sumCoeff,Cyc5.scalar]
  have hc : ((k-seedA s:ℤ):F) = (Cyc5.sumCoeff W:F) := by
    rw [hmass,Int.cast_sub,hs]; ring
  obtain ⟨q,hq,ht⟩ := profile_surj W _ hc
  refine ⟨s,q,ht,?_,?_⟩
  · rw [← Int.cast_sum,ht,hc,hmass]
    exact neg_ne_zero.mpr hd
  · have hbr : p3*b=(5:V)*seedQuot s := hb
    have hW : b+(5:V)*W=η*b := by
      rw [he]
      change b + 5*((d.val:V)*seedQuot s+w*b) =
        (1+(d.val:V)*p3+5*w)*b
      linear_combination -(d.val:V)*hbr
    rw [hq]
    change Cyc5.norm (b+(5:V)*W) = _
    rw [hW,Cyc5.mul_def,Cyc5.norm_mul,hn,(swapped_data s).2.1,mul_comm]
end TaskU.H5.Spectrum
