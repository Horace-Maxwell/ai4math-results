import Research.TaskU.H5.IntegerFactors
import Research.TaskU.H5.Normalize
import Research.TaskU.H5.TraceIntegral
import Research.TaskU.H5.Quotient

namespace TaskU.H5
noncomputable section
open Finset
open scoped BigOperators
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem norm_ray_dvd_iff (f : H → ℤ) (u v : F) :
    5 ∣ Cyc5.norm (ray f u v) ↔ 5 ∣ aug f := by
  rw [Cyc5.five_dvd_norm_iff, ray, profile_mass, counts_total]
  unfold aug
  omega

theorem aug_necessary (f : H → ℤ) (hn : 5 ∣ Cyc5.norm (TraceWords.nonlinear f) ↔ 5 ∣ aug f)
    (hd : 5 ∣ groupDet f) : 5 ∣ aug f := by
  by_contra ha
  have no_cast (n : ℤ) (h : ¬ (5:ℤ) ∣ n) : (n:F) ≠ 0 := fun he =>
    h ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp he)
  have h0 : (groupDet f : F) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hd
  rw [integerFactorization] at h0
  push_cast at h0
  have hr (u v : F) : (Cyc5.norm (ray f u v):F) ≠ 0 :=
    no_cast _ (fun he => ha ((norm_ray_dvd_iff f u v).mp he))
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (no_cast _ ha) (hr 1 0))
    (Finset.prod_ne_zero_iff.mpr (fun j _ => hr j 1)))
    (pow_ne_zero _ (no_cast _ (fun he => ha (hn.mp he))))) h0

theorem exceptional_norm (f : H → ℤ) (hx : mx f = 0) (ha : 5 ∣ aug f) :
    25 ∣ Cyc5.norm (ray f 1 0) := by
  obtain ⟨w, hw⟩ := ray_pi ha 1 0
  have hs : slope (ray f 1 0) = 0 := by simpa [ray_slope,mx] using hx
  obtain ⟨y,hy⟩ := (two_pi hw).mpr hs
  exact ⟨Cyc5.norm y, by rw [hw,hy,Cyc5.norm_mul,Cyc5.norm_mul,Cyc5.norm_pi]; ring⟩

structure Layers (f : H → ℤ) where
  a : ℤ
  e : ℤ
  d : ℤ
  q : F → Cyc5.V
  augmentation : aug f = 5*a
  horizontalNorm : Cyc5.norm (ray f 1 0) = 25*e
  nonlinearNorm : Cyc5.norm (TraceWords.nonlinear f) = 625*d
  ordinary : ∀ j, ray f j 1 = Cyc5.mul Cyc5.pi (q j)

theorem layers_exist (f : H → ℤ) (hx : mx f = 0) (ha : 5 ∣ aug f)
    (hd : 625 ∣ Cyc5.norm (TraceWords.nonlinear f)) : Nonempty (Layers f) := by
  obtain ⟨a,hta⟩ := ha
  obtain ⟨e,hhe⟩ := exceptional_norm f hx ⟨a,hta⟩
  obtain ⟨d,hnd⟩ := hd
  choose q hq using fun j : F => ray_pi (f := f) ⟨a,hta⟩ j 1
  exact ⟨⟨a,e,d,q,hta,hhe,hnd,hq⟩⟩

theorem Layers.value {f : H → ℤ} (c : Layers f) :
    groupDet f = 5^28 * (c.a*c.e*(∏ j, Cyc5.norm (c.q j))*c.d^5) := by
  rw [integerFactorization, c.augmentation, c.horizontalNorm, c.nonlinearNorm]
  simp only [c.ordinary, Cyc5.norm_mul, Cyc5.norm_pi, prod_mul_distrib,
    prod_const, card_univ, ZMod.card]
  ring

theorem Layers.deep_zero {f : H → ℤ} (c : Layers f) (hx : mx f = 0) (hy : my f = 0) :
    5^33 ∣ groupDet f := by
  have hh (j : F) : 5 ∣ Cyc5.norm (c.q j) := by
    apply (Cyc5.five_dvd_norm_iff _).mpr
    apply (Cyc5.pi_dvd_iff _).mp
    apply (two_pi (c.ordinary j)).mpr
    change slope (ray f j 1) = 0
    rw [ray_slope]
    change j * mx f + 1 * my f = 0
    simp [hx,hy]
  choose u hu using hh
  rw [c.value]
  refine ⟨c.a*c.e*(∏j,u j)*c.d^5, ?_⟩
  simp only [hu, prod_mul_distrib, prod_const, card_univ, ZMod.card]
  ring

theorem Layers.small_norm {f : H → ℤ} (c : Layers f) (hx : mx f = 0) (hy : my f ≠ 0)
    {m : ℤ} (hm : 1 ≤ m) (hm' : m ≤ 10) (he : groupDet f = 5^28*m) :
    ∀ j, Cyc5.norm (ray f j 1) = 5 := by
  have hmval : m = c.a*c.e*(∏ j, Cyc5.norm (c.q j))*c.d^5 :=
    mul_left_cancel₀ (by decide : (5:ℤ)^28 ≠ 0) (he.symm.trans c.value)
  intro j
  have hs : slope (ray f j 1) ≠ 0 := by
    rw [ray_slope]
    change j * mx f + 1 * my f ≠ 0
    simpa [hx] using hy
  rw [c.ordinary j,slope_pi, neg_ne_zero] at hs
  have hres : (Cyc5.norm (c.q j):F) = 1 := by
    rw [Cyc5.norm_mod_five]
    exact (by decide : ∀ x : F, x ≠ 0 → x^4=1) _ hs
  have hunit := SmallMultiples.small_signed_unit m (Cyc5.norm (c.q j)) hm hm'
    (SmallMultiples.each_dvd _ _ _ _ _ hmval j) hres
    (Cyc5.inert_fourth _ 2 (by decide)) (Cyc5.inert_fourth _ 3 (by decide))
  rw [c.ordinary j, Cyc5.norm_mul, Cyc5.norm_pi,hunit,mul_one]

theorem Layers.deep_nonlin {f : H → ℤ} (c : Layers f) (h : 25 ∣ TraceWords.integerAverage f) :
    5^33 ∣ groupDet f := by
  obtain ⟨k,hk⟩ := TraceWords.norm_deep f h
  rw [integerFactorization,c.augmentation,c.horizontalNorm,hk]
  refine ⟨c.a*c.e*(∏ j, Cyc5.norm (c.q j))*k^5, ?_⟩
  simp only [c.ordinary, Cyc5.norm_mul, Cyc5.norm_pi, prod_mul_distrib, prod_const, card_univ, ZMod.card]
  ring

end
end TaskU.H5
