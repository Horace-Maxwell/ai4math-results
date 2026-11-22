import Research.TaskU.H5B.PrimeBasis
import Research.TaskU.H5B.LiftRing
import Research.TaskU.H5.CycPos

namespace TaskU.H5.PrimeRing
open Cyc5
noncomputable section

def integralEquiv : V ≃+* PrimeBasis.O where
  toFun := PrimeBasis.toO
  invFun := PrimeBasis.fromO
  left_inv := PrimeBasis.left_inv
  right_inv := PrimeBasis.right_inv
  map_add' x y := by simp [add_def, PrimeBasis.toO,add]; ring
  map_mul' := PrimeBasis.toO_mul

instance : IsDomain V := MulEquiv.isDomain _ integralEquiv.toMulEquiv
instance : IsPrincipalIdealRing V :=
  letI := IsCyclotomicExtension.Rat.five_pid PrimeBasis.K
  IsPrincipalIdealRing.of_surjective integralEquiv.symm.toRingHom integralEquiv.symm.surjective

theorem sigma_square (x : V) : sigma2 (sigma2 x) = conj x := by
  ext <;> simp [sigma2,conj]
  all_goals ring

theorem sigma_cube (x : V) : sigma2 (conj x) = sigma3 x := by
  ext <;> simp [sigma2,sigma3,conj]
  all_goals ring

theorem sigma_fourth (x : V) : sigma2 (sigma3 x) = x := by
  ext <;> simp [sigma2,sigma3,conj]
  all_goals ring

def gal : V ≃+* V where
  toFun := sigma2
  invFun := sigma3
  left_inv x := by rw [sigma3,sigma_square,conj_conj]
  right_inv := sigma_fourth
  map_add' x y := by ext <;> simp [add_def,sigma2,add] <;> ring
  map_mul' x y := by ext <;> simp [mul_def,sigma2,mul] <;> ring

theorem norm_eq_zero {x : V} : norm x = 0 ↔ x=0 := by
  constructor
  · intro h
    have eq : (x*conj x)*(gal x*gal.symm x)=0 := (norm_prod x).trans (by rw [h]; rfl)
    rcases mul_eq_zero.mp eq with h₁ | h₂
    · rcases mul_eq_zero.mp h₁ with hx | hc
      · exact hx
      · rw [←conj_conj x,hc]; rfl
    · rcases mul_eq_zero.mp h₂ with hx | hx
      · exact gal.injective (hx.trans gal.map_zero.symm)
      · exact gal.symm.injective (hx.trans gal.symm.map_zero.symm)
  · rintro rfl; decide

theorem dvd_nat_of_int_cast_dvd_nat {n : ℤ} {q : ℕ}
    (hd : (n:V) ∣ (q:V)) : n ∣ (q:ℤ) := by
  obtain ⟨v,hv⟩ := hd
  have hh : (q:ℤ) = (mul (scalar n) v).a := congrArg V.a hv
  exact ⟨v.a,by simpa [mul,scalar] using hh⟩

end
end TaskU.H5.PrimeRing
