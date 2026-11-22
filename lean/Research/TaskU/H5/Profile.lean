import Research.TaskU.H5.Cyc5
import Research.TaskU.H5.Fourier

namespace TaskU.H5
noncomputable section
open Finset Matrix
open scoped BigOperators

def profile (p : F → ℤ) : Cyc5.V :=
  ⟨p 0-p 4, p 1-p 4, p 2-p 4, p 3-p 4⟩

def aug (f : H → ℤ) : ℤ := ∑ g, f g

def counts {I : Type*} [Fintype I] (f : I → ℤ) (s : I → F) (r : F) : ℤ :=
  ∑ i, if s i = r then f i else 0

def ray (f : H → ℤ) (u v : F) : Cyc5.V :=
  profile (counts f (fun g => u*g.a+v*g.b))

theorem sum_five {R : Type*} [AddCommMonoid R] (q : F → R) :
    ∑ j, q j = q 0+q 1+q 2+q 3+q 4 := by
  exact Fin.sum_univ_five (f := (q : Fin 5 → R))

theorem counts_total {I : Type*} [Fintype I] (f : I → ℤ) (s : I → F) :
    ∑ r, counts f s r = ∑ i, f i := by
  simp only [counts]
  rw [sum_comm]
  simp

theorem counts_weight {I R : Type*} [Fintype I] [CommRing R]
    (f : I → ℤ) (s : I → F) (w : F → R) :
    ∑ j, (counts f s j : R) * w j = ∑ i, (f i : R)*w (s i) := by
  simp only [counts, Int.cast_sum, sum_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i _
  simp [ite_mul, apply_ite]

theorem profile_mass (p : F → ℤ) :
    Cyc5.sumCoeff (profile p) = (∑ i, p i) - 5 * p 4 := by
  rw [sum_five]
  simp [profile, Cyc5.sumCoeff]
  ring

def slope (v : Cyc5.V) : F := (v.b:F)+2*(v.c:F)+3*(v.d:F)

theorem profile_slope (p : F → ℤ) :
    slope (profile p) = ∑ i, (p i:F)*i := by
  rw [sum_five]
  simp only [slope, profile, Int.cast_sub, mul_zero, mul_one, zero_add]
  linear_combination (norm := ring) - (p 4:F) * (by decide : (5:F)=0) * 2

theorem ray_slope (f : H → ℤ) (u v : F) :
    slope (ray f u v) = u * (∑ g : H, (f g:F)*g.a) + v * (∑ g : H, (f g:F)*g.b) := by
  rw [ray, profile_slope, counts_weight, mul_sum, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro g _
  ring

theorem ray_pi {f : H → ℤ} (hf : 5 ∣ aug f) (u v : F) :
    ∃ w, ray f u v = Cyc5.mul Cyc5.pi w := by
  apply (Cyc5.pi_dvd_iff _).mpr
  rw [ray, profile_mass, counts_total]
  exact dvd_sub hf (dvd_mul_right _ _)

theorem slope_pi (w : Cyc5.V) :
    slope (Cyc5.mul Cyc5.pi w) = -(Cyc5.sumCoeff w:F) := by
  simp [slope,Cyc5.mul,Cyc5.pi,Cyc5.sumCoeff]
  linear_combination (norm := ring) (w.d:F) * (by decide : (5:F)=0) * 2

theorem two_pi {x w : Cyc5.V} (he : x = Cyc5.mul Cyc5.pi w) :
    (∃ y, w = Cyc5.mul Cyc5.pi y) ↔ slope x = 0 := by
  rw [he, slope_pi, neg_eq_zero, Cyc5.pi_dvd_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rfl

end
end TaskU.H5
