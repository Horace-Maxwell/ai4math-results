import Research.TaskU.H5B.PrimeOrbit
import Research.TaskU.H5B.PrimeRing
import Research.TaskU.H5B.UnitResidues

namespace TaskU.H5.PrimeExtract
open Cyc5
open ChallengeB
open Spectrum
open PrimeRing

lemma unitImage_of_isUnit {x : V} (hx : IsUnit x) : unitImage x := by
  obtain ⟨u,rfl⟩ := hx
  exact ⟨u,↑u⁻¹, u.val_inv, red_congr.mpr rfl⟩

lemma unitImage_mul {x y : V} (hx : unitImage x) (hy : unitImage y) :
    unitImage (x*y) := by
  obtain ⟨u,v,hu,hr⟩ := hx
  obtain ⟨k,j,hk,hs⟩ := hy
  refine ⟨u*k,v*j,?_,?_⟩
  · change (u*k)*(v*j)=1
    change u*v=1 at hu
    change k*j=1 at hk
    calc (u*k)*(v*j)=(u*v)*(k*j) := by ring
         _=1 := by rw [hu,hk,one_mul]
  · apply red_congr.mpr
    rw [mul_def,red_mul,mul_def,red_mul,red_congr.mp hr,red_congr.mp hs]

theorem prime_visible {x : V} (hx : Prime x) (h5 : ¬(5:ℤ) ∣ norm x) (h : ¬unitImage x)
    (hconj : ∀ y : V, ¬(5:ℤ) ∣ norm y →
      (∃ u : V, norm u=1 ∧ congrFive (conj y) (mul u y)) → unitImage y) :
    ∃ q : ℕ, visible q ∧ norm x = (q:ℤ) := by
  have nc : ¬x∣conj x := by
    intro hd
    have pc : Prime (conj x) := by
      rw [←sigma_square]
      exact (MulEquiv.prime_iff gal).mpr ((MulEquiv.prime_iff gal).mpr hx)
    obtain ⟨u,hu⟩ := hx.associated_of_dvd pc hd
    apply h (hconj x h5 ⟨u, norm_of_unit u.val_inv, ?_⟩)
    apply red_congr.mpr
    change red (conj x) = red ((u:V)*x)
    rw [←hu, _root_.mul_comm]
  have hn : 0 < norm x := lt_of_le_of_ne (norm_nonneg x) (Ne.symm (mt norm_eq_zero.mp hx.ne_zero))
  have hn1 : norm x ≠ 1 := by
    intro he
    obtain ⟨u,hu,_⟩ := unit_inverse he
    exact h ⟨x,u,hu,red_congr.mpr rfl⟩
  let n := (norm x).toNat
  have hncast : (n:ℤ) = norm x := Int.toNat_of_nonneg hn.le
  have hd : x ∣ (n:V) := by
    have hh := norm_prod x
    change (x*conj x)*(gal x*gal.symm x) = ((norm x:ℤ):V) at hh
    rw [←hncast,Int.cast_natCast] at hh
    exact ⟨_,hh.symm.trans (_root_.mul_assoc ..)⟩
  obtain ⟨q,hp,_,hdq⟩ := PrimeOrbit.prime_below_nat hx (by omega : n≠0) hd
  have horbit := PrimeOrbit.four_dvd gal (a:=x) (b:=sigma2 x) (c:=conj x)
    (d:=sigma3 x) rfl (sigma_square _) (sigma_cube _) (sigma_fourth _) hx nc hdq
  change mul (mul x (conj x)) (mul (sigma2 x) (sigma3 x)) ∣ (q:V) at horbit
  rw [norm_prod] at horbit
  have hdiv := dvd_nat_of_int_cast_dvd_nat horbit
  rw [←hncast] at hdiv
  have hqn := (hp.eq_one_or_self_of_dvd n (Int.natCast_dvd_natCast.mp hdiv)).resolve_left (by omega)
  have he : norm x = (q:ℤ) := hncast.symm.trans (congrArg Nat.cast hqn)
  have hqr : q % 5=1 := by
    have hh := norm_mod_five x
    rw [he,Int.cast_natCast] at hh
    have hnon : (sumCoeff x : ZMod 5) ≠ 0 := by
      intro hs
      exact h5 ((five_dvd_norm_iff x).mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp hs))
    rw [(by decide : ∀ t : ZMod 5, t ≠ 0 → t^4=1) _ hnon] at hh
    exact_mod_cast congrArg ZMod.val hh
  exact ⟨q,⟨hp,hqr,x,he,h⟩,he⟩

theorem extract (x : V) (hconj : ∀ y : V, ¬(5:ℤ) ∣ norm y →
    (∃ u : V, norm u=1 ∧ congrFive (conj y) (mul u y)) → unitImage y) :
    ¬(5:ℤ) ∣ norm x → ¬unitImage x → ∃ q : ℕ, visible q ∧ (q:ℤ) ∣ norm x := by
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact (h (by decide)).elim
  | h₂ x hx => intro _ h; exact (h (unitImage_of_isUnit hx)).elim
  | h₃ a p _ hp ih =>
    intro h5 hi
    change ¬(5:ℤ) ∣ norm (mul p a) at h5
    rw [norm_mul] at h5
    by_cases hu : unitImage p
    · obtain ⟨q,hq,hd⟩ := ih (fun h => h5 (dvd_mul_of_dvd_right h _))
          (fun h => hi (unitImage_mul hu h))
      exact ⟨q,hq,by change (q:ℤ) ∣ norm (mul p a); rw [norm_mul]; exact dvd_mul_of_dvd_right hd _⟩
    · obtain ⟨q,hq,he⟩ := prime_visible hp (fun h => h5 (dvd_mul_of_dvd_left h _)) hu hconj
      refine ⟨q,hq,?_⟩
      change (q:ℤ) ∣ norm (mul p a)
      rw [norm_mul,he]
      exact dvd_mul_right .. 

theorem visible_dvd_of_not_unitImage (x : V) (h5 : ¬(5:ℤ) ∣ norm x) (h : ¬unitImage x) :
    ∃ q : ℕ, visible q ∧ (q:ℤ) ∣ norm x :=
  extract x (fun _ => conjugation_fixed) h5 h

#print axioms visible_dvd_of_not_unitImage

end TaskU.H5.PrimeExtract
