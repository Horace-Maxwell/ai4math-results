import Research.Backfill.Paper2.FiniteCoefficients

/-! Integral normalized contraction for the complete original existence contract. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.Existence295762
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint

private theorem square_subst_dvd (F G : PowerSeries ℤ) (n : ℕ) (hd : X ^ n ∣ F - G) :
    X ^ (2 * n) ∣ F.subst ((X : PowerSeries ℤ) ^ 2) - G.subst ((X : PowerSeries ℤ) ^ 2) := by
  have hs := HasSubst.X_pow (R := ℤ) two_ne_zero
  obtain ⟨Q, hQ⟩ := hd
  rw [← subst_sub hs, hQ, subst_mul hs, subst_pow hs, subst_X hs, ← pow_mul]
  exact dvd_mul_right _ _

theorem check_EX_A295762 : EX_A295762 := by
  let h : PowerSeries ℤ → PowerSeries ℤ := fun A => X - 2 * A.subst (X ^ 2)
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun A => X + A.subst (X ^ 2) - (A.subst (h A) - A)
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun A _ => Φ (A ())
  let seed : Unit → PowerSeries ℤ := fun _ => 0
  have norm_zero : ∀ A : Unit → PowerSeries ℤ, Jet 1 A seed → constantCoeff (A ()) = 0 := by
    intro A ha
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_zero] using ha () 0 (by omega)
  have hzero : ∀ A, constantCoeff A = 0 → constantCoeff (h A) = 0 := by
    intro A ha
    simp [h, constantCoeff_subst_X_pow two_ne_zero, ha]
  have hone : ∀ A, coeff 1 (h A) = 1 := by
    intro A
    simp [h, coeff_subst_X_pow two_ne_zero, coeff_X]
  have hp : ∀ A, Jet 1 A seed → Jet 1 (Ψ A) seed := by
    intro A ha i j hj
    have : j = 0 := by omega
    subst j
    have hcomp0 : constantCoeff ((A ()).subst (h (A ()))) = 0 :=
      constantCoeff_subst_eq_zero (hzero _ (norm_zero A ha)) (A ()) (norm_zero A ha)
    simp [Ψ, Φ, seed, coeff_zero_eq_constantCoeff_apply, norm_zero A ha, hcomp0,
      constantCoeff_subst_X_pow two_ne_zero]
  have hc : ∀ n, 1 ≤ n → ∀ A B, Jet 1 A seed → Jet 1 B seed →
      Jet n A B → Jet (n + 1) (Ψ A) (Ψ B) := by
    intro n hn A B ha hb hab
    have ha0 := norm_zero A ha
    have hb0 := norm_zero B hb
    have hd : X ^ n ∣ A () - B () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hab () j hj, sub_self]
    have haH := hzero _ ha0
    have hbH := hzero _ hb0
    have hsA := HasSubst.of_constantCoeff_zero' haH
    have hd2 := square_subst_dvd (A ()) (B ()) n hd
    have hd2' : X ^ (n + 1) ∣ (A ()).subst (X ^ 2) - (B ()).subst (X ^ 2) :=
      (pow_dvd_pow X (by omega : n + 1 ≤ 2 * n)).trans hd2
    have hnear := XadicAlgebra.subst_near_id (A () - B ()) (h (A ())) haH (hone _) n hd
    have hh : X ^ (n + 1) ∣ h (A ()) - h (B ()) := by
      have heq : h (A ()) - h (B ()) = -2 * ((A ()).subst (X ^ 2) - (B ()).subst (X ^ 2)) := by dsimp only [h]; ring
      rw [heq]
      exact dvd_mul_of_dvd_right hd2' _
    have hinner := XadicAlgebra.subst_congr_right (B ()) (h (A ())) (h (B ())) hsA
      (HasSubst.of_constantCoeff_zero' hbH) (n + 1) hh
    have heq : Φ (A ()) - Φ (B ()) =
        ((A ()).subst (X ^ 2) - (B ()).subst (X ^ 2)) -
          (((A () - B ()).subst (h (A ())) - (A () - B ())) +
            ((B ()).subst (h (A ())) - (B ()).subst (h (B ())))) := by
      rw [subst_sub hsA]
      dsimp only [Φ]; ring
    have ht : X ^ (n + 1) ∣ Φ (A ()) - Φ (B ()) := by
      rw [heq]
      exact dvd_sub hd2' (dvd_add hnear hinner)
    rw [X_pow_dvd_iff] at ht
    intro i j hj
    have hz := ht j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨A, ⟨ha, hfix⟩, huniq⟩ := existsUnique_fixed_seed 1 seed Ψ hp hc
  have ha0 := norm_zero A ha
  have he : Φ (A ()) = A () := congrFun hfix ()
  have hAeq : Eq295762 (A ()) := by
    change (A ()).subst (X - 2 * (A ()).subst (X ^ 2)) = X + (A ()).subst (X ^ 2)
    dsimp only [Φ, h] at he
    linear_combination -he
  refine ⟨A (), ⟨ha0, hAeq⟩, ?_⟩
  rintro B ⟨hb0, hb⟩
  let G : Unit → PowerSeries ℤ := fun _ => B
  have hgn : Jet 1 G seed := by
    intro i j hj
    have : j = 0 := by omega
    subst j
    simpa only [G, seed, coeff_zero_eq_constantCoeff_apply, map_zero] using hb0
  have hgf : Ψ G = G := by
    funext i
    change Φ B = B
    change B.subst (X - 2 * B.subst (X ^ 2)) = X + B.subst (X ^ 2) at hb
    dsimp only [Φ, h]
    linear_combination -hb
  exact congrFun (huniq G ⟨hgn, hgf⟩) ()

end BackfillPaper2.Existence295762
#print axioms BackfillPaper2.Existence295762.check_EX_A295762
