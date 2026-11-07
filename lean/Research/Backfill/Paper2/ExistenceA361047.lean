import Research.Backfill.Paper2.FiniteCoefficients

/-! Integral normalized contraction for the complete original existence contract. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.Existence361047
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint
local notation "D" => PowerSeries.derivative (R := ℤ)

theorem check_EX_A361047 : EX_A361047 := by
  let h : PowerSeries ℤ → PowerSeries ℤ := fun A => X - X ^ 3 * (D A) ^ 2
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun A => X - (A.subst (h A) - A)
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun A _ => Φ (A ())
  let seed : Unit → PowerSeries ℤ := fun _ => 0
  have norm_zero : ∀ A : Unit → PowerSeries ℤ, Jet 1 A seed → constantCoeff (A ()) = 0 := by
    intro A ha
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_zero] using ha () 0 (by omega)
  have hzero : ∀ A, constantCoeff (h A) = 0 := by intro A; simp [h]
  have hone : ∀ A, coeff 1 (h A) = 1 := by
    intro A
    simp [h, coeff_X_pow_mul', coeff_X]
  have hp : ∀ A, Jet 1 A seed → Jet 1 (Ψ A) seed := by
    intro A ha i j hj
    have : j = 0 := by omega
    subst j
    have hcomp0 : constantCoeff ((A ()).subst (h (A ()))) = 0 :=
      constantCoeff_subst_eq_zero (hzero _) (A ()) (norm_zero A ha)
    simp [Ψ, Φ, seed, coeff_zero_eq_constantCoeff_apply, norm_zero A ha, hcomp0]
  have hc : ∀ n, 1 ≤ n → ∀ A B, Jet 1 A seed → Jet 1 B seed →
      Jet n A B → Jet (n + 1) (Ψ A) (Ψ B) := by
    intro n hn A B ha hb hab
    have ha0 := norm_zero A ha
    have hb0 := norm_zero B hb
    have hd : X ^ n ∣ A () - B () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hab () j hj, sub_self]
    have hsA := HasSubst.of_constantCoeff_zero' (hzero (A ()))
    have hder : X ^ (n - 1) ∣ D (A ()) - D (B ()) := by
      have ht := XadicAlgebra.derivative_dvd (A () - B ()) (n - 1) (by
        simpa only [Nat.sub_add_cancel hn] using hd)
      simpa only [map_sub] using ht
    have hd2 := hder.trans (sub_dvd_pow_sub_pow (D (A ())) (D (B ())) 2)
    have hh : X ^ (n + 1) ∣ h (A ()) - h (B ()) := by
      have hx : X ^ (n + 2) ∣ X ^ 3 * ((D (A ())) ^ 2 - (D (B ())) ^ 2) := by
        have ht := mul_dvd_mul_left (X ^ 3) hd2
        rw [← pow_add, show 3 + (n - 1) = n + 2 by omega] at ht
        exact ht
      have heq : h (A ()) - h (B ()) = -(X ^ 3 * ((D (A ())) ^ 2 - (D (B ())) ^ 2)) := by dsimp only [h]; ring
      rw [heq]
      exact dvd_neg.mpr ((pow_dvd_pow X (by omega : n + 1 ≤ n + 2)).trans hx)
    have hnear := XadicAlgebra.subst_near_id (A () - B ()) (h (A ())) (hzero _) (hone _) n hd
    have hinner := XadicAlgebra.subst_congr_right (B ()) (h (A ())) (h (B ())) hsA
      (HasSubst.of_constantCoeff_zero' (hzero _)) (n + 1) hh
    have heq : Φ (A ()) - Φ (B ()) =
        -(((A () - B ()).subst (h (A ())) - (A () - B ())) +
            ((B ()).subst (h (A ())) - (B ()).subst (h (B ())))) := by
      rw [subst_sub hsA]
      dsimp only [Φ]; ring
    have ht : X ^ (n + 1) ∣ Φ (A ()) - Φ (B ()) := by
      rw [heq]
      exact dvd_neg.mpr (dvd_add hnear hinner)
    rw [X_pow_dvd_iff] at ht
    intro i j hj
    have hz := ht j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨A, ⟨ha, hfix⟩, huniq⟩ := existsUnique_fixed_seed 1 seed Ψ hp hc
  have ha0 := norm_zero A ha
  have he : Φ (A ()) = A () := congrFun hfix ()
  have hAeq : Eq361047 (A ()) := by
    change (A ()).subst (X - X ^ 3 * (D (A ())) ^ 2) = X
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
    change B.subst (X - X ^ 3 * (D B) ^ 2) = X at hb
    dsimp only [Φ, h]
    linear_combination -hb
  exact congrFun (huniq G ⟨hgn, hgf⟩) ()

end BackfillPaper2.Existence361047
#print axioms BackfillPaper2.Existence361047.check_EX_A361047
