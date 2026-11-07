import Research.Backfill.Paper2.XadicAlgebra

/-! The derivative loses one degree; its two vanishing factors restore strict contraction. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceA301933
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint
local notation "D" => PowerSeries.derivative (R := ℤ)

theorem check_EX_A301933 : EX_A301933 := by
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun A => X + (4 * X - A) * A * D A
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun A _ => Φ (A ())
  let seed : Unit → PowerSeries ℤ := fun _ => 0
  have norm_zero : ∀ A : Unit → PowerSeries ℤ, Jet 1 A seed → constantCoeff (A ()) = 0 := by
    intro A ha
    have he := ha () 0 (by omega)
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_zero] using he
  have hp : ∀ A, Jet 1 A seed → Jet 1 (Ψ A) seed := by
    intro A ha i j hj
    have : j = 0 := by omega
    subst j
    simp [Ψ, Φ, seed, coeff_zero_eq_constantCoeff_apply, norm_zero A ha]
  have hc : ∀ n, 1 ≤ n → ∀ A B, Jet 1 A seed → Jet 1 B seed →
      Jet n A B → Jet (n + 1) (Ψ A) (Ψ B) := by
    intro n hn A B ha hb hab
    have ha0 := norm_zero A ha
    have hb0 := norm_zero B hb
    have hd : X ^ n ∣ A () - B () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hab () j hj, sub_self]
    have hlin : (X : PowerSeries ℤ) ∣ 4 * X - A () - B () := X_dvd_iff.mpr (by simp [ha0, hb0])
    have hfirst : X ^ (n + 1) ∣ (A () - B ()) * (4 * X - A () - B ()) * D (A ()) := by
      have ht : X ^ (n + 1) ∣ (A () - B ()) * (4 * X - A () - B ()) := by
        rw [pow_succ]
        exact mul_dvd_mul hd hlin
      exact dvd_mul_of_dvd_left ht _
    have hpoly : (X : PowerSeries ℤ) ^ 2 ∣ (4 * X - B ()) * B () := by
      rw [pow_two]
      exact mul_dvd_mul (X_dvd_iff.mpr (by simp [hb0])) (X_dvd_iff.mpr hb0)
    have hder : X ^ (n - 1) ∣ D (A ()) - D (B ()) := by
      have ht := XadicAlgebra.derivative_dvd (A () - B ()) (n - 1) (by
        simpa only [Nat.sub_add_cancel hn] using hd)
      simpa only [map_sub] using ht
    have hsecond : X ^ (n + 1) ∣ ((4 * X - B ()) * B ()) * (D (A ()) - D (B ())) := by
      have ht := mul_dvd_mul hpoly hder
      rw [← pow_add, show 2 + (n - 1) = n + 1 by omega] at ht
      exact ht
    have he : Φ (A ()) - Φ (B ()) =
        (A () - B ()) * (4 * X - A () - B ()) * D (A ()) +
          ((4 * X - B ()) * B ()) * (D (A ()) - D (B ())) := by dsimp only [Φ]; ring
    have ht : X ^ (n + 1) ∣ Φ (A ()) - Φ (B ()) := by rw [he]; exact dvd_add hfirst hsecond
    rw [X_pow_dvd_iff] at ht
    intro i j hj
    have hz := ht j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨A, ⟨ha, hfix⟩, huniq⟩ := existsUnique_fixed_seed 1 seed Ψ hp hc
  have ha0 := norm_zero A ha
  have hA : Φ (A ()) = A () := congrFun hfix ()
  have hAeq : Eq301933 (A ()) := by
    change A () * (1 + A () * D (A ())) = X * (1 + 4 * A () * D (A ()))
    dsimp only [Φ] at hA
    linear_combination -hA
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
    change B * (1 + B * D B) = X * (1 + 4 * B * D B) at hb
    dsimp only [Φ]
    linear_combination -hb
  exact congrFun (huniq G ⟨hgn, hgf⟩) ()

end BackfillPaper2.ExistenceA301933
#print axioms BackfillPaper2.ExistenceA301933.check_EX_A301933
