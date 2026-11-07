import Research.Backfill.Paper2.XadicAlgebra

/-! Integer existence from a triangular contraction after A = 1+B. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceA240998
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint

theorem check_EX_A240998 : EX_A240998 := by
  let h : PowerSeries ℤ := X + 2 * X ^ 2
  have h0 : constantCoeff h = 0 := by simp [h]
  have h1 : coeff 1 h = 1 := by simp [h, coeff_X_pow]
  have hs := HasSubst.of_constantCoeff_zero' h0
  have hone : (1 : PowerSeries ℤ).subst h = 1 := by rw [← coe_substAlgHom hs, map_one]
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun B => X + B.subst h - B - B ^ 2
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun B _ => Φ (B ())
  let seed : Unit → PowerSeries ℤ := fun _ => 0
  have norm_zero : ∀ B : Unit → PowerSeries ℤ, Jet 1 B seed → constantCoeff (B ()) = 0 := by
    intro B hb
    have he := hb () 0 (by omega)
    simpa only [seed, coeff_zero_eq_constantCoeff_apply, map_zero] using he
  have hp : ∀ B, Jet 1 B seed → Jet 1 (Ψ B) seed := by
    intro B hb i j hj
    have : j = 0 := by omega
    subst j
    have hb0 := norm_zero B hb
    have ht : constantCoeff ((B ()).subst h) = 0 := constantCoeff_subst_eq_zero h0 (B ()) hb0
    simp only [Ψ, Φ, seed, coeff_zero_eq_constantCoeff_apply, map_sub, map_add, map_pow,
      constantCoeff_X, hb0, ht, zero_add, sub_zero, zero_pow two_ne_zero, map_zero]
  have hc : ∀ n, 1 ≤ n → ∀ B C, Jet 1 B seed → Jet 1 C seed →
      Jet n B C → Jet (n + 1) (Ψ B) (Ψ C) := by
    intro n _ B C hb hcc hd
    have hB0 := norm_zero B hb
    have hC0 := norm_zero C hcc
    have hD : X ^ n ∣ B () - C () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hd () j hj, sub_self]
    have hleft := XadicAlgebra.subst_near_id (B () - C ()) h h0 h1 n hD
    have hpow : X ^ (n + 1) ∣ (B ()) ^ 2 - (C ()) ^ 2 := by
      have hs0 : (X : PowerSeries ℤ) ∣ B () + C () := X_dvd_iff.mpr (by simp [hB0, hC0])
      rw [show (B ()) ^ 2 - (C ()) ^ 2 = (B () - C ()) * (B () + C ()) by ring, pow_succ]
      exact mul_dvd_mul hD hs0
    have he : Φ (B ()) - Φ (C ()) =
        (B () - C ()).subst h - (B () - C ()) - ((B ()) ^ 2 - (C ()) ^ 2) := by
      dsimp only [Φ]
      rw [subst_sub hs]
      ring
    intro i j hj
    have ht : X ^ (n + 1) ∣ Φ (B ()) - Φ (C ()) := by rw [he]; exact dvd_sub hleft hpow
    rw [X_pow_dvd_iff] at ht
    have hz := ht j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨B, ⟨hb, hfix⟩, huniq⟩ := existsUnique_fixed_seed 1 seed Ψ hp hc
  have hb0 := norm_zero B hb
  have hB : Φ (B ()) = B () := congrFun hfix ()
  let A : PowerSeries ℤ := 1 + B ()
  have hA0 : constantCoeff A = 1 := by simp [A, hb0]
  have hA : Eq240998 A := by
    change (1 + B ()) ^ 2 = X + (1 + B ()).subst h
    rw [subst_add hs, hone]
    dsimp only [Φ] at hB
    linear_combination -hB
  refine ⟨A, ⟨hA0, hA⟩, ?_⟩
  rintro D ⟨hd0, hd⟩
  let G : Unit → PowerSeries ℤ := fun _ => D - 1
  have hg0 : Jet 1 G seed := by
    intro i j hj
    have : j = 0 := by omega
    subst j
    simp [G, seed, coeff_zero_eq_constantCoeff_apply, hd0]
  have hgf : Ψ G = G := by
    funext i
    change Φ (D - 1) = D - 1
    dsimp only [Φ]
    rw [subst_sub hs, hone]
    change D ^ 2 = X + D.subst h at hd
    linear_combination -hd
  have he : G = B := huniq G ⟨hg0, hgf⟩
  have hg : D - 1 = B () := congrFun he ()
  change D = 1 + B ()
  linear_combination hg

end BackfillPaper2.ExistenceA240998
#print axioms BackfillPaper2.ExistenceA240998.check_EX_A240998
