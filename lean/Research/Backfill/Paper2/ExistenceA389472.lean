import Research.Backfill.Paper2.FiniteCoefficients

/-! The free quadratic coefficient is fixed exactly as in the original entry.
Above degree two, substituting X²+X³ strictly raises coefficient precision. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceA389472
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint
open BackfillPaper2.FiniteCoefficients

theorem check_EX_A389472 : EX_A389472 := by
  let h : PowerSeries ℤ := X ^ 2 + X ^ 3
  have h0 : constantCoeff h = 0 := by simp [h]
  have hs := HasSubst.of_constantCoeff_zero' h0
  let seed : Unit → PowerSeries ℤ := fun _ => X + X ^ 2
  let Φ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun A _ =>
    PowerSeries.mk fun n => if n < 3 then coeff n (seed ()) else coeff (n + 2) ((A ()).subst h)
  have hp : ∀ A, Jet 3 A seed → Jet 3 (Φ A) seed := by
    intro A _ i j hj
    dsimp only [Φ]
    rw [coeff_mk, ite_eq_left hj]
  have hc : ∀ n, 3 ≤ n → ∀ A B, Jet 3 A seed → Jet 3 B seed →
      Jet n A B → Jet (n + 1) (Φ A) (Φ B) := by
    intro n hn A B _ _ hd
    have hD : X ^ n ∣ A () - B () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hd () j hj, sub_self]
    obtain ⟨Q, hQ⟩ := hD
    have he : h ^ n = X ^ (2 * n) * (1 + X) ^ n := by
      rw [show h = X ^ 2 * (1 + X) by dsimp [h]; ring, mul_pow, ← pow_mul]
    have hsub : X ^ (2 * n) ∣ (A ()).subst h - (B ()).subst h := by
      rw [← subst_sub hs, hQ, subst_mul hs, subst_pow hs, subst_X hs, he, mul_assoc]
      exact dvd_mul_right _ _
    rw [X_pow_dvd_iff] at hsub
    intro i j hj
    dsimp only [Φ]
    rw [coeff_mk, coeff_mk]
    by_cases hlow : j < 3
    · rw [ite_eq_left hlow, ite_eq_left hlow]
    · rw [ite_eq_right hlow, ite_eq_right hlow]
      have ht := hsub (j + 2) (by omega)
      rw [map_sub, sub_eq_zero] at ht
      exact ht
  obtain ⟨A, ⟨ha, hfix⟩, huniq⟩ := existsUnique_fixed_seed 3 seed Φ hp hc
  have ha0 : coeff 0 (A ()) = 0 := by simpa [seed, coeff_X_pow, coeff_X] using ha () 0 (by omega)
  have ha1 : coeff 1 (A ()) = 1 := by simpa [seed, coeff_X_pow, coeff_X] using ha () 1 (by omega)
  have ha2 : coeff 2 (A ()) = 1 := by simpa [seed, coeff_X_pow, coeff_X] using ha () 2 (by omega)
  have haeq : Eq389472 (A ()) := by
    apply PowerSeries.ext
    intro m
    by_cases hsmall : m < 5
    · interval_cases m <;>
        norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Finset.sum_range_succ,
          mul_add, coeff_X_pow, coeff_X_pow_mul', ha0, ha1, ha2]
    · have hn : 3 ≤ m - 2 := by omega
      have hm : m - 2 + 2 = m := by omega
      have he := congrArg (coeff (m - 2)) (congrFun hfix ())
      dsimp only [Φ] at he
      rw [coeff_mk, ite_eq_right (by omega), hm] at he
      change coeff m ((A ()).subst h) = coeff m (X ^ 2 * (1 + A ()))
      rw [coeff_X_pow_mul', ite_eq_left (by omega), map_add, coeff_one,
        ite_eq_right (by omega), zero_add]
      exact he
  refine ⟨A (), ⟨ha2, haeq⟩, ?_⟩
  rintro B ⟨hb2, hb⟩
  have hb0 : coeff 0 B = 0 := by
    have he := congrArg (coeff 0) hb
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Finset.sum_range_succ] at he
    simpa only [coeff_zero_eq_constantCoeff_apply] using he
  have hb1 : coeff 1 B = 1 := by
    have he := congrArg (coeff 2) hb
    norm_num [h, coeff_subst_range _ _ h0, coeff_h389472_pow, Finset.sum_range_succ,
      coeff_X_pow_mul', hb0] at he
    simpa only [← coeff_zero_eq_constantCoeff_apply, hb0, add_zero] using he
  let G : Unit → PowerSeries ℤ := fun _ => B
  have hgnorm : Jet 3 G seed := by
    intro i j hj
    interval_cases j <;> simp [G, seed, coeff_X_pow, coeff_X, hb0, hb1, hb2]
  have hgfix : Φ G = G := by
    funext i
    apply PowerSeries.ext
    intro n
    dsimp only [Φ, G]
    rw [coeff_mk]
    by_cases hlow : n < 3
    · rw [ite_eq_left hlow]
      exact (hgnorm () n hlow).symm
    · rw [ite_eq_right hlow]
      have he := congrArg (coeff (n + 2)) hb
      change coeff (n + 2) (B.subst h) = coeff (n + 2) (X ^ 2 * (1 + B)) at he
      rw [coeff_X_pow_mul', ite_eq_left (by omega), show n + 2 - 2 = n by omega,
        map_add, coeff_one, ite_eq_right (by omega), zero_add] at he
      exact he
  exact congrFun (huniq G ⟨hgnorm, hgfix⟩) ()

end BackfillPaper2.ExistenceA389472
#print axioms BackfillPaper2.ExistenceA389472.check_EX_A389472
