import Research.Backfill.Paper2.CompositionLinearization

/-! Normalized self-composition has linear coefficient 2; subtracting it is triangular. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.ExistenceA120566
open PowerSeries BackfillPaper2.Challenge BackfillPaper2.XadicFixedPoint

private theorem full_congr (F G H I : PowerSeries ℤ) (hH : constantCoeff H = 0)
    (hI : constantCoeff I = 0) (n : ℕ) (hFG : X ^ n ∣ F - G) (hHI : X ^ n ∣ H - I) :
    X ^ n ∣ F.subst H - G.subst I := by
  have he : F.subst H - G.subst I =
      (F.subst H - G.subst H) + (G.subst H - G.subst I) := by ring
  rw [he]
  exact dvd_add (XadicAlgebra.subst_congr_left F G H hH n hFG)
    (XadicAlgebra.subst_congr_right G H I (HasSubst.of_constantCoeff_zero' hH)
      (HasSubst.of_constantCoeff_zero' hI) n hHI)

theorem check_EX_A120566 : EX_A120566 := by
  let seed : Unit → PowerSeries ℤ := fun _ => X
  let Φ : PowerSeries ℤ → PowerSeries ℤ := fun A =>
    2 * A - A.subst A + X * A.subst (A.subst A)
  let Ψ : (Unit → PowerSeries ℤ) → Unit → PowerSeries ℤ := fun A _ => Φ (A ())
  have norm : ∀ A : Unit → PowerSeries ℤ, Jet 2 A seed →
      constantCoeff (A ()) = 0 ∧ coeff 1 (A ()) = 1 := by
    intro A ha
    constructor
    · simpa only [seed, coeff_zero_eq_constantCoeff_apply, constantCoeff_X] using ha () 0 (by omega)
    · simpa [seed, coeff_X] using ha () 1 (by omega)
  have hp : ∀ A, Jet 2 A seed → Jet 2 (Ψ A) seed := by
    intro A ha i j hj
    obtain ⟨ha0, ha1⟩ := norm A ha
    have haa0 : constantCoeff ((A ()).subst (A ())) = 0 := constantCoeff_subst_eq_zero ha0 (A ()) ha0
    have haaa0 : constantCoeff ((A ()).subst ((A ()).subst (A ()))) = 0 :=
      constantCoeff_subst_eq_zero haa0 (A ()) ha0
    have haa1 : coeff 1 ((A ()).subst (A ())) = 1 := by
      rw [FiniteCoefficients.coeff_subst_range _ _ ha0]
      simp [Finset.sum_range_succ, coeff_zero_eq_constantCoeff_apply, ha0, ha1]
    interval_cases j
    · simp [Ψ, Φ, seed, coeff_zero_eq_constantCoeff_apply, ha0, haa0]
    · change coeff (0 + 1) (Φ (A ())) = coeff 1 (X : PowerSeries ℤ)
      simp [Φ, map_add, map_sub, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply,
        ha1, haa1, haaa0]
  have hc : ∀ n, 2 ≤ n → ∀ A B, Jet 2 A seed → Jet 2 B seed →
      Jet n A B → Jet (n + 1) (Ψ A) (Ψ B) := by
    intro n hn A B ha hb hab
    obtain ⟨ha0, ha1⟩ := norm A ha
    obtain ⟨hb0, hb1⟩ := norm B hb
    have hd : X ^ n ∣ A () - B () := by
      rw [X_pow_dvd_iff]
      intro j hj
      rw [map_sub, hab () j hj, sub_self]
    have hself := CompositionLinearization.self_difference (A ()) (B ()) ha0 hb0 ha1 hb1 n (by omega) hd
    have hd2 : X ^ n ∣ (A ()).subst (A ()) - (B ()).subst (B ()) :=
      full_congr _ _ _ _ ha0 hb0 n hd hd
    have haa0 : constantCoeff ((A ()).subst (A ())) = 0 := constantCoeff_subst_eq_zero ha0 (A ()) ha0
    have hbb0 : constantCoeff ((B ()).subst (B ())) = 0 := constantCoeff_subst_eq_zero hb0 (B ()) hb0
    have hd3 : X ^ n ∣ (A ()).subst ((A ()).subst (A ())) -
        (B ()).subst ((B ()).subst (B ())) := full_congr _ _ _ _ haa0 hbb0 n hd hd2
    have hx : X ^ (n + 1) ∣ X * ((A ()).subst ((A ()).subst (A ())) -
        (B ()).subst ((B ()).subst (B ()))) := by
      rw [pow_succ']
      exact mul_dvd_mul_left X hd3
    have he : Φ (A ()) - Φ (B ()) =
        -(((A ()).subst (A ()) - (B ()).subst (B ())) - 2 * (A () - B ())) +
        X * ((A ()).subst ((A ()).subst (A ())) - (B ()).subst ((B ()).subst (B ()))) := by
      dsimp only [Φ]
      ring
    have ht : X ^ (n + 1) ∣ Φ (A ()) - Φ (B ()) := by
      rw [he]
      exact dvd_add ((dvd_neg).mpr hself) hx
    rw [X_pow_dvd_iff] at ht
    intro i j hj
    have hz := ht j hj
    rw [map_sub, sub_eq_zero] at hz
    exact hz
  obtain ⟨A, ⟨ha, hfix⟩, huniq⟩ := existsUnique_fixed_seed 2 seed Ψ hp hc
  obtain ⟨ha0, ha1⟩ := norm A ha
  have hA : Φ (A ()) = A () := congrFun hfix ()
  have hAeq : Eq120566 (A ()) := by
    change A () = (A ()).subst (A ()) - X * (A ()).subst ((A ()).subst (A ()))
    dsimp only [Φ] at hA
    linear_combination hA
  refine ⟨A (), ⟨ha0, ha1, hAeq⟩, ?_⟩
  rintro B ⟨hb0, hb1, hb⟩
  let G : Unit → PowerSeries ℤ := fun _ => B
  have hgn : Jet 2 G seed := by
    intro i j hj
    interval_cases j <;> simp [G, seed, coeff_zero_eq_constantCoeff_apply, hb0, hb1]
  have hgf : Ψ G = G := by
    funext i
    change Φ B = B
    change B = B.subst B - X * B.subst (B.subst B) at hb
    dsimp only [Φ]
    linear_combination hb
  exact congrFun (huniq G ⟨hgn, hgf⟩) ()

end BackfillPaper2.ExistenceA120566
#print axioms BackfillPaper2.ExistenceA120566.check_EX_A120566
