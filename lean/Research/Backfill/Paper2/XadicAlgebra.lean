import Research.Backfill.Paper2.XadicFixedPoint

/-! Ring-valid x-adic congruence tools for the original existence contracts. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.XadicAlgebra
open PowerSeries
variable {R : Type*} [CommRing R]

/-- Composition respects congruences modulo `X^n` in the inner argument. -/
theorem subst_congr_right (F G1 G2 : PowerSeries R) (hG1 : HasSubst G1) (hG2 : HasSubst G2)
    (n : ℕ) (h : X ^ n ∣ G1 - G2) : X ^ n ∣ F.subst G1 - F.subst G2 := by
  rw [X_pow_dvd_iff]
  intro m hm
  rw [map_sub, sub_eq_zero, coeff_subst' hG1, coeff_subst' hG2]
  refine finsum_congr (fun d => ?_)
  have h' : X ^ n ∣ G1 ^ d - G2 ^ d := h.trans (sub_dvd_pow_sub_pow G1 G2 d)
  rw [X_pow_dvd_iff] at h'
  have := h' m hm
  rw [map_sub, sub_eq_zero] at this
  rw [this]


theorem subst_congr_left (F G H : PowerSeries R) (hH : constantCoeff H = 0)
    (n : ℕ) (h : X ^ n ∣ F - G) : X ^ n ∣ F.subst H - G.subst H := by
  have hs := HasSubst.of_constantCoeff_zero' hH
  obtain ⟨Q, hQ⟩ := h
  rw [← subst_sub hs, hQ, subst_mul hs, subst_pow hs, subst_X hs]
  exact dvd_mul_of_dvd_left (pow_dvd_pow_of_dvd (X_dvd_iff.mpr hH) n) _

theorem subst_near_id (G H : PowerSeries R) (h0 : constantCoeff H = 0) (h1 : coeff 1 H = 1)
    (n : ℕ) (hd : X ^ n ∣ G) : X ^ (n + 1) ∣ G.subst H - G := by
  have hs := HasSubst.of_constantCoeff_zero' h0
  obtain ⟨Q, hQ⟩ := hd
  obtain ⟨U, hU⟩ : (X : PowerSeries R) ∣ H := X_dvd_iff.mpr h0
  have hU0 : constantCoeff U = 1 := by
    have he := congrArg (coeff 1) hU
    rw [h1, show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul,
      coeff_zero_eq_constantCoeff_apply] at he
    exact he.symm
  have e1 : G.subst H = H ^ n * Q.subst H := by
    rw [hQ, subst_mul hs, subst_pow hs, subst_X hs]
  have e2 : G.subst H - G =
      X ^ n * ((U ^ n - 1) * Q.subst H + (Q.subst H - Q)) := by
    rw [e1, hQ, hU]; ring
  rw [e2, pow_succ]
  refine mul_dvd_mul_left _ (dvd_add (dvd_mul_of_dvd_left ?_ _) ?_)
  · rw [X_dvd_iff]; simp [hU0]
  · have hXH : (X : PowerSeries R) ^ 1 ∣ H - X := by
      rw [pow_one, X_dvd_iff]; simp [h0]
    have ht := subst_congr_right Q H X hs HasSubst.X' 1 hXH
    rw [X_subst, pow_one] at ht
    exact ht

theorem derivative_dvd (G : PowerSeries R) (n : ℕ) (h : X ^ (n + 1) ∣ G) :
    X ^ n ∣ derivative (R := R) G := by
  rw [X_pow_dvd_iff] at h ⊢
  intro i hi
  rw [coeff_derivative, h (i + 1) (by omega), zero_mul]

theorem jet_unit_iff_dvd (n : ℕ) (F G : PowerSeries R) :
    XadicFixedPoint.Jet n (fun _ : Unit => F) (fun _ : Unit => G) ↔ X ^ n ∣ F - G := by
  rw [X_pow_dvd_iff]
  constructor
  · intro h j hj
    rw [map_sub, h () j hj, sub_self]
  · intro h _ j hj
    have ht := h j hj
    rw [map_sub, sub_eq_zero] at ht
    exact ht

end BackfillPaper2.XadicAlgebra

#print axioms BackfillPaper2.XadicAlgebra.subst_congr_right
#print axioms BackfillPaper2.XadicAlgebra.subst_congr_left
#print axioms BackfillPaper2.XadicAlgebra.subst_near_id
#print axioms BackfillPaper2.XadicAlgebra.derivative_dvd
#print axioms BackfillPaper2.XadicAlgebra.jet_unit_iff_dvd
