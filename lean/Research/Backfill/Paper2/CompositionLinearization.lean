import Research.Backfill.Paper2.FiniteCoefficients

/-! First-order substitution differences over any commutative ring. -/
set_option autoImplicit false
noncomputable section
namespace BackfillPaper2.CompositionLinearization
open PowerSeries
variable {R : Type*} [CommRing R]

/-- `coeff m (H^d) = 0` for `d > m` when `H(0) = 0`. -/
private lemma coeff_pow_eq_zero {H : PowerSeries R} (hH0 : constantCoeff H = 0) {m d : ℕ} (hd : m < d) :
    coeff m (H ^ d) = 0 := by
  have : X ^ d ∣ H ^ d := pow_dvd_pow_of_dvd (X_dvd_iff.mpr hH0) d
  rw [X_pow_dvd_iff] at this
  exact this m hd

/-- For `d ≥ 2`, `X^(m+1) ∣ F1^d - F2^d` when `X^m ∣ F1 - F2` and both have zero constant
term. -/
private lemma pow_sub_pow_dvd {F1 F2 : PowerSeries R} (h1 : constantCoeff F1 = 0)
    (h2 : constantCoeff F2 = 0) {m d : ℕ} (hd : 2 ≤ d) (h : X ^ m ∣ F1 - F2) :
    X ^ (m + 1) ∣ F1 ^ d - F2 ^ d := by
  rw [← geom_sum₂_mul, pow_succ, mul_comm (∑ i ∈ Finset.range d, F1 ^ i * F2 ^ (d - 1 - i))]
  refine mul_dvd_mul h (Finset.dvd_sum fun i hi => ?_)
  rw [Finset.mem_range] at hi
  by_cases hi0 : i = 0
  · subst hi0
    rw [pow_zero, one_mul]
    exact dvd_pow (X_dvd_iff.mpr h2) (by omega)
  · exact dvd_mul_of_dvd_left (dvd_pow (X_dvd_iff.mpr h1) hi0) _

/-- Linearization: if `F1 ≡ F2 (mod X^m)` (`m ≥ 1`), then
`[x^m] G(F1) - [x^m] G(F2) = [x^1] G * ([x^m] F1 - [x^m] F2)`. -/
private theorem coeff_subst_sub (G F1 F2 : PowerSeries R) (h1 : constantCoeff F1 = 0)
    (h2 : constantCoeff F2 = 0) {m : ℕ} (hm : 1 ≤ m) (h : X ^ m ∣ F1 - F2) :
    coeff m (G.subst F1) - coeff m (G.subst F2) = coeff 1 G * (coeff m F1 - coeff m F2) := by
  have hs1 : HasSubst F1 := HasSubst.of_constantCoeff_zero' h1
  have hs2 : HasSubst F2 := HasSubst.of_constantCoeff_zero' h2
  rw [coeff_subst' hs1, coeff_subst' hs2]
  have sup : ∀ F : PowerSeries R, constantCoeff F = 0 →
      (Function.support fun d => coeff d G • coeff m (F ^ d)) ⊆ (Finset.range (m + 1) : Set ℕ) := by
    intro F hF d hd
    simp only [Function.mem_support, Finset.coe_range, Set.mem_Iio] at hd ⊢
    by_contra hlt
    exact hd (by rw [coeff_pow_eq_zero hF (by omega), smul_zero])
  rw [finsum_eq_sum_of_support_subset _ (sup F1 h1), finsum_eq_sum_of_support_subset _ (sup F2 h2),
    ← Finset.sum_sub_distrib, Finset.sum_eq_single 1]
  · simp [smul_eq_mul, mul_sub]
  · intro d _ hd1
    rw [← smul_sub]
    rcases Nat.lt_or_ge d 2 with hd2 | hd2
    · have : d = 0 := by omega
      subst this
      simp
    · have hdv := pow_sub_pow_dvd h1 h2 hd2 h
      rw [X_pow_dvd_iff] at hdv
      rw [← map_sub, hdv m (by omega), smul_zero]
  · intro h1m
    exfalso; exact h1m (Finset.mem_range.mpr (by omega))


theorem inner_difference (G F H : PowerSeries R) (hF : constantCoeff F = 0)
    (hH : constantCoeff H = 0) (n : ℕ) (hn : 1 ≤ n) (hd : X ^ n ∣ F - H) :
    X ^ (n + 1) ∣ (G.subst F - G.subst H) - C (coeff 1 G) * (F - H) := by
  have hbase := XadicAlgebra.subst_congr_right G F H
    (HasSubst.of_constantCoeff_zero' hF) (HasSubst.of_constantCoeff_zero' hH) n hd
  have hlin := coeff_subst_sub G F H hF hH hn hd
  rw [X_pow_dvd_iff] at hd hbase ⊢
  intro m hm
  by_cases hmn : m < n
  · rw [map_sub, hbase m hmn, coeff_C_mul, hd m hmn, mul_zero, sub_self]
  · have hmn : m = n := by omega
    subst m
    simp only [map_sub, coeff_C_mul]
    exact sub_eq_zero.mpr hlin

theorem self_difference (F G : PowerSeries R) (hF0 : constantCoeff F = 0)
    (hG0 : constantCoeff G = 0) (hF1 : coeff 1 F = 1) (hG1 : coeff 1 G = 1)
    (n : ℕ) (hn : 1 ≤ n) (hd : X ^ n ∣ F - G) :
    X ^ (n + 1) ∣ (F.subst F - G.subst G) - 2 * (F - G) := by
  have hs := HasSubst.of_constantCoeff_zero' hF0
  have ho := XadicAlgebra.subst_near_id (F - G) F hF0 hF1 n hd
  have hi := inner_difference G F G hF0 hG0 n hn hd
  rw [hG1, map_one, one_mul] at hi
  have he : (F.subst F - G.subst G) - 2 * (F - G) =
      ((F - G).subst F - (F - G)) + ((G.subst F - G.subst G) - (F - G)) := by
    rw [subst_sub hs]
    ring
  rw [he]
  exact dvd_add ho hi

end BackfillPaper2.CompositionLinearization
#print axioms BackfillPaper2.CompositionLinearization.inner_difference
#print axioms BackfillPaper2.CompositionLinearization.self_difference
