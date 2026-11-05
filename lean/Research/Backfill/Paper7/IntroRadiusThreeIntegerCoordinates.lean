import Research.Backfill.Paper7.IntroPrimeScaledCoordinates
import Research.Backfill.Paper7.IntroRadiusThreeProjectorAlgebra

/-! The integer matrix entries apply to the same supplied normalized
Perron witness. Sides are always relative to the selected anchor sign. -/
set_option autoImplicit false
noncomputable section
open scoped Classical Matrix BigOperators

namespace Paper7IntroIntegerPerron
open Matrix SimpleGraph Paper7IntroProjectors

theorem radius_three_norm360_integer_coordinates
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eps f : V → ℝ) (l : V)
    (hs : ∀ v, eps v = 1 ∨ eps v = -1) (hf : ∀ v, 0 < f v)
    (hl : f l = 1) (hN : (f ⬝ᵥ f) = 360)
    (hproj : ∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
        (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
      radiusThreeT (G.adjMatrix ℝ) u v =
        (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v))
    (hp : (∑ v, if eps v = 1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2)
    (hn : (∑ v, if eps v = -1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2) :
    ∃ z : V → ℤ, (∀ v, 0 < z v) ∧
      (∀ v, eps v = eps l → f v = (z v : ℝ)) ∧
      (∀ v, eps v = -eps l → f v = 3 * (z v : ℝ)) ∧
      (∑ v, if eps v = eps l then z v ^ 2 else 0) = 180 ∧
      (∑ v, if eps v = -eps l then z v ^ 2 else 0) = 20 := by
  have hdiag (v : V) : ∃ h : ℤ, 2 * f v ^ 2 = h := by
    obtain ⟨h, hh⟩ := (radiusThreeST_integer_entries G v v).1
    have he : eps v * eps v = 1 := by
      rcases hs v with he | he <;> rw [he] <;> norm_num
    have hv := (hproj v v).1
    rw [hN, he] at hv
    norm_num at hv
    exact ⟨h, by nlinarith only [hv, hh]⟩
  have hpoint (v : V) : ∃ k : ℤ,
      0 < k ∧ (eps v = eps l → f v = (k : ℝ)) ∧
        (eps v = -eps l → f v = 3 * (k : ℝ)) := by
    by_cases he : eps v = eps l
    · have heprod : eps v * eps l = 1 := by
        rw [he]
        rcases hs l with hh | hh <;> rw [hh] <;> norm_num
      obtain ⟨k, hk⟩ := (radiusThreeST_integer_entries G v l).1
      have hv := (hproj v l).1
      rw [hN, hl, heprod] at hv
      norm_num at hv
      obtain ⟨z, hz⟩ := prime_scaled_coordinate_integral 2 Int.prime_two (f v)
        ⟨k, by norm_num; linarith only [hv, hk]⟩ (hdiag v)
      have hzpos : (0 : ℝ) < z := by rw [← hz]; exact hf v
      refine ⟨z, by exact_mod_cast hzpos, fun _ => hz, ?_⟩
      intro hop
      exfalso
      rcases hs l with hh | hh <;> rw [he, hh] at hop <;> norm_num at hop
    · have hop : eps v = -eps l := by
        rcases hs v with hv | hv
        · rcases hs l with hl' | hl'
          · exact (he (hv.trans hl'.symm)).elim
          · norm_num only [hv, hl']
        · rcases hs l with hl' | hl'
          · norm_num only [hv, hl']
          · exact (he (hv.trans hl'.symm)).elim
      have heprod : eps v * eps l = -1 := by
        rw [hop]
        rcases hs l with hh | hh <;> rw [hh] <;> norm_num
      obtain ⟨k, hk⟩ := (radiusThreeST_integer_entries G v l).2
      have hv := (hproj v l).2
      rw [hN, hl, heprod] at hv
      norm_num at hv
      obtain ⟨z, hz⟩ := two_thirds_coordinate_three_integral (f v)
        ⟨k, by linarith only [hv, hk]⟩ (hdiag v)
      have hzpos : (0 : ℝ) < z := by linarith only [hf v, hz]
      exact ⟨z, by exact_mod_cast hzpos, fun hh => (he hh).elim, fun _ => hz⟩
  choose z hzpos hsame hopp using hpoint
  obtain ⟨hu, hw⟩ := relative_sign_square_sums eps f l (f ⬝ᵥ f) (hs l) hp hn
  rw [hN] at hu hw
  norm_num at hu hw
  have heqU : (∑ v, if eps v = eps l then f v ^ 2 else 0) =
      ∑ v, if eps v = eps l then (z v : ℝ) ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases he : eps v = eps l
    · simp only [he, ite_true, hsame v he]
    · simp only [he, ite_false]
  have heqW : (∑ v, if eps v = -eps l then f v ^ 2 else 0) =
      9 * ∑ v, if eps v = -eps l then (z v : ℝ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _hv
    by_cases he : eps v = -eps l
    · simp only [he, ite_true, hopp v he]
      ring
    · simp only [he, ite_false, mul_zero]
  have huR : (∑ v, if eps v = eps l then (z v : ℝ) ^ 2 else 0) = 180 := by
    linarith only [hu, heqU]
  have hwR : (∑ v, if eps v = -eps l then (z v : ℝ) ^ 2 else 0) = 20 := by
    linarith only [hw, heqW]
  exact ⟨z, hzpos, hsame, hopp, by exact_mod_cast huR, by exact_mod_cast hwR⟩
#print axioms Paper7IntroIntegerPerron.radius_three_norm360_integer_coordinates

theorem radius_three_norm240_integer_coordinates
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (eps f : V → ℝ) (l : V)
    (hs : ∀ v, eps v = 1 ∨ eps v = -1) (hf : ∀ v, 0 < f v)
    (hl : f l = 1) (hN : (f ⬝ᵥ f) = 240)
    (hproj : ∀ u v, radiusThreeS (G.adjMatrix ℝ) u v =
        (360 / (f ⬝ᵥ f)) * f u * f v * (1 + eps u * eps v) ∧
      radiusThreeT (G.adjMatrix ℝ) u v =
        (120 / (f ⬝ᵥ f)) * f u * f v * (1 - eps u * eps v))
    (hp : (∑ v, if eps v = 1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2)
    (hn : (∑ v, if eps v = -1 then f v ^ 2 else 0) = (f ⬝ᵥ f) / 2) :
    ∃ z : V → ℤ, (∀ v, 0 < z v) ∧ (∀ v, f v = (z v : ℝ)) ∧
      (∑ v, if eps v = eps l then z v ^ 2 else 0) = 120 ∧
      (∑ v, if eps v = -eps l then z v ^ 2 else 0) = 120 := by
  have hpoint (v : V) : ∃ k : ℤ, f v = k := by
    by_cases he : eps v = eps l
    · have heprod : eps v * eps l = 1 := by
        rw [he]
        rcases hs l with hh | hh <;> rw [hh] <;> norm_num
      obtain ⟨k, hk⟩ := (radiusThreeST_integer_entries G v l).1
      obtain ⟨h, hh⟩ := (radiusThreeST_integer_entries G v v).1
      have hv := (hproj v l).1
      rw [hN, hl, heprod] at hv
      norm_num at hv
      have hev : eps v * eps v = 1 := by
        rcases hs v with hh' | hh' <;> rw [hh'] <;> norm_num
      have hd := (hproj v v).1
      rw [hN, hev] at hd
      norm_num at hd
      exact prime_scaled_coordinate_integral 3 Int.prime_three (f v)
        ⟨k, by norm_num; linarith only [hv, hk]⟩
        ⟨h, by norm_num; nlinarith only [hd, hh]⟩
    · have hop : eps v = -eps l := by
        rcases hs v with hv | hv
        · rcases hs l with hl' | hl'
          · exact (he (hv.trans hl'.symm)).elim
          · norm_num only [hv, hl']
        · rcases hs l with hl' | hl'
          · norm_num only [hv, hl']
          · exact (he (hv.trans hl'.symm)).elim
      have heprod : eps v * eps l = -1 := by
        rw [hop]
        rcases hs l with hh | hh <;> rw [hh] <;> norm_num
      obtain ⟨k, hk⟩ := (radiusThreeST_integer_entries G v l).2
      have hv := (hproj v l).2
      rw [hN, hl, heprod] at hv
      norm_num at hv
      exact ⟨k, by linarith only [hv, hk]⟩
  choose z hz using hpoint
  have hzpos (v : V) : 0 < z v := by
    have hr : (0 : ℝ) < z v := by rw [← hz v]; exact hf v
    exact_mod_cast hr
  obtain ⟨hu, hw⟩ := relative_sign_square_sums eps f l (f ⬝ᵥ f) (hs l) hp hn
  rw [hN] at hu hw
  simp_rw [hz] at hu hw
  norm_num at hu hw
  exact ⟨z, hzpos, hz, by exact_mod_cast hu, by exact_mod_cast hw⟩
#print axioms Paper7IntroIntegerPerron.radius_three_norm240_integer_coordinates

end Paper7IntroIntegerPerron
