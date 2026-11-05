import Mathlib

/-! Small integer divisibility and relative-side norm transports.
No graph enumeration or additional integrality premise is introduced into
an original graph theorem by these generic helpers. -/
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace Paper7IntroIntegerPerron

theorem prime_scaled_coordinate_integral
    (p : ℤ) (hp : Prime p) (x : ℝ)
    (hx : ∃ k : ℤ, (p : ℝ) * x = k)
    (hxx : ∃ h : ℤ, (p : ℝ) * x ^ 2 = h) :
    ∃ z : ℤ, x = z := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨h, hh⟩ := hxx
  have hsq := congrArg (fun t : ℝ => t ^ 2) hk
  have hh' := congrArg (fun t : ℝ => (p : ℝ) * t) hh
  have he : (k : ℝ) ^ 2 = (p : ℝ) * (h : ℝ) := by
    nlinarith only [hsq, hh']
  have hei : k ^ 2 = p * h := by exact_mod_cast he
  have hpk : p ∣ k := hp.dvd_of_dvd_pow (show p ∣ k ^ 2 from ⟨h, hei⟩)
  obtain ⟨z, hz⟩ := hpk
  have hzr : (k : ℝ) = (p : ℝ) * (z : ℝ) := by exact_mod_cast hz
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  refine ⟨z, ?_⟩
  exact mul_left_cancel₀ hp0 (hk.trans hzr)
#print axioms Paper7IntroIntegerPerron.prime_scaled_coordinate_integral

theorem two_thirds_coordinate_three_integral
    (x : ℝ) (hx : ∃ k : ℤ, 2 * x = 3 * (k : ℝ))
    (hxx : ∃ h : ℤ, 2 * x ^ 2 = h) :
    ∃ z : ℤ, x = 3 * (z : ℝ) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨h, hh⟩ := hxx
  have hsq := congrArg (fun t : ℝ => t ^ 2) hk
  have he : (9 : ℝ) * (k : ℝ) ^ 2 = 2 * (h : ℝ) := by
    nlinarith only [hsq, hh]
  have hei : (9 : ℤ) * k ^ 2 = 2 * h := by exact_mod_cast he
  have hpow : (2 : ℤ) ∣ k ^ 2 := by
    have hd : (2 : ℤ) ∣ 9 * k ^ 2 := ⟨h, hei⟩
    exact (Int.prime_two.dvd_or_dvd hd).resolve_left (by norm_num)
  obtain ⟨z, hz⟩ := Int.prime_two.dvd_of_dvd_pow hpow
  have hzr : (k : ℝ) = 2 * (z : ℝ) := by exact_mod_cast hz
  exact ⟨z, by linarith only [hk, hzr]⟩
#print axioms Paper7IntroIntegerPerron.two_thirds_coordinate_three_integral

theorem relative_sign_square_sums
    {V : Type} [Fintype V] (eps f : V → ℝ) (l : V) (N : ℝ)
    (hl : eps l = 1 ∨ eps l = -1)
    (hp : (∑ v, if eps v = 1 then f v ^ 2 else 0) = N / 2)
    (hn : (∑ v, if eps v = -1 then f v ^ 2 else 0) = N / 2) :
    (∑ v, if eps v = eps l then f v ^ 2 else 0) = N / 2 ∧
      (∑ v, if eps v = -eps l then f v ^ 2 else 0) = N / 2 := by
  rcases hl with hl | hl
  · simpa only [hl] using And.intro hp hn
  · simpa only [hl, neg_neg] using And.intro hn hp
#print axioms Paper7IntroIntegerPerron.relative_sign_square_sums

end Paper7IntroIntegerPerron
