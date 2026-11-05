import Research.Backfill.Paper7.Lemma24Counting
import Research.Backfill.Paper7.SunTheta

/-! A real spectral-moment obstruction for bare cycles; no positive-pendant
assumption and no bounded parameter enumeration is used. -/
set_option autoImplicit false
noncomputable section
namespace Paper7Normalize
open BackfillPaper7.Challenge

theorem large_quartic_ge_three_square (s : Multiset ℝ)
    (hs : ∀ x ∈ s, 2 ≤ |x|) :
    3*(s.map (fun x => x^2)).sum ≤ (s.map (fun x => x^2*(x^2-1))).sum := by
  have h := Multiset.sum_map_le_sum_map (fun x : ℝ => 3*x^2)
    (fun x => x^2*(x^2-1)) (s := s) (fun x hx => by
      have ha := hs x hx
      have h4 : 4 ≤ x^2 := by nlinarith [sq_abs x, sq_nonneg (|x|-2)]
      have hp := mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h4)
      nlinarith)
  simpa only [Multiset.sum_map_mul_left] using h
#print axioms Paper7Normalize.large_quartic_ge_three_square

theorem bare_cycle_not_integral (b : ℕ) (hb : 7 ≤ b) :
    ¬ IsIntegralGraph (SG b (fun _ => 0) (fun _ => 0)) := by
  intro hG
  have hb3 : 3 ≤ b := by omega
  have hb4 : b ≠ 4 := by omega
  have hlow := Paper7Admissible.lemma24_big_square_lower b
    (fun _ => 0) (fun _ => 0) hb3 hG
  simp only [Finset.sum_const_zero, zero_add, Nat.cast_zero] at hlow
  have hquartic := Paper7SunMoments.sg_big_quartic_moment b
    (fun _ => 0) (fun _ => 0) hb3 hG
  have htheta : Theta (SG b (fun _ => 0) (fun _ => 0)) = 2*(b : ℤ) := by
    rw [Paper7Setup.sg_theta b (fun _ => 0) (fun _ => 0) hb3]
    simp [thetaV, mul_comm]
  rw [htheta] at hquartic
  push_cast at hquartic
  simp only [ite_eq_right hb4, mul_zero, add_zero] at hquartic
  have hlarge := large_quartic_ge_three_square
    (bigEigs (SG b (fun _ => 0) (fun _ => 0)))
    (fun _ hx => (Multiset.mem_filter.mp hx).2)
  have hbR : (7 : ℝ) ≤ b := by exact_mod_cast hb
  linarith
#print axioms Paper7Normalize.bare_cycle_not_integral

end Paper7Normalize
