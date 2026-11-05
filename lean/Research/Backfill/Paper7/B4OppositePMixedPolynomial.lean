import Research.Backfill.Paper7.B4SinglePMixedPolynomial

/-! Source-only scalar polynomial for opposite positive P sites and arbitrary Q. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge

def oppositePMixedPolynomial (a c u v s b : ℕ) (t : ℝ) : ℝ :=
  mixedLocalPolynomial a u t*mixedLocalPolynomial c v t*
    (t^2-((s : ℝ)+2)*t+b+s+1)-
  (t-1)^2*(mixedLocalPolynomial a u t+mixedLocalPolynomial c v t)*(2*t-s-2)
#print axioms Paper7B4Analytic.oppositePMixedPolynomial

theorem opposite_p_mixed_factor (p q : Fin 4 → ℕ)
    (hp1 : p 1 = 0) (hp3 : p 3 = 0) (t : ℝ) :
    mixedPolynomial p q t = t^2*
      oppositePMixedPolynomial (p 0) (p 2) (q 0) (q 2) (q 1+q 3) (q 1*q 3) t := by
  unfold mixedPolynomial oppositePMixedPolynomial mixedLocalPolynomial
  rw [hp1,hp3]
  push_cast
  ring
#print axioms Paper7B4Analytic.opposite_p_mixed_factor

theorem opposite_p_poly_zero (a c u v s b : ℕ) :
    oppositePMixedPolynomial a c u v s b 0 =
      (a : ℝ)*c*((b : ℝ)+s+1)+((a : ℝ)+c)*((s : ℝ)+2) := by
  unfold oppositePMixedPolynomial mixedLocalPolynomial
  ring
#print axioms Paper7B4Analytic.opposite_p_poly_zero

theorem opposite_p_poly_swap (a c u v s b : ℕ) (t : ℝ) :
    oppositePMixedPolynomial a c u v s b t = oppositePMixedPolynomial c a v u s b t := by
  unfold oppositePMixedPolynomial
  ring
#print axioms Paper7B4Analytic.opposite_p_poly_swap

end Paper7B4Analytic
