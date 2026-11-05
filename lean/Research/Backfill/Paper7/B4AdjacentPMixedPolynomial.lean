import Research.Backfill.Paper7.B4MixedPolynomial

/-! Source-only scalar reduction for two adjacent positive P sites.
The zero of the reduced polynomial will lie strictly between 0 and 1. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge

def adjacentLocalPolynomial (a q : ℕ) (t : ℝ) : ℝ :=
  2*t^2-((a : ℝ)+q+2)*t+a
#print axioms Paper7B4Analytic.adjacentLocalPolynomial

def adjacentPMixedPolynomial (p q : Fin 4 → ℕ) (t : ℝ) : ℝ :=
  t*mixedLocalPolynomial (p 0) (q 0) t*mixedLocalPolynomial (p 1) (q 1) t*
      (t-q 2-1)*(t-q 3-1)-
    (t-1)^2*((mixedLocalPolynomial (p 0) (q 0) t+t*(t-q 2-1))*
      (mixedLocalPolynomial (p 1) (q 1) t+t*(t-q 3-1)))
#print axioms Paper7B4Analytic.adjacentPMixedPolynomial

theorem adjacent_p_mixed_factor (p q : Fin 4 → ℕ)
    (hp2 : p 2 = 0) (hp3 : p 3 = 0) (t : ℝ) :
    mixedPolynomial p q t = t*adjacentPMixedPolynomial p q t := by
  unfold mixedPolynomial adjacentPMixedPolynomial mixedLocalPolynomial
  rw [hp2,hp3]
  norm_num
  ring
#print axioms Paper7B4Analytic.adjacent_p_mixed_factor

theorem adjacent_p_pair_zero (p q : Fin 4 → ℕ) (t : ℝ) :
    mixedLocalPolynomial (p 0) (q 0) t+t*(t-q 2-1) =
      adjacentLocalPolynomial (p 0) (q 0+q 2) t := by
  unfold mixedLocalPolynomial adjacentLocalPolynomial
  push_cast
  ring
#print axioms Paper7B4Analytic.adjacent_p_pair_zero

theorem adjacent_p_pair_one (p q : Fin 4 → ℕ) (t : ℝ) :
    mixedLocalPolynomial (p 1) (q 1) t+t*(t-q 3-1) =
      adjacentLocalPolynomial (p 1) (q 1+q 3) t := by
  unfold mixedLocalPolynomial adjacentLocalPolynomial
  push_cast
  ring
#print axioms Paper7B4Analytic.adjacent_p_pair_one

end Paper7B4Analytic
