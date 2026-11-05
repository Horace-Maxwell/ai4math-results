import Research.Backfill.Paper7.B4MonodromyRigidity

/-! Source-only polynomial-to-spectrum bridge for arbitrary p and q on C4.
The four transfer entries are cleared separately before the trace identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Matrix Classical

def mixedLocalPolynomial (p q : ℕ) (t : ℝ) : ℝ :=
  t^2-((p : ℝ)+q+1)*t+p
#print axioms Paper7B4Analytic.mixedLocalPolynomial

def mixedPolynomial (p q : Fin 4 → ℕ) (t : ℝ) : ℝ :=
  mixedLocalPolynomial (p 0) (q 0) t * mixedLocalPolynomial (p 1) (q 1) t *
    mixedLocalPolynomial (p 2) (q 2) t * mixedLocalPolynomial (p 3) (q 3) t -
  t*(t-1)^2*(mixedLocalPolynomial (p 0) (q 0) t + mixedLocalPolynomial (p 2) (q 2) t)*
    (mixedLocalPolynomial (p 1) (q 1) t + mixedLocalPolynomial (p 3) (q 3) t)
#print axioms Paper7B4Analytic.mixedPolynomial

theorem scaled_four_trace (a b c d z : ℝ) (hz : z ≠ 0) :
    z^4*((realFourProduct (a/z) (b/z) (c/z) (d/z)).trace-2) =
      a*b*c*d-z^2*(a+c)*(b+d) := by
  rw [real_four_trace]
  field_simp [hz]
  ring
#print axioms Paper7B4Analytic.scaled_four_trace

theorem mixed_transfer_fraction (p q : Fin 4 → ℕ) (m : ℝ)
    (hm0 : m ≠ 0) (hmden : m^2-1 ≠ 0) (i : Fin 4) :
    m-fk 4 p q m i = mixedLocalPolynomial (p i) (q i) (m^2)/(m*(m^2-1)) := by
  unfold fk mixedLocalPolynomial
  field_simp [hm0,hmden]
  ring
#print axioms Paper7B4Analytic.mixed_transfer_fraction

theorem mixed_trace_identity (p q : Fin 4 → ℕ) (m : ℝ)
    (hm0 : m ≠ 0) (hmden : m^2-1 ≠ 0) :
    (m*(m^2-1))^4*((Mono 4 p q m).trace-2) = mixedPolynomial p q (m^2) := by
  have hz : m*(m^2-1) ≠ 0 := mul_ne_zero hm0 hmden
  rw [mono_four_product,
    mixed_transfer_fraction p q m hm0 hmden 0,
    mixed_transfer_fraction p q m hm0 hmden 1,
    mixed_transfer_fraction p q m hm0 hmden 2,
    mixed_transfer_fraction p q m hm0 hmden 3]
  have he := scaled_four_trace
    (mixedLocalPolynomial (p 0) (q 0) (m^2)) (mixedLocalPolynomial (p 1) (q 1) (m^2))
    (mixedLocalPolynomial (p 2) (q 2) (m^2)) (mixedLocalPolynomial (p 3) (q 3) (m^2))
    (m*(m^2-1)) hz
  simpa only [mixedPolynomial,mul_pow] using he
#print axioms Paper7B4Analytic.mixed_trace_identity

theorem mixed_ordinary_spec_iff (p q : Fin 4 → ℕ) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 p q) ↔ mixedPolynomial p q (m^2) = 0 := by
  have hmden : m^2-1 ≠ 0 := by
    intro h
    have hprod : (m-1)*(m+1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hprod with hpos | hneg
    · exact hm1 (by linarith only [hpos])
    · exact hmn (by linarith only [hneg])
  have hz : m*(m^2-1) ≠ 0 := mul_ne_zero hm0 hmden
  have he := mixed_trace_identity p q m hm0 hmden
  rw [← ordinary_trace_iff_spec p q m hmn hm0 hm1]
  constructor
  · intro ht
    rw [ht,sub_self,mul_zero] at he
    exact he.symm
  · intro hpoly
    rw [hpoly] at he
    have ht := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 4 hz)
    linarith only [ht]
#print axioms Paper7B4Analytic.mixed_ordinary_spec_iff

end Paper7B4Analytic
