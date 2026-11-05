import Research.Backfill.Paper7.B4MonodromyRigidity

/-! Source-only polynomial for the entire pure-Q four-cycle family.
Every root used below is connected to the actual adjacency spectrum. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge
open scoped BigOperators Matrix Classical

def pureQPolynomial (a b c d t : ℝ) : ℝ :=
  t*(t-a-1)*(t-b-1)*(t-c-1)*(t-d-1)-
    (t-1)^2*(2*t-a-c-2)*(2*t-b-d-2)
#print axioms Paper7B4Analytic.pureQPolynomial

def pureQThreePolynomial (a b c t : ℝ) : ℝ :=
  t*(t-a-1)*(t-b-1)*(t-c-1)-
    (t-1)*(2*t-a-c-2)*(2*t-b-2)
#print axioms Paper7B4Analytic.pureQThreePolynomial

theorem pure_q_trace_identity (a b c d m : ℝ) (hm : m^2-1 ≠ 0) :
    (m^2-1)^4*((realFourProduct (m-a*m/(m^2-1)) (m-b*m/(m^2-1))
      (m-c*m/(m^2-1)) (m-d*m/(m^2-1))).trace-2) =
      m^2*pureQPolynomial a b c d (m^2) := by
  rw [real_four_trace]
  unfold pureQPolynomial
  field_simp [hm]
  ring
#print axioms Paper7B4Analytic.pure_q_trace_identity

theorem pure_q_ordinary_spec_iff (q : Fin 4 → ℕ) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 (fun _ => 0) q) ↔
      pureQPolynomial (q 0) (q 1) (q 2) (q 3) (m^2) = 0 := by
  have hd : m^2-1 ≠ 0 := by
    intro hh
    have hh' : (m-1)*(m+1) = 0 := by nlinarith only [hh]
    rcases mul_eq_zero.mp hh' with h | h
    · exact hm1 (by linarith)
    · exact hmn (by linarith)
  have he : (m^2-1)^4*((Mono 4 (fun _ => 0) q m).trace-2) =
      m^2*pureQPolynomial (q 0) (q 1) (q 2) (q 3) (m^2) := by
    rw [mono_four_product]
    simpa [fk] using pure_q_trace_identity (q 0) (q 1) (q 2) (q 3) m hd
  rw [← ordinary_trace_iff_spec (fun _ => 0) q m hmn hm0 hm1]
  constructor
  · intro ht
    rw [ht] at he
    have hz : m^2*pureQPolynomial (q 0) (q 1) (q 2) (q 3) (m^2) = 0 := by
      nlinarith only [he]
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 2 hm0)
  · intro hz
    rw [hz,mul_zero] at he
    have ht := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 4 hd)
    linarith
#print axioms Paper7B4Analytic.pure_q_ordinary_spec_iff

theorem pure_q_three_factor (a b c t : ℝ) :
    pureQPolynomial a b c 0 t = (t-1)*pureQThreePolynomial a b c t := by
  unfold pureQPolynomial pureQThreePolynomial
  ring
#print axioms Paper7B4Analytic.pure_q_three_factor

theorem pure_q_small_root_nonintegral (q : Fin 4 → ℕ) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1)
    (he : pureQPolynomial (q 0) (q 1) (q 2) (q 3) t = 0) :
    ¬ IsIntegralGraph (SG 4 (fun _ => 0) q) := by
  intro hG
  let s : ℝ := Real.sqrt t
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht0
  have hsq : s^2 = t := Real.sq_sqrt ht0.le
  have hs1 : s < 1 := by nlinarith
  have hpoly : pureQPolynomial (q 0) (q 1) (q 2) (q 3) (s^2) = 0 := by
    rw [hsq]; exact he
  have hmem := (pure_q_ordinary_spec_iff q s (by linarith) (by linarith)
    (by linarith)).mpr hpoly
  obtain ⟨z,hz⟩ := Paper7Moments.integral_spec_entry _ hG s hmem
  rw [hz] at hs0 hs1
  have hz0 : (0 : ℤ) < z := by exact_mod_cast hs0
  have hz1 : z < (1 : ℤ) := by exact_mod_cast hs1
  omega
#print axioms Paper7B4Analytic.pure_q_small_root_nonintegral

end Paper7B4Analytic
