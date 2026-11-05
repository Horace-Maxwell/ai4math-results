import Research.Backfill.Paper7.B4MonodromyRigidity

/-! Source-only exact ordinary-root equation for p=0 and q supported at
the two opposite positions 0 and 2. Both loads remain arbitrary. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

def qoppositeCubic (a b t : ℝ) : ℝ :=
  t^3-(a+b+6)*t^2+(a*b+3*a+3*b+9)*t-2*a-2*b-4
#print axioms Paper7B4Analytic.qoppositeCubic

theorem qopposite_trace_identity (a b m : ℝ) (hmden : m^2-1 ≠ 0) :
    (m^2-1)^2*((realFourProduct (m-a*m/(m^2-1)) m
      (m-b*m/(m^2-1)) m).trace-2) = m^2*qoppositeCubic a b (m^2) := by
  rw [real_four_trace]
  unfold qoppositeCubic
  field_simp [hmden]
  ring
#print axioms Paper7B4Analytic.qopposite_trace_identity

theorem qopposite_ordinary_spec_iff (q : Fin 4 → ℕ)
    (hq1 : q 1 = 0) (hq3 : q 3 = 0) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 (fun _ => 0) q) ↔ qoppositeCubic (q 0) (q 2) (m^2) = 0 := by
  have hmden : m^2-1 ≠ 0 := by
    intro h
    have hprod : (m-1)*(m+1) = 0 := by nlinarith only [h]
    rcases mul_eq_zero.mp hprod with hpos | hneg
    · exact hm1 (by linarith only [hpos])
    · exact hmn (by linarith only [hneg])
  have he : (m^2-1)^2*((Mono 4 (fun _ => 0) q m).trace-2) =
      m^2*qoppositeCubic (q 0) (q 2) (m^2) := by
    rw [mono_four_product]
    simpa [fk,hq1,hq3] using qopposite_trace_identity (q 0) (q 2) m hmden
  rw [← ordinary_trace_iff_spec (fun _ => 0) q m hmn hm0 hm1]
  constructor
  · intro ht
    rw [ht,sub_self,mul_zero] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero 2 hm0)
  · intro hpoly
    rw [hpoly,mul_zero] at he
    have htrace := (mul_eq_zero.mp he).resolve_left (pow_ne_zero 2 hmden)
    linarith only [htrace]
#print axioms Paper7B4Analytic.qopposite_ordinary_spec_iff

theorem qopposite_cubic_single_factor (a b t : ℝ) (hab : a*b = 0) :
    qoppositeCubic a b t = (t-1)*(t^2-(a+b+5)*t+2*a+2*b+4) := by
  have hz := congrArg (fun x : ℝ => x*t) hab
  unfold qoppositeCubic
  nlinarith only [hz]
#print axioms Paper7B4Analytic.qopposite_cubic_single_factor

end Paper7B4Analytic
