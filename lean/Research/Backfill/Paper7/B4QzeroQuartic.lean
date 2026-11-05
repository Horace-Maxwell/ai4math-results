import Research.Backfill.Paper7.B4PerronBounds

/-! Source-only identities for arbitrary nonnegative q=0 parameters.
No parameter table, positive-support coverage, or classification is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper7B4Analytic
open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra
open scoped BigOperators Matrix Classical

def qzeroQuartic (a b c d t : ℝ) : ℝ :=
  (t-a)*(t-b)*(t-c)*(t-d)-t*(2*t-a-c)*(2*t-b-d)
#print axioms Paper7B4Analytic.qzeroQuartic

theorem qzero_four_trace_identity (a b c d m : ℝ) (hm : m ≠ 0) :
    m^4*((realFourProduct (m-a/m) (m-b/m) (m-c/m) (m-d/m)).trace-2) =
      qzeroQuartic a b c d (m^2) := by
  rw [real_four_trace]
  unfold qzeroQuartic
  field_simp [hm]
  ring
#print axioms Paper7B4Analytic.qzero_four_trace_identity

theorem qzero_ordinary_spec_iff (p : Fin 4 → ℕ) (m : ℝ)
    (hmn : m ≠ -1) (hm0 : m ≠ 0) (hm1 : m ≠ 1) :
    m ∈ spec (SG 4 p (fun _ => 0)) ↔
      qzeroQuartic (p 0) (p 1) (p 2) (p 3) (m^2) = 0 := by
  have he : m^4*((Mono 4 p (fun _ => 0) m).trace-2) =
      qzeroQuartic (p 0) (p 1) (p 2) (p 3) (m^2) := by
    rw [mono_four_product]
    simpa [fk] using qzero_four_trace_identity (p 0) (p 1) (p 2) (p 3) m hm0
  rw [← ordinary_trace_iff_spec p (fun _ => 0) m hmn hm0 hm1]
  constructor
  · intro ht
    rw [ht] at he
    nlinarith only [he]
  · intro hz
    rw [hz] at he
    have hd : (Mono 4 p (fun _ => 0) m).trace-2 = 0 :=
      (mul_eq_zero.mp he).resolve_left (pow_ne_zero 4 hm0)
    linarith
#print axioms Paper7B4Analytic.qzero_ordinary_spec_iff

theorem qzero_identity_parameter_data (p : Fin 4 → ℕ) (m : ℕ) (hm : 0 < m)
    (hid : Mono 4 p (fun _ => 0) m = 1) :
    p 0+p 2 = 2*m^2 ∧ p 1+p 3 = 2*m^2 ∧
      ((p 0 = m^2 ∧ p 2 = m^2) ∨ (p 1 = m^2 ∧ p 3 = m^2)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hprod : realFourProduct ((m : ℝ)-(p 0 : ℝ)/m) ((m : ℝ)-(p 1 : ℝ)/m)
      ((m : ℝ)-(p 2 : ℝ)/m) ((m : ℝ)-(p 3 : ℝ)/m) = 1 := by
    simpa [mono_four_product,fk] using hid
  obtain ⟨h02,h13,h01⟩ := real_four_identity_data _ _ _ _ hprod
  have he02 : (m : ℝ)*(((m : ℝ)-(p 0 : ℝ)/m)+((m : ℝ)-(p 2 : ℝ)/m)) =
      2*(m : ℝ)^2-p 0-p 2 := by field_simp [hm0]; ring
  have he13 : (m : ℝ)*(((m : ℝ)-(p 1 : ℝ)/m)+((m : ℝ)-(p 3 : ℝ)/m)) =
      2*(m : ℝ)^2-p 1-p 3 := by field_simp [hm0]; ring
  have he01 : (m : ℝ)^2*(((m : ℝ)-(p 0 : ℝ)/m)*((m : ℝ)-(p 1 : ℝ)/m)) =
      ((m : ℝ)^2-p 0)*((m : ℝ)^2-p 1) := by field_simp [hm0]
  rw [h02,mul_zero] at he02
  rw [h13,mul_zero] at he13
  rw [h01,mul_zero] at he01
  have hs02R : (p 0 : ℝ)+p 2 = 2*(m : ℝ)^2 := by linarith
  have hs13R : (p 1 : ℝ)+p 3 = 2*(m : ℝ)^2 := by linarith
  have hs02 : p 0+p 2 = 2*m^2 := by exact_mod_cast hs02R
  have hs13 : p 1+p 3 = 2*m^2 := by exact_mod_cast hs13R
  refine ⟨hs02,hs13,?_⟩
  rcases mul_eq_zero.mp he01.symm with h0 | h1
  · have hp0R : (p 0 : ℝ) = (m : ℝ)^2 := by linarith
    have hp0 : p 0 = m^2 := by exact_mod_cast hp0R
    exact Or.inl ⟨hp0,by omega⟩
  · have hp1R : (p 1 : ℝ) = (m : ℝ)^2 := by linarith
    have hp1 : p 1 = m^2 := by exact_mod_cast hp1R
    exact Or.inr ⟨hp1,by omega⟩
#print axioms Paper7B4Analytic.qzero_identity_parameter_data

theorem qzero_quartic_factor_even (M b d t : ℝ) (hs : b+d = 2*M) :
    qzeroQuartic M b M d t = (t-M)^2*(t^2-(2*M+4)*t+b*d) := by
  have hd : d = 2*M-b := by linarith
  rw [hd]
  unfold qzeroQuartic
  ring
#print axioms Paper7B4Analytic.qzero_quartic_factor_even

theorem qzero_quartic_factor_odd (M a c t : ℝ) (hs : a+c = 2*M) :
    qzeroQuartic a M c M t = (t-M)^2*(t^2-(2*M+4)*t+a*c) := by
  have hc : c = 2*M-a := by linarith
  rw [hc]
  unfold qzeroQuartic
  ring
#print axioms Paper7B4Analytic.qzero_quartic_factor_odd

end Paper7B4Analytic
