import Research.Backfill.Paper7.SunSpectralWindowAndFactorization
import Research.Backfill.Paper7.SpectrumCoverage

set_option autoImplicit false

namespace Paper7NullitySieve

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- Every real spectral entry of an integral Sun in the frozen size range
is an integer in the actual window used by the sieve. -/
theorem integral_spectrum_mem_window (b : ℕ) (p q : Fin b → ℕ)
    (hb : 3 ≤ b) (hn : nOf b p q ≤ 49) (hG : IsIntegralGraph (SG b p q))
    (x : ℝ) (hx : x ∈ spec (SG b p q)) :
    ∃ m ∈ integerWindow 9, x = (m : ℝ) := by
  obtain ⟨m, rfl⟩ := Paper7Moments.integral_spec_entry (SG b p q) hG x hx
  have habs :=
    ((Paper7SpectralWindow.check_SunSpectralWindowAndFactorization b p q hb hn).1
      (m : ℝ) hx).2
  refine ⟨m, ?_, rfl⟩
  have hlo : (-10 : ℤ) < m := by exact_mod_cast (abs_lt.mp habs).1
  have hhi : m < (10 : ℤ) := by exact_mod_cast (abs_lt.mp habs).2
  change m ∈ Finset.Icc (-(9 : ℤ)) (9 : ℤ)
  rw [Finset.mem_Icc]
  omega

#print axioms Paper7NullitySieve.integral_spectrum_mem_window

/-- The exact frozen sum of actual eigenvalue multiplicities. -/
theorem check_IntegralMultiplicitySum :
    BackfillPaper7.Challenge.Legacy.Algebra.IntegralMultiplicitySum := by
  intro b p q hb hn hG
  calc
    (∑ m ∈ integerWindow 9, mult (SG b p q) (m : ℝ)) =
        Fintype.card (SunV b (pq b p q)) :=
      Paper7Spectrum.sum_mult_of_integer_cover (SG b p q) (integerWindow 9)
        (integral_spectrum_mem_window b p q hb hn hG)
    _ = nOf b p q := Paper7Setup.sg_order b p q

#print axioms Paper7NullitySieve.check_IntegralMultiplicitySum

#check (check_IntegralMultiplicitySum :
  BackfillPaper7.Challenge.Legacy.Algebra.IntegralMultiplicitySum)

end Paper7NullitySieve
