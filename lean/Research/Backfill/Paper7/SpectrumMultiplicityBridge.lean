import Research.Backfill.Paper7.SpectrumNullity
import Research.Backfill.Paper7.SpectrumFactorization
import Research.Backfill.Paper7.SpectrumCoverage

set_option autoImplicit false

namespace Paper7Spectrum

theorem check_SpectrumMultiplicityBridge :
    BackfillPaper7.Challenge.Legacy.Algebra.SpectrumMultiplicityBridge := by
  intro V _ _ G _
  refine ⟨spec_card G, mult_eq_rational_nullity G, integral_iff_integerFactorization G, ?_⟩
  intro S _hIntegral hS
  exact sum_mult_of_integer_cover G S hS

#print axioms Paper7Spectrum.check_SpectrumMultiplicityBridge

end Paper7Spectrum
