import Research.Backfill.Paper7.WindowBounds
import Research.Backfill.Paper7.IntegerFactorWindow

set_option autoImplicit false

namespace Paper7SpectralWindow

open BackfillPaper7.Challenge BackfillPaper7.Challenge.Legacy.Algebra

/-- Both spectral inequalities and both integer factorizations in the exact
frozen contract, for the actual Sun graph and the actual cleared determinant. -/
theorem check_SunSpectralWindowAndFactorization :
    BackfillPaper7.Challenge.Legacy.Algebra.SunSpectralWindowAndFactorization := by
  intro b p q hb hn
  have hwin := sun_spectral_window b p q hb hn
  refine ⟨hwin, ?_⟩
  intro hG
  exact sun_integer_factorization b p q hb (fun x hx => (hwin x hx).2) hG

#print axioms Paper7SpectralWindow.check_SunSpectralWindowAndFactorization

#check (check_SunSpectralWindowAndFactorization :
  BackfillPaper7.Challenge.Legacy.Algebra.SunSpectralWindowAndFactorization)

end Paper7SpectralWindow
