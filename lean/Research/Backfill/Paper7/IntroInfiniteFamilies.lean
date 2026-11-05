import Research.Backfill.Paper7.VerasPell
import Research.Backfill.Paper7.VerasUnicyclic

set_option autoImplicit false

namespace Paper7Veras

open BackfillPaper7.Challenge

/-- Unbounded orders of genuine integral unicyclic Sun graphs, with every
condition of the original introductory existence statement retained. -/
theorem check_IntroInfiniteFamilies : BackfillPaper7.Challenge.IntroInfiniteFamilies := by
  intro N
  refine ⟨4, VerasSquare (pellParameter N), by decide, ?_, ?_,
    veras_unicyclic (pellParameter N), pell_veras_integral N⟩
  · rw [veras_pendant_count]
    have h := pell_parameter_positive N
    omega
  · rw [veras_order]
    exact pell_orders_unbounded N
#print axioms Paper7Veras.check_IntroInfiniteFamilies

end Paper7Veras
