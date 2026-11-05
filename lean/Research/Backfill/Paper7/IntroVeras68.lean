import Research.Backfill.Paper7.VerasSquares

set_option autoImplicit false

namespace Paper7Veras

open BackfillPaper7.Challenge

theorem veras_sixteen_integral : IsIntegralGraph (sunGraph 4 (VerasSquare 16)) := by
  exact veras_integral_of_squares 16 (by decide) 4 6 (by norm_num) (by norm_num)
#print axioms Paper7Veras.veras_sixteen_integral

theorem check_IntroVeras68 : BackfillPaper7.Challenge.IntroVeras68 := by
  refine ⟨by rw [veras_order], veras_sixteen_integral, ?_⟩
  intro a ha hG
  obtain ⟨u, v, hu, hv⟩ := veras_necessary_squares a ha hG
  have hmin := veras_parameter_minimum a ha u v hu hv
  rw [veras_order]
  omega
#print axioms Paper7Veras.check_IntroVeras68

end Paper7Veras
