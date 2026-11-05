import Research.Backfill.Paper7.HexagonPell
import Research.Backfill.Paper7.HexagonUnicyclic

set_option autoImplicit false

namespace Paper7Hexagon

open BackfillPaper7.Challenge

/-- Exactly the frozen family contract: the attained 42-vertex member,
genuine unbounded six-cycle counterexamples, and the full positive-family minimum. -/
theorem check_IntroHexagonInfiniteFamily :
    BackfillPaper7.Challenge.IntroHexagonInfiniteFamily := by
  refine ⟨hexagon_six_eq, hexagon_six_counterexample,
    by rw [hexagon_order], ?_, ?_⟩
  · intro N
    refine ⟨hexagonPellParameter N, hexagon_pell_positive N, ?_,
      hexagon_unicyclic (hexagonPellParameter N), hexagon_pell_counterexample N⟩
    rw [hexagon_order]
    exact hexagon_pell_orders_unbounded N
  · exact hexagon_order_minimum
#print axioms Paper7Hexagon.check_IntroHexagonInfiniteFamily

end Paper7Hexagon
