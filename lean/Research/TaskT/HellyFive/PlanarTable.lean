import Research.TaskT.HellyFive.PlanarData

namespace TaskT.HellyFive.PlanarData
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exhaust all label functions on five named points. In the second outcome
every possible counterexample must fill its four colors to capacity. -/
theorem table : ∀ a b c d e : Fin 4, row a b c d e := by decide

theorem classify (f : Fin 5 → UpperFive.Color 2) : classification f := by
  have h := table (pack (f 0)) (pack (f 1)) (pack (f 2)) (pack (f 3)) (pack (f 4))
  have he : ![unpack (pack (f 0)),unpack (pack (f 1)),unpack (pack (f 2)),unpack (pack (f 3)),unpack (pack (f 4))] = f := by
    funext i; fin_cases i <;> exact unpack_pack _
  simpa only [row,he] using h

end TaskT.HellyFive.PlanarData
