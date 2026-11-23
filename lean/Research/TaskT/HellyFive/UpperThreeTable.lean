import Research.TaskT.HellyFive.UpperThreeData

namespace TaskT.HellyFive.UpperFive
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Only sorted encodings need evaluation because the five interior-or-boundary
nonvertices are an unordered set. All checks use Lean's kernel. -/
theorem sorted_table :
    ∀ a b c d e : Fin 8, a ≤ b → b ≤ c → c ≤ d → d ≤ e → boundCode a b c d e := by
  decide

end TaskT.HellyFive.UpperFive
