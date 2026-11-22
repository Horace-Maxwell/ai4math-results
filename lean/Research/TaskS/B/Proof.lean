import Research.TaskS.B.Upper
import Research.TaskS.B.Lower

namespace TaskS.B.Proof

/-- For each admissible pair of dimensions, all projected bodies cover at the
stated scale and the coordinate projection has exactly that least scale. -/
theorem ConjectureB : Challenge.ConjectureB := by
  intro n i hi hin
  have hu := Upper.upper n i hi hin
  obtain ⟨p, hp, hlo⟩ := exists_projection_lower n i hi hin
  refine ⟨hu, p, hp, ⟨by positivity, hu p hp⟩, ?_⟩
  intro r hr
  exact hlo r hr.1 hr.2

#print axioms ConjectureB

end TaskS.B.Proof
