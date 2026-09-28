import Research.AxialMSZ.Proof.ExP
import Research.AxialMSZ.Proof.Laws

set_option autoImplicit false

namespace CodexAxial.FromP
open AxialMSZ.Challenge

/-- The known example P witnesses nonsymmetric dominance over a finite symmetric law. -/
theorem check_Dominance_nonsymmetric : Dominance_nonsymmetric := by
  have hP : ExP.Statement := check_RemarkP
  refine ⟨ℚ, inferInstance, (Fin 2 → ℚ), inferInstance, inferInstance,
    FD3, ExP.μ, ExP.X, check_Laws_facts.2.2.2.1, hP.1, ?_⟩
  refine ⟨e 1, ?_, e 0, ?_, hP.2⟩ <;> simp [ExP.X]

#print axioms check_Dominance_nonsymmetric

end CodexAxial.FromP
