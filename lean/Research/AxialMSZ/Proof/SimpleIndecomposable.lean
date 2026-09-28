import Research.AxialMSZ.Challenge

set_option autoImplicit false

namespace CodexAxial
open AxialMSZ.Challenge

section General
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem simple_not_decomposable {μ : V →ₗ[ℚ] V →ₗ[ℚ] V}
    (hs : IsSimpleAlg μ) : ¬ IsDecomposable μ := by
  intro hd
  change sSup {J : Submodule ℚ V | IsIdealIn μ ⊤ J ∧ J ≠ ⊤} = ⊤ at hd
  have hle : sSup {J : Submodule ℚ V | IsIdealIn μ ⊤ J ∧ J ≠ ⊤} ≤ ⊥ := by
    apply sSup_le
    intro J hJ
    have hI : IsIdeal μ J := by
      intro u v hv
      exact hJ.1.2 u (Submodule.mem_top) v hv
    rcases hs.2 J hI with h0 | htop
    · rw [h0]
    · exact (hJ.2 htop).elim
  rw [hd] at hle
  obtain ⟨u,v,hne⟩ := hs.1
  have hu : u = 0 := (Submodule.mem_bot ℚ).mp (hle (Submodule.mem_top))
  exact hne (by simp [hu])

end General

#print axioms simple_not_decomposable

end CodexAxial
